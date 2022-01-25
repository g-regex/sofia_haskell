{-# LANGUAGE EmptyDataDecls             #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE QuasiQuotes                #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE ViewPatterns               #-}

{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}

import Yesod
import Yesod.Core.Types
import GHC.Int
import Database.Persist.Sqlite
import Control.Monad.Trans.Resource (runResourceT)
import Control.Monad.Logger (runStderrLoggingT)

import Data.Text
import Data.List.Split
import Text.Lucius (CssUrl, luciusFile, luciusFileReload, renderCss)
import SofiaCommandParser
import SofiaTree

share [mkPersist sqlSettings, mkMigrate "migrateAll"] [persistLowerCase|
AxiomBuilder
    name      String
    schema    String
    params    Int
    desc      String
    AxiomName name
    deriving Show
|]

data App = App ConnectionPool

mkYesod "App" [parseRoutes|
/            HomeR       GET POST
|]

instance Yesod App where
    defaultLayout widget = do
        pc <- widgetToPageContent $ do
            widget
            toWidget $(luciusFile "style.lucius")
        withUrlRenderer
            [hamlet|
                $doctype 5
                <html>
                    <head>
                        <title>#{pageTitle pc}
                        ^{pageHead pc}
                    <body>
                        <div #mainBox>
                            ^{pageBody pc}
            |]

instance RenderMessage App FormMessage where
    renderMessage _ _ = defaultFormMessage

instance YesodPersist App where
    type YesodPersistBackend App = SqlBackend

    runDB action = do
        App pool <- getYesod
        runSqlPool action pool

getHomeR :: Handler Html
getHomeR = postHomeR

strProoflines :: Proof -> [Text]
strProoflines p = case p of
                PListEnd -> []
                _        -> Prelude.map pack $
                                (Data.List.Split.splitOn "\n" $ show $ p) ++
                                [""]

helpText = $(whamletFile "help.hamlet")

axEmpty = AxiomBuilder "" "" 0 ""

{-dbTranslate :: String -> String
dbTranslate cs =
    if validateSyntax sRecallRaw cs == []
    then "recall " ++ (axiomBuilderSchema axiom)
    else cs
    where
        args   = recallRawParse cs
        axiomH = runDB $ get (toSqlKey 1 :: (Key AxiomBuilder))
        axiom  = case axiomH of
                    HandlerFor Nothing -> axEmpty
                    HandlerFor (Just ax) -> ax-}

postHomeR :: Handler Html
postHomeR = do
    pg   <- runInputPost $ iopt textField "page"
    hst  <- runInputPost $ iopt textField "history"
    msg  <- runInputPost $ iopt textField "message"
    theory <- runDB $ selectList [AxiomBuilderParams >. 0] []
    -- axiom  <- runDB $ get (toSqlKey 1 :: (Key AxiomBuilder))
    let history = case hst of
            Nothing -> []
            Just h  -> unpack h
    let message = case msg of
            Nothing -> []
            Just m  -> unpack m
    let oldpage = case pg of
            Nothing -> []
            Just p  -> unpack p
    let newpage = case message of       -- defining navigation commands
            ":help" -> "help"
            ":db"   -> "db"
            _       -> ""
    let page = if newpage == []
               then
                    if oldpage == []
                    then "help"         -- default page
                    else oldpage
               else newpage
    let isRecall = validateSyntax sRecallRaw message == []
    let recall = if isRecall
                 then recallRawParse message
                 else (0, [])
    axiom  <- runDB $ get (toSqlKey
                           (read $ show $ fst recall :: GHC.Int.Int64) -- ugly
                           :: (Key AxiomBuilder)
                          )
    let command = case newpage of       -- only process non-navigation cmds
            []  -> message
            _   -> []
    let errorSyntax = if command == []
                      then []
                      else validateSyntax sCommand command
    let historylist = case history == [] of
            True  -> []
            False -> (Data.List.Split.splitOn ";" history)
    let oldproof = evalList historylist
    let errorSemantics = if and [errorSyntax == [], command /= []]
                         then validateSemantics command oldproof
                         else []
    let errorMsgs = errorSyntax ++ errorSemantics
    let newhistory = if or [errorMsgs /= [], command == []]
                     then history
                     else
                        if history == [] then command
                        else (history ++ ";" ++ command)
    let newhistorylist = case newhistory == [] of
            True  -> []
            False -> (Data.List.Split.splitOn ";" newhistory)
    let proof    = evalList newhistorylist
    let lines    = strProoflines proof
    let valid    = errorMsgs == []
    defaultLayout
     [whamlet|
     $maybe ax <- axiom
        #{axiomBuilderName ax}
     <form method=post action=@{HomeR}>
      <table width="100%" cellspacing="0" border="1" #tbl>
         <tr .row>
          <td #proof valign="top" width="50%">
           <div .inside>
                 $if or [newhistory /= [], not valid]
                     $forall line <- lines
                         #{line}<br>
                     <input type=hidden name=history
                        value="#{pack newhistory}">
                     $forall line <- Prelude.map pack errorMsgs
                         <b>Error: #{line}<br>
                 $else
                     Hello! You can start creating a proof.
             <br>
          <td #info valign="top" width="50%">
           <div .inside>
            $if page == "help"
                ^{helpText}
            $else
                <table>
                    <tr>
                     <td>ID
                     <td>Name
                     <td>Params
                     <td>Description
                    $forall Entity id axiom_builder <- theory
                        <tr>
                            <td>#{fromSqlKey id}
                            <td>#{axiomBuilderName axiom_builder}
                            <td>#{axiomBuilderParams axiom_builder}
                            <td>#{axiomBuilderDesc axiom_builder}
      <br>
      <div #cmd>
         <input type=hidden name=page value=#{page}>
         <input #prompt type=text name=message
            placeholder="Type Command ..." size="80" autofocus>
     |] 

openConnectionCount :: Int
openConnectionCount = 10

main :: IO ()
main = runStderrLoggingT $ withSqlitePool "theory.db" openConnectionCount
    $ \pool -> liftIO $ do
        warp 3000 $ App pool
