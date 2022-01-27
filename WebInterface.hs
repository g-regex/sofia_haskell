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
import SofiaAxiomParser
import SofiaTree
import Parsing
import ListHelpers
import Sofia -- for validateAxiomParams

share [mkPersist sqlSettings, mkMigrate "migrateAll"] [persistLowerCase|
AxiomBuilder
    rubric    String
    name      String
    schema    String
    params    Int
    desc      String
    hist      String
    Axiom     rubric name
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

axEmpty = AxiomBuilder "" "" "" 0 ""

linesFromHist :: [String] -> [ProofLine]
linesFromHist hist = toListFromProof $ evalList hist

propFromLines :: [ProofLine] -> (String, String)
propFromLines pl = ("{`" ++ pstr ++ "`, 0, []}", "Postulate: " ++ pstr)
    where
        t     = treeFromLn $ Prelude.head pl
        t'    = treeFromLn $ Prelude.last pl
        pstr  = show (treeSTMT ([t, treeIMP, t']))

postHomeR :: Handler Html
postHomeR = do
    pg   <- runInputPost $ iopt textField "page"
    msg  <- runInputPost $ iopt textField "message"
    hst  <- runInputPost $ iopt textField "history"
    let history = case hst of
            Nothing -> []
            Just h  -> unpack h
    let historylist = case history == [] of
            True  -> []
            False -> (Data.List.Split.splitOn ";" history)
    let oldpage = case pg of
            Nothing -> []
            Just p  -> unpack p
    case msg of
        Nothing -> mainHandler history [] "" oldpage
        Just "" -> mainHandler history [] "" oldpage
        Just m -> do
            let message = unpack m
            let metacmd = if Prelude.head message == ':'
                          then Prelude.tail message
                          else ""
            let metaParse = parse sMeta metacmd
            let pErr = parsingErrors metaParse
            case pErr of
                [] -> case fst $ fst $ Prelude.head metaParse of
                        "postulate" ->
                            if Prelude.length historylist <= 1
                            then mainHandler history ["Proof not long enough."]
                                             "" oldpage
                            else do
                                let pLines = linesFromHist historylist
                                if (numDepth $ Prelude.last pLines) /= 0
                                then mainHandler
                                             history
                                             ["Not at depth 0."]
                                             ""
                                             oldpage
                                else do
                                    let newName = Prelude.head
                                           (snd $ fst $ Prelude.head metaParse)
                                    axiom <- runDB $ getBy (Axiom "User" newName)
                                    case axiom of
                                        Nothing -> do
                                            let prop = propFromLines pLines
                                            runDB $ insert $
                                              AxiomBuilder "User"
                                                           newName
                                                           (fst prop)
                                                           0
                                                           (snd prop)
                                                           history
                                            mainHandler history [] "" oldpage
                                        _       ->
                                            mainHandler
                                              history
                                              ["Name not available"]
                                              ""
                                              oldpage
                        "load"    -> do
                                    let index = read (Prelude.head $ snd $ fst $
                                            Prelude.head metaParse) ::
                                            GHC.Int.Int64
                                    axiom <- runDB $ get (toSqlKey index ::
                                            (Key AxiomBuilder))
                                    case axiom of
                                        Nothing ->
                                            mainHandler
                                              history
                                              ["Entry not found in database."]
                                              ""
                                              oldpage
                                        Just ax -> do
                                            let loadhist = axiomBuilderHist ax
                                            if loadhist == ""
                                            then mainHandler
                                                  history
                                                  ["No history for this entry."]
                                                  ""
                                                  oldpage
                                            else mainHandler
                                                  loadhist
                                                  []
                                                  ""
                                                  oldpage
                        "help"    -> mainHandler history [] "" "help"
                        "theory"  -> mainHandler history [] "" "theory"
                        "new"     -> mainHandler "" [] "" oldpage
                        "back"    -> mainHandler hpop [] "" oldpage
                            where
                             hpop = join ";" $ pop historylist
                        _  -> mainHandler history [] message oldpage
                _  -> mainHandler history [] message oldpage

tableView newhistory valid pLines page theory errorMsgs =
    defaultLayout
     [whamlet|
     <form #theform method=post action=@{HomeR}>
      <table width="100%" cellspacing="10" border="0" #outertable>
       <tbody>
        <tr #outertabletoptr>
         <td #outertabletoptd>
          <table width="100%" cellspacing="0" border="1" #tbl>
           <tbody>
            <tr .row>
             <td #proof valign="top" width="50%">
              ^{proofWidget newhistory valid pLines errorMsgs}
             <td #info valign="top" width="50%">
              ^{infoWidget page theory}
        <tr #outertablebottom>
         <td>
          <div #cmd>
             <input #prompt type=text name=message
                placeholder="Type Command ..." size="80" autofocus>
     |]

divView newhistory valid pLines page theory errorMsgs =
    defaultLayout
     [whamlet|
     <form #theform method=post action=@{HomeR}>
      <div #tablediv>
         <div #proof .tddiv>
          ^{proofWidget newhistory valid pLines errorMsgs}
         <div #info .tddiv>
          ^{infoWidget page theory}
      <br>
      <div #cmd>
         <input #prompt type=text name=message
            placeholder="Type Command ..." size="80" autofocus>
     |]

proofWidget newhistory valid pLines errorMsgs=
    [whamlet|
      <div .inside1>
       <div .inside2>
            $if or [newhistory /= [], not valid]
                $forall line <- pLines
                    #{line}<br>
                <input type=hidden name=history
                   value="#{pack newhistory}">
                $forall line <- Prelude.map pack errorMsgs
                    <b>Error: #{line}<br>
            $else
                Hello! You can start creating a proof.
    |]

infoWidget page theory =
     [whamlet|
      <div .inside1>
       <div .inside2>
        <input type=hidden name=page value=#{page}>
        $if page == "help"
            ^{helpText}
        $else
            Type <code><kbd>:help</kbd></code> to get help.<br><br>
            <table #theory>
                <tr>
                 <th>ID
                 <th>Name
                 <th>Params
                 <th>Description
                $forall Entity id ab <- theory
                    <tr>
                        <td valign="top">#{fromSqlKey id}
                        <td valign="top">
                            $if axiomBuilderRubric ab == ""
                                #{axiomBuilderName ab}
                            $else
                                #{axiomBuilderRubric ab}:
                                #{axiomBuilderName ab}
                        <td valign="top">
                            #{axiomBuilderParams ab}
                        <td valign="top">
                         $if axiomBuilderRubric ab == "Example"
                          Type
                          <code>
                           <kbd>:load
                           #{fromSqlKey id} 
                          to load this example.<br><br>
                         $else
                          $if validateSyntax sDesc (axiomBuilderDesc ab) == []
                           $forall d <- descParse (axiomBuilderDesc ab)
                            $if snd d /= ""
                                #{fst d}<code>#{snd d}</code>
                            $else 
                                #{fst d}
                          $else
                            #{axiomBuilderDesc ab}
     |]

mainHandler :: String -> [String] -> String -> String -> Handler Html
mainHandler history errorMeta message page = do
    theory <- runDB $ selectList [] []
    let isRecall = validateSyntax sRecallRaw message == []
    let recall = if isRecall
                 then recallRawParse message
                 else (0, [])
    axiom <- runDB $ get (toSqlKey
                          (read $ show $ fst recall :: GHC.Int.Int64) -- ugly
                          :: (Key AxiomBuilder)
                         )
    let dbError = case axiom of
            Nothing -> ["Axiom not found in theory database."]
            Just ax ->  if params == Prelude.length (snd recall)
                        then showErrors $ validateAxiomParams $ snd recall
                        else ["Incorrect number of parameters."]
                        where
                            params = axiomBuilderParams ax
    let recallcmd = case axiom of
            Nothing -> []
            Just ax -> if dbError == []
                       then "recall (\"" ++ show result ++ "\",\"" ++ axName
                         ++ "\")"
                       else []
                       where 
                           strSchema = axiomBuilderSchema ax
                           schema    = axiomParse strSchema
                           args      = snd recall
                           axName    = axiomBuilderRubric ax ++ ": " ++
                                        axiomBuilderName ax
                           result    = axiomBuild schema args
    let command =  if isRecall
                   then recallcmd
                   else message
    let errorSyntax = if command == []
                      then []
                      else validateSyntax sCommand command
    let historylist = case history == [] of
            True  -> []
            False -> (Data.List.Split.splitOn ";" history)
    let oldproof = evalList historylist
    let errorSemantics = if and [errorSyntax == [],
                                 or [command /= [], isRecall]]
                         then 
                            if isRecall 
                            then dbError
                            else validateSemantics command oldproof
                         else []
    let errorMsgs = errorMeta ++ errorSyntax ++ errorSemantics
    let newhistory = if or [errorMsgs /= [], command == []]
                     then history
                     else
                        if history == [] then command
                        else (history ++ ";" ++ command)
    let newhistorylist = case newhistory == [] of
            True  -> []
            False -> (Data.List.Split.splitOn ";" newhistory)
    let proof    = evalList newhistorylist
    let pLines    = strProoflines proof
    let valid    = errorMsgs == []
    divView newhistory valid pLines page theory errorMsgs
 
openConnectionCount :: Int
openConnectionCount = 10

main :: IO ()
main = runStderrLoggingT $ withSqlitePool "theory.db" openConnectionCount
    $ \pool -> liftIO $ do
        warp 3000 $ App pool
