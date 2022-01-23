{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE QuasiQuotes           #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeFamilies          #-}

import Yesod
import Data.Text
import Data.List.Split
import Text.Lucius (CssUrl, luciusFile, luciusFileReload, renderCss)
import SofiaCommandParser
import SofiaTree

data App = App

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

getHomeR :: Handler Html
getHomeR = postHomeR

strProoflines :: Proof -> [Text]
strProoflines p = case p of
                PListEnd -> []
                _        -> Prelude.map pack $
                                (Data.List.Split.splitOn "\n" $ show $ p) ++
                                [""]

helpText = $(whamletFile "help.hamlet")

postHomeR :: Handler Html
postHomeR = do
    pg   <- runInputPost $ iopt textField "page"
    hst  <- runInputPost $ iopt textField "history"
    msg  <- runInputPost $ iopt textField "message"
    let history = case hst of
            Nothing -> []
            Just h  -> unpack h
    let message = case msg of
            Nothing -> []
            Just m  -> unpack m
    let oldpage = case pg of
            Nothing -> []
            Just p  -> unpack p
    let newpage = case message of
            ":help" -> "help"
            ":db"   -> "db"
            _       -> ""
    let page = if newpage == []
               then
                    if oldpage == []
                    then "help"
                    else oldpage
               else newpage
    let command = case newpage of
            []  -> message
            _   -> []
    let errorSyntax = if command == []
                      then []
                      else validateSyntax command
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
                Here will be a table.
      <br>
      <div #cmd>
         <input type=hidden name=page value=#{page}>
         <input #prompt type=text name=message
            placeholder="Type Command ..." size="80" autofocus>
     |] 

main :: IO ()
main = warp 3000 App
