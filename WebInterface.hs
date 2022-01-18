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
    hst <- runInputPost $ iopt textField "history"
    msg <- runInputPost $ iopt textField "message"
    let history = case hst of
            Nothing -> []
            Just h  -> unpack h
    let errorSyntax = case msg of
            Nothing -> []
            Just m  -> validateSyntax $ unpack m
    let message = case msg of
            Nothing -> []
            Just m  -> unpack m
    let newhistory = if or [errorSyntax /= [], message == []]
                     then history
                     else
                        if history == [] then message
                        else (history ++ ";" ++ message)
    let newhistorylist = case newhistory == [] of
            True  -> []
            False -> (Data.List.Split.splitOn ";" newhistory)
    let historylist = case history == [] of
            True  -> []
            False -> (Data.List.Split.splitOn ";" history)
    let oldproof = evalList historylist
    let proof    = evalList newhistorylist
    let lines    = strProoflines proof
    let valid    = errorSyntax == []
    let errorSemantics = if and [errorSyntax == [], message /= []]
                         then validateSemantics message oldproof
                         else []
    let errorMsgs = errorSyntax ++ errorSemantics
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
            ^{helpText}
      <br>
      <div #cmd>
         <input #prompt type=text name=message
            placeholder="Type Command ..." size="80" autofocus>
     |] 

main :: IO ()
main = warp 3000 App
