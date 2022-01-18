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

genProof :: String -> [String] -> [Text]
genProof h ms = Prelude.map pack $
                 Data.List.Split.splitOn "\n" $ show $ evalList $
                 (Data.List.Split.splitOn ";" h) ++ ms

helpText = $(whamletFile "help.hamlet")

postHomeR :: Handler Html
postHomeR = do
    hst <- runInputPost $ iopt textField "history"
    msg <- runInputPost $ iopt textField "message"
    let errorMsgs = case msg of
            Nothing -> []
            Just m  -> validateCmd $ unpack m
    let valid = errorMsgs == []
    defaultLayout
     [whamlet|
     <form method=post action=@{HomeR}>
      <table width="100%" cellspacing="0" border="1" #tbl>
         <tr .row>
          <td #proof valign="top" width="50%">
           <div .inside>
             $maybe m <- msg
                 $if valid
                     $maybe h <- hst
                             $forall line <- genProof (unpack h) [unpack m]
                                 #{line}<br>
                             <input type=hidden name=history value="#{h};#{m}">
                     $nothing
                         #{pack (show $ evalList [unpack m])}<br>
                         <input type=hidden name=history value="#{m}">
                 $else
                     $maybe h <- hst
                         $forall line <- genProof (unpack h) []
                             #{line}<br>
                         <input type=hidden name=history value="#{h}"><br>
                     $forall line <- Prelude.map pack errorMsgs
                         <b>Error: #{line}<br>
             $nothing
                 $maybe h <- hst
                     $forall line <- genProof (unpack h) []
                         #{line}<br>
                     <input type=hidden name=history value="#{h}">
                 $nothing
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
