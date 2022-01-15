{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE QuasiQuotes           #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeFamilies          #-}
import Yesod
import Data.Text
import Data.List.Split
import SofiaCommandParser

data App = App

mkYesod "App" [parseRoutes|
/            HomeR       GET POST
|]

instance Yesod App where
    defaultLayout widget = do
        pc <- widgetToPageContent $ do
            widget
            toWidget [lucius|
                     body {
                          font-family: verdana;
                          background: #181a1b;
                          color: white;
                          font-size: 12pt;
                     }
                     #mainBox {
                       border-radius: 25px;
                       padding: 20px;
                       margin: 50px;
                     }

                     .column {
                         float: left;
                         width: 50%;
                         flex: 1;
                     }

                     .row {
                         margin: 10px;
                         display: flex;
                     }

                     #proof {
                         border-top-left-radius: 25px;
                         border-bottom-left-radius: 25px;
                         background: #3e4446;
                     }

                     #info {
                         border-top-right-radius: 25px;
                         border-bottom-right-radius: 25px;
                         background: #35393b;
                     }

                     .inside {
                         margin: 20px;
                     }

                     #cmd {
                       border-radius: 25px;
                       background: #3e4446;
                       padding: 20px;
                       margin: 10px;
                     }

                     #prompt {
                       width: 100%;
                     }

                     input[type=text] {
                          border: none;
                          background: #3e4446;
                          border-bottom: 2px solid darkgrey;
                          color: white;
                          font-size: 12pt;
                     }

                     input[type=text]:focus {
                          border-bottom: 2px solid grey;
                          outline: none;
                     }
                    |]
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

postHomeR :: Handler Html
postHomeR = do
    hst <- runInputPost $ iopt textField "history"
    msg <- runInputPost $ iopt textField "message"
    defaultLayout
     [whamlet|
     <form method=post action=@{HomeR}>
         <div .row>
          <div .column #proof>
           <div .inside>
             $maybe m <- msg
                 $if validateCmd $ unpack m
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
                         <input type=hidden name=history value="#{h}">
                     <br><b>Error: Invalid command.</b>
             $nothing
                 $maybe h <- hst
                     $forall line <- genProof (unpack h) []
                         #{line}<br>
                     <input type=hidden name=history value="#{h}">
                 $nothing
                     Hello! You can start creating a proof.
             <br>
          <div .column #info>
           <div .inside>
            blabla
         <div #cmd>
             <input #prompt type=text name=message
                placeholder="Type Command ..." autofocus>
     |]

main :: IO ()
main = warp 3000 App
