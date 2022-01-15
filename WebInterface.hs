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
/set-message SetMessageR POST
|]

instance Yesod App where
    defaultLayout widget = do
        pc <- widgetToPageContent widget
        withUrlRenderer
            [hamlet|
                $doctype 5
                <html>
                    <head>
                        <title>#{pageTitle pc}
                        ^{pageHead pc}
                    <body>
                        ^{pageBody pc}
            |]

instance RenderMessage App FormMessage where
    renderMessage _ _ = defaultFormMessage

getHomeR :: Handler Html
getHomeR = do
    mmsg <- getMessage
    defaultLayout
        [whamlet|
            $maybe msg <- mmsg
                <p>Your message was: #{msg}
            <form method=post action=@{HomeR}>
                My message is: #
                <input type=hidden name=history>
                <input type=text name=message>
                <button>Go
        |]

genProof :: Text -> Text -> [Text]
genProof h msg = Prelude.map pack $
                 Data.List.Split.splitOn "\n" $ show $ evalList $
                 (Data.List.Split.splitOn ";" (unpack h)) ++ [unpack msg]

postHomeR :: Handler Html
postHomeR = do
    hst <- runInputPost $ iopt textField "history"
    msg <- runInputPost $ ireq textField "message"
    defaultLayout
        [whamlet|
            <p>Your message was:<br>
                $maybe h <- hst
                    $forall line <- genProof h msg
                        #{line}<br>
                $nothing
                    #{pack (show $ evalList [unpack msg])}<br>
            <form method=post action=@{HomeR}>
                My message is:<br>
                $maybe h <- hst
                    <input type=text name=history value="#{h};#{msg}">
                $nothing
                    <input type=text name=history value="#{msg}">
                <br>
                <input type=text name=message>
                <button>Go
        |]

postSetMessageR :: Handler ()
postSetMessageR = do
    msg <- runInputPost $ ireq textField "message"
    setMessage $ toHtml msg
    redirect HomeR

main :: IO ()
main = warp 3000 App
