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
                        <b>Error: Invalid command.</b>
                $nothing
                    $maybe h <- hst
                        $forall line <- genProof (unpack h) []
                            #{line}<br>
                        <input type=hidden name=history value="#{h}">
                    $nothing
                        Hello! You can start creating a proof.
                <br><br>
                <input type=text name=message>
                <button>Go
        |]

main :: IO ()
main = warp 3000 App
