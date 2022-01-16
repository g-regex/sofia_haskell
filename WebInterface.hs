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

helpText =
    [hamlet|
        Available commands:
         <ul>
          <li><code>assume <var>String</var></code><br>
            (e.g. <code>assume "[x]"</code>)<br>
            Parameters:
            <ul>
                <li>A Sofia expression.
          <li><code>restate <var>[(Int, Int)] [String]</var></code><br>
            (e.g. <code>restate [(1,1), (1,2)] ["x"]</code>)<br>
            Parameters:
            <ul>
                <li>List of positions (line, column) of atoms.
                <li>List of new names of free variables to be renamed.
          <li><code>synapsis</code>
          <li><code>apply <var>Int [(Int, Int)] Int</var></code><br>
            (e.g. <code>apply 2 [(1,1), (1,2)] 3</code>)<br>
            Parameters:
            <ul>
                <li>The line of the implication to be applied.
                <li>List of positions (line, column) of atoms for replacements.
                <li>The column of the implication to be applied.
          <li><code>rightsub <var>Int Int [Int] Int Int</var></code><br>
            (e.g. <code>rightsub 2 3 [1, 2] 1 4</code>)<br>
            Parameters:
            <ul>
                <li>The line of the equality.
                <li>The line of the statement.
                <li>A list of indices of the atoms which are to be substituted.
                <li>The column of the equality.
                <li>The column of the statement.
          <li><code>leftsub <var>Int Int [Int] Int Int</var></code><br>
            (e.g. <code>leftsub 2 3 [1, 2] 1 4</code>)<br>
            The parameters are the same as for <code>rightsub</code>.
    |]

postHomeR :: Handler Html
postHomeR = do
    hst <- runInputPost $ iopt textField "history"
    msg <- runInputPost $ iopt textField "message"
    defaultLayout
     [whamlet|
     <form method=post action=@{HomeR}>
      <table width="100%" cellspacing="0" border="1" #tbl>
         <tr .row>
          <td #proof valign="top" width="50%">
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
