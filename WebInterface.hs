{-
The SOFiA proof assistant.
Copyright (C) 2022  Gregor Feierabend

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program.  If not, see <https://www.gnu.org/licenses/>.
-}

{-|
Module      : WebInterface
Description : Part of the Sofia proof assistant.
Copyright   : Gregor Feierabend
License     : GNU General Public License v3 (GPLv3)
Maintainer  : Gregor Feierabend
Stability   : experimental
Portability : POSIX
-}

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

{-# OPTIONS_HADDOCK prune #-}

module WebInterface (
        -- * Helper functions
        strProoflines,
        linesFromHist,
        propFromLines,

        -- * Yesod Widgets
        helpText,
        proofWidget,
        infoWidget,

        -- * Yesod Handlers
        getHomeR,
        postHomeR,
        mainHandler,
        metaHandler,
        divView

        ) where

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
/                      HomeR       GET POST
/Sofia-Haskell.pdf     DocR        GET
/theory.db3            DataR       GET
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

openConnectionCount :: Int
openConnectionCount = 10

main :: IO ()
main = runStderrLoggingT $ withSqlitePool "theory.db3" openConnectionCount
    $ \pool -> liftIO $ do
        warp 3000 $ App pool

---------------------------------- Helpers -------------------------------------

-- |Converts a `Proof` into a list containing for each `ProofLine` a `Text`
-- representation.
strProoflines ::    Proof   -- ^The `Proof` to be converted.
                 -> [Text]  -- ^The resulting list of `Text` representations.
strProoflines p = case p of
                PListEnd -> []
                _        -> Prelude.map pack $
                                (Data.List.Split.splitOn "\n" $ show $ p) ++
                                [""]

-- |Given a list of user inferface commands the resulting `Proof` is calculated
-- and then the corresponding list of `ProofLine`s is returned.
linesFromHist ::    [String]        -- ^A list of user interface commands.
                 -> [ProofLine]     -- ^The resulting list of `ProofLine`s.
linesFromHist hist = toListFromProof $ evalList hist

-- |Given a list of `ProofLine`s, a pair containing two `String`s is returned.
-- The first `String` is a representation of the `AxiomSchema` (see
-- `SofiaAxiomParser` module) generating the `Postulate` resulting
-- from the given proof. The second `String` is a simple description of the
-- `Postulate` based on the `String` representation of the underlying
-- `SofiaTree`.
propFromLines ::    [ProofLine]         -- ^A list of `ProofLine`s constituting
                                        --  a proof.
                 -> (String, String)    -- ^The resulting pair containing
                                        --  information to be stored in a
                                        --  database.
propFromLines pl = ("{`" ++ pstr ++ "`, 0, []}", "Postulate: " ++ pstr)
    where
        t     = treeFromLn $ Prelude.head pl
        t'    = treeFromLn $ Prelude.last pl
        pstr  = show (treeSTMT ([t, treeIMP, t']))

------------------------------------- Widgets ----------------------------------

-- |Contains a static help text, which is loaded from the corresponding Hamlet
-- file.
helpText :: Widget
helpText = $(whamletFile "help.hamlet")

-- |Generates the HTML representation of the proof to be displayed.
proofWidget ::      String      -- ^The history of commands that were used to
                                --  build the current proof.
                 -> Bool        -- ^`True` if the last entered command did not
                                --  result in any errors.
                 -> [Text]      -- ^A list of `Text` representations of the
                                --  `ProofLine`s constituting the current proof.
                 -> [String]    -- ^A list of error messages resulting from
                                --  the last entered command.
                 -> Widget      -- ^The resulting `Widget`.
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

-- TODO: Change this so that axiom builders are only fetched from DB when
-- necessary.
-- |Generates the HTML representation of the "Info" area (showing a help text or
-- the theory database).
infoWidget ::      String                   -- ^Indentifies the page to be
                                            --  displayed (e.g. help).
                -> [Entity AxiomBuilder]    -- ^List of axiom builders retrieved
                                            --  from the database.
                -> Widget                   -- ^The resulting `Widget`.
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

------------------------------------ Handlers ----------------------------------

-- |Routes directly to `postHomeR`.
getHomeR :: Handler Html
getHomeR = postHomeR

-- |Does some preprocessing of the retrieved data from the input fields and
-- either calls `metaHandler` (if a meta command was issued) or `mainHandler`
-- (otherwise).
postHomeR :: Handler Html
postHomeR = do
    pg   <- runInputPost $ iopt textField "page"
    msg  <- runInputPost $ iopt textField "message"
    hst  <- runInputPost $ iopt textField "history"
    let history = case hst of
            Nothing -> []
            Just h  -> unpack h
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
                [] -> metaHandler history (fst $ Prelude.head metaParse)
                                  message oldpage
                _  -> mainHandler history [] message oldpage


-- |Processes a `meta command' and then calls the `mainHandler`.
metaHandler ::     String               -- ^The command history.
                -> (String, [String])   -- ^Ordered pair containing a `String`
                                        --  representation of the command
                                        --  and a list of the parameters of that
                                        --  command.
                -> String               -- ^An unparsed verson of the command.
                -> String               -- ^The previously active page in the
                                        --  `Info' area.
                -> HandlerFor App Html  -- ^The result.
metaHandler history parsedMeta message oldpage = do
    let historylist = case history == [] of
            True  -> []
            False -> (Data.List.Split.splitOn ";" history)
    case fst $ parsedMeta of
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
                           (snd $ parsedMeta)
                    axiom <- runDB $ getBy (Axiom "User"
                                                  newName)
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
                    let index = read (Prelude.head $ snd $ parsedMeta) ::
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
        "doc"     -> redirect DocR
        "database" -> redirect DataR
        _  -> mainHandler history [] message oldpage

getDocR :: Handler Html
getDocR = sendFile "application/pdf" "doc/doc.pdf"

getDataR :: Handler Html
getDataR = sendFile "application/x-sqlite3" "theory.db3"

mainHandler ::      String              -- ^The command history.
                -> [String]             -- ^A list of error messages resulting
                                        --  from executing a meta command.
                -> String               -- ^The command entered by the user.
                -> String               -- ^The page to be displayed in the
                                        --  `Info' area.
                -> Handler Html         -- ^The result.
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

-- |Generates the final web interface, viewable in web browsers such as Firefox.
divView ::     String                -- ^The history of commands that were used
                                     --  to build the current proof.
            -> Bool                  -- ^`True` if the last entered command did
                                     --  not result in any errors.
            -> [Text]                -- ^A list of `Text` representations of the
                                     --  `ProofLine`s constituting the current
                                     --  proof.
            -> String                -- ^Indentifies the page to be
                                     --  displayed (e.g. help). 
            -> [Entity AxiomBuilder] -- ^List of axiom builders retrieved
                                     --  from the database.
            -> [String]              -- ^A list of error messages resulting from
                                     --  the last entered command.
            -> HandlerFor App Html   -- ^The result.
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

----------------------------------- deprecated ---------------------------------

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
