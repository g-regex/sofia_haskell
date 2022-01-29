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
Module      : SofiaAxiomParser
Description : Part of the Sofia proof assistant.
Copyright   : Gregor Feierabend
License     : GNU General Public License v3 (GPLv3)
Maintainer  : Gregor Feierabend
Stability   : experimental
Portability : POSIX

The `SofiaAxiomParser` module contains the definition of the `AxiomSchema` data
type to store recursive definitions of axiom schemata. Further, it contains
functions to parse `String` representations of `AxiomSchema`ta and functions to
create `Postulate`s from `AxiomSchema`ta.
-}

{-# OPTIONS_HADDOCK prune #-}

module SofiaAxiomParser
        (
        AxiomSchema (ReplaceString, ReplaceAll, FinalString, Final),
        axiomParse,
        axiomBuild
        ) where

import Parsing
import SofiaTree
import SofiaParser
import ListHelpers

-- |Recursively defines an axiom schema. An `AxiomSchema` on its own, however,
-- is not enough to build an axiom. It should be understood within the context
-- of its possible /external/ parameters. `ReplaceString` and `ReplaceAll` both
-- refer to these respectively by their second parameter, if that parameter is
-- greater than 0.
data AxiomSchema = ReplaceString String Int [AxiomSchema]
                   -- ^An axiom schema of this type is parametrised by a
                   -- `String`, which may contain placeholders of the form
                   -- [[]]. To refer to these placeholders, the second parameter
                   -- must be 0; otherwise the second parameter must be greater
                   -- than zero and refers to an /external/ parameter. The last
                   -- parameter is a list of `AxiomSchema`ta. These can be
                   -- understood as already recursively processed and hence as
                   -- valid `SofiaTree`s. When an axiom builder function is
                   -- applied to the `ReplaceString`, each occurrence of a
                   -- placeholder or an external parameter (as indicated by the
                   -- `Int`) will be replaced by one of the `SofiaTree`s
                   -- resulting from recursively processing the list of
                   -- `AxiomSchema`ta (from left to right).
                   | ReplaceAll Int Int AxiomSchema
                   -- ^This type of axiom schema directly refers to an
                   -- /external/ parameter by the first `Int`. Occurrences of a
                   -- second /external/ parameter, as given by the second `Int`
                   -- are all to be replaced by the result of processing the
                   -- `AxiomSchema` given as the third parameter.
                   | FinalString String
                   -- ^This axiom schema will literally by translated into the
                   -- `SofiaTree` resulting from parsing the `String`
                   -- parametrising this `AxiomSchema`.
                   | Final Int
                   -- ^This axiom schema will be translated into the `SofiaTree`
                   -- resulting from parsing the /external/ parameter with the
                   -- index number given by the `Int`.
                   deriving (Show -- ^The `Show` instance is derived for
                                  --  debugging purposes only.
                            )

-- |Parses a `String` representation of an `AxiomSchema` and returns the
-- resulting `AxiomSchema`.
axiomParse :: String -> AxiomSchema
axiomParse x = fst $ head $ parse sAxiom x

-- |Builds a `SofiaTree` by combining an `AxiomSchema` with a list of paramters
-- (i.e.\ `String` representations of atomic `Sofia` statements) /external/ to
-- the `AxiomSchema`.
axiomBuild ::   AxiomSchema
             -> [String]
             -> SofiaTree
axiomBuild ax css = axiomBuilderHelper ax (map treeParse css)

axiomBuilderHelper :: AxiomSchema -> [SofiaTree] -> SofiaTree
axiomBuilderHelper (Final i) ts     = getIndex i ts
axiomBuilderHelper (FinalString cs) ts     = treeParse cs
axiomBuilderHelper (ReplaceAll i i' ax) ts  =
    treeSubstPattern (getIndex i ts) ts' sub
     where
      ts' = [axiomBuilderHelper ax ts | i <- [1..]]
      sub = if i' == 0 then [atomPH] else [(getIndex i' ts)]
axiomBuilderHelper (ReplaceString cs i axs) ts =
    treeSubstPattern (treeParse cs) ts' sub
     where
      ts' = [axiomBuilderHelper ax ts | ax <- axs]
      sub = if i == 0 then [atomPH] else [(getIndex i ts)]

atomPH :: SofiaTree
atomPH = head $ getSubtrees $ treeParse "[[]]"

treeSubstPattern :: SofiaTree ->
             [SofiaTree] ->
             [SofiaTree] ->
             SofiaTree
treeSubstPattern t ts ts' = head $ fst $ treesSubstPattern [t]
                            (map getSubtrees ts) ts'

treesSubstPattern  ::  [SofiaTree] ->
                       [[SofiaTree]] ->
                       [SofiaTree] ->
                       ([SofiaTree], [[SofiaTree]])
treesSubstPattern []      tss      _ = ([], tss)
treesSubstPattern (t:ts') []       _ = ((t:ts'), [])
treesSubstPattern (t:ts') (ts:tss) ts'' =
    if elem t ts''
    then (ts ++ rest_tree, rest_i)
    else ((newSofiaTree (getSymbol t)
                        (toType t)
                        (subtree)) : rest_tree, rest_i)
       where
        incr       = if elem t ts'' then tss else (ts:tss)
        recur      = treesSubstPattern (getSubtrees t) incr ts''
        subtree    = fst recur
        rest       = treesSubstPattern ts' (snd recur) ts''
        rest_tree  = fst rest
        rest_i     = snd rest

-- parses a list of similar tokens zero or more times (behaves like curly
-- braces in EBNF)
option :: Parser [a] -> Parser [a]
option p = option1 p <|> return []
option1 :: Parser [a] -> Parser [a]
option1 p =
    do vs1 <- p
       vs2 <- option p
       return (vs1 ++ vs2)

legalChars = ['[', ']'] ++ ['a'..'z'] ++ ['A'..'Z'] ++ ['0'..'9'] ++
             ['%',' ','+', '!', ':', '=']

sCharacter :: Parser Char
sCharacter = sat (\x -> elem x legalChars)

sDigit :: Parser Char
sDigit = sat (\x -> elem x ['0'..'9'])

specialChar :: Char -> Parser Char
specialChar x = sat (== x)

sWord :: String -> Parser String
sWord [] = return []
sWord (c:cs) = do x <- specialChar c
                  xs <- sWord cs
                  return (x:xs)

sAxiom :: Parser AxiomSchema
sAxiom =
    do many (specialChar ' ')
       specialChar '{'
       x <- sString
       specialChar ','
       y <- sInt
       specialChar ','
       z <- sList sItem
       specialChar '}'
       many (specialChar ' ')
       return (ReplaceString x y z)
     <|> do many (specialChar ' ')
            specialChar '{'
            x <- sInt
            specialChar ','
            y <- sInt
            specialChar ','
            z <- sItem
            specialChar '}'
            many (specialChar ' ')
            return (ReplaceAll x y z)

sString :: Parser String
sString =
    do many (specialChar ' ')
       specialChar '`'
       xs <- many sCharacter
       specialChar '`'
       many (specialChar ' ')
       return xs

sInt :: Parser Int
sInt =
    do many (specialChar ' ')
       x  <- sDigit
       xs <- many sDigit
       many (specialChar ' ')
       return (read (x:xs) :: Int)

sList :: Parser a -> Parser [a]
sList p =
    do many (specialChar ' ')
       specialChar '['
       specialChar ']'
       many (specialChar ' ')
       return []
      <|> do many (specialChar ' ')
             specialChar '['
             x <- p
             xs <- many (do specialChar ','; x' <- p; return x')
             specialChar ']'
             many (specialChar ' ')
             return (x:xs)

sItem :: Parser AxiomSchema
sItem = do many (specialChar ' ')
           x <- sInt
           many (specialChar ' ')
           return (Final x)
         <|> do many (specialChar ' ')
                x <- sString
                many (specialChar ' ')
                return (FinalString x)
              <|> do many (specialChar ' ')
                     x <- sAxiom
                     many (specialChar ' ')
                     return x
