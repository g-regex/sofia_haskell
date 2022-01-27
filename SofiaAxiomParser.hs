{-# OPTIONS_HADDOCK prune #-}

{-|
Module      : SofiaAxiomParser
Description :
Copyright   :
License     :
Maintainer  :
Stability   : experimental
Portability : POSIX

The parser for axiom builders of the Sofia proof assistant.
-}

module SofiaAxiomParser
        (
        axiomParse,
        axiomBuild,
        AxiomSchema (ReplaceString, ReplaceAll, FinalString, Final)
        ) where

import Parsing
import SofiaTree
import SofiaParser
import ListHelpers

data AxiomSchema = ReplaceString String Int [AxiomSchema] |
                   ReplaceAll Int Int AxiomSchema |
                   FinalString String |
                   Final Int deriving (Show)

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

axiomParse :: String -> AxiomSchema
axiomParse x = fst $ head $ parse sAxiom x

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

axiomBuild :: AxiomSchema -> [String] -> SofiaTree
axiomBuild ax css = axiomBuilderHelper ax (map treeParse css)
