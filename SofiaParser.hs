{-|
Module      : SofiaParser
Description : Part of the Sofia proof assistant.
Copyright   : Gregor Feierabend
License     : GNU General Public License v3 (GPLv3)
Maintainer  : Gregor Feierabend
Stability   : experimental
Portability : POSIX

The parser for the Sofia proof assistant.
-}

{-# OPTIONS_HADDOCK prune #-}

module SofiaParser (treeParse, legalSymbolChars, isValidSymbol) where

import Parsing
import SofiaTree
import ListHelpers

-- parses a list of similar tokens zero or more times (behaves like curly
-- braces in EBNF)
option :: Parser [a] -> Parser [a]
option p = option1 p <|> return []
option1 :: Parser [a] -> Parser [a]
option1 p =
    do vs1 <- p
       vs2 <- option p
       return (vs1 ++ vs2)

legalSymbolChars = ['a'..'z'] ++ ['A'..'Z'] ++ ['0'..'9'] ++ ['%',' ','+', '!',
                    '\'']

isValidSymbol :: String -> Bool
isValidSymbol cs = [c | c <- cs, not $ elem c legalSymbolChars] == []

sCharacter :: Parser Char
sCharacter = sat (\x -> elem x legalSymbolChars)

specialChar :: Char -> Parser Char
specialChar x = sat (== x)

sSymbol :: Parser String
sSymbol =
    do x <- sCharacter
       xs <- many sCharacter
       return [y | y <- (x:xs), y /= ' ']

sFormulator :: Parser SofiaTree
sFormulator = 
    do many $ specialChar ' '
       specialChar ':'
       many $ specialChar ' '
       return (newSofiaTree [] Implication [])
      <|> do many $ specialChar ' '
             specialChar '='
             many $ specialChar ' '
             return (newSofiaTree [] Equality [])
            <|> do x <- sSymbol
                   return (newSofiaTree x Symbol [])

sAtom :: Parser SofiaTree
sAtom =
    do many (specialChar ' ')  
       specialChar '['
       many (specialChar ' ')
       x <- sFormula
       many (specialChar ' ')
       specialChar ']'
       many (specialChar ' ')
       return (newSofiaTree "" Atom [x])
      <|> do many (specialChar ' ')
             specialChar '['
             many (specialChar ' ')
             x <- sStatement
             many (specialChar ' ')
             specialChar ']'
             many (specialChar ' ')
             return (newSofiaTree "" Atom [x])
      <|> do many (specialChar ' ')
             specialChar '['
             many (specialChar ' ')
             specialChar ']'
             many (specialChar ' ')
             return (newSofiaTree "" Atom [])

sStatement :: Parser SofiaTree
sStatement = do x <- sAtom
                xs <- many sAtom
                return (newSofiaTree "" Statement (x:xs))

sFormula :: Parser SofiaTree
sFormula =
    do x <- sFormulator;
       do y <- sStatement;
          zs <- option
                    (do z1 <- sFormulator
                        z2 <- sStatement
                        return [z1, z2]
                    )
          do f <- sFormulator
             return (newSofiaTree "" Formula ([x, y] ++ zs ++ [f]))
            <|> return (newSofiaTree "" Formula ([x, y] ++ zs))
         <|> return (newSofiaTree "" Formula [x])
      <|> do x <- sStatement
             y <- sFormulator
             zs <- option
                    (do z1 <- sStatement
                        z2 <- sFormulator
                        return [z1, z2]
                    )
             do f <- sStatement
                return (newSofiaTree "" Formula ([x, y] ++ zs ++ [f]))
               <|> return (newSofiaTree "" Formula ([x, y] ++ zs))

sExpression :: Parser SofiaTree
sExpression =
    do x <- sFormula
       return x
      <|> do x <- sStatement
             return x

treeParse :: String -> SofiaTree
treeParse x = case parsed of
                []        -> newSofiaTree "" Error []
                [(_, x:xs)] -> newSofiaTree "" Error []
                _         ->  fst $ head $ parsed
                where parsed = parse sExpression x
