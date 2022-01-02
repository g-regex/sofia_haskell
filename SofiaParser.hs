{-# OPTIONS_HADDOCK prune #-}

{-|
Module      : SofiaParser
Description :
Copyright   :
License     :
Maintainer  :
Stability   : experimental
Portability : POSIX

The parser for the Sofia proof assistant.
-}

--module SofiaParser where
module SofiaParser (treeParse) where

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

legalChars = ['a'..'z'] ++ ['A'..'Z'] ++ ['0'..'9'] ++ ['%',' ','+']

sCharacter :: Parser Char
sCharacter = sat (\x -> elem x legalChars)

specialChar :: Char -> Parser Char
specialChar x = sat (== x)

sSymbol :: Parser String
sSymbol =
    do x <- sCharacter
       xs <- many sCharacter
       return [y | y <- (x:xs), y /= ' ']

sFormulator :: Parser SofiaTree
sFormulator = 
    do x <- specialChar ':'
       return (newSofiaTree [] Implication [])
      <|> do x <- specialChar '='
             return (newSofiaTree [] Equality [])
            <|> do x <- sSymbol
                   return (newSofiaTree x Symbol [])

sAtom :: Parser SofiaTree
sAtom =
    do specialChar '['
       x <- sFormula
       specialChar ']'
       return (newSofiaTree "" Atom [x])
      <|> do specialChar '['
             x <- sStatement
             specialChar ']'
             return (newSofiaTree "" Atom [x])
      <|> do specialChar '['
             specialChar ']'
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
treeParse x = fst $ head $ parse sExpression x
