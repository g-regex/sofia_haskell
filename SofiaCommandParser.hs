{-# OPTIONS_HADDOCK prune #-}

{-|
Module      : SofiaCommandParser
Description :
Copyright   :
License     :
Maintainer  :
Stability   : experimental
Portability : POSIX

The parser for commands of the Sofia proof assistant.
-}

module SofiaCommandParser (commandParse, evalList, validateCmd) where

import Parsing
import Sofia
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

sString :: Parser String
sString =
    do many (specialChar ' ')
       specialChar '"'
       xs <- many sCharacter
       specialChar '"'
       many (specialChar ' ')
       return xs

sInt :: Parser Int
sInt =
    do many (specialChar ' ')
       x  <- sDigit
       xs <- many sDigit
       many (specialChar ' ')
       return (read (x:xs) :: Int)

sPair :: Parser (Int, Int)
sPair =
    do many (specialChar ' ')
       specialChar '('
       x  <- sInt
       specialChar ','
       y <- sInt
       specialChar ')'
       many (specialChar ' ')
       return (x,y)

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

sPairList :: Parser [(Int, Int)]
sPairList = sList sPair

sIntList :: Parser [Int]
sIntList = sList sInt

sAssume :: Parser (Proof -> Proof)
sAssume = do sWord "assume"
             cs <- sString
             return (assume cs)

sRestate :: Parser (Proof -> Proof)
sRestate = do sWord "restate"
              pl  <- sList sPair
              css <- sList sString
              return (restate pl css)

sSynapsis :: Parser (Proof -> Proof)
sSynapsis = do sWord "synapsis"
               return (synapsis)

sApply :: Parser (Proof -> Proof)
sApply = do sWord "apply"
            x  <- sInt
            pl <- sList sPair
            y  <- sInt
            return (apply x pl y)

sSelfequate :: Parser (Proof -> Proof)
sSelfequate = do sWord "selfequate"
                 p <- sPair
                 return (selfequate p)

sRightSub :: Parser (Proof -> Proof)
sRightSub = do sWord "rightsub"
               x  <- sInt
               y  <- sInt
               pl <- sList sInt
               x' <- sInt
               y' <- sInt
               return (rightsub x y pl x' y')

sLeftSub :: Parser (Proof -> Proof)
sLeftSub  = do sWord "leftsub"
               x  <- sInt
               y  <- sInt
               pl <- sList sInt
               x' <- sInt
               y' <- sInt
               return (leftsub x y pl x' y')

sCommand :: Parser (Proof -> Proof)
sCommand = do many (specialChar ' ')
              x <- (sAssume <|> sRestate <|> sSynapsis <|> sApply <|> sRightSub
                   <|> sLeftSub <|> sSelfequate)
              many (specialChar ' ')
              return x

commandParse :: String -> (Proof -> Proof)
commandParse x = fst $ head $ parse sCommand x

listParse :: [String] -> [(Proof -> Proof)]
listParse x = map commandParse x

evalPList :: Proof -> [(Proof -> Proof)] -> Proof
evalPList p [] = p
evalPList p (pp:pps) = evalPList (pp p) pps

evalList :: [String] -> Proof
evalList css = evalPList newProof (listParse css)

validateCmd :: String -> Bool
validateCmd cs = and [length (parsed) == 1,
                      (length $ snd $ head $ parsed) == 0]
                    where
                     parsed = parse sCommand cs
