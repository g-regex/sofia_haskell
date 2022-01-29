{-|
Module      : SofiaCommandParser
Description : Part of the Sofia proof assistant.
Copyright   : Gregor Feierabend
License     : GNU General Public License v3 (GPLv3)
Maintainer  : Gregor Feierabend
Stability   : experimental
Portability : POSIX

The parser for commands of the Sofia proof assistant.
-}

{-# OPTIONS_HADDOCK prune #-}

module SofiaCommandParser (commandParse, evalList, validateSyntax,
        validateSemantics, sValidation, sCommand, sDesc, sRecallRaw,
        recallRawParse, descParse, sMeta, parsingErrors) where

import Parsing
import Sofia
import SofiaTree
import SofiaParser
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
             ['%',' ','+', '!', ':', '=', '\'']

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

sPair :: (Parser a, Parser b) -> Parser (a, b)
sPair (p1, p2) =
    do many (specialChar ' ')
       specialChar '('
       x  <- p1
       specialChar ','
       y <- p2
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

sIntList :: Parser [Int]
sIntList = sList sInt
          <|> do many (specialChar ' ')
                 specialChar '['
                 many (specialChar ' ')
                 i <- sInt
                 many (specialChar ' ')
                 sWord ".."
                 many (specialChar ' ')
                 specialChar ']'
                 many (specialChar ' ')
                 return [i..]

sAssume :: Parser DeductionRule
sAssume = do sWord "assume"
             cs <- sString
             return (Assumption cs)

sRestate :: Parser (DeductionRule)
sRestate = do sWord "restate"
              pl  <- sList (sPair (sInt, sInt))
              css <- sList sString
              return (Restate pl css)

-- NOTE 0 0 will be disregrded
sSynapsis :: Parser (DeductionRule)
sSynapsis = do sWord "synapsis"
               return (Synapsis 0 0)

sApply :: Parser (DeductionRule)
sApply = do sWord "apply"
            x  <- sInt
            pl <- sList (sPair (sInt, sInt))
            y  <- sInt
            return (Apply x pl y)

sSelfequate :: Parser (DeductionRule)
sSelfequate = do sWord "selfequate"
                 p <- sPair (sInt, sInt)
                 return (Selfequate p)

sRightSub :: Parser (DeductionRule)
sRightSub = do sWord "rightsub"
               x  <- sInt
               y  <- sInt
               pl <- sIntList
               x' <- sInt
               y' <- sInt
               return (RightSub x y pl x' y')

sLeftSub :: Parser (DeductionRule)
sLeftSub  = do sWord "leftsub"
               x  <- sInt
               y  <- sInt
               pl <- sIntList
               x' <- sInt
               y' <- sInt
               return (LeftSub x y pl x' y')

sRecall :: Parser (DeductionRule)
sRecall  = do sWord "recall"
              (x, y)  <- sPair (sString, sString)
              return (Recall ((treeParse x), y))

sCommand :: Parser (Proof -> Proof)
sCommand = do many (specialChar ' ')
              x <- (sAssume <|> sRestate <|> sSynapsis <|> sApply <|> sRightSub
                   <|> sLeftSub <|> sSelfequate <|> sRecall)
              many (specialChar ' ')
              return (commandFromDedRule x)

sRecallRaw :: Parser (Int, [String])
sRecallRaw = do sWord "recall"
                i  <- sInt
                css <- sList sString
                return (i, css)

sMetaPost :: Parser (String, [String])
sMetaPost = do cs <- sWord "postulate"
               cs' <- sString
               return (cs, [cs'])

sMetaLoad :: Parser (String, [String])
sMetaLoad = do cs <- sWord "load"
               i  <- sInt
               return (cs, [show i])

sMeta :: Parser (String, [String])
sMeta =    do cs <- sWord "help"
              return (cs, [])
            <|> do cs <- sWord "theory"
                   return (cs, [])
            <|> do cs <- sWord "new"
                   return (cs, [])
            <|> do cs <- sWord "back"
                   return (cs, [])
            <|> do cs <- sWord "doc"
                   return (cs, [])
            <|> do cs <- sWord "database"
                   return (cs, [])
            <|> do x <- sMetaPost
                   return x
            <|> do x <- sMetaLoad
                   return x

sNoBrackets :: Parser Char
sNoBrackets = do x <- sat (\x -> not (elem x ['[', ']']))
                 return x

sBrackets :: Parser String
sBrackets = do specialChar '['
               xs <- many sNoBrackets
               ys <- option (do xs' <- sBrackets
                                ys' <- many sNoBrackets
                                return (xs' ++ ys'))
               specialChar ']'
               return ("[" ++ xs ++ ys ++ "]")

sDescPair :: Parser (String, String)
sDescPair = do x <- sNoBrackets
               xs <- many sNoBrackets
               ys <- option sBrackets
               return (x:xs, ys)
             <|> do ys <- sBrackets
                    return ("", ys)

sDesc :: Parser [(String, String)]
sDesc = do xs <- many sDescPair
           return xs

sValidation :: Proof -> Parser [String]
sValidation p = do
              many (specialChar ' ')
              x <- (sAssume <|> sRestate <|> sSynapsis <|> sApply <|> sRightSub
                   <|> sLeftSub <|> sSelfequate <|> sRecall)
              many (specialChar ' ')
              return (validationFromDedRule x p)

-- TODO recall
commandFromDedRule :: DeductionRule -> (Proof -> Proof)
commandFromDedRule dr = case dr of
    Assumption cs       -> assume cs
    Selfequate ii       -> selfequate ii
    Restate iis css     -> restate iis css
    Synapsis i i'       -> synapsis
    Apply a xs b        -> apply a xs b
    RightSub a c xs b d -> rightsub a c xs b d
    LeftSub  a c xs b d -> leftsub a c xs b d
    Recall (a, b)       -> recall (a, b)

-- TODO recall
validationFromDedRule :: DeductionRule -> Proof -> [String]
validationFromDedRule dr p = showErrors validation
   where
    validation = case dr of
        Assumption cs       -> validateAssume cs
        Selfequate ii       -> validateSelfequate ii p
        Restate iis css     -> validateRestate iis css p
        Synapsis i i'       -> validateSynapsis p
        Apply a xs b        -> validateApply a xs b p
        RightSub a c xs b d -> validateSubst a c b d p
        LeftSub  a c xs b d -> validateSubst a c b d p
        Recall (a, b)       -> validateRecall a

commandParse :: String -> (Proof -> Proof)
commandParse x = fst $ head $ parse sCommand x

recallRawParse :: String -> (Int, [String])
recallRawParse x = fst $ head $ parse sRecallRaw x

descParse :: String -> [(String, String)]
descParse x = fst $ head $ parse sDesc x

listParse :: [String] -> [(Proof -> Proof)]
listParse x = map commandParse x

evalPList :: Proof -> [(Proof -> Proof)] -> Proof
evalPList p [] = p
evalPList p (pp:pps) = evalPList (pp p) pps

evalList :: [String] -> Proof
evalList css = evalPList newProof (listParse css)

parsingErrors :: [(a, String)] -> [String]
parsingErrors parsed = if correctSyntax then []
                 else ["Syntax error in command."]
    where
     correctSyntax = and [length (parsed) == 1,
                      (length $ snd $ head $ parsed) == 0]

validateSyntax :: Parser a -> String -> [String]
validateSyntax psr cs = if correctSyntax then []
                 else ["Syntax error in command."]
    where
     parsed = parse psr cs
     correctSyntax = and [length (parsed) == 1,
                      (length $ snd $ head $ parsed) == 0]

validateSemantics :: String -> Proof -> [String]
validateSemantics cs p = if parsingSuccess then fst $ head $ parsed
                 else ["Unparsed input (" ++ (snd $ head parsed) ++ ")."]
    where
     parsed = parse (sValidation p) cs
     parsingSuccess = and [length (parsed) == 1,
                      (length $ snd $ head $ parsed) == 0]
