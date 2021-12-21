--{-# LANGUAGE FlexibleInstances #-}

import Parsing

legalChars = ['a'..'z'] ++ ['A'..'Z'] ++ ['0'..'9'] ++ ['%',' ']

isLegal :: Char -> Bool
isLegal x = if length [a | a <- legalChars, a == x] == 1 then True else False

data TypeOfNode = Expression | Single | Statement | Formula | Implication | Equality | Symbol deriving (Show)
data Tree a b = Node [a] b [Tree a b] --deriving (Show)

class SType a where
   gettype       :: a -> TypeOfNode

instance SType TypeOfNode where
   gettype x = x

class Printable a where
    printable :: a -> String

instance Printable Char where
    printable x = id [x]

--instance Show a => Show [a] where
--   show a = "Hello"

instance (Printable a, Show a, SType b, Show b) => Show (Tree a b) where
    show (Node a b c) = case gettype b of
                             Expression     -> "Expression: " ++ showtree c
                             Single         -> "[" ++ showtree c ++ "]"
                             Implication    -> printableString a
                             Symbol         -> printableString a
                             _              -> showtree c
                             where showtree z = case z of
                                                     []   -> ""
                                                     x:xs -> (show x) ++ (showtree xs) 
                                   printableString [] = ""
                                   printableString (x:xs) = (printable x) ++ (printableString xs)

-- type NodeVal = (String, TypeOfNode)
-- type STree = Tree NodeVal
type STree = Tree Char TypeOfNode

sCharacter :: Parser Char
sCharacter = sat (\x -> elem x legalChars)

specialChar :: Char -> Parser Char
specialChar x = sat (== x)

sSymbol :: Parser String
sSymbol = do       x <- sCharacter
                   xs <- many sCharacter
                   return [y | y <- (x:xs), y /= ' ']

sFormulator :: Parser STree
sFormulator = do x <- specialChar ':'; return (Node [x] Implication [])
               <|> do x <- sSymbol; return (Node x Symbol [])

sSingle :: Parser STree
sSingle = do specialChar '[';
                      x <- sFormula;
                      specialChar ']';
                      return (Node "" Single [x])
                    <|> do specialChar '[';
                           x <- sStatement;
                           specialChar ']';
                           return (Node "" Single [x])

sStatement :: Parser STree
sStatement = do x <- sSingle;
                xs <- many sSingle;
                return (Node "" Statement (x:xs))

option :: Parser [a] -> Parser [a]
option p = option1 p <|> return []
option1 :: Parser [a] -> Parser [a]
option1 p = do vs1 <- p
               vs2 <- option p
               return (vs1 ++ vs2)

sFormula :: Parser STree
sFormula = do x <- sFormulator;
              do y <- sStatement;
                 zs <- option (do z1 <- sFormulator; z2 <- sStatement; return [z1, z2])
                 do f <- sFormulator; return (Node "" Formula ([x, y] ++ zs ++ [f]))
                  <|> return (Node "" Formula ([x, y] ++ zs))
               <|> return (Node "" Formula [x])
             <|> do x <- sStatement;
                    y <- sFormulator;
                    zs <- option (do z1 <- sStatement; z2 <- sFormulator; return [z1, z2])
                    do f <- sStatement; return (Node "" Formula ([x, y] ++ zs ++ [f]))
                     <|> return (Node "" Formula ([x, y] ++ zs))

sExpression :: Parser STree
sExpression = do x <- sFormula
                 return (Node "" Expression [x])
               <|> do x <- sStatement
                      return (Node "" Expression [x])
