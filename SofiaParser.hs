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
module SofiaParser
    (assumeT,
     SofiaTree,
     DeductionRule (Assumption, Selfequate, Restate),
     TypeOfNode (Atom, Statement, Formula, Implication, Equality, Symbol,
                 Error),
     newSofiaTree,
     getAtom,
     getSubtrees,
     getSymbol,
     toSofiaTree,
     toType) where

import Parsing
import ListHelpers

class Printable a where
    printable :: a -> String

instance Printable Char where
    printable x = id [x]

toString :: Printable a => [a] -> String
toString [] = ""
toString (x:xs) = (printable x) ++ (toString xs)

data TypeOfNode = Atom | Statement | Formula | Implication | Equality | Symbol |
                  Error deriving (Show, Eq)
-- |A 'Tree' is a Node with two types of values (a list and another value)
-- and a list of sub'Tree's.
data Tree a b = Node [a] b [Tree a b]
              deriving
              (Eq -- ^Two 'Tree's are equal if and only if all their 'Node's
                  -- are equal.
              )
newSofiaTree :: [Char] -> TypeOfNode -> [SofiaTree] -> SofiaTree
newSofiaTree a b c = Node a b c

-- |A 'Tree' will be printed as the underlying Sofia string, if its
-- parameters belong to the helper classes 'Printable' and 'SType'. The
-- 'Printable' class ensures that the corresponding parameter can be
-- converted to a 'String' and the 'SType' class ensures that the
-- corresponding parameter can be converted to a 'TypeOfNode'.
instance (Printable a, Show a, SType b, Show b) => Show (Tree a b) where
    show (Node a b c) = case toType b of
                             Error          -> "Error" 
                             Atom           -> "[" ++ showtree c ++ "]"
                             Implication    -> ":"
                             Equality       -> "="
                             Symbol         -> toString a
                             _              -> showtree c
                             where showtree z = case z of
                                                     []   -> ""
                                                     x:xs -> (show x) ++ (showtree xs)

-- |A (possibly parametrised) deduction rule.
data DeductionRule = Assumption | Selfequate (Int, Int) | Restate [(Int, Int)]
                     deriving (Show)

-- |A 'Tree' containing a parsed Sofia string. Each 'Node' of such a 'Tree'
-- contains a list of 'Char's (only non-empty, if the 'TypeOfNode' is
-- 'Symbol') equal to the 'String' representation of the 'Node' and the
-- 'TypeOfNode' of the 'Node'.
type SofiaTree = Tree Char TypeOfNode

class SType a where
    toType       :: a -> TypeOfNode

instance SType TypeOfNode where
    toType x = x

instance SType b => SType (Tree a b) where
    toType (Node a b c) = toType b

toSofiaTreeList :: (Printable a, SType b) => [Tree a b] -> [SofiaTree]
toSofiaTreeList [] = []
toSofiaTreeList ((Node a b c):ns)  = (Node (toString a) (toType b) (toSofiaTreeList c)):(toSofiaTreeList ns)

toSofiaTree :: (Printable a, SType b) => Tree a b -> SofiaTree
toSofiaTree x = head (toSofiaTreeList [x])

class SofiaTreeClass a where
    getAtom :: Int -> a -> SofiaTree
    --getStatement :: Int -> a -> SofiaTree
    getSubtrees :: a -> [a]
    getSymbol :: a -> [Char]
    isFormulator :: a -> Bool

-- parses a list of similar tokens zero or more times (behaves like curly
-- braces in EBNF)
option :: Parser [a] -> Parser [a]
option p = option1 p <|> return []
option1 :: Parser [a] -> Parser [a]
option1 p = do vs1 <- p
               vs2 <- option p
               return (vs1 ++ vs2)

legalChars = ['a'..'z'] ++ ['A'..'Z'] ++ ['0'..'9'] ++ ['%',' ']

sCharacter :: Parser Char
sCharacter = sat (\x -> elem x legalChars)

specialChar :: Char -> Parser Char
specialChar x = sat (== x)

sSymbol :: Parser String
sSymbol = do       x <- sCharacter
                   xs <- many sCharacter
                   return [y | y <- (x:xs), y /= ' ']

sFormulator :: Parser SofiaTree
sFormulator = do x <- specialChar ':'; return (Node [] Implication [])
               <|> do x <- specialChar '='; return (Node [] Equality [])
               <|> do x <- sSymbol; return (Node x Symbol [])

sAtom :: Parser SofiaTree
sAtom = do specialChar '[';
             x <- sFormula;
             specialChar ']';
             return (Node "" Atom [x])
           <|> do specialChar '[';
                  x <- sStatement;
                  specialChar ']';
                  return (Node "" Atom [x])

sStatement :: Parser SofiaTree
sStatement = do x <- sAtom;
                xs <- many sAtom;
                return (Node "" Statement (x:xs))

sFormula :: Parser SofiaTree
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

sExpression :: Parser SofiaTree
sExpression = do x <- sFormula
                 return x
               <|> do x <- sStatement
                      return x

assumeT :: String -> SofiaTree
assumeT x = fst $ head $ parse sExpression x

instance (Printable a, SType b) => SofiaTreeClass (Tree a b) where
    getAtom i (Node a b cs) = case and [0 < i, i <= length cs] of
                                    True -> case toType b of
                                        Statement -> toSofiaTree (getIndex i cs)
                                        _         -> Node [] Error []
                                    False -> Node [] Error []
    getSubtrees (Node a b cs) = cs
    getSymbol (Node a b cs) = toString a
    isFormulator (Node a b cs) = not (or [toType b == Statement, toType b == Formula, toType b == Atom])

getSubSofiaTrees :: (Printable a, SType b) => Tree a b -> [SofiaTree]
getSubSofiaTrees t = [toSofiaTree c | c <- getSubtrees t]

----------------------------------- DEBUGGING ----------------------------------
{-varDepths :: [Char] -> SofiaTree -> Int -> [Int]
varDepths sym tree i = if isFormulator tree then [] else 
                     case elem sym (vars tree) of
                       True -> i : rest
                       False -> rest
                       where rest = [x | subtree <- (getSubSofiaTrees tree), x <- (varDepths sym subtree incr)]
                             incr = if (toType tree == Statement) then i + 1 else i

preorderDepth :: SofiaTree -> Int -> [(Int, TypeOfNode)]
preorderDepth t i = if getSubSofiaTrees t == [] then [(i, toType t)]
                    else (i, toType t) : [x | t' <- (getSubSofiaTrees t), x <- preorderDepth t' (i+1)] -}
