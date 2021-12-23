--{-# LANGUAGE FlexibleInstances #-}

import Parsing

legalChars = ['a'..'z'] ++ ['A'..'Z'] ++ ['0'..'9'] ++ ['%',' ']

isLegal :: Char -> Bool
isLegal x = if length [a | a <- legalChars, a == x] == 1 then True else False

class Printable a where
    printable :: a -> String

instance Printable Char where
    printable x = id [x]

toString :: Printable a => [a] -> String
toString [] = ""
toString (x:xs) = (printable x) ++ (toString xs)

data TypeOfNode = Atom | Statement | Formula | Implication | Equality | Symbol | Error deriving (Show, Eq)
data Tree a b = Node [a] b [Tree a b] deriving (Eq) --deriving (Show)
--              Node (a,b) [Tree a b] deriving (Show)

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

type STree = Tree Char TypeOfNode

class SType a where
    toType       :: a -> TypeOfNode

instance SType TypeOfNode where
    toType x = x

instance SType b => SType (Tree a b) where
    toType (Node a b c) = toType b

toSTreeList :: (Printable a, SType b) => [Tree a b] -> [STree]
toSTreeList [] = []
toSTreeList ((Node a b c):ns)  = (Node (toString a) (toType b) (toSTreeList c)):(toSTreeList ns)

toSTree :: (Printable a, SType b) => Tree a b -> STree
toSTree x = head (toSTreeList [x])

getIndex :: Int -> [a] -> a
getIndex i xs = fst $ head $ [(j, k) | (j, k) <- pairs, k == i] where pairs = zip [y | y <- xs] [1..]

class SProofTree a where
    getAtom :: Int -> a -> STree
    getStatement :: Int -> a -> STree
    getSubSTrees :: a -> [STree]
    getSymbol :: a -> [Char]
    isExpression :: a -> Bool

-- TODO error checks (see below)
line :: (Printable a, SType b) => [Tree a b] -> [STree]
line []     = []
line [x]   = [toSTree x]
line (x:xs) = (toSTree x) : line (tail xs)

instance (Printable a, SType b) => SProofTree (Tree a b) where
    getAtom i (Node a b cs) = case and [0 < i, i <= length cs] of
                                    True -> case toType b of
                                        Statement -> toSTree (getIndex i cs)
                                        _         -> Node [] Error []
                                    False -> Node [] Error []
    -- TODO check whether tree is of correct type (i.e. Statement
    -- Implication Statement Implication Statement ... ) and index is in
    -- range
    getStatement i (Node a b cs) = case toType b of
                                   Formula -> getIndex i (line cs)
                                   _       -> Node [] Error []
    getSubSTrees (Node a b cs) = [toSTree c | c <- cs]
    getSymbol (Node a b cs) = toString a
    isExpression (Node a b cs) = or [toType b == Statement, toType b == Formula, toType b == Atom]

-- TODO check whether this behaves correctly
topLevelSym :: STree -> [[Char]]
topLevelSym tree = [getSymbol x4 | x1 <- filter (\x -> toType x == Statement) (getSubSTrees tree),
                                   x2 <- filter (\x -> toType x == Atom) (getSubSTrees x1),
                                   x3 <- filter (\x -> toType x == Formula) (getSubSTrees x2),
                                   length (getSubSTrees x3) == 1, -- TODO make more efficient 
                                   x4 <- filter (\x -> toType x == Symbol) (getSubSTrees x3)]

depths :: [Char] -> STree -> Int -> [Int]
depths sym tree i = if not (isExpression tree) then [] else 
                     case elem sym (topLevelSym tree) of
                       True -> i : rest
                       False -> rest
                       where rest = [x | subtree <- (getSubSTrees tree), x <- (depths sym subtree incr)]
                             incr = if (toType tree == Statement) then i + 1 else i

preorderDepth :: STree -> Int -> [(Int, TypeOfNode)]
preorderDepth t i = if getSubSTrees t == [] then [(i, toType t)]
                    else (i, toType t) : [x | t' <- (getSubSTrees t), x <- preorderDepth t' (i+1)]

selfequate :: (Int, Int) -> STree -> STree
selfequate pos x = Node [] Statement [Node [] Atom [n, (Node [] Equality []), n]] where
                            n = toSTree (getAtom (snd $ pos) (getStatement (fst $ pos) x))

restate :: [(Int, Int)] -> STree -> STree
restate xs y = Node [] Statement atomlist where
    atomlist = [getAtom (snd $ x) (getStatement (fst $ x) y) | x <- xs]
 
sCharacter :: Parser Char
sCharacter = sat (\x -> elem x legalChars)

specialChar :: Char -> Parser Char
specialChar x = sat (== x)

sSymbol :: Parser String
sSymbol = do       x <- sCharacter
                   xs <- many sCharacter
                   return [y | y <- (x:xs), y /= ' ']

sFormulator :: Parser STree
sFormulator = do x <- specialChar ':'; return (Node [] Implication [])
               <|> do x <- specialChar '='; return (Node [] Equality [])
               <|> do x <- sSymbol; return (Node x Symbol [])

sAtom :: Parser STree
sAtom = do specialChar '[';
             x <- sFormula;
             specialChar ']';
             return (Node "" Atom [x])
           <|> do specialChar '[';
                  x <- sStatement;
                  specialChar ']';
                  return (Node "" Atom [x])

sStatement :: Parser STree
sStatement = do x <- sAtom;
                xs <- many sAtom;
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
                 return x
               <|> do x <- sStatement
                      return x

assume :: String -> STree
assume x = fst $ head $ parse sExpression x
