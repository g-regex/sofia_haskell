--{-# LANGUAGE FlexibleInstances #-}

--------------------------- Using Graham Hutton's code -------------------------
import Parsing

rmdups :: Eq a => [a ] -> [a ]
rmdups [] = []
rmdups (x:xs) = x:rmdups (filter (/= x) xs)

--------------------------------------------------------------------------------

-- inf = read "Infinity" :: Float

intersect :: (Eq a) => [[a]] -> [a]
intersect xss = [x | xs <- xss, x <- xs, and $ map (elem x) xss]

without :: (Eq a) => [a] -> [a] -> [a]
without xs ys = [x | x <- xs, not (elem x ys)]

getIndex :: Int -> [a] -> a
getIndex i xs = fst $ head $ [(j, k) | (j, k) <- pairs, k == i] where pairs = zip [y | y <- xs] [1..]

curLineNo :: Proof -> Int
curLineNo [] = 0
curLineNo x = first $ last x

curDepth :: Proof -> Int
curDepth [] = -1
curDepth x = second $ last x

depthAt :: Int -> Proof -> Int
depthAt i p = second $ getIndex i p

first :: (a, b, c, d) -> a
first (a, _, _, _) = a

second :: (a, b, c, d) -> b
second (_, b, _, _) = b

third :: (a, b, c, d) -> c
third (_, _, c, _) = c

fourth :: (a, b, c, d) -> d
fourth (_, _, _, d) = d

class Printable a where
    printable :: a -> String

instance Printable Char where
    printable x = id [x]

toString :: Printable a => [a] -> String
toString [] = ""
toString (x:xs) = (printable x) ++ (toString xs)

data TypeOfNode = Atom | Statement | Formula | Implication | Equality | Symbol |
                  Error deriving (Show, Eq)
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

data DeductionRule = Assumption | Selfequate (Int, Int) | Restate [(Int, Int)]
                     deriving (Show)

type STree = Tree Char TypeOfNode
type ProofLine = (Int, Int, STree, DeductionRule)
type Proof = [ProofLine]

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

class STreeClass a where
    getAtom :: Int -> a -> STree
    --getStatement :: Int -> a -> STree
    getSubtrees :: a -> [a]
    getSymbol :: a -> [Char]
    isFormulator :: a -> Bool

-- TODO error checks (see below)
{-line :: (Printable a, SType b) => [Tree a b] -> [STree]
line []     = []
line [x]   = [toSTree x]
line (x:xs) = (toSTree x) : line (tail xs)-}

instance (Printable a, SType b) => STreeClass (Tree a b) where
    getAtom i (Node a b cs) = case and [0 < i, i <= length cs] of
                                    True -> case toType b of
                                        Statement -> toSTree (getIndex i cs)
                                        _         -> Node [] Error []
                                    False -> Node [] Error []
    getSubtrees (Node a b cs) = cs
    getSymbol (Node a b cs) = toString a
    isFormulator (Node a b cs) = not (or [toType b == Statement, toType b == Formula, toType b == Atom])

getSubSTrees :: (Printable a, SType b) => Tree a b -> [STree]
getSubSTrees t = [toSTree c | c <- getSubtrees t]

----------------------------------- DEBUGGING ----------------------------------
varDepths :: [Char] -> STree -> Int -> [Int]
varDepths sym tree i = if isFormulator tree then [] else 
                     case elem sym (vars tree) of
                       True -> i : rest
                       False -> rest
                       where rest = [x | subtree <- (getSubSTrees tree), x <- (varDepths sym subtree incr)]
                             incr = if (toType tree == Statement) then i + 1 else i

preorderDepth :: STree -> Int -> [(Int, TypeOfNode)]
preorderDepth t i = if getSubSTrees t == [] then [(i, toType t)]
                    else (i, toType t) : [x | t' <- (getSubSTrees t), x <- preorderDepth t' (i+1)]
--------------------------------------------------------------------------------


------------------------------- Parser functions ------------------------------- 

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

-- For consiseness, the following naming conventions for parameters are
-- used.
-- t (arbitrary STree)
-- v (STree of type Symbol which contains a variable)
-- p (Proof)
-- pl (ProofLine)
-- f (filter function)
-- b (Boolean constant function)
-- s (String)
-- c (Char)
-- i (Int)
-- r ((String, String), 'r' stands for 'rename')
-- y (TypeOfNode)
--
-- For function names the following conventions are used. Every function
-- name is of the form prefixName, where "Name" should correlate to the
-- meaning of the function and "prefix" correlates to the type of the
-- function, when all arguments are provided. Options for "prefix" are:
-- is (Bool)
-- vars (STree of type Symbol which contains a variable)
-- num/max/min (Int)
-- str (String)
-- tree (STree)
-- rn ((String, String), 'rn' stands for 'rename')

---------------------------- RESTATE HELPERS -----------------------------------

-- returns a list resulting from a preorder traversal of tree t and
-- applying s to each subtree; direct children of subtrees are skipped whenever
-- the filter-condition f is not met; this is recursively communicated by
-- setting b to False
preorder :: (STreeClass a, Eq a) => (a -> b) ->  (a -> Bool) -> a -> Bool -> [b]
preorder s f t b = if getSubtrees t == []
  then ts
  else ts ++ [ x | t' <- (getSubtrees t), x <- preorder' t' ] where
  preorder' t' = if f t then preorder s f t' True else preorder s f t' False
  ts = if b then [s t] else []

-- 'True' if an STree directly corresponds to a variable; 'False'
-- otherwise.
isVar :: STree -> Bool
isVar = \t -> length (getSubtrees t) == 1

-- A list of all variables contained in a tree (does a deep search for
-- variables).
varsDeep :: STree -> [[Char]]
varsDeep t = rmdups [s | s <- preorder getSymbol isVar t True, s /= ""]

-- The minimum depth of the occurrence of a variable in a given proof.
minVarDepth :: String -> Proof -> Int
minVarDepth s p = case depths of
                       [] -> -1
                       _  -> minimum depths
                       where
                           depths = [second $ pl | pl <- p,
                                                   elem s (vars (third pl))]

-- A list of free variables in a specific statement with respect to a given
-- proof.
varsFree :: STree -> Proof -> [[Char]]
varsFree t p = [v | v <- varsDeep t,
                    or [minVarDepth v p == -1, curDepth p < minVarDepth v p]]
                    -- TODO optimise

-- Replaces a string x with another string y, if the list rs contains
-- a pair (x, y); otherwise x remains unchanged.
strSub :: [(String, String)] -> String -> String
strSub rs s = if elem s $ map fst rs
                then head [snd r | r <- rs, fst r == s]
                else s

-- Replaces an STree x with another STree y, if the list rs contains
-- a pair (x', y'), where x', y' are the string representations of the
-- trees x, y; otherwise x remains unchanged.
treeSub :: [(String, String)] -> STree -> STree
treeSub rs (Node s y ts) = Node (strSub rs s) y [treeSub rs t | t <- ts]

-- Replaces a string "x" with "x'", "x''", "x'''", "x1", "x2", ... based on
-- the availability as indicated by the list of unavailable variables.
strRenameVar :: String -> [String] -> String
strRenameVar s ss = head (without ([s] ++  [s ++ s' | s' <- ss']) ss) where
    ss' = ["'", "''", "'''"] ++ [show i | i <- [1..]]

-- Given a variable x, a pair (x, x') is created, where x' is the next
-- available alternative name for x.
rnVar :: String -> Proof -> (String, String)
rnVar s p = (s, strRenameVar s  (boundVars 1 p))

-- Given a list of variables x1, x2, ... pairs (x1, x1'), (x2, x2') are created,
-- where the xi' are the next available alternatives name for the xi.
rnVarList :: [String] -> Proof -> [(String, String)]
rnVarList ss p = [rnVar s p | s <- ss]

-- Replaces all variable names in a given expression by the next available
-- alternative name.
treeAutoSub :: STree -> Proof -> STree
treeAutoSub t p = treeSub rs t where
    rs = rnVarList ss p
    ss = varsDeep t

-- Renames one variable in an expression to a provided new name.
treeSubOne :: String -> String -> STree -> Proof -> STree
treeSubOne s s' t p = treeSub ss t where
    ss = [(s, strRenameVar s'  (boundVars 1 p))]

---------------------------- SYNAPSIS HELPERS ----------------------------------

vars :: (STreeClass a, SType a) => a -> [[Char]]
vars tree = [getSymbol x4 | x1 <- filter (\x -> toType x == Statement) [tree],
                            x2 <- filter (\x -> toType x == Atom) (getSubtrees x1),
                            x3 <- filter (\x -> toType x == Formula) (getSubtrees x2),
                            length (getSubtrees x3) == 1, -- TODO make more efficient 
                            x4 <- filter (\x -> toType x == Symbol) (getSubtrees x3)]

getLastBracket :: Proof -> Proof
getLastBracket p = takeWhile (\x -> second x == curDepth p) (reverse p)

pairLastBracket :: Proof -> (STree, STree)
pairLastBracket p = (third $ last p', third $ head p') where p' = getLastBracket p

stmtsWithDepthLT :: Int -> Proof -> [STree]
stmtsWithDepthLT i p = [third pl | pl <- p, second pl < i]

boundVars :: Int -> Proof -> [[Char]]
boundVars i p = [v | stmt <- stmts, v <- vars stmt] where
    stmts = stmtsWithDepthLT (lastStmtDepth + i) p
    lastStmtDepth = second $ last p

lastContext :: Proof -> [[Char]]
lastContext p = without [v | pl <- getLastBracket p, v <- varsDeep (third pl)] (boundVars 0 p)

contextSpecifcVars :: Proof -> [[Char]]
contextSpecifcVars p = rmdups $intersect [varsDeep lastStmt, lastContext p] where
    lastStmt = third $ last p

------------------------- Functions generating STrees  ------------------------- 

equals :: STree
equals = (Node [] Equality [])

implies :: STree
implies = (Node [] Implication [])

truth :: STree
truth = Node [] Statement [Node [] Atom []]

makeStatementF :: [STree] -> STree
makeStatementF ts = Node [] Statement [Node [] Atom [Node [] Formula ts]]

selfequateT :: Int -> STree -> STree
selfequateT pos x =  makeStatementF [n, equals, n] where
                            n = toSTree (getAtom pos x)

restateT :: [(STree, Int)] -> STree
restateT xs = Node [] Statement atomlist where
    atomlist = [getAtom (snd $ x) (fst $ x) | x <- xs]

assumeT :: String -> STree
assumeT x = fst $ head $ parse sExpression x

synapsisT :: Proof -> STree
synapsisT p = makeStatementF (newVars ++ [(fst pair), implies, (snd pair)]) where
    pair    = pairLastBracket p
    newVars = [makeStatementF [Node v Symbol []] | v <- contextSpecifcVars p,
                                                   not (elem v (vars (fst pair)))]

------------------------- Functions generating Proofs  ------------------------- 

assume :: String -> Proof -> Proof
assume s p = p ++ [(1 + curLineNo p, 1 + curDepth p, t, Assumption)] where
    t = treeAutoSub (assumeT s) p

--selfequate :: (Int, Int) -> STree -> STree
selfequate :: (Int, Int) -> Proof -> Proof
selfequate (line, pos) p = p ++ [(1 + curLineNo p, curDepth p, t, r)] where
    t = selfequateT pos (third $ getIndex line p)
    r = Selfequate (line, pos)

--restate :: [(Int, Int)] -> STree -> STree
restate :: [(Int, Int)] -> String -> Proof -> Proof
restate lps s2 p = p ++ [s] where
    t  = restateT [(stmt, pos) | (line, pos) <- lps,
                                stmt <- [third $ getIndex line p]]
    s  = (1 + curLineNo p, curDepth p, treeSubOne v s2 t p, r)
    v = if fv == [] then "" else head fv
    fv = varsFree t p
    r  = Restate lps

----------------------------------- Examples  ---------------------------------- 

p = assume "[K][[K][b]e[[[c][d]f[a]:[b]]]][r]" []
p0 = assume "[[X]=[X]][s]" p
p1 = selfequate (1,1) p0
p2 = restate [(1,2)] "y" p1
p3 = selfequate (2,1) p2
p4 = restate [(5,1)] "K" p3
a = assumeT "[a][r][z][[a]and[b]=[k]]"
