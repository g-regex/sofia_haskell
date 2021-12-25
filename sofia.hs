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

-- For consiseness, the following naming conventions for variables are
-- used:
-- t (arbitrary STree)
-- v (STree of type Symbol which contains a variable)
-- p (Proof)
-- pl (ProofLine)
-- f (filter function)
-- b (Boolean constant function)
-- s (String)
-- c (Char)
-- i (Int)
-- r ((String, String), r stands for 'rename')
-- y (TypeOfNode)

---------------------------- RESTATE HELPERS -----------------------------------

-- returns a list resulting from a preorder traversal of tree t and
-- applying s to each subtree; direct children of subtrees are skipped
-- whenever the filter-condition f is not met; this is recursively
-- communicated by setting b to False
preorder :: (STreeClass a, Eq a) => (a -> b) ->  (a -> Bool) -> a -> Bool -> [b]
preorder s f t b = if getSubtrees t == [] then ts
               else ts ++  [x | t' <- (getSubtrees t), x <- preorder' t'] where
                   preorder' t' = if f t
                                   then preorder s f t' True
                                   else preorder s f t' False
                   ts = if b then [s t] else []

isVar :: STree -> Bool
isVar = \t -> length (getSubtrees t) == 1

deepVars :: STree -> [[Char]]
deepVars t = rmdups [s | s <- preorder getSymbol isVar t True, s /= ""]

minVarDepth :: String -> Proof -> Int
minVarDepth s p = case depths of
                       [] -> -1
                       _  -> minimum depths
                       where
                           depths = [second $ pl | pl <- p,
                                                   elem s (vars (third pl))]

freeVars :: STree -> Proof -> [[Char]]
freeVars t p = [v | v <- deepVars t,
                    or [minVarDepth v p == -1, curDepth p < minVarDepth v p]]
                    -- TODO optimise

-- substitute s1 with s2 in s3 (only whole string is matched)
{-sub :: String -> String -> String -> String
sub s1 s2 s3 = if s1 == s3 then s2 else s3

substTree :: String -> String -> STree -> STree
substTree s1 s2 (Node a b cs) = Node (sub s1 s2 a) b [substTree s1 s2 c | c <- cs]-}

sub' :: [(String, String)] -> String -> String
sub' rs s = if elem s $ map fst rs
                then head [snd r | r <- rs, fst r == s]
                else s

substTree' :: [(String, String)] -> STree -> STree
substTree' rs (Node s y ts) = Node (sub' rs s) y [substTree' rs t | t <- ts]

renameVar :: String -> [String] -> String
renameVar s ss = head (without ([s] ++  [s ++ s' | s' <- ss']) ss) where
    ss' = ["'", "''", "'''"] ++ [show i | i <- [1..]]

pairVar :: String -> Proof -> (String, String)
pairVar s p = (s, renameVar s  (boundVars 1 p))

pairVarList :: [String] -> Proof -> [(String, String)]
pairVarList ss p = [pairVar s p | s <- ss]

substAllVars :: STree -> Proof -> STree
substAllVars t p = substTree' rs t where
    rs = pairVarList ss p
    ss = deepVars t

substVar :: String -> String -> STree -> Proof -> STree
substVar s s' t p = substTree' ss t where
    ss = [(s, renameVar s'  (boundVars 1 p))]

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
lastContext p = without [v | pl <- getLastBracket p, v <- deepVars (third pl)] (boundVars 0 p)

contextSpecifcVars :: Proof -> [[Char]]
contextSpecifcVars p = rmdups $intersect [deepVars lastStmt, lastContext p] where
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
    t = substAllVars (assumeT s) p

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
    s  = (1 + curLineNo p, curDepth p, substVar v s2 t p, r)
    v = if fv == [] then "" else head fv
    fv = freeVars t p
    r  = Restate lps

----------------------------------- Examples  ---------------------------------- 

p = assume "[K][[K][b]e[[[c][d]f[a]:[b]]]][r]" []
p0 = assume "[[X]=[X]][s]" p
p1 = selfequate (1,1) p0
p2 = restate [(1,2)] "y" p1
p3 = selfequate (2,1) p2
p4 = restate [(5,1)] "K" p3
a = assumeT "[a][r][z][[a]and[b]=[k]]"
