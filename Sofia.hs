-- {-# LANGUAGE FlexibleInstances #-}
-- {-# OPTIONS_HADDOCK prune #-}

{-|
Module      : Sofia
Description :
Copyright   :
License     :
Maintainer  :
Stability   : experimental
Portability : POSIX

The Sofia proof assistant.
-}
module Sofia (
    -- * Types
    ProofLine,
    Proof,

    -- * Naming Convention
    -- $naming

    -- * Deductions
    assume,
    restate,
    selfequate
) where

--------------------------- Using Graham Hutton's code -------------------------
import SofiaParser
import SofiaTree
import ListHelpers
--------------------------------------------------------------------------------

main :: IO ()
main = pure ()

-- $naming
-- For consiseness and readability of the source code, the following naming
-- conventions for function parameters are used. These parameter names are,
-- however, invisible to the user and are only of interest when reading the
-- function definitions. The following list shows the parameter names as
-- well as the type of the parameter in brackets. If within the function
-- definition multiple variables share the same type, one or two
-- apostrophes or the numbers 3, 4, 5, ... are appended to the variable
-- names (in this order). If lists of the respective types are used, then
-- an __s__ (__ss__ for lists of lists and so on) is appended to the
-- respective variable name.
--
--
--      * @t@ (arbitrary @SofiaTree@)
--
--      * @v@ (@SofiaTree@ of type @Symbol@ which contains a variable)
--
--      * @p@ (@Proof@)
--
--      * @pl@ (@ProofLine@)
--
--      * @f@ (filter function)
--
--      * @b@ (constant @Bool@ function)
--
--      * @s@ (@String@)
--
--      * @c@ (@Char@)
--
--      * @i@ (@Int@)
--
--      * @r@ (@(String, String)@, @r@ stands for /rename/)
--
--      * @y@ (@TypeOfNode@)
--
-- For function names the following conventions are used. Every function
-- name is of the form /prefixName/, where /Name/ should describe the
-- purpose of the function and /prefix/ describes the return-type of the
-- function, when all arguments are provided. Options for /prefix/ are:
--
--      * @is@ (@Bool@)
--
--      * @vars@ (@SofiaTree@ of type @Symbol@ which contains a variable)
--
--      * @num@ \/ @max@ \/ @min@ (@Int@)
--
--      * @str@ (@String@)
--
--      * @tree@ (@SofiaTree@)
--
--      * @rn@ (@(String, String)@, @rn@ stands for /rename/)
--
-- Functions not matching any of these return types (maybe because the
-- return type is more general) are not prefixed by the above rule. That is
-- for example the case for all deduction functions as their return type is
-- @Proof@.

-- |A 4-tuple where the first element is the line number, the second
-- element is the line depth, the third is a Sofia expression and the
-- fourth element is the deduction rule that was used to obtain the Sofia
-- expression.
type ProofLine = (Int, Int, SofiaTree, DeductionRule)

-- |A Sofia proof is a sequence of `ProofLine`s
type Proof = [ProofLine]

first :: (a, b, c, d) -> a
first (a, _, _, _) = a

second :: (a, b, c, d) -> b
second (_, b, _, _) = b

third :: (a, b, c, d) -> c
third (_, _, c, _) = c

fourth :: (a, b, c, d) -> d
fourth (_, _, _, d) = d

curLineNo :: Proof -> Int
curLineNo [] = 0
curLineNo x = first $ last x

curDepth :: Proof -> Int
curDepth [] = -1
curDepth x = second $ last x

depthAt :: Int -> Proof -> Int
depthAt i p = second $ getIndex i p


---------------------------- RESTATE HELPERS -----------------------------------

-- |Returns a list resulting from a preorder traversal of tree t and
-- applying s to each subtree; direct children of subtrees are skipped whenever
-- the filter-condition f is not met; this is recursively communicated by
-- setting b to False
preorder :: (SofiaTree -> b) ->  (SofiaTree -> Bool) -> SofiaTree -> Bool -> [b]
preorder s f t b = if getSubtrees t == []
  then ts
  else ts ++ [ x | t' <- (getSubtrees t), x <- preorder' t' ] where
  preorder' t' = if f t then preorder s f t' True else preorder s f t' False
  ts = if b then [s t] else []

-- |'True' if an SofiaTree directly corresponds to a variable; 'False'
-- otherwise.
isVar :: SofiaTree -> Bool
isVar = \t -> length (getSubtrees t) == 1

-- |A list of all variables contained in a tree (does a deep search for
-- variables).
varsDeep :: SofiaTree -> [[Char]]
varsDeep t = rmdups [s | s <- preorder getSymbol isVar t True, s /= ""]

-- |The minimum depth of the occurrence of a variable in a given proof.
minVarDepth :: String -> Proof -> Int
minVarDepth s p = case depths of
                       [] -> -1
                       _  -> minimum depths
                       where
                           depths = [second $ pl | pl <- p,
                                                   elem s (vars (third pl))]

-- |A list of free variables in a specific statement with respect to a given
-- proof.
varsFree :: SofiaTree -> Proof -> [[Char]]
varsFree t p = [v | v <- varsDeep t,
                    or [minVarDepth v p == -1, curDepth p < minVarDepth v p]]
                    -- TODO optimise

-- |Replaces a string x with another string y, if the list rs contains
-- a pair (x, y); otherwise x remains unchanged.
strSub :: [(String, String)] -> String -> String
strSub rs s = if elem s $ map fst rs
                then head [snd r | r <- rs, fst r == s]
                else s

-- |Replaces an SofiaTree x with another SofiaTree y, if the list rs contains
-- a pair (x', y'), where x', y' are the string representations of the
-- trees x, y; otherwise x remains unchanged.
treeSub :: [(String, String)] -> SofiaTree -> SofiaTree
--treeSub rs (newSofiaTrees y ts) = newSofiaTree(strSub rs s) y [treeSub rs t | t <- ts]
treeSub rs t = newSofiaTree(strSub rs (getSymbol t)) (toType t) [treeSub rs t' | t' <- getSubtrees t]

-- |Replaces a string "x" with "x'", "x''", "x'''", "x1", "x2", ... based on
-- the availability as indicated by the list of unavailable variables.
strRenameVar :: String -> [String] -> String
strRenameVar s ss = head (without ([s] ++  [s ++ s' | s' <- ss']) ss) where
    ss' = ["'", "''", "'''"] ++ [show i | i <- [1..]]

-- |Given a variable x, a pair (x, x') is created, where x' is the next
-- available alternative name for x.
rnVar :: String -> Proof -> (String, String)
rnVar s p = (s, strRenameVar s  (boundVars 1 p))

-- |Given a list of variables x1, x2, ... pairs (x1, x1'), (x2, x2') are created,
-- where the xi' are the next available alternatives name for the xi.
rnVarList :: [String] -> Proof -> [(String, String)]
rnVarList ss p = [rnVar s p | s <- ss]

-- |Replaces all variable names in a given expression by the next available
-- alternative name.
treeAutoSub :: SofiaTree -> Proof -> SofiaTree
treeAutoSub t p = treeSub rs t where
    rs = rnVarList ss p
    ss = varsDeep t

-- |Renames one variable in an expression to a provided new name.
treeSubOne :: String -> String -> SofiaTree -> Proof -> SofiaTree
treeSubOne s s' t p = treeSub ss t where
    ss = [(s, strRenameVar s'  (boundVars 1 p))]

---------------------------- SYNAPSIS HELPERS ----------------------------------

vars :: SofiaTree -> [[Char]]
vars tree = [getSymbol x4 | x1 <- filter (\x -> toType x == Statement) [tree],
                            x2 <- filter (\x -> toType x == Atom) (getSubtrees x1),
                            x3 <- filter (\x -> toType x == Formula) (getSubtrees x2),
                            length (getSubtrees x3) == 1, -- TODO make more efficient 
                            x4 <- filter (\x -> toType x == Symbol) (getSubtrees x3)]

getLastBracket :: Proof -> Proof
getLastBracket p = takeWhile (\x -> second x == curDepth p) (reverse p)

pairLastBracket :: Proof -> (SofiaTree, SofiaTree)
pairLastBracket p = (third $ last p', third $ head p') where p' = getLastBracket p

stmtsWithDepthLT :: Int -> Proof -> [SofiaTree]
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

------------------------- Functions generating SofiaTrees  ------------------------- 

equals :: SofiaTree
equals = (newSofiaTree[] Equality [])

implies :: SofiaTree
implies = (newSofiaTree[] Implication [])

truth :: SofiaTree
truth = newSofiaTree[] Statement [newSofiaTree[] Atom []]

makeStatementF :: [SofiaTree] -> SofiaTree
makeStatementF ts = newSofiaTree[] Statement [newSofiaTree[] Atom [newSofiaTree[] Formula ts]]

selfequateT :: Int -> SofiaTree -> SofiaTree
selfequateT pos x =  makeStatementF [n, equals, n] where
                            n = toSofiaTree (getAtom pos x)

restateT :: [(SofiaTree, Int)] -> SofiaTree
restateT xs = newSofiaTree[] Statement atomlist where
    atomlist = [getAtom (snd $ x) (fst $ x) | x <- xs]

synapsisT :: Proof -> SofiaTree
synapsisT p = makeStatementF (newVars ++ [(fst pair), implies, (snd pair)]) where
    pair    = pairLastBracket p
    newVars = [makeStatementF [newSofiaTree v Symbol []] | v <- contextSpecifcVars p,
                                                   not (elem v (vars (fst pair)))]

------------------------- Functions generating Proofs  ------------------------- 

-- |Takes a @String@ @s@ and a @Proof@ @p@ and appends a new @ProofLine@
-- @pl@ to @p@ where the assumption depth is increased by one (with respect to
-- the last @ProofLine@ in @p@) and the @SofiaTree@ in @pl@ is the result
-- of parsing @s@.
assume :: String -> Proof -> Proof
assume s p = p ++ [(1 + curLineNo p, 1 + curDepth p, t, Assumption)] where
    t = treeAutoSub (treeParse s) p

--selfequate :: (Int, Int) -> SofiaTree -> SofiaTree
selfequate :: (Int, Int) -> Proof -> Proof
selfequate (line, pos) p = p ++ [(1 + curLineNo p, curDepth p, t, r)] where
    t = selfequateT pos (third $ getIndex line p)
    r = Selfequate (line, pos)

--restate :: [(Int, Int)] -> SofiaTree -> SofiaTree
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
a = treeParse "[a][r][z][[a]and[b]=[k]]"
