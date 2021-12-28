--{-# LANGUAGE FlexibleInstances #-}
--{-# LANGUAGE UndecidableInstances #-}
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
-- conventions for names of functions and function parameters are used
-- within the @Sofia@ module (but not necessarily within the @SofiaTree@ or
-- @SofiaParser@ modules). Where appropriate (in terms of readability)
-- these conventions are not strictly adhered to. The parameter names are
-- invisible to the user and are only of interest when reading the function
-- definitions. The following list shows the parameter names as well as the
-- type of the parameter in brackets. If within the function definition
-- multiple variables share the same type, one or two apostrophes or the
-- numbers 3, 4, 5, ... are appended to the variable names (in this order).
-- If lists of the respective types are used, then an __s__ (__ss__ for
-- lists of lists and so on) is appended to the respective variable name.
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
--      * @vars@ (@String@ containing a variable name)
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

-- NOTE: currently not in use
numDepthAt :: [ProofLine] -> Int -> Int
numDepthAt p i = numDepth $ getIndex i p

numCurLn :: [ProofLine] -> Int
numCurLn [] = 0
numCurLn x = numLine $ last x

numCurDepth :: [ProofLine] -> Int
numCurDepth [] = -1
numCurDepth x = numDepth $ last x

---------------------- functions to extract variables --------------------------

varsTopLvl :: SofiaTree -> [[Char]]
varsTopLvl tree =
    ts
       where
        ts = [getSymbol x4
             |
             x1 <- filter (\x -> toType x == Statement) [tree],
             x2 <- filter (\x -> toType x == Atom) (getSubtrees x1),
             x3 <- filter (\x -> toType x == Formula) (getSubtrees x2),
             length (getSubtrees x3) == 1,
             x4 <- filter (\x -> toType x == Symbol) (getSubtrees x3)
             ]

treesScope :: [ProofLine] -> [SofiaTree]
treesScope p = map treeFromLn (increasingSublist numDepth p)

varsBound :: [ProofLine] -> [[Char]]
varsBound p = [v | vs <- map varsTopLvl (treesScope p), v <- vs]

-- |Returns a list resulting from a preorder traversal of tree t and
-- applying xf to each subtree; direct children of subtrees are skipped whenever
-- the filter-condition f is not met; this is recursively communicated by
-- setting b to False
preorderFilter :: (SofiaTree -> b) ->
                  (SofiaTree -> Bool) ->
                  SofiaTree ->
                  Bool ->
                  [b]
preorderFilter xf f t b =
    if getSubtrees t == []
    then ts
    else ts ++ [x | t' <- (getSubtrees t), x <- preorder' t'] where
        preorder' t' =
            if f t
            then preorderFilter xf f t' True
            else preorderFilter xf f t' False
        ts =
            if b
            then [xf t]
            else []

-- |'True' if an SofiaTree directly corresponds to a variable; 'False'
-- otherwise.
isVar :: SofiaTree -> Bool
isVar t = 
    and cond
       where
        ts   = (getSubtrees t)
        cond = [length ts == 1, toType (head ts) == Symbol, toType t == Formula]

-- |A list of all variables contained in a tree (does a deep search for
-- variables).
varsDeep :: SofiaTree -> [[Char]]
varsDeep t = rmdups [s | s <- preorderFilter getSymbol isVar t True, s /= ""]

-- |A list of free variables in a specific statement with respect to a given
-- proof.
varsFree :: [ProofLine] -> SofiaTree -> [[Char]]
varsFree p t =
    without [v | v <- varsDeep t]
            (varsBound p)

------------------------ functions for renaming symbols ------------------------

-- |Replaces a string x with another string y, if the list rs contains
-- a pair (x, y); otherwise x remains unchanged.
strSub :: [(String, String)] -> String -> String
strSub rs s =
    if elem s $ map fst rs
    then head [snd r | r <- rs, fst r == s]
    else s

-- |Replaces an SofiaTree x with another SofiaTree y, if the list rs contains
-- a pair (x', y'), where x', y' are the string representations of the
-- trees x, y; otherwise x remains unchanged.
treeSubstSymbol :: [(String, String)] -> SofiaTree -> SofiaTree
treeSubstSymbol rs t =
    newSofiaTree    (strSub rs (getSymbol t))
                    (toType t)
                    [treeSubstSymbol rs t' | t' <- getSubtrees t]

-- |Replaces a string "x" with "x'", "x''", "x'''", "x1", "x2", ... based on
-- the availability as indicated by the list of unavailable variables.
strRenameVar :: String -> [String] -> String
strRenameVar s ss =
    head (without ([s] ++  [s ++ s' | s' <- ss']) ss) where
        ss' = ["'", "''", "'''"] ++ [show i | i <- [1..]]

-- |Given a variable x, a pair (x, x') is created, where x' is the next
-- available alternative name for x.
rnVar :: [ProofLine] -> String -> (String, String)
rnVar p s = (s, strRenameVar s (varsBound p))

-- |Given a list of variables x1, x2, ... pairs (x1, x1'), (x2, x2') are
-- created, where the xi' are the next available alternatives name for the
-- xi.
rnVarList :: [ProofLine] -> [String] -> [(String, String)]
rnVarList p ss = [rnVar p s | s <- ss]

-- |Replaces all variable names in a given expression by the next available
-- alternative name.
treeAutoSubstVars :: [ProofLine] -> SofiaTree -> SofiaTree
treeAutoSubstVars p t =
    treeSubstSymbol rs t where
        rs = rnVarList p ss
        ss = varsDeep t

-- |Renames one variable in an expression to a provided new name.
treeSubstOneSymbol :: [ProofLine] -> String -> String -> SofiaTree -> SofiaTree
treeSubstOneSymbol p s s' t =
    treeSubstSymbol ss t where
        ss = [(s, strRenameVar s'  (varsBound p))]

---------------------------- SYNAPSIS HELPERS ----------------------------------

proofLastBracket :: [ProofLine] -> [ProofLine]
proofLastBracket p =
    reverse p'
       where
        p' = takeWhile (\pl -> numDepth pl >= numCurDepth p) (reverse p)

varsLastContext :: [ProofLine] -> [[Char]]
varsLastContext p =
    without [v | pl <- p', v <- varsDeep (treeFromLn pl)]
            (varsBound p')
       where
        p' = proofLastBracket p

varsContextSpecific :: [ProofLine] -> [[Char]]
varsContextSpecific p =
    rmdups $ intersect [varsDeep t, varsLastContext p]
       where
        t = treeFromLn $ last p

------------------------- Functions generating SofiaTrees  ------------------------- 

treeEQ :: SofiaTree
treeEQ = (newSofiaTree [] Equality [])

treeIMP :: SofiaTree
treeIMP = (newSofiaTree [] Implication [])

treeTRUTH :: SofiaTree
treeTRUTH = newSofiaTree [] Statement [newSofiaTree[] Atom []]

treeSTMT :: [SofiaTree] -> SofiaTree
treeSTMT ts =
        newSofiaTree []
                     Statement
                     [newSofiaTree [] Atom [newSofiaTree[] Formula ts]]

treeDeduceSELF :: SofiaTree -> Int -> SofiaTree
treeDeduceSELF t i = treeSTMT [statement, treeEQ, statement] where
    statement = getAtom i t

treeDeduceREST :: [(SofiaTree, Int)] -> SofiaTree
treeDeduceREST xs = newSofiaTree [] Statement atoms where
    atoms = [getAtom (snd $ x) (fst $ x) | x <- xs]

treeDeduceSYN :: [ProofLine] -> SofiaTree
treeDeduceSYN p = treeSTMT (ts ++ [t, treeIMP, t'])
   where
    p'   = proofLastBracket p
    t    = treeFromLn $ head p'
    t'   = treeFromLn $ last p'
    ts   = [treeSTMT [newSofiaTree v Symbol []]  -- statements introducing
                                                 -- context specific
                                                 -- variables
           |
           v <- varsContextSpecific p,
           not (elem v (varsTopLvl t))  -- exclude variables that were
                                        -- introduced in the first
                                        -- statement of the current bracket
           ]

------------------------- Functions generating Proofs  ------------------------- 

-- |Takes a @String@ @s@ and a @Proof@ @p@ and appends a new @ProofLine@
-- @pl@ to @p@ where the assumption depth is increased by one (with respect to
-- the last @ProofLine@ in @p@) and the @SofiaTree@ in @pl@ is the result
-- of parsing @s@.
assume :: String -> Proof -> Proof
assume s p = p <+> pl
   where
    p' = toListFromProof p
    pl = toProofFromList [newLine
         (1 + numCurLn p')   -- increase line number
         (1 + numCurDepth p') -- increase depth
         t
         Assumption]
    t  = treeAutoSubstVars p' (treeParse s) -- substitute reserved variable
                                            -- names

selfequate :: (Int, Int) -> Proof -> Proof
selfequate (line, col) p = p <+> pl
   where
    p' = toListFromProof p
    pl = toProofFromList [newLine
         (1 + numCurLn p')   -- increase line number
         (numCurDepth p')     -- keep depth the same
         t
         (Selfequate (line, col))]
    t  = treeDeduceSELF (treeFromLn $ getIndex line p') col

restate :: [(Int, Int)] -> String -> Proof -> Proof
restate pos_list s p = p <+> pl
   where
    p' = toListFromProof p
    pl = toProofFromList [newLine
         (1 + numCurLn p')       -- increase line number
         (numCurDepth p')         -- keep depth the same
         (treeSubstOneSymbol p' v s t)    -- substitute first free variable with s
         (Restate pos_list)]
    t  = treeDeduceREST [(t', col)
                        |
                        (line, col) <- pos_list,
                        t' <- [treeFromLn $ getIndex line p']
                        ]
    v  = if vs == []
         then ""
         else head vs           -- first free variable in t (or empty string)
    vs = varsFree p' t          -- list of all free variables in t

synapsis :: Proof -> Proof
synapsis p = p <+> pl
   where
    p' = toListFromProof p
    pl = toProofFromList [newLine
         (1 + numCurLn p')               -- increase line number
         (numCurDepth p' - 1)             -- decrease assumption depth
         (t)
         Synapsis]
    t  = treeDeduceSYN p'

----------------------------------- Examples  ---------------------------------- 

p = assume "[K][[K][b]e[[[c][d]f[a]:[b]]]][r]" newProof
p0 = assume "[[X]=[X]][s]" p
p1 = selfequate (1,1) p0
p2 = restate [(1,2)] "y" p1
p3 = selfequate (2,1) p2
p4 = restate [(5,1)] "K" p3
a = treeParse "[a][r][z][[a]and[b]=[k]]"
