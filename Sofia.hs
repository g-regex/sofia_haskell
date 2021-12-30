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
--      * @v@ (@SofiaTree@ of type @Atom@ which contains a variable)
--
--      * @l@ (@ProofLine@)
--
--      * @f@ (filter function)
--
--      * @b@ (constant @Bool@ function)
--
--      * @c@ (@Char@)
--
--      * @cs@ (@String@)
--
--      * @cscs@ (@(String, String)@)
--
--      * @cscss@ (@[(String, String)]@)
--
--      * @i@ (@Int@)
--
--      * @ii@ (@(Int, Int)@)
--
--      * @iis@ (@[(Int, Int)]@)
--
--      * @y@ (@TypeOfNode@)
--
-- For function names the following conventions are used. Every function
-- name is of the form /prefixName/, where /Name/ should describe the
-- purpose of the function and /prefix/ describes the return-type of the
-- function, when all arguments are provided. Options for /prefix/ are:
--
--      * @is@ \/ @has@ \/ @matches@ (@Bool@)
--
--      * @num@ \/ @max@ \/ @min@ (@Int@)
--
--      * @str@ (@String@)
--
--      * @tree@ (@SofiaTree@)
--
--      * @vars@ (@SofiaTree@ of type @Atom@ which contains a variable)
--
--      * @strstr@ (@(String, String)@)
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
numCurDepth [] = 0
numCurDepth x = numDepth $ last x

----------------------------------- patterns -----------------------------------

type Pattern = (Int, [(TypeOfNode, Int)])

patternFromTree :: SofiaTree -> Int -> Pattern
patternFromTree t depth =
    (depth, preorderFilterDepth (\x -> (toType x, length $ getSubtrees x))
                        (\x -> (toType x, 0))
                        (\x -> True) depth t)

patternAtomParse :: String -> Int -> Pattern
patternAtomParse cs depth =
    patternFromTree (head $ getSubtrees $ treeParse cs) depth

patternVar :: Pattern
patternVar = patternAtomParse "[x]" (-1)

patternEq :: Pattern
patternEq = patternAtomParse "[[x]=[y]]" (2)

patternImp :: Pattern
patternImp = patternAtomParse "[[x]:[y]]" (2)

matchesPattern :: Pattern -> SofiaTree -> Bool
matchesPattern (i, yis) t = patternFromTree t i == (i, yis)

-- |'True' if a SofiaTree is an Atom containing a variable
isVar :: SofiaTree -> Bool
isVar t =  matchesPattern patternVar t

---------------------- functions to extract variables --------------------------

atomsFromStmts :: [SofiaTree] -> [SofiaTree]
atomsFromStmts ts = 
    [t'
    |
    t <- filter (\x -> toType x == Statement) ts,
    t' <- filter (\x -> toType x == Atom) (getSubtrees t)
    ]

strFromVar :: SofiaTree -> [Char] -- TODO: write a more general function
strFromVar t =
    if matchesPattern patternVar t
    then last $ preorderFilter getSymbol (\x -> True) t
    else ""

varsTopLvl :: SofiaTree -> [SofiaTree]
varsTopLvl t = [t' | t' <- ts, isVar t'] where ts = atomsFromStmts [t]

treesScope :: [ProofLine] -> [SofiaTree]
treesScope ls =
    map treeFromLn (reverse (decreasingSublist numDepth (reverse ls)))

atomsScope :: [ProofLine] -> [SofiaTree]
atomsScope ls = atomsFromStmts (treesScope ls)

varsBound :: [ProofLine] -> [SofiaTree]
varsBound ls = [v | vs <- map varsTopLvl (treesScope ls), v <- vs]

atomsConditions :: SofiaTree -> [SofiaTree] -- TODO
atomsConditions t =
    if matchesPattern patternImp t
    then
        [t''
        |
        t' <- takeWhile (\x -> toType x == Statement) ts,
        t'' <- takeWhile (\x -> toType x == Atom) (getSubtrees t')
        ]
    else []
       where
        ts = getSubtrees $ head $ getSubtrees t

treesImplied :: SofiaTree -> SofiaTree -- TODO
treesImplied t =
    if matchesPattern patternImp t
    then
        getIndex 3 $ getSubtrees $ head $ getSubtrees t
    else newSofiaTree "" Error []

leftHS :: Int
leftHS = 1

rightHS :: Int
rightHS = 3

stmtFromEQ :: Int -> SofiaTree -> SofiaTree -- TODO
stmtFromEQ side t =
    if matchesPattern patternEq t
    then
        getIndex side $ getSubtrees $ head $ getSubtrees t
    else newSofiaTree "" Error []

-- |Returns a list resulting from a preorder traversal of a tree t,
-- filtered by a function f. To each matched node a function xf is applied.
preorderFilter :: (SofiaTree -> b) ->
                  (SofiaTree -> Bool) ->
                  SofiaTree ->
                  [b]
preorderFilter xf f t =
    if getSubtrees t == []
    then filtered
    else filtered ++ [x | t' <- (getSubtrees t), x <- preorderFilter xf f t']
       where
        filtered = if f t
               then [xf t]
               else []

-- |Returns a list resulting from a preorder traversal of a tree t up to
-- a depth i, filtered by a function f. To each matched internal node a function
-- xf' and to each match leaf node a function xf'' is applied.
preorderFilterDepth :: (SofiaTree -> b) ->
                  (SofiaTree -> b) ->
                  (SofiaTree -> Bool) ->
                  Int ->
                  SofiaTree ->
                  [b]
preorderFilterDepth xf' xf'' f i t = preorderFDHelper xf' xf'' f i t 0

-- |Helper function for @preorderFilterDepth@. The additonal parameter
-- @cur_depth@ is used to keep track of the current depth during preorder
-- traversal.
preorderFDHelper :: (SofiaTree -> b) ->
                  (SofiaTree -> b) ->
                  (SofiaTree -> Bool) ->
                  Int ->
                  SofiaTree ->
                  Int ->
                  [b]
preorderFDHelper xf' xf'' f max_depth t cur_depth =
    if or [getSubtrees t == [], max_depth == cur_depth]
    then filtered xf''
    else filtered xf' ++ [x
                     |
                     t' <- (getSubtrees t),
                     x <- preorderFDHelper xf' xf'' f max_depth t'
                            (cur_depth + 1)
                     ]
       where
        filtered xf = if f t
               then [xf t]
               else []

-- |A list of all variables (atoms) contained in a tree (does a deep search for
-- variables).
varsDeep :: SofiaTree -> [SofiaTree]
varsDeep t = rmdups [t' | t' <- preorderFilter id isVar t]

-- |A list of free variables (atoms) in a specific statement with respect
-- to a given proof.
varsFree :: [ProofLine] -> SofiaTree -> [SofiaTree]
varsFree p t = without [t' | t' <- varsDeep t] (varsBound p)

------------------------ functions for renaming symbols ------------------------

-- |Replaces `x` with `y`, if the list `xys` contains
-- a pair `(x, y)`; otherwise x remains unchanged.
substitute :: (Eq a) => [(a, a)] -> a -> a
substitute xys x =
    if elem x $ map fst xys
    then head [snd xy | xy <- xys, fst xy == x]
    else x

-- |Replaces a SofiaTree `t` with another SofiaTree `t'`, if the list cscss
-- contains a pair `(cs, cs')`, where `cs`, `cs'` are the string
-- representations of the trees `t`, `t'`; otherwise `t` remains unchanged.
treeSubstSymbol :: [(String, String)] -> SofiaTree -> SofiaTree
treeSubstSymbol cscss t =
    newSofiaTree    (substitute cscss (getSymbol t))
                    (toType t)
                    [treeSubstSymbol cscss t' | t' <- getSubtrees t]

-- |Replaces a SofiaTree `t` (atom) with another SofiaTree `t'`, if the list
-- `aas` contains a pair `(t, t')` and the number of matched occurrences of
-- `t` is in the list `is`; otherwise `t` remains unchanged.
treeSubstTree :: [(SofiaTree, SofiaTree)] -> SofiaTree -> [Int] -> SofiaTree
treeSubstTree aas t is = 
    if t == t'
    then newSofiaTree (getSymbol t)
                      (toType t)
                      (fst (treeSubstTreeHelper aas (getSubtrees t) is 1))
    else t'
       where
        t' = substitute aas t

-- |Helper function for `treeSubstTree`, where the additional variable `i`
-- is used to keep track of the number of the matched occurences of `t`.
treeSubstTreeHelper :: [(SofiaTree, SofiaTree)] ->
                  [SofiaTree] ->
                  [Int] ->
                  Int ->
                  ([SofiaTree], Int)
treeSubstTreeHelper rs [] is i = ([], i)
treeSubstTreeHelper rs (t:ts) is i =
    if or [t == t', not (elem i is)]
    then ((newSofiaTree (getSymbol t)
                        (toType t)
                        (subtree)) : rest_tree, rest_i)
    else (t' : rest_tree, rest_i)
       where
        incr       = if t == t' then 0 else 1
        t'         = substitute rs t
        recur      = treeSubstTreeHelper rs (getSubtrees t) is (i + incr)
        subtree    = fst recur
        cumulative = snd recur
        rest       = treeSubstTreeHelper rs ts is cumulative
        rest_tree  = fst rest
        rest_i     = snd rest

-- |Replaces a string "x" with "x'", "x''", "x'''", "x1", "x2", ... based on
-- the availability as indicated by the list of unavailable variables.
strRenameStr :: String -> [String] -> String
strRenameStr s ss =
    head (without ([s] ++  [s ++ s' | s' <- ss']) ss) where
        ss' = ["'", "''", "'''"] ++ [show i | i <- [1..]]

-- |Given a variable x, a pair (x, x') is created, where x' is the next
-- available alternative name for x.
strstrRename :: [ProofLine] -> String -> (String, String)
strstrRename p s = (s, strRenameStr s (map strFromVar (varsBound p)))

-- |Given a list of variables x1, x2, ... pairs (x1, x1'), (x2, x2') are
-- created, where the xi' are the next available alternatives name for the
-- xi.
strstrsRename :: [ProofLine] -> [String] -> [(String, String)]
strstrsRename p ss = [strstrRename p s | s <- ss]

-- |Replaces all variable names in a given expression by the next available
-- alternative name.
treeAutoSubstSymbols :: [ProofLine] -> SofiaTree -> SofiaTree
treeAutoSubstSymbols p t =
    treeSubstSymbol rs t where
        rs = strstrsRename p ss
        ss = map strFromVar (varsDeep t)

-- |Renames one variable in an expression to a provided new name.
treeSubstOneSymbol :: [ProofLine] -> String -> String -> SofiaTree -> SofiaTree
treeSubstOneSymbol p s s' t =
    treeSubstSymbol ss t where
        ss = [(s, strRenameStr s' (map strFromVar (varsBound p)))]

---------------------------- SYNAPSIS HELPERS ----------------------------------

-- |Given a list of `ProofLine`s (i.e.\ a proof), a list a `ProofLine`s
-- corresponding to the last bracket (i.e.\ /mini-proof/) is returned.
linesLastBracket :: [ProofLine] -> [ProofLine]
linesLastBracket p =
    reverse p'
       where
        p' = takeWhile (\pl -> numDepth pl >= numCurDepth p) (reverse p)

-- |Returns the `String` representations of all variables which where
-- introduced in the context of the last /mini-proof/.
strsLastContext :: [ProofLine] -> [[Char]]
strsLastContext p =
    without [v | pl <- p', v <- map strFromVar (varsDeep (treeFromLn pl))]
            (map strFromVar (varsBound p'))
       where
        p' = linesLastBracket p

-- |Returns the `String` representations of all variables that were
-- introduced in the last /mini-proof/ and occur on its last line.
strsContextSpecific :: [ProofLine] -> [[Char]]
strsContextSpecific p =
    rmdups $ intersect [map strFromVar (varsDeep t), strsLastContext p]
       where
        t = treeFromLn $ last p

-- |Returns a list of `SofiaTree`s (atoms), at the given coordinates.
atomsFromCoords :: [ProofLine] -> [(Int, Int)] -> [SofiaTree]
atomsFromCoords p xs =
    [t | x <- xs, t <- atoms x]
       where
        atoms (line, col) =
            [getAtom col t
            |
            t <- [treeFromLn $ getIndex line p]
            ]

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

treeDeduceREST :: [ProofLine] -> [(Int, Int)] -> SofiaTree
treeDeduceREST p xs = newSofiaTree [] Statement (atomsFromCoords p xs)

treeDeduceSYN :: [ProofLine] -> SofiaTree
treeDeduceSYN p = treeSTMT (ts ++ [t, treeIMP, t'])
   where
    p'   = linesLastBracket p
    t    = treeFromLn $ head p'
    t'   = treeFromLn $ last p'
    ts   = [treeSTMT [newSofiaTree v Symbol []]  -- statements introducing
                                                 -- context specific
                                                 -- variables
           |
           v <- strsContextSpecific p,
           not (elem v (map strFromVar (varsTopLvl t)))
                                        -- exclude variables that were
                                        -- introduced in the first
                                        -- statement of the current bracket
           ]

treeDeduceAPPLY :: [ProofLine] ->
                   [(SofiaTree, SofiaTree)] ->
                   SofiaTree ->
                   SofiaTree
treeDeduceAPPLY p rs t =
    if subset (atomsConditions t') (atomsScope p)
    then treesImplied t'
    else newSofiaTree "" Error []
       where
        t' = treeSubstTree rs t [1..]

treeDeduceLS :: SofiaTree -> SofiaTree -> [Int] -> SofiaTree
treeDeduceLS subst target indices =
    treeSubstTree [(rhs, lhs)] target indices
       where
        lhs = head $ getSubtrees $ stmtFromEQ leftHS subst
        rhs = head $ getSubtrees $ stmtFromEQ rightHS subst

treeDeduceRS :: SofiaTree -> SofiaTree -> [Int] -> SofiaTree
treeDeduceRS subst target indices =
    treeSubstTree [(lhs, rhs)] target indices
       where
        lhs = head $ getSubtrees $ stmtFromEQ leftHS subst
        rhs = head $ getSubtrees $ stmtFromEQ rightHS subst

------------------------- Functions generating Proofs  ------------------------- 

-- |Takes a @String@ @s@ and a @Proof@ @p@ and appends a new @ProofLine@
-- @pl@ to @p@ where the assumption depth is increased by one (with respect to
-- the last @ProofLine@ in @p@) and the @SofiaTree@ in @pl@ is the result
-- of parsing @s@.
assume ::    String -- ^The `String` representation of the Sofia statement to
                    --  be assumed.
          -> Proof
          -> Proof
assume s p = p <+> pl
   where
    p' = toListFromProof p
    pl = toProofFromList [newLine
         (1 + numCurLn p')   -- increase line number
         (1 + numCurDepth p') -- increase depth
         t
         Assumption]
    t  = treeAutoSubstSymbols p' (treeParse s) -- substitute reserved variable
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

-- possible improvement: substitute more than one free variable
restate :: [(Int, Int)] -> String -> Proof -> Proof
restate pos_list s p = p <+> pl
   where
    p' = toListFromProof p
    pl = toProofFromList [newLine
         (1 + numCurLn p')       -- increase line number
         (numCurDepth p')         -- keep depth the same
         (treeSubstOneSymbol p' v s t)    -- substitute first free variable with s
         (Restate pos_list)]
    t  = treeDeduceREST p' pos_list
    v  = if vs == []
         then ""
         else head vs           -- first free variable in t (or empty string)
    vs = map strFromVar (varsFree p' t)   -- list of all free variables in t

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

apply :: Int -> [(Int, Int)] -> Int -> Proof -> Proof
apply line pos_list col p = p <+> pl
   where
    p' = toListFromProof p
    pl = toProofFromList [newLine
         (1 + numCurLn p')       -- increase line number
         (numCurDepth p')         -- keep depth the same
         (t)
         (Apply pos_list)]
    t' = getAtom col $ treeFromLn $ getIndex line p'
    t  = treeDeduceAPPLY p' rs t'
    rs = zip (varsFree p' t') (atomsFromCoords p' pos_list)

rightsub :: Int -> Int -> [Int] -> Int -> Int -> Proof -> Proof
rightsub sub_line tgt_line is sub_col tgt_col p = p <+> pl
   where
    p' = toListFromProof p
    pl = toProofFromList [newLine
         (1 + numCurLn p')               -- increase line number
         (numCurDepth p')
         (t)
         RightSub]
    t  = treeDeduceRS subst target is
    subst = head (atomsFromCoords p' [(sub_line, sub_col)])
    target = head (atomsFromCoords p' [(tgt_line, tgt_col)])

----------------------------------- Examples  ---------------------------------- 

p = assume "[K][b][[K][b]:[[[c][d]f[a]:[b]]]][r]" newProof
p0 = assume "[[X]=[X]][s]" p
p1 = selfequate (1,1) p0
p2 = restate [(1,2)] "y" p1
p3 = selfequate (2,1) p2
p4 = restate [(5,1)] "K" p3
p5 = assume "[K]" p4
p6 = synapsis p5

px = toListFromProof p6
px1 = treeFromLn $ getIndex 1 px
px2 = getIndex 3 (getSubtrees px1)

{->>>> S.a("[[Mark[]] is human][[X][[X] is human]:[[X] can feel]]")
>>>> S.a("[Mark[]]")
>>>> S.d(1,[[2,1]],2)-}

q1 = assume "[[Mark[]] is human][[X][[X] is human]:[[X] can feel]]" newProof
q2 = assume "[Mark[]]" q1
q3 = apply 1 [(2,1)] 2 q2
q4 = synapsis q3
q5 = synapsis q4

m1 = assume "[X][Y][[X]=[Y]]" newProof
m2 = selfequate (1,1) m1
m3 = rightsub 1 2 [1] 3 1 m2
m4 = synapsis m3

a2 = treeFromLn (plast q2)

a = treeParse "[[a]=[b]]"
b = treeParse "[r]"
c = treeParse "[[t]he]"
b1 = getAtom 1 b
c1 = getAtom 1 c

-- QUESTIONS:
-- How are statements that comprise several atoms are to be replaced? / Is
-- the form of an equality always [..]=[..]?
