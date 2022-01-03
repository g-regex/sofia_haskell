--{-# LANGUAGE FlexibleInstances #-}
--{-# LANGUAGE UndecidableInstances #-}

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
    -- * Naming Convention
    -- $naming

    -- * General commands
    postulate,

    -- * Proof building commands
    assume,
    recall,
    restate,
    selfequate,
    synapsis,
    apply,
    rightsub,
    leftsub,

    -- * Patterns
    -- $patterns
    Pattern,
    patternFromTree,
    patternAtomParse,
    -- $somepatterns
    patternVar,
    patternEq,
    patternImp,
    -- $matching
    matchesPattern,
    isVar,
    -- $matchingexample

    -- *Scope
    -- $scope
    atomsFromStmts,
    treesScope,
    atomsScope,
    -- $scopeexample

    -- *Variables
    -- $variables
    varsTopLvl,
    varsBound,
    varsDeep,
    varsFree,

    -- *Substitution
    -- $substitution
    substitute,
    treeSubstSymbol,
    treeSubstTree,
    strAltName,
    strstrsRename,
    treeAutoSubstSymbols,
    treeSubstOneSymbol

    -- *Examples
    -- $examples
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
--      * @f@ (filter function, i.e.\ @(a -> Bool)@)
--
--      * @b@ (@Bool@)
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
--      * @pattern@ (@Pattern@)
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
-- $patterns
-- In order to identify certain classes of expressions the `Pattern` data
-- type is introduced.

-- |A `Pattern` is an ordered pair of an integer and a list. The integer
-- indicates the depth of a to be performed preorder traversal of
-- a `SofiaTree`. The list contains ordered pairs where the first component
-- indicates the expected `TypeOfNode` of a traversed node and the second
-- component indicates the number of child nodes or 0, if the node is
-- a leaf node. Nodes at the maximum depth of the preorder traversal are
-- considered leaf nodes..
type Pattern = (Int, [(TypeOfNode, Int)])

-- |Creates a `Pattern` from a `SofiaTree` with a given maximum depth.
patternFromTree ::     SofiaTree    -- ^The `SofiaTree`.
                    -> Int          -- ^The maximum depth (-1 means infinity).
                    -> Pattern      -- ^The resulting pattern.
patternFromTree t depth =
    (depth, preorderFilterDepth (\x -> (toType x, length $ getSubtrees x))
                        (\x -> (toType x, 0))
                        (\x -> True) depth t)

-- |Creates a `Pattern` with a specified maximum depth from a given `String`
-- containing a statement with exactly one atom. Instead of starting the
-- preorder traversal at the root of the corresponding `SofiaTree`, the
-- traversal is started at the only child of the root, which is an atom.
patternAtomParse ::    String   -- ^The String.
                    -> Int      -- ^The maximum depth (-1 means infinity).
                    -> Pattern  -- ^The resulting pattern.
patternAtomParse cs depth =
    patternFromTree (head $ getSubtrees $ treeParse cs) depth

-- $somepatterns
-- `Pattern`s for common structures can now be created.
-- To identify a `SofiaTree` containing a variable we can for example
-- create the following `Pattern`:
-- 
-- >>> patternAtomParse "[x]" (-1)
-- (-1,[(Atom,1),(Formula,1),(Symbol,0)])
--
-- For convenience we create `Pattern`s for the most commonly occurring
-- structures, namely variables, equalities and implications.

-- |Contains the pattern to identify a variable.
patternVar :: Pattern
patternVar = patternAtomParse "[x]" (-1)

-- |Contains the pattern to identify an equality.
patternEq :: Pattern
patternEq = patternAtomParse "[[x]=[y]]" (2)

-- |Contains the pattern to identify an implication.
patternImp :: Pattern
patternImp = patternAtomParse "[[x]:[y]]" (2)

-- $matching
-- To simplify the code further, the following `Pattern` matching functions
-- are introduced.

-- |Returns `True` if the given `SofiaTree` matches the given pattern and
-- `False` otherwise.
matchesPattern ::      Pattern      -- ^The `Pattern` to be matched.
                    -> SofiaTree    -- ^The `SofiaTree`.
                    -> Bool         -- ^The resulting `Bool`.
matchesPattern (i, yis) t = patternFromTree t i == (i, yis)

-- |'True' if a SofiaTree is an Atom containing a variable
isVar :: SofiaTree -> Bool
isVar t =  matchesPattern patternVar t

-- $matchingexample
-- We can now check whether a given `SofiaTree` is for example a variable.
-- Since our template `Pattern` was created with `patternAtomParse`, we
-- have to make sure that the `SofiaTree` which should match the `Pattern`
-- is an atom as well. To create an example `SofiaTree` we use the
-- `treeParse` function from the `SofiaTree` module. To access the children
-- of the root we use the `getSubtrees` function from the same module.
--
-- >>> isVar $ head $ getSubtrees $ treeParse "[a]"
-- True

------------------------------------ scope -------------------------------------
-- $scope
-- A `ProofLine` `a` (statement) is said to be in the /scope/ of of another
-- `ProofLine` `b` of the same `Proof`, if and only if the reversed list of all
-- `ProofLine`s in the `Proof` contains a sublist whose first and last
-- `ProofLine`s are `b` and `a` respectively and which is such that the
-- list of the assumption depths of the `ProofLine`s in this sublist are
-- increasing.

-- |Given a list of statements a list of atoms which make up these
-- statements is returned.
atomsFromStmts ::      [SofiaTree]  -- ^The list of statements.
                    -> [SofiaTree]  -- ^The list of atoms.
atomsFromStmts ts = 
    [t'
    |
    t <- filter (\x -> toType x == Statement) ts,
    t' <- filter (\x -> toType x == Atom) (getSubtrees t)
    ]

-- |Given a list of `ProofLine`s a list of trees which are in the scope of
-- the last `ProofLine` in the list is returned.
treesScope ::      [ProofLine]  -- ^The list of `ProofLine`s.
                -> [SofiaTree]  -- ^The resulting list of `SofiaTree`s.
treesScope ls =
    map treeFromLn (reverse (decreasingSublist numDepth (reverse ls)))

-- |Given a list of `ProofLine`s a list of atoms which are in the scope of
-- the last `ProofLine` in the list is returned.
atomsScope ::      [ProofLine]  -- ^The list of `ProofLine`s.
                -> [SofiaTree]  -- ^The resulting list of atoms.
atomsScope ls = atomsFromStmts (treesScope ls)

-- $scopeexample
-- To illustrate the behaviour of the functions above, we consider the
-- following partial `Proof` of Russel's paradox. We use the function
-- `toListFromProof` to convert from a `Proof` to a list of `ProofLine`s.
-- 
-- >>> ex8_6
-- ╔[X][[x]:[[[x]in[X]]=[[[x]in[x]]:[False[]]]]] /L1: assumption.
-- ║[[[X]in[X]]=[[[X]in[X]]:[False[]]]] /L2: application of L1.2 (with concretization [(1,1)]).
-- ║╔[[X]in[X]] /L3: assumption.
-- ║║[[[X]in[X]]:[False[]]] /L4: right substitution, L2(1) in L3(1).
-- ║╚[False[]] /L5: application of L4.1 (with concretization []).
-- ║[[[X]in[X]]:[False[]]] /L6: synapsis (L3-5).
-- >>> atomsScope $ toListFromProof ex8_6
-- [[X],[[x]:[[[x]in[X]]=[[[x]in[x]]:[False[]]]]],[[[X]in[X]]=[[[X]in[X]]:[False[]]]],[[[X]in[X]]:[False[]]]]
--
-- The resulting list contains all atoms from lines 1, 2 and
-- 6 respectively.

---------------------- functions to extract variables --------------------------
-- $variables
-- Variables are a fundamental concept in the Sofia language. To handle
-- them efficiently a number of functions are introduced.

-- |Given an atom containing a variable, the symbol (i.e.\ `String`)
-- representing the variable is returned.
strFromVar ::      SofiaTree  -- ^The atom containing a variable.
                -> [Char]     -- ^The `String` representation of the variable.
strFromVar t =
    if matchesPattern patternVar t
    then last $ preorderFilter getSymbol (\x -> True) t
    else ""

-- |Given a statement the variables introduced as children of the root of
-- the corresponding `SofiaTree` are returned in a list.
varsTopLvl ::   SofiaTree   -- ^The statement.
             -> [SofiaTree] -- ^The list of variables.
varsTopLvl t = [t' | t' <- ts, isVar t'] where ts = atomsFromStmts [t]

-- |Given a list of `ProofLine`s, a list a variables which are bound on the
-- last `ProofLine` in the list is returned.
varsBound ::       [ProofLine] -- ^The list of `ProofLine`s
                -> [SofiaTree] -- ^The resulting list of variables.
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

-- |Returns a list of all variables (atoms) contained in a `SofiaTree`
-- (does a deep search for variables).
varsDeep ::    SofiaTree    -- ^The `SofiaTree` to be searched for variables.
            -> [SofiaTree]  -- ^The resulting list of found variables.
varsDeep t = rmdups [t' | t' <- preorderFilter id isVar t]

-- |Returns a list of free variables (atoms) in a specific statement with
-- respect to a given proof.
varsFree ::     [ProofLine] -- ^A list a `ProofLine`s constituting the proof.
             -> SofiaTree   -- ^The `SofiaTree` which should be searched for
                            --  free variables.
             -> [SofiaTree] -- ^The resulting list of free variables.
varsFree p t = without [t' | t' <- varsDeep t] (varsBound p)

------------------------ functions for renaming symbols ------------------------
-- $substitution
-- If a statement is recalled and it contains variables whose name are
-- already in use, these variables must be renamed. Similarly, if an
-- implication is applied and the assumption depth is decreased, it might
-- become necessary to rename variables to not get in conflict with
-- variables which are deeper nested in the proof structure. Besides these
-- two cases, the user might want to replace whole statements with other
-- statements, when making use of equalities. The following functions
-- enable us to do all these things.

-- |Replaces `x` with `y`, if the list `xys` of ordered pairs contains
-- a pair `(x, y)`; otherwise x remains unchanged.
substitute :: (Eq a) => 
                 [(a, a)] -- ^The list `xys` of ordered pairs (i.e.\ possible
                          --  substitutions).
              -> a        -- ^Object `x` to be substituted.
              -> a        -- ^The (possibly substituted) object.
substitute xys x =
    if elem x $ map fst xys
    then head [snd xy | xy <- xys, fst xy == x]
    else x

-- |Replaces a SofiaTree `t` with another SofiaTree `t'`, if the list `cscss`
-- contains a pair `(cs, cs')`, where `cs`, `cs'` are the string
-- representations of the trees `t`, `t'`; otherwise `t` remains unchanged.
treeSubstSymbol ::      [(String, String)] -- ^The list `cscss` of ordered pairs
                                           --  (i.e.\ possible substitutions).
                     -> SofiaTree          -- ^`SofiaTree` `t` to be substituted.
                     -> SofiaTree          -- ^The resulting (possibly
                                           --  substituted) `SofiaTree`.
treeSubstSymbol cscss t =
    newSofiaTree    (substitute cscss (getSymbol t))
                    (toType t)
                    [treeSubstSymbol cscss t' | t' <- getSubtrees t]

-- |Replaces a SofiaTree `t` (atom) with another SofiaTree `t'`, if the list
-- `aas` contains a pair `(t, t')` and the number of matched occurrences of
-- `t` is in the list `is`; otherwise `t` remains unchanged.
treeSubstTree ::    [(SofiaTree, SofiaTree)] -- ^The list `cscss` of ordered pairs
                                             --  (i.e.\ possible substitutions).
                 -> SofiaTree                -- ^`SofiaTree` `t` to be
                                             --  substituted.
                 -> [Int]                    -- ^List `is` of indices of
                                             --  occurrences to be
                                             --  replaced.
                 -> SofiaTree                -- ^The resulting (possibly
                                             --  substituted) `SofiaTree`.
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
strAltName :: String -> [String] -> String
strAltName s ss =
    head (without ([s] ++  [s ++ s' | s' <- ss']) ss) where
        ss' = ["'", "''", "'''"] ++ [show i | i <- [1..]]

-- |Given a list of variables x1, x2, ... pairs (x1, x1'), (x2, x2') are
-- created, where the xi' are the next available alternative name for the
-- xi.
strstrsRename ::   [SofiaTree]        -- ^List of unavailable variables.
                -> [SofiaTree]        -- ^List of variables to be renamed.
                -> [(String, String)] -- ^A list of pairs of the form
                                      --  (/old name/, /new name/).
strstrsRename ts ts' = [strstrR t | t <- ts']
   where
    strstrR t = (cs, strAltName cs (map strFromVar ts))
       where
        cs = strFromVar t

-- |Replaces all variable names in a given expression by the next available
-- alternative name in the context of a given proof.
treeAutoSubstSymbols ::    [ProofLine] -- ^A list a `ProofLine`s constituting
                                       --  the proof.
                        -> SofiaTree   -- ^The expression in which variables
                                       --  shoujld be renamed.
                        -> Bool        -- ^Should be set to `True`, if bound
                                       --  variable names may be used;
                                       --  should be set to `False`, if
                                       --  bound variable names must be
                                       --  replaced.
                        -> SofiaTree   -- ^The resulting expression with renamed
                                       --  variables.
treeAutoSubstSymbols ls t b =
     (treeSubstSymbol cscs2 (treeSubstSymbol cscs1 t)) where
        varsMentioned = [t | ts <- map varsDeep $ map treeFromLn ls, t <- ts] 
        vs1           = (without (varsTopLvl t) (varsBound ls))
        cscs1         = strstrsRename (without varsMentioned (varsBound ls)) vs1
        vs2           = if b then [] else (varsDeep t)
        cscs2         = if b then [] else strstrsRename (varsBound ls) vs2

-- |Renames one variable in an expression to a provided new name or the
-- next available alternative in the context of a given proof.
treeSubstOneSymbol ::   [ProofLine] -- ^A list a `ProofLine`s constituting
                                    --  the proof.
                     -> String      -- ^`String` representation of the variable
                                    --  to be renamed (e.g.\ "x")
                     -> String      -- ^`String representation of the suggested
                                    --  new name for the variable (e.g.\
                                    --  "y")
                     -> SofiaTree   -- ^The expression in which the variable
                                    --  should be renamed.
                     -> SofiaTree   -- ^The resulting expression.
treeSubstOneSymbol ls cs cs' t =
    treeSubstSymbol cscss t where
        cscss = [(cs, strAltName cs' (map strFromVar (varsBound ls)))]

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
            (map strFromVar (varsBound p))
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

treeSTMT' :: [SofiaTree] -> SofiaTree
treeSTMT' ts =
        newSofiaTree []
                     Statement
                     ts

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
    treeSTMT' [treeSubstTree [(rhs, lhs)] target indices]
       where
        lhs = head $ getSubtrees $ stmtFromEQ leftHS subst
        rhs = head $ getSubtrees $ stmtFromEQ rightHS subst

treeDeduceRS :: SofiaTree -> SofiaTree -> [Int] -> SofiaTree
treeDeduceRS subst target indices =
    treeSTMT' [treeSubstTree [(lhs, rhs)] target indices]
       where
        lhs = head $ getSubtrees $ stmtFromEQ leftHS subst
        rhs = head $ getSubtrees $ stmtFromEQ rightHS subst

-- |Takes a `String` representation of a Sofia statement and `String`
-- containing a name for the statement and converts it to an ordered pair
-- containing the corresponding `SofiaTree` and the name for later use as
-- an axiom or theorem in a `Proof`.
postulate ::     String                 -- ^The `String` representation of the
                                        --  axiom or theorem..
              -> String                 -- ^The name of the axiom or theorem.
              -> (SofiaTree, String)    -- ^The resulting `SofiaTree`, paired
                                        --  with the name of the axiom or
                                        --  theorem.
postulate cs cs' = (treeParse cs, cs')

------------------------- Functions generating Proofs  ------------------------- 

-- |Takes a @String@ @s@ and a @Proof@ @p@ and appends a new @ProofLine@
-- @pl@ to @p@ where the assumption depth is increased by one (with respect to
-- the last @ProofLine@ in @p@) and the @SofiaTree@ in @pl@ is the result
-- of parsing @s@.
assume ::        String       -- ^The `String` representation of the Sofia
                              --  statement to be assumed.
              -> Proof        -- ^The `Proof` to which the generated `ProofLine`
                              --  should be appended to.
              -> Proof        -- ^The resulting `Proof`.
assume s p = p <+> pl
   where
    p' = toListFromProof p
    pl = toProofFromList [newLine
         (1 + numCurLn p')          -- increase line number
         (1 + numCurDepth p')       -- increase depth
         t
         Assumption]
    t  = treeParse s

-- |Takes an ordered pair, previously generated by `postulate`, and
-- a `Proof` `p` and appends a new `ProofLine` to `p`, containing the
-- `SofiaTree` from the ordered pair.
-- The assumption depth is kept the same (with respect to the last
-- `ProofLine` in `p`).
recall ::        (SofiaTree, String)    -- ^The ordered pair, previously
                                        --  generated by `postulate`.
              -> Proof        -- ^The `Proof` to which the generated `ProofLine`
                              --  should be appended to.
              -> Proof        -- ^The resulting `Proof`.
recall tcs p = p <+> pl
   where
    p' = toListFromProof p
    pl = toProofFromList [newLine
         (1 + numCurLn p')              -- increase line number
         (numCurDepth p')               -- keep depth
         t'
         (Recall (snd tcs))]
    t' = treeAutoSubstSymbols p' (fst tcs) False  -- substitute reserved variable
                                            -- names

-- |Equates a statement at a given position to itself.
selfequate ::    (Int, Int)   -- ^Position of the form /(line, column)/ of the
                              --  statement that should be equated to itself.
              -> Proof        -- ^The `Proof` to which the generated `ProofLine`
                              --  should be appended to.
              -> Proof        -- ^The resulting `Proof`.
selfequate (line, col) p = p <+> pl
   where
    p' = toListFromProof p
    pl = toProofFromList [newLine
         (1 + numCurLn p')          -- increase line number
         (numCurDepth p')           -- keep depth the same
         t
         (Selfequate (line, col))]
    t  = treeDeduceSELF (treeFromLn $ getIndex line p') col

-- TODO: possible improvement: substitute more than one free variable
-- |Restates given statements and renames the first free variable with
-- a provided name.
restate ::       [(Int, Int)] -- ^List of positions of the form /(line, column)/
                              --  of the atoms from which the new statement
                              --  should be built.
              -> String       -- ^The new name of variable to be renamed; empty
                              --  `String` if no renaming is desired.
              -> Proof        -- ^The `Proof` to which the generated `ProofLine`
                              --  should be appended to.
              -> Proof        -- ^The resulting `Proof`.
restate pos_list s p = p <+> pl
   where
    p' = toListFromProof p
    pl = toProofFromList [newLine
         (1 + numCurLn p')              -- increase line number
         (numCurDepth p')               -- keep depth the same
         (treeSubstOneSymbol p' v s t)  -- substitute first free variable with s
         (Restate pos_list)]
    t  = treeDeduceREST p' pos_list
    v  = if vs == []
         then ""
         else head vs                     -- first free variable in t
                                          -- (or empty string)
    vs = map strFromVar (varsFree p' t)   -- list of all free variables in t


-- |Steps out of the current `mini-proof', which is summarised by
-- a statement, stating that the first line of the `mini-proof' implies its
-- last line. Newly introduced variables are included in the beginning of
-- this statement.
synapsis ::      Proof        -- ^The `Proof` to which the generated `ProofLine`
                              --  should be appended to.
              -> Proof        -- ^The resulting `Proof`.
synapsis p = p <+> pl
   where
    p' = toListFromProof p
    pl = toProofFromList [newLine
         (1 + numCurLn p')                -- increase line number
         (numCurDepth p' - 1)             -- decrease assumption depth
         (t)
         (Synapsis i1 i2)]
    t  = treeDeduceSYN p'
    ls = linesLastBracket p'
    i1 = numLine (head ls)
    i2 = numLine (last ls)

-- |Applies an implication. Given a list of statements (their positions),
-- free variables in the implication are replaced by the statements. Then
-- the conditions of the implication are checked and if they match
-- statements (atoms) within the scope of the current line of the proof,
-- the implied statement forms the new `ProofLine`.
apply ::         Int          -- ^The line of the implication to be applied.
              -> [(Int, Int)] -- ^List of positions of the form /(line, column)/
                              --  of the atoms used for the replacements.
              -> Int          -- ^The column of the implication to be applied.
              -> Proof        -- ^The `Proof` to which the generated `ProofLine`
                              --  should be appended to.
              -> Proof        -- ^The resulting `Proof`.
apply line pos_list col p = p <+> pl
   where
    p' = toListFromProof p
    pl = toProofFromList [newLine
         (1 + numCurLn p')          -- increase line number
         (numCurDepth p')           -- keep depth the same
         (t)
         (Apply line pos_list col)]
    t' = getAtom col $ treeFromLn $ getIndex line p'
    t  = treeAutoSubstSymbols p' (treeDeduceAPPLY p' rs t') True
    rs = zip (varsFree p' t') (atomsFromCoords p' pos_list)

-- |Right substitution: The right hand side of the equality at a given
-- position replaces certain occurences (whose indicies, numbered in
-- a preorder traversal, are given in a list) of the left hand side of
-- the equality in a given statement.
rightsub ::     Int         -- ^The line number of the equality.
             -> Int         -- ^The line number of the statement.
             -> [Int]       -- ^The list of indices
             -> Int         -- ^The column number of the equality.
             -> Int         -- ^The column number of the statement.
             -> Proof       -- ^The `Proof` to which the generated `ProofLine`
                            --  should be appended to.
             -> Proof       -- ^The resulting `Proof`.
rightsub sub_line tgt_line is sub_col tgt_col p = p <+> pl
   where
    p' = toListFromProof p
    pl = toProofFromList [newLine
         (1 + numCurLn p')               -- increase line number
         (numCurDepth p')
         (t)
         (RightSub sub_line tgt_line is sub_col tgt_col)]
    t  = treeDeduceRS subst target is
    subst = head (atomsFromCoords p' [(sub_line, sub_col)])
    target = head (atomsFromCoords p' [(tgt_line, tgt_col)])

-- |Left substitution: The left hand side of the equality at a given
-- position replaces certain occurences (whose indicies, numbered in
-- a preorder traversal, are given in a list) of the right hand side of
-- the equality in a given statement.
leftsub ::      Int         -- ^The line number of the equality.
             -> Int         -- ^The line number of the statement.
             -> [Int]       -- ^The list of indices
             -> Int         -- ^The column number of the equality.
             -> Int         -- ^The column number of the statement.
             -> Proof       -- ^The `Proof` to which the generated `ProofLine`
                            --  should be appended to.
             -> Proof       -- ^The resulting `Proof`.
leftsub sub_line tgt_line is sub_col tgt_col p = p <+> pl
   where
    p' = toListFromProof p
    pl = toProofFromList [newLine
         (1 + numCurLn p')               -- increase line number
         (numCurDepth p')
         (t)
         (LeftSub sub_line tgt_line is sub_col tgt_col)]
    t  = treeDeduceLS subst target is
    subst = head (atomsFromCoords p' [(sub_line, sub_col)])
    target = head (atomsFromCoords p' [(tgt_line, tgt_col)])

--------------------------------------------------------------------------------
-- TODO:
-- * handling mistakes
-- * axiom builders
-- * add an option for not replacing variable names, when restating
-- * user interface
--
-- QUESTIONS:
-- How are statements that comprise several atoms are to be replaced? / Is
-- the form of an equality always [..]=[..]?
--
-- Can variables be replaced by statements?
--
----------------------------------- Examples  ---------------------------------- 
-- "Reflexivity of Equality"
ex1_1 = assume "[X]" newProof
ex1_2 = selfequate (1,1) ex1_1
ex1_3 = synapsis ex1_2
--
-- "Symmetry of Equality"
ex3_1 = assume "[X][Y][[X]=[Y]]" newProof
ex3_2 = selfequate (1,1) ex3_1
ex3_3 = rightsub 1 2 [1] 3 1 ex3_2
ex3_4 = synapsis ex3_3
--
-- "Transitivity of Equality"
ex4_1 = assume "[X][Y][Z][[X]=[Y]][[Y]=[Z]]" newProof
ex4_2 = rightsub 1 1 [1] 5 4 ex4_1
ex4_3 = synapsis ex4_2
--
-- "Mark can feel"
ex5_1 = assume "[[Mark[]] is human][[X][[X] is human]:[[X] can feel]]" newProof
ex5_2 = assume "[Mark[]]" ex5_1
ex5_3 = apply 1 [(2,1)] 2 ex5_2
ex5_4 = synapsis ex5_3
ex5_5 = synapsis ex5_4
--
-- "Mark can feel 2"
ex6_1 = assume "[Mark[]][[Mark[]] is human][[X][[X] is human]:[[X] can feel]]"
            newProof
ex6_2 = apply 1 [(1,1)] 3 ex6_1
ex6_3 = synapsis ex6_2
--
-- "Subset Axiom"
axiom_subset = postulate ("[[X][[X] is a set][Y][[Y] is a set]:[[[X] sub " ++
    "[Y]]=[[x][[x] is a set]:[[[x] in [X]]:[[x] in [Y]]]]]]") "Subset Axiom"
--
-- "Subset Reflexivity"
ex7_1 = assume "[X][[X] is a set]" newProof
ex7_2 = assume "[x][[x] is a set]" ex7_1
ex7_3 = assume "[[x] in [X]]" ex7_2
ex7_4 = restate [(3,1)] "" ex7_3
ex7_5 = synapsis ex7_4
ex7_6 = synapsis ex7_5
ex7_7 = recall axiom_subset ex7_6
ex7_8 = apply 7 [(1,1), (1,1)] 1 ex7_7
ex7_9 = leftsub 8 6 [1..] 1 1 ex7_8
ex7_10 = synapsis ex7_9
--
-- "Russel"
ex8_1 = assume "[X][[x]:[[[x] in [X]]=[[[x] in [x]]:[False[]]]]]" newProof
ex8_2 = apply 1 [(1,1)] 2 ex8_1
ex8_3 = assume "[[X] in [X]]" ex8_2
ex8_4 = rightsub 2 3 [1..] 1 1 ex8_3
ex8_5 = apply 4 [] 1 ex8_4
ex8_6 = synapsis ex8_5
ex8_7 = leftsub 2 6 [1..] 1 1 ex8_6
ex8_8 = apply 6 [] 1 ex8_7
ex8_9 = synapsis ex8_8
--
-- "Axiom: Addition"
axiom_addition = postulate "[[x][y][[x]num][[y]num]:[[x]+[y]][[[x]+[y]]num]]"
                    "Addition"
--
-- "Axiom: Number construction"
axiom_number_construction = postulate "[0[]][[0[]]num][1[]][[1[]]num]"
                                "Number construction"
--
-- "Axiom: Commutativity"
axiom_commutativity = postulate "[[x][y][[x]num][[y]num]:[[[x]+[y]]=[[y]+[x]]]]"
                        "Commutativity"
--
-- "Axiom: Associativity"
axiom_associativity = postulate ("[[x][y][z][[x]num][[y]num][[z]num]:" ++
                        "[[[[x]+[y]]+[z]]=[[x]+[[y]+[z]]]]]")
                        "Associativity"
--
-- "Axiom: Identity"
axiom_identity = postulate "[[x][[x]num]:[[[0[]]+[x]]=[x]]]" "Identity"
--
-- "Right Identity"
ex9_1 = assume "[x][[x]num]" newProof
ex9_2 = recall axiom_identity ex9_1
ex9_3 = recall axiom_commutativity ex9_2
ex9_4 = apply 2 [(1,1)] 1 ex9_3
ex9_5 = recall axiom_number_construction ex9_4
ex9_6 = apply 3 [(1,1),(5,1)] 1 ex9_5
ex9_7 = recall axiom_identity ex9_6
ex9_8 = apply 7 [(1,1)] 1 ex9_7
ex9_9 = rightsub 8 6 [1..] 1 1 ex9_8
ex9_10 = synapsis ex9_9
--
-- "Axiom: Variable Introduction"
axiom_variable_introduction = postulate "[[x]:[y][[y]=[x]]]"
                                "Variable Introduction"
--
-- "Existential Theorem Example"
right_identity = (treeFromLn $ plast ex9_10, "Right Identity")
ex10_1 = recall axiom_number_construction newProof
ex10_2 = recall right_identity ex10_1
ex10_3 = recall axiom_variable_introduction ex10_2
ex10_4 = apply 3 [(1,1)] 1 ex10_3
ex10_5 = leftsub 4 1 [1..] 2 2 ex10_4
ex10_6 = leftsub 4 2 [1..] 2 1 ex10_5
ex10_7 = restate [(5,1),(6,1)] "x" ex10_6

-- $examples
-- At the end of the source of the `Sofia` some of the examples from the
-- Python version were converted to this Haskell version. For completeness'
-- sake the output of a selection of these examples is given here.
--
-- >>> ex1_3
-- ╔[X] /L1: assumption.
-- ╚[[X]=[X]] /L2: self-equate from L1(1).
-- [[X]:[[X]=[X]]] /L3: synapsis (L1-2).
--
-- >>> ex3_4
-- ╔[X][Y][[X]=[Y]] /L1: assumption.
-- ║[[X]=[X]] /L2: self-equate from L1(1).
-- ╚[[Y]=[X]] /L3: right substitution, L1(3) in L2(1).
-- [[X][Y][[X]=[Y]]:[[Y]=[X]]] /L4: synapsis (L1-3).
--
-- >>> ex4_3
-- ╔[X][Y][Z][[X]=[Y]][[Y]=[Z]] /L1: assumption.
-- ╚[[X]=[Z]] /L2: right substitution, L1(5) in L1(4).
-- [[X][Y][Z][[X]=[Y]][[Y]=[Z]]:[[X]=[Z]]] /L3: synapsis (L1-2).
