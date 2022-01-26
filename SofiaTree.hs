{-# OPTIONS_HADDOCK prune #-}

{-|
Module      : SofiaTree
Description :
Copyright   :
License     :
Maintainer  :
Stability   : experimental
Portability : POSIX

The `SofiaTree` module contains definitions of data types created
specifically for the Sofia proof assistant.
-}

module SofiaTree
    (TypeOfNode (Atom, Statement, Formula, Implication, Equality, Symbol,
                 Placeholder, Error),
     Tree,
     SofiaTree,
     DeductionRule (Assumption, Recall, Selfequate, Restate, Synapsis, Apply,
                    RightSub, LeftSub),
     ProofLine,
     Proof (PListEnd),

     -- * Operators
     (<+>),
     pdo,
     plast,
     phead,
     preverse,

     -- Extracting parameters
     getAtom,
     getSubtrees,
     getSymbol,
     numLine,
     numDepth,
     treeFromLn,
     ruleFromLn,
     toSofiaTree,
     toType,

     -- * Converting types
     toListFromProof,
     toProofFromList,

     newSofiaTree,
     newProof,
     newLine) where

import ListHelpers

class Printable a where
    printable :: a -> String

instance Printable Char where
    printable x = id [x]

toString :: Printable a => [a] -> String
toString [] = ""
toString (x:xs) = (printable x) ++ (toString xs)

-- |Nodes in a `SofiaTree` must have a type not equal to `Error`.
data TypeOfNode = Atom | Statement | Formula | Implication | Equality | Symbol |
                  Placeholder | Error
                  deriving (Show -- ^Membership of the `Show` class is derived
                                 --  (for debugging purposes).
                           , Eq  -- ^Membership of the `Eq` class is derived. 
                           )
-- |A 'Tree' is a `Node` parametrised with two types of values (a list and
-- another value) and a list of sub'Tree's.
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
    show (Node a b c) =
        case toType b of
             Error          -> "Error" 
             Placeholder    -> "..." 
             Atom           -> "[" ++ showtree c ++ "]"
             Implication    -> ":"
             Equality       -> "="
             Symbol         -> toString a
             _              -> showtree c
            where showtree z = case z of
                                    []   -> ""
                                    x:xs -> (show x) ++ (showtree xs)

-- |A (possibly parametrised) deduction rule.
data DeductionRule = Assumption String | Selfequate (Int, Int)
                     | Restate [(Int, Int)] [String]
                     | Synapsis Int Int | Apply Int [(Int, Int)] Int
                     | RightSub Int Int [Int] Int Int
                     | LeftSub  Int Int [Int] Int Int
                     | Recall (SofiaTree, String)
                     deriving (Eq -- ^`DeductionRule` is a derived instance
                                  --  of the `Eq` class.
                              )

-- |`DeductionRule` is displayed in a similar way as in the Python
-- implementation.
instance Show (DeductionRule) where
    show (Assumption a)        = "assumption."
    show (Selfequate (a,b))    = "self-equate from L" ++ (show a) ++ "(" ++
                                 (show b) ++ ")."
    show (Restate xs css)      = "restatement (see lines " ++ (show xs) ++ ")."
    show (Synapsis a b)        = "synapsis (L" ++ (show a) ++ "-" ++ (show b) ++
                                 ")."
    show (Apply a xs b)        = "application of L" ++ (show a) ++ "." ++
                                (show b) ++ " (with concretization " ++
                                (show xs) ++ ")."
    show (RightSub a c xs b d) = "right substitution, L" ++ (show a) ++ "(" ++
                                (show b) ++ ") in L" ++ (show c) ++ "(" ++
                                (show d) ++ ")."
    show (LeftSub a c xs b d)  = "left substitution, L" ++ (show a) ++ "(" ++
                                (show b) ++ ") in L" ++ (show c) ++ "(" ++
                                (show d) ++ ")."
    show (Recall (a, b))       = "recalling " ++ (show b) ++ "."

-- |A `SofiaTree` is a `Tree` containing a parsed Sofia string. Each 'Node'
-- of such a 'Tree' contains a list of 'Char's (only non-empty, if the
-- 'TypeOfNode' is 'Symbol') equal to the 'String' representation of the
-- 'Node' and the 'TypeOfNode' of the 'Node'.
type SofiaTree = Tree Char TypeOfNode

class SType a where
    toType       :: a -> TypeOfNode

instance SType TypeOfNode where
    toType x = x

instance SType b => SType (Tree a b) where
    toType (Node a b c) = toType b

toSofiaTreeList :: (Printable a, SType b) => [Tree a b] -> [SofiaTree]
toSofiaTreeList []                = []
toSofiaTreeList ((Node a b c):ns) =
    (Node (toString a) (toType b) (toSofiaTreeList c)):(toSofiaTreeList ns)

toSofiaTree :: (Printable a, SType b) => Tree a b -> SofiaTree
toSofiaTree x = head (toSofiaTreeList [x])

class SofiaTreeClass a where
    getAtom :: Int -> a -> SofiaTree
    getSubtrees :: a -> [a]
    getSymbol :: a -> [Char]
    isFormulator :: a -> Bool

instance (Printable a, SType b) => SofiaTreeClass (Tree a b) where
    getAtom i (Node a b cs)    =
        case and [0 < i, i <= length cs] of
             True -> case toType b of
                 Statement -> toSofiaTree (getIndex i cs)
                 _         -> Node [] Error []
             False -> Node [] Error []
    getSubtrees (Node a b cs)  = cs
    getSymbol (Node a b cs)    = toString a
    isFormulator (Node a b cs) =
        not (or [toType b == Statement, toType b == Formula, toType b == Atom])

-- |A `ProofLine` is a `Line` with 4 parameters. The first `Int` is the
-- number of the `Line` in a `Proof`, the second `Int` is the assumption
-- depth, the `SofiaTree` is the statement contained in the line and the
-- `DeductionRule` is the rule that justifies the occurrence of the
-- `ProofLine` in a `Proof`.
data ProofLine = Line Int Int SofiaTree DeductionRule
    deriving Eq -- ^Membership of the `Eq` class is simply derived. This is
                --  needed to reverse a list of `ProofLine`s, if required.

-- |A `ProofLine` shows a string representation of the Sofia statement it
-- contains as well as the justifying `DeductionRule`.
instance Show (ProofLine) where
    show (Line a b c d) = (show c) ++ " /L" ++ (show a) ++ ": " ++ (show d)

-- |A `Proof` is a list of `ProofLine`s. To allow for creating a customised
-- instance of `Show` for `Proof`, an own list type is implemented here.
-- To resemble a list, a `Proof` consists of a `PListItem` parametrised by
-- a `ProofLine` (the head of the list) and a `Proof` (the tail of the
-- list)
data Proof = PListItem ProofLine Proof | PListEnd

showLine :: ProofLine -> Bool -> String
showLine pl b =
    showLine' pl (numDepth pl)
      where
       showLine' pl 0 = ""
       showLine' pl 1 = case ruleFromLn pl of
                        Assumption cs -> if b then "■" else "╔"
                        _             -> if b then "╚" else "║"
       showLine' pl i = "║" ++ (showLine' pl (i - 1))

-- |A `Proof` is displayed in bracket proof form like in the Python
-- version.
instance Show (Proof) where
    show (PListEnd)      = ""
    show (PListItem x PListEnd) = (showLine x False) ++ (show x)
    show (PListItem x y) = (showLineWrapper x) ++ (show x) ++ "\n" ++ (show y)
       where
        showLineWrapper x = if numDepth (phead y) >= numDepth x
                            then showLine x False
                            else showLine x True

phead :: Proof -> ProofLine
phead (PListItem x y) = x

plast :: Proof -> ProofLine
plast (PListItem x PListEnd) = x
plast (PListItem x y) = plast y

-- |The infix operator `<+>` concatenates two `Proofs`. In practice it is
-- only used to append a `Proof` containing a single `ProofLine` to an
-- existing `Proof`.
(<+>) ::    Proof  -- ^Some `Proof`.
         -> Proof  -- ^Another `Proof`.
         -> Proof  -- ^The concatenation of the two `Proof`s.
infixr 5 <+>
PListItem v w <+> PListEnd = PListItem v w
PListEnd <+> PListItem x y = PListItem x y
PListItem v w <+> PListItem x y = PListItem v (w <+> (PListItem x y))

preverse :: Proof -> Proof
preverse (PListItem x PListEnd) = PListItem x PListEnd
preverse (PListItem x y) = (preverse y) <+> (PListItem x PListEnd)

-- |Converts a list of `ProofLine`s to a `Proof`.
toProofFromList ::     [ProofLine] -- ^The list of `ProofLine`s to be converted.
                    -> Proof       -- ^The resulting `Proof`.
toProofFromList [] = PListEnd
toProofFromList (pl:pls) = PListItem pl (toProofFromList pls)

-- |Converts a `Proof` to a list of `ProofLine`s.
toListFromProof ::      Proof       -- ^The `Proof` to be converted.
                     -> [ProofLine] -- ^The resulting list of `ProofLine`s.
toListFromProof PListEnd = []
toListFromProof (PListItem pl pls) = pl : (toListFromProof pls)

newProof :: Proof
newProof = PListEnd

newLine :: Int -> Int -> SofiaTree -> DeductionRule -> ProofLine
newLine a b c d = Line a b c d

numLine :: ProofLine -> Int
numLine (Line a _ _ _) = a

numDepth :: ProofLine -> Int
numDepth (Line _ b _ _) = b

treeFromLn :: ProofLine -> SofiaTree
treeFromLn (Line _ _ c _) = c

-- NOTE: currently not in use
ruleFromLn :: ProofLine -> DeductionRule
ruleFromLn (Line _ _ _ d) = d

pdo :: ([ProofLine] -> a) -> Proof -> a
pdo func proof = func (toListFromProof proof)
