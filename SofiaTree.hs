{-
The SOFiA proof assistant.
Copyright (C) 2022  Gregor Feierabend

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program.  If not, see <https://www.gnu.org/licenses/>.
-}

{-|
Module      : SofiaTree
Description : Part of the Sofia proof assistant.
Copyright   : Gregor Feierabend
License     : GNU General Public License v3 (GPLv3)
Maintainer  : Gregor Feierabend
Stability   : experimental
Portability : POSIX

The `SofiaTree` module contains definitions of data types created
specifically for the Sofia proof assistant.
-}

{-# OPTIONS_HADDOCK prune #-}

module SofiaTree
    (TypeOfNode (Atom, Statement, Formula, Implication, Equality, Symbol,
                 Error),
     Tree (Node),
     SofiaTree,
     DeductionRule (Assumption, Recall, Selfequate, Restate, Synapsis, Apply,
                    RightSub, LeftSub),
     ProofLine (Line),
     Proof (PListItem, PListEnd),

     -- * Operators
     (<+>),
     pdo,
     plast,
     phead,
     preverse,

     -- * Extracting parameters

     -- `SofiaTreeClass` instance functions.
     getAtom,
     getSubtrees,
     getSymbol,
     toType,

     numLine,
     numDepth,
     treeFromLn,
     ruleFromLn,

     -- * Converting types
     toListFromProof,
     toProofFromList,

     -- * Generating data structures
     newSofiaTree,
     newProof,

     treeEQ,
     treeIMP,
     treeTRUTH,
     treeERR,
     treeSTMTform,
     treeSTMT
     ) where

import ListHelpers

class Printable a where
    printable :: a -> String

instance Printable Char where
    printable x = id [x]

toString :: Printable a => [a] -> String
toString [] = ""
toString (x:xs) = (printable x) ++ (toString xs)

-- |Nodes in a `SofiaTree` can have any of the following types. A node has type
-- `Error`, when a parsing error occurred.
data TypeOfNode = Atom | Statement | Formula | Implication | Equality | Symbol |
                  Error
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
-- of such a 'Tree' contains a 'String' (only non-empty, if the
-- 'TypeOfNode' is 'Symbol') and has a specified 'TypeOfNode'.
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

-- |The `Int`s are respectively the
-- number of the `Line` and the assumption
-- depth. The `SofiaTree` must be a statement and the
-- `DeductionRule` justifies the occurrence of the
-- statement in a `Proof`.
data ProofLine = Line Int Int SofiaTree DeductionRule
    deriving Eq -- ^Membership of the `Eq` class is simply derived. This is
                --  needed to reverse a list of `ProofLine`s, if required.

-- |Shows a string representation of the contained `Sofia` statement  as well as
-- the justifying `DeductionRule`.
instance Show (ProofLine) where
    show (Line a b c d) = (show c) ++ " /L" ++ (show a) ++ ": " ++ (show d)

-- |A `Proof` is a list of `ProofLine`s. To create a customised
-- instance of `Show`, an own list type is implemented.
-- It consists of a `PListItem` parametrised by a `ProofLine` (the list's head)
-- and a `Proof` (the list's tail).
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

-- |A `Proof` is displayed in bracket proof format like in the Python
-- implementation.
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

-- |Extracts the line number from a given `ProofLine`.
numLine :: ProofLine -> Int
numLine (Line a _ _ _) = a

-- |Extracts the assumption depth from a given `ProofLine`.
numDepth :: ProofLine -> Int
numDepth (Line _ b _ _) = b

-- |Extracts the `SofiaTree` from a given `ProofLine`.
treeFromLn :: ProofLine -> SofiaTree
treeFromLn (Line _ _ c _) = c

-- |Extracts the `DeductionRule` from a given `ProofLine`.
ruleFromLn :: ProofLine -> DeductionRule
ruleFromLn (Line _ _ _ d) = d

-- |Returns an empty `Proof` containing no `ProofLine`s.
newProof :: Proof
newProof = PListEnd

pdo :: ([ProofLine] -> a) -> Proof -> a
pdo func proof = func (toListFromProof proof)

--------------------------------------------------------------------------------

-- |A `SofiaTree` consisting only of an `Equality` formultor. To be used as a
-- shorthand for the formulator in other functions.
treeEQ :: SofiaTree
treeEQ = (newSofiaTree [] Equality [])

-- |A `SofiaTree` consisting only of an `Implication` formultor. To be used as a
-- shorthand for the formulator in other functions.
treeIMP :: SofiaTree
treeIMP = (newSofiaTree [] Implication [])

-- |The `Error` tree resulting from a parsing error.
treeERR :: SofiaTree
treeERR = newSofiaTree "" Error []

-- |A `SofiaTree` comprised of an atomic empty statement.
treeTRUTH :: SofiaTree
treeTRUTH = newSofiaTree [] Statement [newSofiaTree[] Atom []]

-- |Returns a `SofiaTree` comprised of an atomic statement containing a formula. 
treeSTMTform ::    [SofiaTree]  -- ^The list of subtrees making up the formula.
                -> SofiaTree    -- ^The resulting statement.
treeSTMTform ts =
        newSofiaTree []
                     Statement
                     [newSofiaTree [] Atom [newSofiaTree [] Formula ts]]

-- |Returns a statement comrprised of a list of atoms.
treeSTMT ::     [SofiaTree] -- ^The list of atoms contained in the statement.
             -> SofiaTree   -- ^The resulting statement.
treeSTMT ts =
        newSofiaTree []
                     Statement
                     ts

