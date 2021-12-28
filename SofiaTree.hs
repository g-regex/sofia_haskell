module SofiaTree
    (SofiaTree,
     DeductionRule (Assumption, Selfequate, Restate, Synapsis),
     TypeOfNode (Atom, Statement, Formula, Implication, Equality, Symbol,
                 Error),
     newSofiaTree,
     getAtom,
     getSubtrees,
     getSymbol,
     toSofiaTree,
     toType,
     Proof,
     ProofLine,
     newProof,
     newLine,
     toListFromProof,
     toProofFromList,
     numLine,
     numDepth,
     treeFromLn,
     ruleFromLn,
     (<+>),
     pdo,
     plast,
     phead,
     preverse) where

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
data DeductionRule = Assumption | Selfequate (Int, Int) | Restate [(Int, Int)]
                     | Synapsis deriving (Show, Eq)

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


data ProofLineData a b c d = Line a b c d deriving (Eq)

instance (Show a, Show b, Show c, Show d) => Show (ProofLineData a b c d) where
    show (Line a b c d) = (show c) ++ " /L" ++ (show a) ++ ": " ++ (show d)

type ProofLine = ProofLineData Int Int SofiaTree DeductionRule
--type ProofLine = (Int, Int, SofiaTree, DeductionRule)

data Proof = PListItem ProofLine Proof | PListEnd

showLine :: ProofLine -> Bool -> String
showLine pl b =
    showLine' pl (numDepth pl)
      where
       showLine' pl 0 = ""
       showLine' pl 1 = case ruleFromLn pl of
                        Assumption -> if b then "■" else "╔"
                        Synapsis   -> "╚"
                        _          -> "║"
       showLine' pl i = "║" ++ (showLine' pl (i - 1))

instance Show (Proof) where
    show (PListEnd)      = ""
    show (PListItem x PListEnd) = (showLine x False) ++ (show x)
    show (PListItem x y) = (showLineWrapper x) ++ (show x) ++ "\n" ++ (show y)
       where
        showLineWrapper x = if numDepth (phead y) == numDepth x
                            then showLine x False
                            else showLine x True

phead :: Proof -> ProofLine
phead (PListItem x y) = x

plast :: Proof -> ProofLine
plast (PListItem x PListEnd) = x
plast (PListItem x y) = plast y

infixr 5 <+>
PListItem v w <+> PListEnd = PListItem v w
PListEnd <+> PListItem x y = PListItem x y
PListItem v w <+> PListItem x y = PListItem v (w <+> (PListItem x y))

preverse :: Proof -> Proof
preverse (PListItem x PListEnd) = PListItem x PListEnd
preverse (PListItem x y) = (preverse y) <+> (PListItem x PListEnd)

toProofFromList :: [ProofLine] -> Proof
toProofFromList [] = PListEnd
toProofFromList (pl:pls) = PListItem pl (toProofFromList pls)

toListFromProof :: Proof -> [ProofLine]
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
