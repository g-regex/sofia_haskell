{-data Expr = Stat String | Form String deriving (Show)

genExpr :: String -> {-Expr-}
genExpr xs | xs == "[a]"  = Stat "[a]"
           | otherwise   = Stat "[]"-}

legalChars = ['a'..'z'] ++ ['A'..'Z'] ++ ['0'..'9'] ++ ['%']

isLegal :: Char -> Bool
isLegal x = if length [a | a <- legalChars, a == x] == 1 then True else False


--data Formulator = Implication | Equality | Symbol [Char]
--data Expression = Statement [Expression] | Formula 

dummyChar = '*'

character :: Char -> Char
character x = if length [a | a <- legalChars, a == x] == 1 then x else dummyChar

{-character' :: Char -> Formulator
character' x = if isLegal x then (Symbol [x]) else Incorrect -}

{-character :: Char -> Maybe Char
character x = if length [a | a <- legalChars, a == x] == 1 then Just x else Nothing-}

symbol :: [Char] -> [Char]
symbol [] = []
symbol (x:xs) = if character x == dummyChar then symbol xs else character x : symbol xs

--formulator :: [Char] -> [Char]

--genAxiom :: String -> [Expression]
--genAxiom "[x]" 

data TypeOfNode = Statement | Implication | Equality | Variable | Constant
type NodePair = (String, TypeOfNode)

data Tree a = Node a [Tree a] deriving (Show)

--genExpr :: String -> Tree NodePair

--context :: Tree (String, TypeOfNode) -> [
