{-|
Module      : ListHelpers
Description : Part of the Sofia proof assistant.
Copyright   : Gregor Feierabend
License     : GNU General Public License v3 (GPLv3)
Maintainer  : Gregor Feierabend
Stability   : experimental
Portability : POSIX
-}

module ListHelpers where

intersect :: (Eq a) => [[a]] -> [a]
intersect xss = rmdups [x | xs <- xss, x <- xs, and $ map (elem x) xss]

subset :: (Eq a) => [a] -> [a] -> Bool
subset xs ys = (rmdups xs) == intersect [xs, ys]

without :: (Eq a) => [a] -> [a] -> [a]
without xs ys = rmdups [x | x <- xs, not (elem x ys)]

getIndex :: Int -> [a] -> a
getIndex i xs = head $ getSublistIndex i xs

getSublistIndex :: Int -> [a] -> [a]
getSublistIndex i xs =
    map fst [(j, k) | (j, k) <- pairs, k >= i]
       where
        pairs = zip [y | y <- xs] [1..]

decreasingSublist :: (Ord b, Eq a) => (a -> b) -> [a] -> [a]
decreasingSublist toOrd [] = []
decreasingSublist toOrd [x] = [x]
decreasingSublist toOrd (pl:pls) =
    [pl] ++ decreasingSublist toOrd (dropWhile f pls)
       where
        f  = (\pl' -> toOrd pl' > toOrd pl)
                                                                      
-- this function is by Graham Hutton
rmdups :: Eq a => [a] -> [a]
rmdups [] = []
rmdups (x:xs) = x:rmdups (filter (/= x) xs)

pop :: [a] -> [a]
pop [] = []
pop xs = init xs

-- https://stackoverflow.com/questions/9220986/is-there-any-haskell-function-to-concatenate-list-with-separator
join sep xs = foldr (\a b-> a ++ if b=="" then b else sep ++ b) "" xs
