module ListHelpers where

intersect :: (Eq a) => [[a]] -> [a]
intersect xss = [x | xs <- xss, x <- xs, and $ map (elem x) xss]

without :: (Eq a) => [a] -> [a] -> [a]
without xs ys = [x | x <- xs, not (elem x ys)]

getIndex :: Int -> [a] -> a
getIndex i xs = head $ getSublistIndex i xs

getSublistIndex :: Int -> [a] -> [a]
getSublistIndex i xs =
    map fst [(j, k) | (j, k) <- pairs, k >= i]
       where
        pairs = zip [y | y <- xs] [1..]

increasingSublist :: Ord b => (a -> b) -> [a] -> [a]
increasingSublist toOrd [] = []
increasingSublist toOrd [x] = [x]
increasingSublist toOrd p3  = [pl] ++ increasingSublist toOrd (dropWhile f p3)
   where
    pl = head p3
    f  = (\pl' -> toOrd pl' <= toOrd pl)
                                                                      
-- this function is by Graham Hutton
rmdups :: Eq a => [a ] -> [a ]
rmdups [] = []
rmdups (x:xs) = x:rmdups (filter (/= x) xs)
