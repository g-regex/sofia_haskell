module ListHelpers where

intersect :: (Eq a) => [[a]] -> [a]
intersect xss = [x | xs <- xss, x <- xs, and $ map (elem x) xss]

without :: (Eq a) => [a] -> [a] -> [a]
without xs ys = [x | x <- xs, not (elem x ys)]

getIndex :: Int -> [a] -> a
getIndex i xs = fst $ head $ [(j, k) | (j, k) <- pairs, k == i] where pairs = zip [y | y <- xs] [1..]

-- this function is by Graham Hutton
rmdups :: Eq a => [a ] -> [a ]
rmdups [] = []
rmdups (x:xs) = x:rmdups (filter (/= x) xs)
