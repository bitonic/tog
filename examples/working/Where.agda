module Where where

test1 : (A : Set) -> A -> A
test1 A x = y
  where
    y : A
    y = x

test2 : (A B : Set) -> A -> B
test2 A B = f
  where
    postulate f : A -> B

-- sortBy cmp = mergeAll . sequences
--   where
--     sequences (a:b:xs)
--       | a `cmp` b == GT = descending b [a]  xs
--       | otherwise       = ascending  b (a:) xs
--     sequences xs = [xs]

--     descending a as (b:bs)
--       | a `cmp` b == GT = descending b (a:as) bs
--     descending a as bs  = (a:as): sequences bs

--     ascending a as (b:bs)
--       | a `cmp` b /= GT = ascending b (\ys -> as (a:ys)) bs
--     ascending a as bs   = as [a]: sequences bs

--     mergeAll [x] = x
--     mergeAll xs  = mergeAll (mergePairs xs)

--     mergePairs (a:b:xs) = merge a b: mergePairs xs
--     mergePairs xs       = xs

--     merge as@(a:as') bs@(b:bs')
--       | a `cmp` b == GT = b:merge as  bs'
--       | otherwise       = a:merge as' bs
--     merge [] bs         = bs
--     merge as []         = as
