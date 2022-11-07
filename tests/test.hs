module Main where

import Control.Monad
import Control.Monad.ST
import Data.List (sort)
import Data.Maybe
import Data.Word
import Data.WordMap
import Test.QuickCheck
import Prelude hiding (lookup)

propToListFromList :: [(Word64, Int)] -> Property
propToListFromList xs = noDuplicates (map fst xs) ==> (sort (toList (fromList xs)) === sort xs)
  where
    noDuplicates [] = True
    noDuplicates (x : xs) = x `notElem` xs && noDuplicates xs

propLookup :: [(Word64, Int)] -> Word64 -> Int -> Property
propLookup xs key value =
  let map = insert key value $ fromList xs
   in lookup key map === Just value

propLookupNothing :: [(Word64, Int)] -> Word64 -> Property
propLookupNothing xs key =
  let map = fromList [(k, v) | (k, v) <- xs, k /= key]
   in lookup key map === Nothing

propLookupLT :: [(Word64, Int)] -> Word64 -> Bool
propLookupLT xs key =
  let map = fromList xs
   in case lookupLT key map of
        Nothing -> all (\(k, v) -> k >= key) xs
        Just (k, v) -> lookup k map == Just v && all (\(k', _) -> k' <= k || k' >= key) xs

propInsert :: [(Word64, Int)] -> [(Word64, Int)] -> Property
propInsert xs ys =
  let map0 = fromList xs
      map1 = foldl (\map (k, v) -> insert k v map) map0 ys
   in toList map0 === toList (fromList xs) .&&. toList map1 === toList (fromList (xs ++ ys))

propInsertT :: [(Word64, Int)] -> [(Word64, Int)] -> Property
propInsertT xs ys = runST $ do
  let map0 = fromList xs
  let tMap0 = transient map0
  tMap1 <- foldM (\map (k, v) -> insertT k v map) tMap0 ys
  map1 <- persistent tMap1
  return $ toList map0 === toList (fromList xs) .&&. toList map1 === toList (fromList (xs ++ ys))

propExtendFromAscList :: [(Word64, Int)] -> OrderedList Word64 -> Property
propExtendFromAscList xs (Ordered ys) =
  let map = fromList xs
      zs = zip (deduplicate ys) (repeat 0)
      extendedMap = extendFromAscList zs map
      expectedMap = foldl (\map (k, v) -> insert k v map) map zs
   in toList expectedMap === toList extendedMap

propDelete :: [(Word64, Int)] -> [Word64] -> Property
propDelete xs ys =
  let map0 = fromList xs
      map1 = foldl (flip delete) map0 ys
      difference = [(k, v) | (k, v) <- xs, k `notElem` ys]
   in toList map0 === toList (fromList xs) .&&. toList map1 === toList (fromList difference)

propDeleteT :: [(Word64, Int)] -> [Word64] -> Property
propDeleteT xs ys = runST $ do
  let map0 = fromList xs
  let tMap0 = transient map0
  tMap1 <- foldM (flip deleteT) tMap0 ys
  map1 <- persistent tMap1
  let difference = [(k, v) | (k, v) <- xs, k `notElem` ys]
  return $ toList map0 === toList (fromList xs) .&&. toList map1 === toList (fromList difference)

propUnion :: [(Word64, Int)] -> [(Word64, Int)] -> Property
propUnion xs ys =
  let map1 = fromList xs
      map2 = fromList ys
      unionMap = union map1 map2
      expectedMap = foldl (\map (k, v) -> insert k v map) map2 xs
   in toList expectedMap === toList unionMap

propFromAscList :: OrderedList Word64 -> Property
propFromAscList (Ordered xs) = ys === toList (fromAscList ys)
  where
    ys = zip (deduplicate xs) (repeat 0)

deduplicate :: Eq a => [a] -> [a]
deduplicate (x1 : x2 : xs)
  | x1 == x2 = deduplicate (x2 : xs)
  | otherwise = x1 : deduplicate (x2 : xs)
deduplicate xs = xs

main = do
  quickCheck propToListFromList
  quickCheck propLookup
  quickCheck propLookupNothing
  quickCheck propLookupLT
  quickCheck propInsert
  quickCheck propInsertT
  quickCheck propExtendFromAscList
  quickCheck propDelete
  quickCheck propDeleteT
  quickCheck propUnion
  quickCheck propFromAscList
