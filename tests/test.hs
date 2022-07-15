module Main where

import Control.Monad
import Control.Monad.ST
import Data.List (sort)
import Data.Word
import Test.QuickCheck
import WordMap
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

propInsert :: [(Word64, Int)] -> [(Word64, Int)] -> Property
propInsert xs ys =
  let map0 = fromList xs
      map1 = foldl (\map (k, v) -> insert k v map) map0 ys
   in map0 === fromList xs .&&. map1 === fromList (xs ++ ys)

propInsertT :: [(Word64, Int)] -> [(Word64, Int)] -> Property
propInsertT xs ys = runST $ do
  let map0 = fromList xs
  let tMap0 = transient map0
  tMap1 <- foldM (\map (k, v) -> insertT k v map) tMap0 ys
  map1 <- persistent tMap1
  return $ map0 === fromList xs .&&. map1 === fromList (xs ++ ys)

propDelete :: [(Word64, Int)] -> [Word64] -> Property
propDelete xs ys =
  let map0 = fromList xs
      map1 = foldl (flip delete) map0 ys
      difference = [(k, v) | (k, v) <- xs, k `notElem` ys]
   in map0 === fromList xs .&&. map1 === fromList difference

propDeleteT :: [(Word64, Int)] -> [Word64] -> Property
propDeleteT xs ys = runST $ do
  let map0 = fromList xs
  let tMap0 = transient map0
  tMap1 <- foldM (flip deleteT) tMap0 ys
  map1 <- persistent tMap1
  let difference = [(k, v) | (k, v) <- xs, k `notElem` ys]
  return $ map0 === fromList xs .&&. map1 === fromList difference

main = do
  quickCheck propToListFromList
  quickCheck propLookup
  quickCheck propLookupNothing
  quickCheck propInsert
  quickCheck propInsertT
  quickCheck propDelete
  quickCheck propDeleteT
