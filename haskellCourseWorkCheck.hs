-- This document is designed for UCL COMP0002 2019 course work
-- It simulates, to some extend, of how the course work would be checcked using quickCheck module
-- This file assumes the installation on quickCheck package

import Data.Set
import Test.QuickCheck
{-
Part one: set up:
Please change your definition of data type Set to the name "Tree" below
because we used the originial haskell package of Set, which has a built in type Set
-}

-- you may change this to your own data type, please leave the name Tree unchanged
newtype Tree a = Tree { unSet :: [a] }

{-
Part two:
Main test functions
Ord constraint are included to make the test possible, according to the marking schemes
But it is not garanteed such that this will be the exact way this coursework is tested

Please do remember to change your function to the function name below
-}

toList' :: Tree a -> [a]
toList' x = undefined

-- Note that this file assumes the user immplementation of fromList is accurate and well defined
fromList' :: (Ord a) => [a] -> Tree a
fromList' x = undefined

testToList :: (Ord a) => [a] -> Bool
testToList a = (toList (fromList a)) == (toList' (fromList' a))

-- ==========================================================================================

singleton' :: a -> Tree a
singleton' a = undefined

testSingleton :: (Ord a) => a -> Bool
testSingleton a = (toList' (singleton' a)) == (toList (singleton a))

-- ==========================================================================================

insert' :: (Ord a) => a -> Tree a -> Tree a
insert' a b = undefined

testInsert :: (Ord a) => [a] -> a -> Bool
testInsert a x = (toList' (insert' x (fromList' a))) == (toList (insert x (fromList a)))

-- ==========================================================================================

union' :: (Ord a) => Tree a -> Tree a -> Tree a
union' x y = undefined

testUnion :: (Ord a) => [a] -> [a] -> Bool
testUnion a b = (toList' (union' (fromList' a) (fromList' b))) == (toList (union (fromList a) (fromList b)))

-- ==========================================================================================

intersection' :: (Ord a) => Tree a -> Tree a -> Tree a
intersection' (a) (b) = undefined

testIntersection :: (Ord a) => [a] -> [a] -> Bool
testIntersection a b = (toList' (intersection' (fromList' a) (fromList' b))) == (toList (intersection (fromList a) (fromList b)))

-- ==========================================================================================

difference' :: (Ord a) => Tree a -> Tree a -> Tree a
difference' a b = undefined

testDifference :: (Ord a) => [a] -> [a] -> Bool
testDifference a b = toList' (difference' (fromList' a) (fromList' b)) == toList (difference (fromList a) (fromList b))

-- ==========================================================================================

member' :: (Ord a) => a -> Tree a -> Bool
member' a b = undefined

testMember :: (Ord a) => a -> [a] -> Bool
testMember a b = (member' a (fromList' b)) == (member a (fromList b))

-- ==========================================================================================

cardinality' :: Tree a -> Int
cardinality' a = undefined

testCardinality :: (Ord a) => [a] -> Bool
testCardinality a = (cardinality' (fromList' a)) == (size (fromList a))

-- ==========================================================================================

setmap' :: (Ord b) => (a -> b) -> Tree a -> Tree b
setmap' f b = undefined

testSetMap :: (Ord a, Ord b) => (a -> b) -> [a] -> Bool
testSetMap f a = toList' (setmap' f (fromList' a)) == toList (Data.Set.map f (fromList a))

-- ==========================================================================================

setfoldr :: (a -> b -> b) -> Tree a -> b -> b
setfoldr f a b = undefined

testFoldr :: (Ord a, Ord b) => (a -> b -> b) -> [a] -> b -> Bool
testFoldr f a b = (setfoldr f (fromList' a) b) == (Data.Set.foldr f b (fromList a))

-- ==========================================================================================

cartesian :: Tree a -> Tree b -> Tree (a, b)
cartesian a b = undefined

testCartesian :: (Ord a, Ord b) => [a] -> [b] -> Bool
testCartesian a b = (toList' (cartesian (fromList' a) (fromList' b))) == (toList (cartesianProduct (fromList a) (fromList b)))

-- ==========================================================================================

{-
The definition of powerSet and partition is missing because it involves more helper function to implement
To use the file, run this file
and use the command quickCheck "the function you want to check with"
and the compiler will tell you whether this implementation violates some of the special cases
-}