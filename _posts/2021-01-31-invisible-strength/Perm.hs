module Perm(disjoint_cycles, cycle_as_swaps, bij) where

-- Permutation utilities

import Data.List ((\\),elemIndex)

-- find disjoint cycle representation of a bijection f : supp -> supp
disjoint_cycles f [] = []
disjoint_cycles f (x:xs) = 
    let cycle = orbit_rec f x [] in
    if length cycle > 1
      then cycle : disjoint_cycles f (xs \\ cycle)
      else         disjoint_cycles f (xs \\ cycle)
  where
    orbit_rec f x xs
      | x `elem` xs = reverse xs
      | otherwise   = orbit_rec f (f x) (x:xs)

-- (1 2 3 4) = (1 4)(1 3)(1 2)
cycle_as_swaps (x:xs) = [ (x,y) | y <- reverse xs ]

-- generating all bijections between sets
-- notice the expected numbers of transpositions in sym n equals (n - H_n)

-- sym n = permutations on {0,..,n-1}
--sym 1 = [id]
--sym n = [ sigma . swap (n-1,i) | i <- [0..n-1], sigma <- sym (n-1) ] 

-- bij xs ys = all permutations pi with pi(xs) = ys, no matter where ys \\ xs goes
-- first compute partial bijections xs -> ys, then complete values on ys \\ xs

partbij [] [] = [ id ]
partbij [x] [y] = [ \c -> if c == x then y else c ]
partbij (x:xs) ys = [ \c -> if c == x then y else sigma c | y <- ys, sigma <- partbij xs (ys \\ [y]) ]
partbij _ _ = [] -- no bijection between sets of different sizes

-- complete a partial bijection to a total one
complete f xs ys c
    | c `elem` xs = f c
    | c `elem` ys = cycle_begin f xs c
    | otherwise = c 
  where
    cycle_begin f xs c =
        case [ x | x <- xs, f x == c ] of
            [x] -> cycle_begin f xs x
            []  -> c

bij xs ys = map (\f -> complete f xs ys) $ partbij xs ys

