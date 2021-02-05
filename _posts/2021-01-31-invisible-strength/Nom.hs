{-#LANGUAGE GADTs, ExistentialQuantification, StandaloneDeriving, FlexibleInstances #-}

module Nom where

import Data.List (intercalate)

import Data.Set (Set,(\\),empty)
import qualified Data.Set as Set

import Perm

newtype A = Atom Int deriving (Eq,Ord)

instance Show A where
    show (Atom a) = [['a'..'z'] !! (a-1)] -- TODO make this better

-- Create some atoms
a = Atom 1
b = Atom 2
c = Atom 3
d = Atom 4
e = Atom 5
f = Atom 6

-- Holy guarantee: Every function x -> y between nominal sets shall be equivariant
class Nom x where
    supp :: x -> Set A
    swap :: (A,A) -> x -> x

a # x = a `Set.notMember` (supp x)

freshfor x = head [ a | i <- [1..], let a = Atom i, a # x ]

instance Nom A where
    supp a = Set.singleton a
    swap (a,b) c
      | c == a = b
      | c == b = a
      | otherwise = c

instance (Nom x, Nom y) => Nom (x,y) where
    supp (x,y) = (supp x) `Set.union` (supp y)
    swap t (x,y) = (swap t x, swap t y)

instance (Nom x, Nom y, Nom z) => Nom (x,y,z) where
    supp (x,y,z) = (supp x) `Set.union` (supp y) `Set.union` (supp z)
    swap t (x,y,z) = (swap t x, swap t y, swap t z)

instance Nom Int where
    supp n = empty
    swap t = id

instance Nom Bool where
    supp b = empty
    swap t = id

instance Nom () where
    supp () = empty
    swap t = id

instance Nom (Set A) where
    supp xs = xs
    swap t xs = Set.map (swap t) xs

{- Finitely supported functions -}
data Fs x y where
    Closure :: (Nom c) => ((x,c) -> y) -> c -> Fs x y -- defined via closures

transpose :: (Nom a) => ((a,x) -> y) -> (a -> Fs x y)
transpose f = Closure (\(x,c) -> f (c,x))

eval :: (Fs x y, x) -> y
eval (Closure f c, x) = f (x, c)

-- for convenience (violates holy guarantee)
ev :: Fs x y -> x -> y 
ev = curry eval

lift :: (x -> y) -> Fs x y
lift f = Closure body () where body (x,()) = f x 

o :: Fs y z -> Fs x y -> Fs x z
o (Closure f c) (Closure g d) = Closure comp (c,d) where comp (x,(c,d)) = f(g(x,d),c)

tensor :: Fs x y -> Fs z w -> Fs (x,z) (y,w)
tensor (Closure f c) (Closure g d) = Closure body (c,d)
  where body ((x,z), (c,d)) =(f(x,c), g(z,d))

instance Nom (Fs x y) where
    supp (Closure f c) = supp c -- could be smaller!
    swap t (Closure f c) = Closure f (swap t c)

{- Strong functors -}
class Strong f where
    smap :: (Nom x, Nom y) => (Fs x y) -> Fs (f x) (f y)

-- Strength
str :: (Strong f, Nom x, Nom y) => (x, f y) -> f (x,y)
str (x, m) = ev (smap (transpose id x)) m

{- Name abstraction -}
data Abs x = Abs A x
bind = Abs

instance (Eq x, Nom x) => Eq (Abs x) where
    (Abs a x) == (Abs b y)
      | a == b = (x == y)
      | otherwise = (a # y) && (x == swap (a,b) y) 

instance Nom x => Nom (Abs x) where
    supp (Abs a x) = supp x \\ supp a
    swap t (Abs a x) = Abs (swap t a) (swap t x)

instance Show x => Show (Abs x) where
    show (Abs a x) = "<" ++ show a ++ ">" ++ show x

-- Functoriality
instance Functor Abs where
    fmap f (Abs a x) = Abs a (f x)

-- alpha-rename to an equivalent abstraction that avoids a set of names 
freshenA :: Nom x => Abs x -> Set A -> Abs x
freshenA (Abs a x) as = 
    let b = freshfor (x,as) in
    bind b (swap (a,b) x)

instance Strong Abs where
    smap =
      Closure (\(abs,f) ->
        let abs' = freshenA abs (supp f) in
        fmap (ev f) abs') 

{- Name generation -}
data T x = Res (Set A) x
res as x = Res (Set.fromList as) x

instance Show x => Show (T x) where
    show (Res as x) = "{" ++ (intercalate "," . map show . Set.toList $ as) ++ "}" ++ show x

instance (Eq x, Nom x) => Eq (T x) where
    (Res as x) == (Res bs y) = 
      let (xs,ys) = (supp x, supp y) in
      let free_a = xs \\ as in
      let free_b = ys \\ bs in
      (free_a == free_b) && rename (xs \\ free_a) (ys \\ free_a) x y
        where 
          rename as bs x y = 
              let (alist, blist, s) = (Set.toList as, Set.toList bs, Set.toList (Set.union as bs)) in
              any (\p -> apply p s x == y) (bij alist blist)
          apply p s = 
              let swaps = [ swap tau | cycle <- disjoint_cycles p s, tau <- cycle_as_swaps cycle ] in
              foldl (.) id swaps  

instance Nom x => Nom (T x) where
    supp (Res as x) = supp x \\ as
    swap t (Res as x) = Res (Set.map (swap t) as) (swap t x)

-- Functoriality
instance Functor T where
    fmap f (Res as x) = Res as (f x)

joinT (Res as (Res bs x)) = Res (Set.union as bs) x
returnT x = Res empty x
bindT t f = joinT (fmap f t) 

instance Applicative T where
    pure = returnT
    s <*> t = s `bindT` (\f -> t `bindT` (\a -> Res empty (f a)))    

instance Monad T where
    return = returnT
    (>>=) = bindT

-- Strength
freshenT :: Nom x => T x -> Set A -> T x
freshenT (Res as x) bs = 
    let (ds,x') = freshenrec (Set.toList as) x bs in Res (Set.fromList ds) x'
  where
    freshenrec [] x forbidden = ([],x)
    freshenrec (c:cs) x forbidden
      | c # x = freshenrec cs x forbidden
      | c `Set.notMember` bs =
        let (ds,x') = freshenrec cs x forbidden in (c:ds,x')
      | otherwise =
        let d = freshfor (x,Set.fromList cs,forbidden) in
        let (ds,x') = freshenrec cs (swap (c,d) x) (Set.insert d forbidden) in (d:ds,x')
    
instance Strong T where
    smap = 
      Closure (\(abs,f) ->
        let abs' = freshenT abs (supp f) in
        fmap (ev f) abs') 

-- Normal monad join
join :: Monad m => m (m a) -> m a
join m = m >>= id

kleisli :: Monad m => (x -> m y) -> m x -> m y
kleisli f x = x >>= f

-- Strong monad
skleisli :: (Nom x, Nom y) => Fs x (T y) -> Fs (T x) (T y)
skleisli f = lift join `o` smap f 

sextend :: (Nom a, Nom x, Nom y) => ((a,x) -> T y) -> (a, T x) -> T y
sextend f = kleisli f . str

sbind :: (Nom a, Nom x, Nom y) => (a, T x) -> ((a,x) -> T y) -> T y
sbind (a,x) f = str (a,x) >>= f

-- Nu-calculus
new :: T A
new = res [a] a
