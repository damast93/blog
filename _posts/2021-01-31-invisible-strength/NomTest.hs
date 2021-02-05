import Nom

import Prelude hiding (pi)

import qualified Data.Set as Set
import Data.Set(fromList)

trues = 
  [ a == a
  , (a,b) == (a,b)
  -- Swap
  , swap (a,b) a == b
  , swap (a,b) b == a
  , swap (a,b) c == c
  , swap (a,b) (a,b) == (b,a)
  , swap (a,b) (a,c) == (b,c)
  -- Support
  , supp a == fromList [a]
  , supp (a,(b,c)) == fromList [a,b,c]

  -- Name abstraction
  , bind a a == bind a a
  , bind a a == bind b b
  , bind a b == bind c b
  , bind a (a,b) == bind c (c,b)
  , not (bind a b == bind b b)
  , not (bind a (a,b) == bind b (b,b))
  , swap (a,b) (bind a b) == bind b a
  , supp (bind a a) == Set.empty
  , supp (bind a b) == fromList [b]
  , supp (bind a (a,b)) == fromList [b]

  -- Name generation
  , res [a] a == res [a] a
  , res [a] a == res [b] b
  , res [a] a == res [a,b] a
  , not (res [a] a == res [b] a)
  , res [b] a == res [c] a
  , res [b] a == res [] a
  , res []  a == res [b,c] a
  , not (res []  a == res [a] a)
  , res [a,b] (a,b) == res [a,b] (b,a)
  , res [a] (a,a) == res [b] (b,b)
  , not (res [a] (a,a) == res [a,b] (a,b))
  , res [a,b,c,d] (a,(b,c)) == res [a,d,e,f] (f,(e,d))
  , supp (res [] a) == fromList [a]
  , supp (res [a] a) == fromList []
  , supp (res [a] b) == fromList [b]
  , supp (res [a] (a,b)) == fromList [b]
  , supp (res [a,b] (a,(b,c))) == fromList [c]

  -- Fs functions
  , ev pi a == b
  , ev pi b == a
  , ev pi c == c
  , ev (char a) a == True
  , ev (char a) b == False
  , ev (char b) b == True
  , supp (char a) == fromList [a]
  , supp pi == fromList [a,b]
  , supp (swap (a,c) pi) == fromList [b,c]
  , supp (swap (a,c) (char a)) == fromList [c]
  , supp (swap (a,c) (char b)) == fromList [b]
  , ev (swap (a,c) (char a)) a == False
  , ev (swap (a,c) (char a)) c == True
  , ev (swap (a,c) (char a)) b == False
  , ev (swap (a,c) pi) c == b
  , ev (swap (a,c) pi) b == c

  -- Strong maps
  , ev (smap pi) (bind a b) == (bind b a)
  , ev (smap pi) (bind a a) == (bind a a)
  , not (ev (smap pi) (bind a b) == bind a a)
  , ev (swap (a,c) (smap pi)) (bind a b) == (bind a c)
  , ev (swap (a,c) (smap pi)) (bind b b) == (bind b b)
  ]


-- Examples for fs maps
pi :: Fs A A
pi = Closure cf (a,b) 
  where cf (x,t) = swap t x 

char :: A -> Fs A Bool
char = Closure (\(x,c) -> x == c)

pro = tensor (char a) (char c)
oneof = lift (\(a,b) -> a || b) `o` pro `o` lift (\x -> (x,x))

-- Monad

-- Naive do-notation won't work, the strength is hidden everywhere
demo = do
   x <- new
   y <- new
   return (x, y)
   
demo2 =
    new >>= (\x ->
    new >>= (\y ->
    return (x,y)))

-- Strong monad semantics

l1 = new >>= l2
l2 a = sextend l3 (a,new) 
l3 (a,b) = return (a,b,a)

eq a = sextend (\(a,b) -> return (a == b)) (a,new)

demo3 =
   ((),new) `sbind` (\((),x) ->
   (x ,new) `sbind` (\( x,y) ->
   return (x,y)))