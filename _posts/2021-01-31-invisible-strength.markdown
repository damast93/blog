---
layout: post
title:  "Invisible Strength: From Monads to Alpha-Conversion"
date:   2021-01-31 18:22:29 +0100
categories: jekyll update
usemathjax: true
---
# Strong monads and $$\alpha$$-conversion

Maybe the most famous piece of Haskell wisdom is that *effectful computation* corresponds to *monads*. The idea goes back to Moggi's 1991 paper "Notions of computations and monads". It's often overlooked that from this paper to the popular wisdom, a tiny adjective went missing: Effectful computation corresponds to *strong* monads. Indeed, from the semantics it is clear why any old monad is not enough: An effectful computation $$\Gamma \vdash u : A$$ is interpreted as a morphism $$u : \Gamma \to TA$$ where $$T$$ is the monad. Let us try to interpret sequencing of effectful programs:

$$
\frac{\Gamma \vdash u : A \quad \Gamma, x : A \vdash v : B }{\Gamma \vdash \mathrm{let}\,x\leftarrow u\,\mathrm{in}\,v}
$$

The rest of the program gives a map $$\Gamma \times A \xrightarrow v TB$$. We can Kleisli-extend this to $$T(\Gamma \times A) \xrightarrow{v^\ast} TB$$. From the expression $$u$$, we can form $$\Gamma \xrightarrow{u} TA$$. Now the continuation $$v$$ needs a copy of the context $$\Gamma$$, so we copy it out as $$\Gamma \xrightarrow{\langle \mathrm{id}_\Gamma, u\rangle} \Gamma \times TA$$, but now we hit an impasse. We can't quite compose a map into $$\Gamma \times TA$$ with a map out of $$T(\Gamma \times A)$$. The solution is to just *demand* that a little piece of glue exists, to then compose as

$$
\Gamma \xrightarrow{\langle \mathrm{id}_\Gamma, u\rangle} \Gamma \times TA \xrightarrow{\mathrm{st}_{\Gamma,A}} T(\Gamma \times A) \xrightarrow{v^\ast} TB
$$

This piece of glue $$\mathrm{st}_{\Gamma,A} : \Gamma \times T A \to T(\Gamma \times A)$$ is called a *strength* for the monad $$T$$. A strong monad is a monad equipped with a such a strength, satisfying some axioms. Strength is not a property, it is extra data. That is, the same monad can admit different strengths. 

Whenever we sequence programs with some context, i.e. free variables around, a strength is needed. It's no surprise that strength show up in other important definitions like *commutative monads*, which deal with sequencing. Commutativity means that

$$
\begin{matrix}\mathrm{let}\,x\leftarrow u\,\mathrm{in} \\
\mathrm{let}\,y\leftarrow v\,\mathrm{in} \\
w
\end{matrix} \quad = \quad
\begin{matrix}\mathrm{let}\,y\leftarrow v\,\mathrm{in} \\
\mathrm{let}\,x\leftarrow u\,\mathrm{in} \\
w
\end{matrix}
$$

that is, independent program lines can be reordered. This is generally false for state-like effect. Importantly, it does hold for [probability-like](http://www.cs.ox.ac.uk/people/samuel.staton/papers/esop2017.pdf) effects by Fubini's theorem, to the extent that one might view any commutative monads as [some sort](https://arxiv.org/abs/1108.5952) of [probability theory](https://arxiv.org/abs/1908.07021).

Why is it that strength is often overlooked, or seems an unintuitive or uninteresting technical condition? As we'll see below, often a *default strength* exists which does very little. We'll seek some instructive example, where the strength does some heavy lifting: $$\alpha$$-conversion.

# Why the Strength seems Invisible

Haskell programmers might be slightly confused at this point. Surely they have composed monadic computation all the time, without any of this strength business. `do` notation just works. This is because in Haskell there is a *default strength* around for any *functor*, which we can implement like this:

```haskell
st :: Functor f => (a, f b) -> f (a, b)
st (a, m) = fmap (\b -> (a,b)) m
```

 Given an `a` and a container of `b`s, we just tuple the `a` in front of all the `b`s. Done.  

```haskell
st (1,"Hello") == [(1,'H'),(1,'e'),(1,'l'),(1,'l'),(1,'o')]
```

That's surely the most boring of tricks, is this what all the fuss was about? Every functor on the category **Set** has a default strength available for the same reason: For every $$a \in A$$, let $$t_a : B \to A \times B, b \mapsto (a,b)$$ denote the tupling map. Then for every functor $$F$$, we can define

$$
\mathrm{st}_{A,B}(a,m) = F(t_a)(m)
$$

So not only does a default strength exist, for all sorts of common monads, it is exactly what we want. List, state, probability, all use the default strength. Two natural questions arise: Is there always a default strength? And are non-default strengths interesting? 


# Strong = Enriched

In this section, let us have a precise look at why the default strength trick works in Haskell and **Set**, and why it may fail elsewhere.

Before we do, lets us briefly recall the difference between homsets and exponential objects: In a category $$C$$, the homset $$C(A,B)$$ is a *set*, and its elements are the maps $$f : A \to B$$. The exponential $$A \Rightarrow  B$$ is an *object* of $$C$$, and morphisms $$D \to (A \Rightarrow B)$$ are in natural correspondence with morphisms $$D \times A \to B$$. It follows that *global elements* $$1 \to (A \Rightarrow B)$$ correspond to elements $$f \in C(A,B)$$. Exponentials are the *internal version* of morphisms, and homsets represent the external view. Other than that, $$C(A,B)$$ and $$A \Rightarrow B$$ have a completely different formal status. In logic, homsets are deductions $$A \vdash B$$ and exponentials are propositions $$A \to B$$. It doesn't help the distinction that in many concrete categories, $$A \Rightarrow B$$ happens to be the set $$C(A,B)$$ equipped with extra structure. This is an incorrect intuition, and our key example will show the difference quite clearly.

Back to strengths: Let's try to perform the default strength trick for a functor $$F : C \to C$$ in an arbitrary cartesian closed category: We wish to give a map

$$
A \times FB \to F(A \times B)
$$

By uncurrying, it is enough to find a map 

$$
A \to (FB \Rightarrow F(A \times B))
$$

We have the identity $$A \times B \to A \times B$$, which we curry to get the tupling map $$A \to (B \Rightarrow A \times B)$$. We would be done if we could apply the functorial action on exponentials

$$
A \to (B \Rightarrow A \times B) \xrightarrow{\widetilde F_{B,A \times B}} (FB \Rightarrow F(A \times B))
$$

**But wait**. The functorial action of $$F$$ is a **Set**-map between homsets

$$
F_{X,Y} : C(X,Y) \to C(FX,FY)
$$

We need an *internal version* of the functorial action which operates on exponentials

$$
\widetilde F_{X,Y} : (X \Rightarrow Y) \to (FX \Rightarrow FY)
$$

A functor that admits such an internal action is called *enriched* (as in, enriched category theory). In general, the exponential can be much more complicated than the homset, and the homset action of $$F$$ fixes $$\widetilde F_{X,Y}$$ only on global elements. Our argument goes both ways and can be used to show the following proposition:

> **[Proposition](https://ncatlab.org/nlab/show/tensorial+strength#description)** To give a strength for a functor is to give an enrichment.

We can now see precisely why strength is invisible in **Set** and Haskell: Those categories are *self-enriched*, there is no distinction between homsets and exponentials. In the category of sets, $$(X \Rightarrow Y) = \mathbf{Set}(X,Y)$$. In Haskell, `fmap : (a -> b) -> (f a -> f b)` *is* an enriched action. This shows that not only does every functor in these categories have a default strength, it it also the only possible strength.

# Nominal Sets

We want to find a good example where there is no default strength, and a strength does nontrival work.

I'll use one of my favourite examples in all of category theory: Nominal Sets. They are a great example because they are concrete and intuitive to work with (e.g. they have *elements*, but the underlying set functor is not representable) and give a very clear distinction between internal and external statements. I can't possibly introduce all about them (here), and will instead refer to [this wonderful book](https://www.cambridge.org/core/books/nominal-sets/80F2B0C1B78A1DC309072CCEDAA88422). A quick summary is this:

Nominal sets are like sets, but instead of building everything from sets-containing-empty sets, there are *atoms* written $$a,b,c,\ldots$$ All the atoms are collected into a nominal set called $$\mathbb A$$. The crux is that these atoms are all indistinguishable, and we ought to treat them uniformly. A morphism of nominal sets $$f : X \to Y$$ is thus an *equivariant function*, that is for every permutation $$\pi$$ of atoms, we have $$f(\pi \cdot x) = \pi \cdot f(x)$$. Here, we apply a permutation to an element by applying it to all the atoms it uses, e.g. if $$\pi = (a\, b)$$ is the transposition swapping atoms $$a$$ and $$b$$, then 

$$
\pi \cdot \{a,\{42,b\},c\} = \pi \cdot \{b,\{42,a\},c\}
$$

> **Exercise** Show that there is only one equivariant function $$\mathbb A \to \mathbb A$$. There are no equivariant functions $$1 \to \mathbb A$$. That is, no atoms are visible externally.

> **Exercise** Let $$X=\{ \{a,b\} : a, b \in \mathbb A,  a \neq b \}$$, $$Y=\{(a,b) : a,b \in \mathbb A, a \neq b \}$$ and $$p : Y \to X, (a,b) \mapsto \{a,b\}$$. Show that $$p$$ is equivariant and surjective, but has no equivariant section. That is, the axiom of choice fails in nominal sets. *Hint*: Show that there is no equivariant map $$X \to \mathbb A$$.

The category **Nom** of nominal sets has exponentials (and much more - it is a Grothendieck topos), but their underlying set is *not* the set of equivariant functions. For example, we ought to have $$(1 \Rightarrow \mathbb A) \cong \mathbb A$$ but $$\mathbf{Nom}(1,\mathbb A) = \emptyset$$. Similarly, consider the equality test

$$
(=) : \mathbb A \times \mathbb A \to 2
$$

(make sure this is equivariant). Currying it gives a map

$$
\chi : \mathbb A \to 2^\mathbb A, a \mapsto \lambda b.[b=a]
$$

but the function $$f = \chi(a) \in 2^\mathbb A : b \mapsto [b=a]$$ is *not* equivariant. We have $$f(b) = 0$$ but $$f((a\, b) \cdot b) = f(a) = 1$$. Because the function $$f$$ mentions the name $$a$$ in its body, it doesn't treat the input $$a$$ uniformly. Such an equivariant-with-finite-exceptions function is called *finitely supported* and in **Nom** we have

$$
X \Rightarrow Y = \{ f : X \xrightarrow{fs} Y \}
$$

The permutation action on the exponential reads 

$$
\pi \cdot f (x)=\pi \cdot f(\pi^{-1} \cdot x)
$$

> **Exercise** Show that equivariant maps $$X \to Y$$ are precisely the *invariant* elements of $$X \Rightarrow Y$$

> **Exercise** Derive the permutation action from the set-theoretic encoding of the function $$f$$ as its graph.

> **Exercise** Show that the only subobjects of $$\mathbb A$$ are $$\emptyset$$ and $$\mathbb A$$. On the other hand, the internal powerset $$2^\mathbb A$$ can be identified with the subsets of atoms that are finite or co-finite.

To summarize. Homsets in **Nom** are very manageable, equivariance is a powerful restriction. Exponentials have a lot going on, all possible finite exceptions to equivariance. We can already see why strength will become important. Making some construction on **Nom** a functor is easy, as we just need to deal with equivariant maps. Making it strong means enriching it, i.e. dealing with all the finite support business. That is, the trouble of renaming.


# Name Generation: Heavy Lifting

Nominal sets are useful in computer science because they can model renaming and generativity, that is whenever people write `new`. The purest instance of this is name generation: A fresh name should be, well, fresh, and not equal to any previous name. Think metaprogramming, where we want to pick variable names that don't accidentally clash with anything else (`gensym`). Other examples are GUIDs, memory locations, etc.

Using nominal sets, we can use atoms for names. Generating fresh names is an effect, and thus modelled by a strong monad $$T$$ on **Nom** which is commonly called the *name-generation monad*. There is a morphism $$\nu : 1 \to T\mathbb A$$ for making a fresh name, and the program

$$
\begin{matrix}\mathrm{let}\,x\leftarrow \nu\,\mathrm{in} \\
\mathrm{let}\,y\leftarrow \nu\,\mathrm{in} \\
\mathrm{return}\, [x=y]
\end{matrix}
$$

equals `return false`, because fresh names are distinct. (In fact, $$T$$ is a commutative monad, which makes it amenable to probabilistic thinking. Interpreting name generation by probability turns out to be a really [good idea](https://arxiv.org/abs/2007.08638)) 

The precise construction of the name-generation monad is surprisingly complex. Roughly, the element of $$TX$$ can be written $$\{a_1,\ldots,a_n\}x$$ where $$a_1, \ldots, a_n \in \mathbb A$$ and $$x \in X$$. There is an equivalence relation on these that allows the names $$a_i$$ to be taken up to $$\alpha$$-equivalence. Unused names can be dropped. For example 

$$
\{a\}(a,a,b) = \{c\}(c,c,b) = \{a,c\}\{c,c,b\} \neq \{b\}(b,b,b)
$$

The $$a_1, \ldots, a_n$$ thus represent private or bound names. 

> **Exercise** Show that every element of $$T\mathbb A$$ is of the form $$\{\}a$$ with $$a \in \mathbb A$$ or $$\nu = \{a\}a$$. Conclude $$T\mathbb A \cong \mathbb A+1$$. 
>
> **Exercise** Show that $$T(\mathbb A \times \mathbb A) \cong (\mathbb A+1)\times(\mathbb A+1) + 1$$. Try to use statistical terminology, like correlation and independence.

Let's try to define a strength for $$T$$. Consider the easy case $$\mathrm{st}_{\mathbb A,\mathbb A} : \mathbb A \times T\mathbb A \to T(\mathbb A \times \mathbb A)$$. We still want to tuple with the first argument, but that might require $$\alpha$$-renaming to avoid accidental capture. For example, we must write 

$$
\mathrm{st}_{\mathbb A,\mathbb A}(a,\{a\}a) = \{b\}(a,b)
$$

It would be wrong to output $$\{a\}(a,a)$$ without renaming.

We can tell the same story under the enriched setting: The functorial action of $$T$$ is straightforward. If $$f : X \to Y$$ is equivariant, then $$Tf : TX \to TY$$ sends

$$
\{a_1,\ldots,a_n\}x \mapsto \{a_1,\ldots,a_n\}f(x)
$$

This can be checked to be well-defined and equivariant. But what about the enrichment of $$T$$, i.e. how do we define $$\widetilde T : (X \Rightarrow Y) \to (TX \Rightarrow TY)$$? This can't have the simple equivariant definition, must involve renaming, because we can reproduce the problematic example via the tupling map. We can send

$$
\{a_1,\ldots,a_n\}x \mapsto \{a_1,\ldots,a_n\}f(x)
$$

only if $$a_1, \ldots, a_n$$ are *fresh enough* for the finitely supported function $$f$$. (For an equivariant function, every set of names is fresh enough). Finally, we can define the strength of $$T$$ as 

$$
\mathrm{st}(x, \{a_1,\ldots,a_n\}y) = \{a'_1,\ldots,a'_n\}(x,y')
$$

where $$\{a_1,\ldots,a_n\}y = \{a'_1,\ldots,a'_n\}y$$ and the $$a'_i$$ are fresh enough for $$x$$.  

We recap: In name generation, the strength is exactly where the difficult business of renaming happens. Programs that can be written without strength require no $$\alpha$$-conversion.

# Give me the Strength to Rename Things

Let's develop these ideas in Haskell.  We can start by representing atoms by mere numbers, wrapped in their own type

```haskell
{-#LANGUAGE GADTs, ExistentialQuantification, StandaloneDeriving, FlexibleInstances #-}

module Nom where

import Data.List (intercalate)

import Data.Set (Set,(\\),empty)
import qualified Data.Set as Set

newtype A = Atom Int deriving (Eq,Ord)

instance Show A where
    show (Atom a) = [['a'..'z'] !! (a-1)]

-- Create some atoms
a = Atom 1
b = Atom 2
c = Atom 3
d = Atom 4
e = Atom 5
f = Atom 6
```

One way of implementing nominal sets `X` is by specifying two things
* How permutations act on each element `x`
* What the support of each `x` is 

The permutation part is easy: Because every finite permutation decomposes into transpositions, it is enough to specify how to swap pairs of atoms.

I haven't told you so far what support are: Intuitively, a set $$A$$ of atoms *supports* $$x \in X$$ if it contains all the atoms which $$x$$ mentions. Formally, every permutation which fixes all atoms in $$A$$ also fixes $$x$$. For a nominal set, it is required by definition that every element have some finite set of atoms supporting it. One can then show that there is a least set supporting it, called *the support* of $$x$$. 

> **Exercise** Show that the support of $$(a,b) \in \mathbb A \times \mathbb A$$ is $$\{a,b\}$$. Show that the support of $$\lambda b.[a=b] \in 2^\mathbb A$$ is $$\{a\}$$. Show that the support of $$\{a\}a \in T\mathbb A$$ is empty.

In Haskell, we are generally unable to compute exactly which names get used by an expression. But we can keep track of some superset of the atoms, i.e. return for every element `x` some set of atoms supporting it. 

```haskell
-- Holy guarantee: Every function x -> y between nominal sets shall be equivariant
class Nom x where
    supp :: x -> Set A
    swap :: (A,A) -> x -> x

a # x = a `Set.notMember` (supp x)

freshfor x = head [ a | i <- [1..], let a = Atom i, a # x ]
```

We can describe a bunch of nominal sets

```haskell
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
```

We test out the capabilities of the `Nom` class

```haskell
supp (a,b) == fromList [a,b]
swap (a,b) (a, 42) == (b, 42)
```

The most difficult part is how to represent finitely supported functions: The Haskell function type `a -> b` is opaque; we cannot analyze the body of a function to find out which names it uses. So we must find some sort of explicit representation for finitely supported functions, that keeps track of names in terms of simpler nominal sets.

Recall how we discovered the need for finitely supported functions in the first place. If $$F : X \times C \to Y$$ is equivariant and $$c \in C$$, then the closure $$f=F(-,c)$$ is generally not equivariant but finitely supported, and the datum $$c$$ captures the amount of asymmetry that $$f$$ is allowed. It turns out that every finitely supported function is of this form.

> **Theorem** For every finitely supported function $$f : X \xrightarrow{fs} Y$$ there is a nominal set $$C$$ and an equivariant function $$F : X \times C \to Y$$ and an element $$c \in C$$ such that $$f = F(-,c)$$. 

So finitely supported functions are closures! This gives us a way of representing them in code

```haskell
{- Finitely supported functions -}
data Fs x y where
    Closure :: (Nom c) => ((x,c) -> y) -> c -> Fs x y

transpose :: (Nom a) => ((a,x) -> y) -> (a -> Fs x y)
transpose f = Closure (\(x,c) -> f (c,x))

eval :: (Fs x y, x) -> y
eval (Closure f c, x) = f (x, c)
```

(As an aside, the distinction between equivariant and finitely supported maps is reminiscent of the difference between a pure C function pointer, and a C++ lambda)

The tupling function would be written as

```
tuple :: (Nom a, Nom b) => a -> (Fs b (a,b))
tuple a = Closure (\(b,a) -> (a,b)) a
```

We make `Fs x y` into a nominal set as follows 

```haskell
instance Nom (Fs x y) where
    supp (Closure f c) = supp c -- careful, the real support could be smaller!
    swap t (Closure f c) = Closure f (swap t c)
```

> **Exercise** Prove the `swap` rule correct. That is $$\pi \cdot F(-, c) = F(-, \pi \cdot c)$$.

We can lift equivariant functions to `Fs` by choosing $$C=1$$, and define composition as follows

```haskell
ev :: Fs x y -> x -> y 
ev = curry eval -- for convenience (violates holy guarantee)

lift :: (x -> y) -> Fs x y
lift f = Closure body () where body (x,()) = f x 

o :: Fs y z -> Fs x y -> Fs x z
o (Closure f c) (Closure g d) = Closure comp (c,d) where comp (x,(c,d)) = f(g(x,d),c)

tensor :: Fs x y -> Fs z w -> Fs (x,z) (y,w)
tensor (Closure f c) (Closure g d) = Closure body (c,d)
  where body ((x,z), (c,d)) =(f(x,c), g(z,d))
```

We can now define a framework for strong/enriched nominal functors, which we call `Strong` 

```haskell
{- Strong functors -}
class Strong f where
    smap :: (Nom x, Nom y) => (Fs x y) -> Fs (f x) (f y)
```

From enriched `smap`, we can derive an explicit strength as follows

```haskell
str :: (Strong f, Nom x, Nom y) => (x, f y) -> f (x,y)
str (x, m) = ev (smap (transpose id x)) m
```

Representatives for the name-generation monad are straightforward to define

```haskell
{- Name generation -}
data T x = Res (Set A) x -- Res stands for (name) restriction
res as x = Res (Set.fromList as) x -- represents {as}x

instance Nom x => Nom (T x) where
    supp (Res as x) = supp x \\ as -- the names `as` are bound
    swap t (Res as x) = Res (Set.map (swap t) as) (swap t x)
    
-- The Eq instance is tricky; we need to find an appropriate renaming ...
```

We can make elements of the name generation monad like this

```haskell
new :: T A
new = res [a] a

pair :: T (A,A)
pair = res [a,b] (a,b)
```

The functor and monad structure of `T` are again straightforward, because they only concern the equivariant part and no renaming is necessary

```haskell
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
```

In order to define the strength for `T`,  we need to define a function `freshenT` which finds an $$\alpha$$-equivalent representative avoiding certain names `bs` 

```haskell
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
```

We can now define a `Strong` instance for `T` as follows

```haskell
instance Strong T where
    smap = 
      Closure (\(abs,f) ->
        let abs' = freshenT abs (supp f) in
        fmap (ev f) abs') 
        
-- Normal monad operations
join :: Monad m => m (m a) -> m a
join m = m >>= id

kleisli :: Monad m => (x -> m y) -> m x -> m y
kleisli f x = x >>= f

-- Strong monad operations
skleisli :: (Nom x, Nom y) => Fs x (T y) -> Fs (T x) (T y)
skleisli f = lift join `o` smap f 

sextend :: (Nom a, Nom x, Nom y) => ((a,x) -> T y) -> (a, T x) -> T y
sextend f = kleisli f . str

sbind :: (Nom a, Nom x, Nom y) => (a, T x) -> ((a,x) -> T y) -> T y
sbind (a,x) f = str (a,x) >>= f
```

You can find the source code of the `Nom` class [here](https://github.com/damast93/blog/tree/master/_posts/2021-01-31-invisible-strength).

# Demo

Let's test our framework. Recall the definition of $$\nu = \{a\}a \in T\mathbb A$$, i.e.

```haskell
new :: T A
new = res [a] a
```

And consider the following name-generating program

```haskell
-- Naive do-notation won't work, the strength is hidden everywhere
demo :: T (A,A)
demo = do
   x <- new
   y <- new
   return (x, y)
```

Because `do`-notation uses the default-strength of Haskell, no renaming takes place, and we obtain the incorrect result $$\{a\}(a,a)$$. We want to use our renaming strength. But Haskell has no builtin support for custom strong monads, so we need to desugar everything. The program above desugars to

```haskell
demo =
    new >>= (\x ->
    new >>= (\y ->
    return (x,y)))
```

Now we can use `sbind` everywhere instead of `>>=`, the explicit bind-with-context of strong monads. 

```haskell
correct_demo :: T (A,A)
correct_demo =
   ((),new) `sbind` (\((),x) -> -- nothing in context
   (x ,new) `sbind` (\( x,y) -> -- `x` in context
   return (x,y)))
```

 We obtain the correct output $$\{a,b\}(a,b)$$.



