---
layout: post
title : "Monadic Refinement types for CoDeEc Propification"
date  : 2014-04-23 15:30:00
categories : Research Notes
---

Monadic definition of eventually consistent operations with specifications are
refinements.

{% highlight haskell %}

data Effect
data Sort = Rd | Inc | Silent

mkEffect :: Sort -> Effect
sort     :: Effect -> Sort

type Ctxt = {soup     :: Set Effect,
             vis      :: Effect -> Effect -> Prop,
			 so       :: Effect -> Effect -> Prop,
			 s        :: Session, -- Current Session
			 inSess   :: Effect -> Session -> Prop}

----------------
-- Monadic types
----------------

type rdProp =
  (\e1 :: Effect. \x :: Ctxt. ∀e2::Effect.
	sort(e1) = Rd /\ sort(e2) = Inc /\ x.so(e2,e1) => x.vis(e2,e1))
read :: CST a Effect readProp

type incProp =
  (\e1 :: Effect. \x :: Ctxt. ∀e2::Effect.
    sort(e1) = Inc /\ sort(e2) = Inc /\ e1 ≠ e2
	/\ x.so(e2,e1) => x.vis(e2,e1))
increment :: CST a Effect incProp

---------------
-- Transformers
---------------

pre :: (Effect -> Ctxt -> Prop) -> Ctxt -> Prop
pre ms x =
  ∀e::Effect. ¬(e ∈ x.soup)
		    /\ ms e x[so -> soExt x e][inSess -> x.inSess ∪ {e,x.s}]

post :: (Effect -> Ctxt -> Prop) -> Ctxt -> Ctxt -> Prop
post ms e preX postX =
    -- Post-condition should hold
  	ms e postX
	-- Original soup is a subset of the resultant soup. The resultant
	-- soup contains the effect
  	/\ {e} ∪ preX.soup ⊆ postX.soup
	-- Original vis is a subset of the resultant vis.
	/\ preX.vis ⊆ postX.vis -- Should '⊆' be '=' ?
	-- Original so extended with session order for the effect e is a
	-- subset of the resultant so
    /\ soExt preX e ⊆ postX.so
	-- The session is the same
	/\ postX.s = preX.s
	-- Original inSess extended with a binding for the new effect is
	-- a subset of the resultant session
	/\ {e,postX.s} ∪ preX.inSess ⊆ postX.inSess

type SessionOrder = Effect -> Effect -> Prop
soExt :: Ctxt -> Sesion -> Effect -> SessionOrder
soExt x e = x.so ∪ ((x.soup >>= \e' -> x.inSess(e',x.s)) Χ e)

-------------------
-- Functional types
-------------------

read :: {x::ctxt | pre readspec x} ->
        {a * e::Effect * x'::ctxt | post readspec e x x'}

inc  :: {x::ctxt | pre incProp x} ->
        {a * e::Effect * x'::ctxt | post incProp e x x'}


------------
-- CST Monad
------------

return :: a -> CST a (mkEffect Silent) (\e.\x.True)

bindProp e1 r1 e2 r2 = \e.\x. ∃x1,x2. pre r1 x1
								   /\ post r1 e1 x1 x2
								   /\ pre r2 x2
								   /\ post r2 e2 x2 x

bind :: CST a {e1::Effect} r1 -> (a -> CST b {e2::Effect} r2) -> CST b e2 (bindProp e1 r1 e2 r2)

{% endhighlight %}

</br>
# References

* [Dijkstra monad](http://research.microsoft.com/en-us/um/people/nswamy/papers/dijkstra-submitted-pldi13.pdf)
* [Ynot](http://software.imdea.org/~aleks/papers/ynot/ynot08.pdf)

</br>
# Scratch

{% highlight haskell %}

let comp = inc >> inc

<==Types==>

-- sort(e1) = sort(e2) = Inc
-- e1 ≠ e2
-- p = \e3 -> \x -> ∀e4. sort(e3) = sort(e4) = Inc /\ x.so(e4,e3) => x.vis(e4,e3)

let comp :: CST int e2 (bindProp e1 p e2 p) = do
  inc :: CST int e1 p
  inc :: CST int e2 p

<==Focus on comp (bind) type==>

CST int e2 (bindProp e1 p e2 p)

<==Expand==>

-- ProblemXXX:: x3 is always assumed to be post heap in this formulation of q.
let q = (\e5.\x3. ∃x1,x2. pre p x1 /\ post p e1 x1 x2 /\ pre p x2 /\ post p e2 x2 x3)

CST int {e2::Effect} q

<==Functional type==>

-- ProblemXXX:: x3 is always assumed to be post heap in this formulation of q.
-- But the heap supplied here is the pre-heap.
{x::Ctxt | pre q x} -> {int * e2::Effect * x'::Ctxt | post q e2 x x'} (1)

<==Focus on pre q x==>

pre q x

<==>

∀e. ¬(e ∈ x.soup) /\ q e x[so -> soExt x e][inSess -> x.inSess ∪ {e,x.s}]

<==>

∀e. ¬(e ∈ x.soup) /\ ∃x1,x2. pre p x1 /\ post p e1 x1 x2 /\ pre p x2 /\ post p e2 x2 x

<==>

∃x1,x2. pre p x1
/\ post p e1 x1 x2
/\ pre p x2
/\ post p e2 x2 x

<==>

∃x1,x2. (∀e.¬(e ∈ x1.soup) /\ p e x1[so -> soExt x1 e][inSess -> x1.inSess ∪ {e,x1.s}])
/\ p e1 x2 /\ {e1} ∪ x1.soup ∈ x2.soup /\ x1.vis ⊆ x2.vis /\ soExt x1 e1 ⊆ x2.so /\ x2.s = x1.s /\ {e1,x2.s} ∪ x1.inSess ∈ x2.inSess
/\ (∀e.¬(e ∈ x2.soup) /\ p e x2[so -> soExt x2 e][inSess -> x2.inSess ∪ {e,x2.s}])
/\ p e2 x /\ e2 ∪ x2.soup ∈ x.soup /\ x2.vis ⊆ x.vis /\ soExt x2 e2 ⊆ x.so /\ x.s = x2.s /\ {e2,x.s} ∪ x2.inSess ∈ x.inSess

<==>

let x3 = x1[so -> soExt x1 e][inSess -> x1.inSess ∪ {e,x1.s}]
    x4 = x2[so -> soExt x2 e][inSess -> x2.inSess ∪ {e,x2.s}]
in
∃x1,x2. (∀e.¬(e ∈ x1.soup) /\ p e x3)
/\ p e1 x2 /\ {e1} ∪ x1.soup ∈ x2.soup /\ x1.vis ⊆ x2.vis /\ soExt x1 e1 ⊆ x2.so /\ x2.s = x1.s /\ {e1,x2.s} ∪ x1.inSess ∈ x2.inSess
/\ (∀e.¬(e ∈ x2.soup) /\ p e x4)
/\ p e2 x /\ e2 ∪ x2.soup ∈ x.soup /\ x2.vis ⊆ x.vis /\ soExt x2 e2 ⊆ x.so /\ x.s = x2.s /\ {e2,x.s} ∪ x2.inSess ∈ x.inSess

<==>

let x3 = x1[so -> soExt x1 e][inSess -> x1.inSess ∪ {e,x1.s}]
    x4 = x2[so -> soExt x2 e][inSess -> x2.inSess ∪ {e,x2.s}]
in
∃x1,x2. (∀e.¬(e ∈ x1.soup) /\ (∀e2. sort(e) = sort(e2) = Inc /\ x3.so(e4,e3) => x3.vis(e4,e3)))
/\ (∀e. sort(e) = sort(e1) = Inc /\ x2.so(e,e1) => x2.vis(e,e1)) /\ {e1} ∪ x1.soup ∈ x2.soup /\ x1.vis ⊆ x2.vis /\ soExt x1 e1 ⊆ x2.so /\ x2.s = x1.s /\ {e1,x2.s} ∪ x1.inSess ∈ x2.inSess
/\ (∀e.¬(e ∈ x2.soup) /\ (∀e2. sort(e) = sort(e2) = Inc /\ x4.so(e4,e3) => x4.vis(e4,e3)))
/\ (∀e. sort(e) = sort(e2) = Inc /\ x.so(e,e2) => x.vis(e,e2)) /\ e2 ∪ x2.soup ∈ x.soup /\ x2.vis ⊆ x.vis /\ soExt x2 e2 ⊆ x.so /\ x.s = x2.s /\ {e2,x.s} ∪ x2.inSess ∈ x.inSess

{% endhighlight %}

Suppose a single increment operation had already been issued in the same
session before the `comp` computation. The assignment for x1,x2, and x that
would satisfy the preco
