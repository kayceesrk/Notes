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

type Ctxt = {vis   :: Effect -> Effect -> Prop,
			 so    :: Effect -> Effect -> Prop,
			 -- is this effect in current session?
			 isLoc :: Effect -> Prop}

----------------
-- Monadic types
----------------

type rdProp =
  (\e1 :: Effect -> \x :: Ctxt -> ∀e2::Effect.
	sort(e1) = Rd /\ sort(e2) = Inc /\ x.so(e2,e1) => x.vis(e2,e1))
read :: CST a [Effect] readProp

type incProp =
  (\e1 :: Effect -> \x :: Ctxt -> ∀e2::Effect.
    sort(e1) = Inc /\ sort(e2) = Inc /\ x.so(e2,e1) => x.vis(e2,e1))
increment :: CST a [Effect] incProp

---------------
-- Transformers
---------------

pre :: (Effect -> Ctxt -> Prop) -> Ctxt -> Prop
pre ms x =
  ∀elist::[Effect].
	-- Restriction on so
	Rob*(elist) ⊆ x.so /\ (locActs(x) - Rmem(elist)) Χ Rmem(elist) ⊆ so /\
	-- Assertion on individual e
	∀e ∈ Rmem(elist). x.vis(e) ∈ Rmem(elist) /\ ms e x

post :: (Effect -> Ctxt -> Prop) -> [Effect] -> Ctxt -> Ctxt -> Prop
post ms elist preX postX =
  -- Original vis is a subset of the resultant vis.
  preX.vis ⊆ postX.vis
  /\ preX.so ⊆ postX.so
  /\ Rmem(elist) ∪ preX.isLoc ⊆ postX.isLoc
  /\ ∀e ∈ Rmem(elist). ms e postX

-------------------
-- Helper functions
-------------------

locActs :: Ctxt -> Set Effects
locActs x = (domain(x.so) ∪ range(x.so)) ∩ x.isLoc

-------------------
-- Functional types
-------------------

read :: {x::ctxt | pre readspec x} ->
        {a * e::[Effect] * x'::ctxt | post readspec e x x'}

inc  :: {x::ctxt | pre incProp x} ->
        {a * e::[Effect] * x'::ctxt | post incProp e x x'}


------------
-- CST Monad
------------

return :: a -> CST a [(mkEffect Silent)] (\e.\x.True)

bindProp e1 r1 e2 r2 =
  \e -> \x -> r1 e1 x /\ r2 e2 x

bind :: CST a {e1::[Effect]} r1
     -> (a -> CST b {e2::[Effect]} r2)
	 -> CST b (e1++e2) (bindProp e1 r1 e2 r2)

{% endhighlight %}

</br>
# References

* [Dijkstra monad](http://research.microsoft.com/en-us/um/people/nswamy/papers/dijkstra-submitted-pldi13.pdf)
* [Ynot](http://software.imdea.org/~aleks/papers/ynot/ynot08.pdf)

