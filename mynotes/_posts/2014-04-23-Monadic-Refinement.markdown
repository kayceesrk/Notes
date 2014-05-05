---
layout: post
title : "Monadic Refinement types for CoDeEc Specifications"
date  : 2014-04-23 15:30:00
categories : Research Notes
---

Our idea is to cast the idea of consistency specifications associated with
operations on replicated objects as types. Subsequently, this would enable us
to discharge the problem of checking for **Coordination Freedom** as a type
checking procedure.

The inspiration for the type encoding presented here draws from two previous
papers on verification of stateful programs: [Ynot][Ynot] and [Dijkstra
monad][dijkstra].

# Ynot

This paper describes an axiomatic extension to Coq proof assistant, that
supports writing, reasoning about, and extracting higher-order,
dependently-typed programs with side-effects. The main idea is the type `HST
pre a post` and the associated programming constructs. HST is a delayed
effectful computation that returns a value of type a, similar to the IO-monad
in Haskell. However, in addition to the return value type, the type is indexed
with the precondition pre and the postcondition post, capturing the Hoare logic
specifications in the type. When a computation of type `HST pre a post` is run
in a heap h1 satisfying `pre h1`, and it terminates, it will produce a value x
of type `a` and a result in a new heap h2 such that the preducate `post x h2`
holds.

The type `HST pre a post` can be undestood as the type `{h::heap | pre h} ->
{x::a * h'::heap | post x h h'}`. The two main operations that come with `HST`
are:

* `returnHST :: ∀a,p,x. a → HST (p x) a p`
* `bindHST   :: ∀a,b,p,q,r. HST p a q → ({x::a} -> HST (q x) b r) → HST p b r`

Arranging hoare-style specifications as monadic types leads to a very
convenient formulation whereby the inference rules directly serve as monadic
term constructors with specific operational behavior. Program verification
becomes syntax directed, and there is no need for annotation burden. Proof of
any particular program component becomes independent of the context in which
the program appears, and thus does not break when the program is considered in
a larger context.

# Concurrent state monad

## Relation to heap manipulating programs

While Ynot is concerned with heap manipulating programs, in our setting, we are
concerned with programs that manipulate an **execution context** `Ctxt`. Where
is heap is modelled as a relation (a map) from locations to values (`type Heap
= Locations -> Values`), our execution context is modelled as a record with
three relations as follows:

{% highlight haskell %}
type Ctxt = {vis   :: Effect -> Effect -> Prop, -- Visibility relation
			 so    :: Effect -> Effect -> Prop, -- Session order relation
			 isLoc :: Effect -> Prop} -- is this effect in current session?
{% endhighlight %}


While heap manipulating programs provide primitives to create (`ref`), assign
(`:=`) and examine (`!`) heap locations, the CoDeEc programs operating over
replicated objects provide operations that manipulate individual objects. For
example, a replicated bank account may provide operations to perform withdraw,
deposit and examine the current account balance (getBalance). Each of these
operations may produce one or more effects. Here, `Effect` is an abstract type,
capturing the effect of an operation. Each effect has a sort associated to it
that identifies the effect kind. We provide the following helper primitives for
creating an examining effects, whose utility will become clear when we look at
examples.

{% highlight haskell %}
data Effect
Class Sort

mkEffect :: (Sort a) => a -> Effect
sort     :: (Sort a) => Effect -> a
{% endhighlight %}

While the heap manipulating programs are modelled using McCarthy's
select/update theory of functional maps, we will utilize Catalyst-style
specifications (whenever possible; ideally should be everywhere) to reason
about operations manipulating the execution context Ctxt.

## Monadic type

The concurrent state monad is represented by a type `CST a (Set Effect) Spec` which
represents a delayed computation operating over a replicated data type,
producing a value of type a, producing a set of effects, and is associated
with the specificaiton `Spec`. The `Spec` is of the form `Effect -> Ctxt ->
Prop` and represents consistency specification of the operation encapsulated in
the monadic computation. This CST type can be understood by looking at its
functional equivalent.

{% highlight haskell %}
-- Monadic type
type CSTMonadic = CST a (Set Effect) spec
-- is equivalent to the functional type
type CSTFunctional =
  {x::Ctxt | pre spec x} ->
  {a * eset::Set Effect * x'::Ctxt | post spec eset x x'}
{% endhighlight %}

Given an input context x on which `pre spec x` holds, and the computation
terminates, the result would be a value of type a, a set of effects, and an
output context x', on which `post spec eset x x'` holds.

## Predicate constructors

We utilize the predicate constructors `pre` and `post` in order to obtain the
pre-condition and post-condition respectively. They are defined as follows:

{% highlight haskell linenos %}

---------------
-- Transformers
---------------
pre :: (Effect -> Ctxt -> Prop) -> Ctxt -> Prop
pre ms x =
  ∀eset::Set Effect.
	-- Restriction on so
	(dom(x.isLoc) - eset) Χ eset ⊆ so /\
	-- Assertion on individual e
	∀e ∈ eset. x.vis(e) ⊆ eset /\
	-- Monadic specification holds
	ms eset x

post :: (Effect -> Ctxt -> Prop) -> Set Effect -> Ctxt -> Ctxt -> Prop
post ms eset preX postX =
  -- Original vis is a subset of the resultant vis.
  preX.vis ⊆ postX.vis
  /\ preX.so ⊆ postX.so
  /\ (eset Χ {True}) ∪ preX.isLoc ⊆ postX.isLoc
  /\ ms eset postX
{% endhighlight %}

Let us closely examine the predicate constructors. The `pre` constructor takes
a specification and an input context, and produces a precondition for the
monadic computation. In particular, we require that ∀eset::Set Effect (the use
of ∀ is inspired from the weakest precondition transformer for `ref` in
[Dijkstra monad][dijkstra] paper) that we wish to perform in the context x,

* The elements in the eset are ordered after previous actions in the same
  session by session order (line 8),
* The effects are only visible to other effects in the effect set (line 10).
  This models the fact that the effects haven't taken place yet.
* The specification holds for the effect set in the context x (line 12).

The post constructor is straight-forward and asserts that it extends the
original context, and the monadic specification holds.

## Example

Let us consider an example. Assume that we are modelling a counter with
increment and read operations. The monadic type for read and increment are
given below:

{% highlight haskell %}
data Counter = Rd | Inc | Silent
instance Sort Counter

-- Assume that the syntax {e1} stands for singleton set
type RdSpec = \{e1} -> \x -> sort(e1) = Rd /\ ∀e2. sort(e2) = Inc /\
                             x.so(e2,e1) => x.vis(e2,e1)
read :: CST a (Set Effect) RdSpec

type IncSpec = \{e1} -> \x -> sort(e1) = Inc /\ ∀e2. sort(e2) = Inc /\ x.so(e2,e1) =>
							  x.vis(e2,e1)
increment :: CST a (Set Effect) IncSpec
{% endhighlight %}

with corresponding functional types

{% highlight haskell %}
read :: {x::ctxt | pre RdSpec x} ->
		{a * e::Set Effect * x'::ctxt | post RdSpec e x x'}

inc  :: {x::ctxt | pre IncSpec x} ->
		{a * e::Set Effect * x'::ctxt | post IncSpec e x x'}
{% endhighlight %}

Now, `pre RdSpec x` expands to,

{% highlight haskell %}
∀eset.(dom(x.isLoc) - eset) Χ eset ⊆ so /\
	   ∀e1 ∈ eset. x.vis(e1) ⊆ eset /\ sort(e1) = Rd  /\
	   ∀e2. sort(e2) = Inc /\ x.so(e2,e1) => x.vis(e2,e1)
{% endhighlight %}

which is the precondition for executing read operation.

</br>
# Work in progress

{% highlight haskell %}

-------------------
-- Functional types
-------------------

read :: {x::ctxt | pre readspec x} ->
        {a * e::(Set Effect) * x'::ctxt | post readspec e x x'}

inc  :: {x::ctxt | pre incProp x} ->
        {a * e::(Set Effect) * x'::ctxt | post incProp e x x'}


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

* [Dijkstra monad][dijkstra]
* [Ynot][Ynot]

[dijkstra]: http://research.microsoft.com/en-us/um/people/nswamy/papers/dijkstra-submitted-pldi13.pdf
[Ynot]: http://software.imdea.org/~aleks/papers/ynot/ynot08.pdf
