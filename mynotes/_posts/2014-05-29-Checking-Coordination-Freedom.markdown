---
layout: post
title: "Decision procedure for sticky-available operations"
date: 2014-05-29 12:03:00
categories: Research Notes
---

The focus of this post is to derive a decision procedure for sticky-available
operations. Recall that an **available** operation is one whose visibility
obligations can be satisfied with an empty set, where as a sticky-available
operation is one whose visibility obligations involve witnessing effects that
either preceded the current effect in the same session or happened before an
effect that preceded the current effect in the same session.

The idea is to obtain a deterministic procedure (``isContextReady``)for computing
when it is safe to discharge a coordination-free (available + sticky-available)
operation. By safe, we mean that under the given context (that includes a set
of known effects), the visibility obligations of the specification are
satisfied. For discharging an available operation at runtime, we have a
deterministic procedure for filtering out those effects from the set of known
effects (in the context) whose inclusion would violate the visibility
obligations. In particular, for an available operation, we only include those
known effects which are not preceded in happens-before by an unknown effect.
This set is the maximal subset of currently known effects under which the
visibility obligations hold.

However, for a sticky-available operation, there does not always exists a
subset of the known effects under which the visibility obligations of the
specification are satisfied. A naive deterministic procedure is to simply wait
for all effects that precede the current effect under $(so \cup hb;so)$, where
$;$ is a sequencing operation on binary relations. For example, if the
specification is read-my-writes, which only obligates $\lambda x. \forall a.
so(a,x) \subseteq vis(a,x)$, it is unnecessary to wait for any effect $b$ such
that $vis(b,a) \wedge so(a,x) \wedge \neg so(b,x)$. The challenge is to derive
an deterministic procedure from a sticky-available specification, that only
checks the knowledge of those effects which must be visible to $x$ and nothing
more.

# Model for sticky-available specification

We will build a **model** - a small over-approximation of the precise knowledge
required to check whether an operation can be discharged. A model for a
sticky-available specification is an abstraction of the happens-before
visibility obligations imposed by the specification. At runtime, we will check
whether the given context satisfies the model. As we will see, the runtime
check is deterministic and has a complexity on the order of the size of the
context and the size of the model.

Our model $M = (S,T,S\_0)$ where $S \subseteq {\tt State}$ is a set of states,
$T \subseteq S \times S \times ({\tt Effect} \times {\tt Effect} \to {\tt
Bool})$ is the transition relation between the states annotated with the step
condition and edge kinds, and $S\_0 \in S$ is the initial state. As an example,
for the sticky-available read-my-writes $rmw$ specification,

{% highlight haskell %}
rmw :: Spec
rmw x = forall_ $ \a -> so a x ==> vis a x
{% endhighlight %}

<div></div>
the representative model is:

<div align="center">
{% graphviz %}
digraph G {
  Sx -> Sa [label = " \\(src,dst) -> so(dst,src)", fontname = "Courier New", fontsize = 10.0];
  Sa -> Sa [label = " \\(src,dst) -> so(dst,src)", fontname = "Courier New", fontsize = 10.0];
}
{% endgraphviz %}
</div>

with $Sx$ as the initial state. The model is an abstraction of the
happens-before visibility obligations required by the specification. A slightly
more complex sticky-available specification is given below:

<a name="visso"> </a>
{% highlight haskell %}
spec x = \forall_ $ \a -> forall_ $ \b -> sort(a,A) /\ sort (b,B) /\ vis(b,a) /\ so(a,x) ==> vis(b,x)
{% endhighlight %}

<div></div>
The model for this specification is:

<div align="center">
{% graphviz %}
digraph G{
  Sx -> Sa [label = " \\(src,dst) -> sort(dst) == A && so(dst,src)", fontname = "Courier New", fontsize = 10.0];
  Sa -> Sa [label = " \\(src,dst) -> sort(dst) == A && so(dst,src)", fontname = "Courier New", fontsize = 10.0];
  Sa -> Sb [label = " \\(src,dst) -> sort(dst) == B && vis(dst,src)", fontname = "Courier New", fontsize = 10.0];
}
{% endgraphviz %}
</div>

Such a model is generated statically for every sticky-available specification.

# The runtime bit

<a name="ctxt"> </a>
## Context

At runtime, we will have a context $C = (E,known,so,vis,sort,x)$ where $E
\subseteq {\tt Effect}$ is the set of effects, out of which $known \subseteq E$
is the set of known effects (whose contents/values can be examined), $so
\subseteq E \times E$, $vis \subseteq E \times E$, and $sort \subseteq E \times
Con$ are the session order, visibility relation and the sort function that maps
effects to their sorts, and $x$ is the current effect (the effect
that will be produced when the current operation is discharged). We call $E -
known$ to be unknown --- effects whose contents/values cannot be examined in
the given context.

In particular, $\forall a. \neg (vis(a,x) \vee vis(x,a) \vee so(x,a))$, which
captures the idea that the effect has has not yet taken place -- $x$ is not
visible to any effect, is not succeeded in session order by any effect, and
nothing is visible to $x$ in $C$. Additionally, $\forall a. so(a,x)$ may (if
$x$ is not the first effect in some session) or may not ($x$ is the first
effect in some session) hold. After discharging the operation, the visibility
realtion will be extended to $vis'$ to include a subset of known effects
($subKnown$) being made visible to $x$. Hence, $vis' \subseteq vis$ and
$\forall a \in subKnown. vis'(a,x)$.

<a name="filter"></a>
## Filter

First, we filter the context to obtain a new context $C' =
(E',known',so,vis,sort,x)$ that does not include those effects whose inclusion would
may violate the visibility obligation of the specification, but whose exclusion
would not. Here, $E' \subseteq E$ and $known' = known \cap E'$ such that

<div>
\[
\forall a \in E. \neg hb(a,x) \wedge
                 ite ~(\exists b. hb(b,a) \wedge b \notin known) ~(a \notin E') ~(a \in E')
\]
</div>

As an aside, for an available operation, the filtered context $C' =
(E',known',so,vis,sort,x)$ such that

<div>
\[
\forall a \in E. ite ~(\exists b. hb(b,a) \wedge b \notin known) ~(a \notin E') ~(a \in E')
\]
</div>

would always be suitable for discharging an available operation.

Coming back to sticky-available operations, $C'$ gets rid of unwanted effects.
But there is a possibility of some effect $a$ with $hb(a,x)$ whose visibility
is obligated by the specification, but is not currently known. A simple example
is an execution with two completed operations in a session with corresponding
effects $a$ and $b$ with $a \overset{so}{\rightarrow} b
\overset{so}{\rightarrow} x$ and $a$ is known, but $b$ is not.


## DFS

We check for such effects by performing a DFS on the happens-before $x$
fragment of the context (combination of $E'$, $so$ and $vis$) using the
statically generated model $M$ corresponding to the specification to guide our
search for necessary but unknown effects. Let us start by defining some helper
definitions first.

Given a model $M = (S,T,S\_0)$, let $M.step = T$ be the set of all transfer
functions. Let ``prev :: Effect -> Effect option`` be the immediate predecessor
in session order. Let ``vis :: Effect -> Set Effect`` be the set of effects
visible to the given effect.

{% highlight haskell linenos %}
data EdgeKind = SO | VIS

fun core(cur :: Effect, Nothing :: Maybe Effect, s :: State, m :: Model, ek :: EdgeKind) = ()
fun core(cur :: Effect, (Just next) :: Maybe Effect, s :: State, m :: Model, ek :: EdgeKind) =
  -- Assume that ∀a ∈ Effect,b ∈ Con. ¬(a ∈ known) => sort(a,b)
  if ∃(s,s',prop) = m.step && prop(cur,next) then
    if next ∈ known then dfs(next,s',m)
    else error "Context Not Ready!"
  else case ek of
         SO -> core(cur,prev(next),s,m,SO)
         VIS -> ()

fun dfs(cur :: Effect, s :: State, m :: Model) =
  outEdges = vis(cur)
  foreach (next in outEdges) -> core(cur,next,s,m,VIS)
  core(cur,prev cur,s,m,SO)
{% endhighlight %}

We initiate the dfs as follows:

{% highlight haskell %}
-- x is the current effect
-- s0 is the initial state in Model m
core(x,prev x,s0,m,SO)
{% endhighlight %}

The key idea here is that as we perform the DFS, we step through the states in
the model derived from the sticky-available specification. We only explore the
tree for interesting effects, those for which a transition exists in the model.
Hence, we do not explore the entire set of effects that are in hb with $x$.
More importantly, for any effect that is deemed interesting, we want the effect
to be known. Otherwise, the context is not ready (lines 5-7).

## Example

Assume that we have the specification and the model described [here](#visso),
and we have the following context. Each node in the following graph has a label
of the form ${\tt Effect};{\tt Sort}$. For unknown effects, the sort is $?$
with the node colored red. Assume that $x$ is the current effect.

{% graphviz %}
digraph G {
    a [label = "a;A"];
	b [label = "b;B"];
	b1 [label = "b1;B"];
	b2 [label = "b2;?", style=filled, fillcolor=red];
	a1 [label = "a1;?", style=filled, fillcolor=red];
	a2 [label = "a2;B"];
	a3 [label = "a3;?", style=filled, fillcolor=red];
	b -> x [label = "  so"];
	a -> b [label = "  so"];
	b1 -> b [label = "  vis", constraint = false];
	b2 -> b [label = "  vis", constraint = false];
	b1 -> b2 [label = "  so"];
	a2 -> a [label = "  vis", constraint = false];
	a1 -> a2 [label = "  so"];
	a3 -> a [label = "  vis", constraint = false];
}
{% endgraphviz %}

We start the dfs at ``core(x,prev(x),Sx,m,SO)``. Since the sort of effect $b$
is $B$ which does not match the step condition in the model, we do not take a
step in the model. However, since the edge kind is $SO$ and since session order
is a transitive relation, we continue depth first search along $SO$ (line 10).
As a result, we will not explore the unnecessary effects $b1$ and $b2$.

The dfs now moves to $a$. Since $so(a,x) \wedge sort(a) == A$, we take a step
in the model as well (to state [Sa](#visso)), and continue the dfs. Notice that
there are no effects that precede $a$ in $so$. Suppose the dfs next moves to
$a2$ which is visible to $a$. The sort of $a2$ is $B$. Hence, the step
condition in the model is satisfied and we move to [Sb](#visso) in the model.
The dfs moves to $a2$. From $a2$ we try to explore deeper in the dfs. But the
only edge $a1 \rightarrow a2$ does not correspond to a step in the model (the
state Sb is a terminal state). Moreover, since the edge kind is $VIS$, we will
not explore any deeper from $a2$ (line 11). As a result, ignore the unnecessary
effect $a1$, whose visibility is not mandated by the specification -- it is OK
for $a1$ to be unknown.

The dfs now returns to $a$, and steps to $a3$. Since $a3$ is not known,
$sort(a3,B)$ holds. Moreover, the step condition in the model from $Sa
\rightarrow Sb$ is satisfied for the dfs transition from $a \rightarrow a3$.
However, $a3$ is not known. The specification says that $a3$ which preceded $a$
in visibility, which in turn preceded $x$ is $so$ must be visible to $x$. Since
unknown effects cannot be made visible, we consider this context to not be
ready and an exception is raised (line 8).

This example illustrates the utility of models for runtime checks.
