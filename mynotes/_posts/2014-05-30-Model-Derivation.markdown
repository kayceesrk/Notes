---
layout: post
title: "Model Derivation from Sticky-available contracts"
date: 2014-05-30 16:03:00
categories: Research Notes
---

This article is a followup of the [article][Model] on the necessity and utility
of models. In this article, we will focus on the mechanics of model derivation
and runtime use of the models.

<a name="ctrt"></a>
# contract Language

We will go for a modified contract language that is different from the
language used in previous articles. The two main differenences are:

- The contract only relates effects on the same object.
- contract provides relational operators: union, intersection and
  transitive closure.

Restricting the contract to relations on the same object is a pragmatic
decision, which avoids the necessecity to track dependencies across objects and
simplifies the system for the purpose of formal description. Ideally, once we
are happy with per-object relations, we should expand to include cross object
relations as well. The contract language is given below:

<div>
\[
\newcommand{\ALT}{~\mid~}
\begin{array}{cclcl}
a & \in & {\tt Effect} \\
k & \in & {\tt Cons} & := & \bigcup_{\tau \in {\tt ObjType}} {\tt Con}_{~\tau} \\
r & \in & {\tt Relation} & := & vis \ALT so \ALT r^+ \ALT r_1 \cup r_2 \ALT r_1 \cap r_2 \\
p & \in & {\tt Prop} & := & true \ALT false \ALT \forall a.p \ALT \exists a. p \ALT \neg p \ALT r(a_1,a_2) \ALT sort(a,k) \\
  &		&			 & \ALT & p_1 \wedge p_2 \ALT p_1 \vee p_2 \ALT p_2 \Rightarrow p_2 \\
\psi & \in & {\tt Contract} & := & \lambda a.p
\end{array}
\]
</div>

This language provides a transitive closure ($^+$), union ($\cup$) and
intersection ($\cap$) operators, using which expressive relations can be
defined. For example, **happens-before** relation is defined as $hb = (so \cup
vis)^+$.

# Model

Let a model $M = (S,T,tk,s\_0)$ where:

- $S \subseteq {\tt State}$ is a set of states
- $T\ \subseteq S \times S \times ({\tt Effect} \times {\tt Effect} \to {\tt
  Bool})$ is the transition relation between the states indexed with the step
  condition
- $tk \subseteq S \to K$ is a map from each state to an edge kind set $K
  \subseteq \\{a \ALT a = SOE \vee a = TVISE\\}$ which qualifies the transitions from
  state $s$ to some state $s'$ such that $(s,s',prop) \in T$. $SOE$ models a
  transition which models a session order relation. $TVISE$ models a transition
  which models a $vis^+$ relation. The utility of $tk$ will become clear when
  we discuss the runtime check.
- $s\_0$ is the initial state.

The model is generated statically from the contract, and will be utilized at runtime.

# Model generation

# Runtime check

The first step is to filter the context to get rid of unwanted effects. This
process is the same as the one described in the [previous article][filter].

{% highlight haskell linenos %}
-- Assume the following values in the environment
-- known  :: Effect -> Bool which is the known set of effects.
-- prev   :: Effect -> Maybe Effect returns the immediate predecessor of Effect in session order.
-- visSet :: Effect -> Set Effect return the set of effects visible to the given effect.
-- model  :: Model. If $M = (S,T,tk,s_0)$ then initSt(model) = s_0, step(model) = T and stepKind(model) = tk.
-- sort   :: Effect -> Con which is the sort function. Assume that ∀a ∈ Effect, b ∈ Con. ¬(a ∈ known) => sort.

core :: Effect -> Maybe Effect -> State -> IO Bool
core _ Nothing _ = return True
core cur (Just next) s =
  if ∃(s, s', prop) = step model && prop cur next then
    if next ∈ known then dfs next s'
    else throw ContextNotReady
  else if stepKind model s = {SOE,TVISE} then
    dfs next s
  else if stepKind model s = {SOE} then
    core next (prev next) s
  else if stepKind model s = {TVISE} then
    procVis next s
  else return True

procVis :: Effect -> State -> IO Bool
procVis (cur :: Effect) (s :: State) = do
  mapM (\next -> core cur (Just next) s) $ visSet cur
  return True

dfs :: Effect -> State -> IO Bool
dfs (cur :: Effect) (s :: State) = do
  core cur (Just cur) s
  procVis cur s

-- Initiation of the runtime check.
-- x is the current effect
init :: Effect -> IO Bool
init x =
  catch (dfs x x $ initSt model) (\_ -> return False)
{% endhighlight %}

[Model]: http://multimlton.cs.purdue.edu/mML/Notes/research/notes/2014/05/29/Checking-Coordination-Freedom.html
[filter]: http://multimlton.cs.purdue.edu/mML/Notes/research/notes/2014/05/29/Checking-Coordination-Freedom.html#filter
