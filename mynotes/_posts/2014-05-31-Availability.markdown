---
layout: post
title: "What is availability?"
date: 2014-05-31 17:15:00
categories: Research Notes
---

In this article, we will try to distill the intuition behind an available
**contract** (note the change of terminology; we would have used
**specification** here in earlier articles), and its axiomatic definition.

# Preliminaries

The contract language is defined in a [previous article][Ctrt]. Every operation
in our system is associated with a contract. An operation is performed in the
given context. The definition of a context and its structure is given
[here][Ctxt]. It is important to glance through the preliminary definitions
before proceeding.

Let us assume a context $C = (E,known,so,vis,sort,x)$, where $x$ is the current
effect (the effect that will be produced by the operation $O$ that is about to
be discharged). Let $\psi$ by the contract of this operation $O$, which is of
the form $\lambda a.p$. The only uninterpreted function symbols in $p$ are
$vis$, $so$, and $sort$. We say that a context $C = (E,known,so,vis,sort,x)$
**satisfies** a contract $\psi$ (written $C \models \psi$) if $\psi(x)$ is
**valid** when the uninterpreted function symbols $vis$, $so$ and $sort$ in
$\psi$ are replaced with $vis$, $so$ and $sort$ from $C$, and $E$ defines the
universe of effects for $\psi$.

# Contract and the obligation on the implementation

For some operation $O$ which will produce an effect $x$, let the contract be
$\psi$ and let the context be $C = (E,known,so,vis,sort,x)$. We know that $x$
is the last effect in its session ($\forall a. \neg so(x,a)$), but which might
be preceded by other effects in its session. In addition, we know that no
effects are visible to $x$ in the given context ($\forall a. \neg vis(a,x)$).
Hence, if $\psi$ is a coordination-free contract, then $C \not\models \psi$.

<a name="subKnown"></a>
The implementation is **free to choose** the set of effects $subKnown \in
known$ that are made visible to the current operation $x$ while ensuring that
the contract is satisfied in the resultant context. Let $vis'$ be the new
visibility relation, such that $vis' = vis \cup \\{(a,x) ~\mid~ a \in
subKnown\\}$ if the implementation makes effect $a$ visible to $x$.
Importantly, $\psi$ mandates that the implementation ensures
$(E,known,so,vis',sort,x) \models \psi$.

# Coordination-freedom and its specializations

Again, let $O$ be the operation producing an effect $x$ discharged under the
context $C = (E,known,so,vis,sort,x)$ with contract $\psi$. We say that the
contract $\psi$ is coordination-free if under the assumption that all effects
that happened-before $x$ is visible to $x$, the contract is valid. Formally,

<div>
\[
\newcommand{\cf}{ {\sf CoordFree} (\psi)}
\newcommand{\wt}{ {\sf WellTyped} (\psi)}
\frac
{\begin{array}{c}
hb = (so \cup vis)^+ \;\;\; \forall a. hb(a,x) \Rightarrow vis(a,x) \vdash \psi(x)
\end{array}}
{\begin{array}{c}
\cf
\end{array}}
\]
</div>

If $\psi$ is coordination-free, then $(E,known,so,vis',sort,x) \models \psi$
where $vis' = vis \cup \\{(a,x) ~\mid~ hb(a,x)\\}$.

## Closer look

Let us closely look at the definition of $\forall a. hb(a,x)$ where $x$ is the
current effect.

<div>
\[
\begin{array}{cll}
				 & \forall a. hb(a,x) \\
\Leftrightarrow  & \forall a. (so \cup vis)^+ (a,x) & \textrm{(definition)}\\
\Leftrightarrow  & \forall a. so(a,x) \vee vis(a,x) \\
				 & \;\;\;\;\; \vee~ \exists b. (so \cup vis)^+(a,b) \wedge (so(b,x) \vee vis(b,x)) & \textrm{(unwrap 1 step)}\\
\Leftrightarrow  & \forall a. so(a,x) \vee \forall a. vis(a,x) \\
				 & \vee~ \exists b. (so \cup vis)^+(a,b) \wedge so(b,x) \\
				 & \vee~ \exists b. (so \cup vis)^+(a,b) \wedge vis(b,x) & \textrm{(distribute)} \\
\Leftrightarrow  & \forall a. (so(a,x) \vee \exists b. (so \cup vis)^+(a,b) \wedge so(b,x)) \\
				 & \vee~ \forall a. (vis(a,x) \vee \exists b. (so \cup vis)^+(a,b) \wedge vis(b,x)) & \textrm{(rearrange)} \\
\end{array}
\]
</div>

<a name="hbVis"></a>
Let

- $\forall a. hbSo(a,x) = \forall a. (so(a,x) \vee \exists b. (so \cup vis)^+(a,b) \wedge so(b,x))$
- $\forall a. hbVis(a,x) = \forall a. (vis(a,x) \vee \exists b. (so \cup vis)^+(a,b) \wedge vis(b,x))$

Now, $\forall a.hb(a,x) \Leftrightarrow \forall a.hbSo(a,x) ~\vee~ \forall
a.hbVis(a,x)$.

The important distinction between $hbSo$ and $hbVis$ is this. For any $a$ such
that $hbSo(a,x)$ holds, if we expand $hbSo$ to its constituent $so$ and $vis$
relations, as follows:

<div>
\[
hbSo(a,x) = a \xrightarrow{so ~\mid~ vis} \ldots \xrightarrow{so} x
\]
</div>

the last relation is an $so$. Similarly, if we expand $hbVis(a,x)$,

<div>
\[
hbVis(a,x) = a \xrightarrow{so ~\mid~ vis} \ldots \xrightarrow{vis} x
\]
</div>

the last relation is $vis$. We now define specializations of coordination-free
contracts using $hbSo$ and $hbVis$ as follows:

<a name="viscf"></a>

<div>
\[
\newcommand{\socf}{ {\sf SoCoordFree(\psi)} }
\newcommand{\viscf}{ {\sf VisCoordFree(\psi)} }
\frac
{\begin{array}{c}
\forall a. hbSo(a,x) \Rightarrow vis(a,x) \vdash \psi(x)
\end{array}}
{\begin{array}{c}
\socf
\end{array}}

\;\;\;\;\;\;

\frac
{\begin{array}{c}
\forall a. hbVis(a,x) \Rightarrow vis(a,x) \vdash \psi(x)
\end{array}}
{\begin{array}{c}
\viscf
\end{array}}
\]
</div>

Let us define a class of contracts this is trivially valid.

<div>
\[
\newcommand{\al}{ {\sf Trivial} (\psi)}
\frac
{\begin{array}{c}
\vdash \psi(x)
\end{array}}
{\begin{array}{c}
\al
\end{array}}
\]
</div>

# Significance of the specializations

Let $O$ be the operation producing an effect $x$. Let $R$ be the set of
replicas. Let $O$ be applied to any one replica $r \in R$. Let $C =
(E,known,so,vis,sort,x)$ be the context at $r$. Notice that the context may be
different if $O$ were applied to some replica $r' \in R \wedge r \neq r'$. In
particular, since any operation from any session may be performed at any
replica, at any given time the replicas might include a different set of
effects $E$. Consequently, the $so$, $vis$, and $sort$ relations might also be
different at different replicas. The replicas are expected to converge
eventually such that every replica includes the same set of effects $E$.

## Sticky available (blocking coordination free) operations

Let the contract be $\psi$ such that $\socf ~\wedge~ \neg\al$. This
indicates that $\psi$ obligates the visibility of some $a$ at $x$ such that either
$so(a,x)$ or $\exists b.(so \cup vis)^+(a,b) \wedge so(b,x)$. Importantly, in
either case, **there is an obligation to see some set of effects that precede
$x$ in so**.

In the context $C$, for any $a$, $so(a,x)$ is set in stone. Since the replica
$r$ to which the operation $O$ is applied to might not include all previous
operations preceding $x$ in session order, there is a possibility that $C
\not\models \psi$. In this case, $O$ is said to **block**.

Due to eventual consistency, eventually $r$ is sure to include all operations
that happened-before $x$ (which includes all $a$'s such that $hbSo(a,x)$). Now,
let $C' = (E',known',so',vis',sort',x)$ be this context at $r$ where $\forall
a.hbSo(a,x) \Rightarrow known'$; all the effects necessary for $\psi$ are
known.

The implementation can now choose those set of known effects that are made
visible to $x$ which satisfies the contract. In particular, if the
implementation picks $vis'' = vis' \cup \\{ (a,x) ~\mid~ hbSo(a,x) \\}$, then
$(E',known',so',vis'',sort',x) \models \psi$. Hence, $O$ can be discharged
under $C'$. $O$ is said to be **unblocked**.

In earlier articles, we would have called $\psi$ with $\socf ~\wedge~
\neg\al$ a **sticky-available** contract.

## Highly available (non-Blocking coordination free) operations

Let the contract be $\psi$ such that $\viscf ~\wedge~ \neg \al$. This indicates
that $\psi$ obligates the visibility of some $a$ at $x$ such that either
$vis(a,x)$ (tautology) or $\exists b.(so \cup vis)^+(a,b) \wedge vis(b,x)$. The
only obligation is to see some set of effects that precede $x$ in $vis$.
Importantly, recall that unlike $so(a,x)$ which is set in stone in $C$, the
implementation is [free to choose](#subKnown) the effects that are visible to
$x$.

The key intuition is that the implementation can choose to make no effects
visible to $x$ to satisfy $\psi$. Let $O$ be applied to any replica $r$ and let
the context at $r$ be $C = (E,known,so,vis,sort,x)$. By [definition][Ctxt], we
know that $\forall a. \neg vis(a,x)$. By [definition](#hbVis), $\forall a. \neg
hbVis(a,x)$. By [definition](#viscf), $\viscf$ holds. Hence, $C \models \psi$
**always** holds. Hence, the operation $O$ does not need to block and hence can
be immediately discharged. In other words, $O$ with contract $\psi$ with
$\viscf$ is **non-blocking**.

In earlier articles, we would have called $\psi$ with $\viscf ~\wedge~ \neg\al$ a
**highly-available** contract.

### What a highly-available contract is not.

Although an empty visibility set for $x$ will satisfy a highly available
contract, any arbitrary subset of known effects will not satisfy a
highly-available contract. Consider for example a highly-available contract
$\psi(x) = \forall a,b. vis(a,b) \wedge vis(b,x) \Rightarrow vis(a,x)$. Suppose
we have a context $C = (E = \\{a,b,x\\}, known = \\{a,b\\}, so = \emptyset, vis
= \\{(a,b)\\},sort,x)$.

By definition, $C \models \psi$, where no effects are visible to $x$. In
addition, $C' = (C.E,C.known,C.so,C.vis \cup S,C.sort,x) \models \psi$ where $S
\in \\{\\{(a,x),(b,x)\\}, \\{(a,x)\\}\\}$. But $C'' = (C.E,C.known,C.so,C.vis
\cup \\{(b,x)\\},C.sort,x) \not\models \psi$ since $\psi$ obligates that $a$
which is visible to $b$ should be visible to $x$ if $b$ is visible to $x$.

### Deterministic procedure for determining the visibility set for highly-available operations

Given a highly-available operation, while an empty effect set would not violate
the contract, it is not particularly useful. A simple and useful strategy is to
define $subKnown \subseteq known$ (the set of effects that will be made
visible) such that $\forall a \in known. ite (\exists b. hb(b,a) ~\wedge~ b
\notin known) (a \notin subKnown) (a \in subKnown)$. Deriving such a $subKnown$
set is **non-blocking** (can be derived from any given context $C$ at replica
$r$) and once the replica converges $C.E = C.known$, **all known effects are
made visible** to the current operation ($C.known = subKnown$).

# Hierarchy and relationship

<div align="center">
{% graphviz %}
digraph G {
  w [label = "WellTyped", shape=none];
  cf [label = "CoordFree", shape=none];
  blk [label = "SoCoordFree", shape=none];
  nblk [label = "VisCoordFree", shape=none];
  t [label = "Trivial", shape = none];
  cf -> w;
  blk -> cf;
  nblk -> cf;
  t -> blk;
  t -> nblk;
}
{% endgraphviz %}
</div>

In the above graph, the directed edge capture subtyping relation i.e., $a
\xrightarrow{*} b \Rightarrow a <: b$

| Contract Type  | Implication |
| :------------: | :---------- |
| $\wt \wedge \neg \cf$ | Requires sequential consistency |
| $\socf \wedge \neg \al$ | Coordination-free but blocking (Sticky available) |
| $\viscf \wedge \neg \al$ | Coordination-free and non-blocking (Highly available) |
| $\al$	| Trivial |
[Ctrt]: http://multimlton.cs.purdue.edu/mML/Notes/research/notes/2014/05/30/Model-Derivation.html#ctrt
[Ctxt]: http://multimlton.cs.purdue.edu/mML/Notes/research/notes/2014/05/29/Checking-Coordination-Freedom.html#ctxt
