---
layout: post
title: "What is availability?"
date: 2014-05-31 17:15:00
categories: Research Notes
---

In this article, we will try to distill the intuition behind an available
**contract** (note the change of terminology; we would have used
**specification** here in earlier articles), and its axiomatic defintion.

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
\frac
{\begin{array}{c}
hb = (so \cup vis)^+ \;\;\; \forall a. hb(a,x) \Rightarrow vis(a,x) \vdash \psi(x)
\end{array}}
{\begin{array}{c}
{\sf CoordFree(\psi)}
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

Let

- $\forall a. hb1(a,x) = \forall a. (so(a,x) \vee \exists b. (so \cup vis)^+(a,b) \wedge so(b,x))$
- $\forall a. hb2(a,x) = \forall a. (vis(a,x) \vee \exists b. (so \cup vis)^+(a,b) \wedge vis(b,x))$

Now, $\forall a.hb(a,x) \Leftrightarrow \forall a.hb1(a,x) ~\vee~ \forall
a.hb2(a,x)$.

The important distinction between $hb1$ and $hb2$ is this. For any $a$ such
that $hb1(a,x)$ holds, if we expand $hb1$ to its constituent $so$ and $vis$
relations, as follows:

<div>
\[
hb1(a,x) = a \xrightarrow{so ~\mid~ vis} \ldots \xrightarrow{so} x
\]
</div>

the last relation is an $so$. Similarly, if we expand $hb2(a,x)$,

<div>
\[
hb2(a,x) = a \xrightarrow{so ~\mid~ vis} \ldots \xrightarrow{vis} x
\]
</div>

the last relation is $vis$. We now define specializations of coordination-free
contracts using $hb1$ and $hb2$ as follows:

<div>
\[
\frac
{\begin{array}{c}
\forall a. hb1(a,x) \Rightarrow vis(a,x) \vdash \psi(x)
\end{array}}
{\begin{array}{c}
{\sf BlockingCoordFree(\psi)}
\end{array}}

\;\;\;\;\;\;

\frac
{\begin{array}{c}
\forall a. hb2(a,x) \Rightarrow vis(a,x) \vdash \psi(x)
\end{array}}
{\begin{array}{c}
{\sf NonBlockingCoordFree(\psi)}
\end{array}}
\]
</div>

In earlier articles, BlockingCoordFree contract is called a **sticky-available
specification** while NonBlockingCoordFree contract is called an **available
specification**.

# Significance of the specilizations

# Corollary

BlockingCoordFreedom(NonBlockingCoordFreedom) is **strictly** stronger than
coordination freedom. Moreover, a coordination-free specification is either
blocking or non-blocking.

<div>
\[
\begin{array}{rcl}
{\sf BlockingCoordFree(\psi)} & \Rightarrow & {\sf CoordFree(\psi)} \\
{\sf CoordFree(\psi)} & \not\Rightarrow & {\sf BlockingCoordFree(\psi)} \\\\
{\sf NonBlockingCoordFree(\psi)} & \Rightarrow & {\sf CoordFree(\psi)} \\
{\sf CoordFree(\psi)} & \not\Rightarrow & {\sf NonBlockingCoordFree(\psi)} \\\\
{\sf CoordFree(\psi)} & \Rightarrow & {\sf BlockingCoordFree(\psi)} ~\vee~ {\sf NonBlockingCoordFree(\psi)}
\end{array}
\]
</div>

[Ctrt]: http://multimlton.cs.purdue.edu/mML/Notes/research/notes/2014/05/30/Model-Derivation.html#ctrt
[Ctxt]: http://multimlton.cs.purdue.edu/mML/Notes/research/notes/2014/05/29/Checking-Coordination-Freedom.html#ctxt
