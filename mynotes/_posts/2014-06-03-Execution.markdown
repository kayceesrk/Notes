---
layout: post
title: "Execution and Contracts"
date: 2014-05-31 17:15:00
categories: Research Notes
---

In this article, we will precisely define the relationship of execution and
contracts. $
\newcommand{\Effect}{ {\sf Effect}}
\newcommand{\CtrtMap}{\Psi}
\newcommand{\Exec}{({\sf A},{\sf \CtrtMap},vis,so,sort)}
\newcommand{\Mod}[2]{ {\sf Mod}(#1,#2)}
$

Let the contract language be:

<div>
\[
\newcommand{\ALT}{~\mid~}
\begin{array}{cclcl}
e & \in & {\tt Effect} \\
k & \in & {\tt Sort} \\
r & \in & {\tt Relation} & := & vis \ALT so \ALT r^+ \ALT r_1 \cup r_2 \ALT r_1 \cap r_2 \\
\pi & \in & {\tt Prop} & := & true \ALT false \ALT \forall e.\pi \ALT \exists e. \pi \ALT \neg \pi \ALT r(e_1,e_2) \ALT sort(e,k) \\
  &		&			 & \ALT & \pi_1 \wedge \pi_2 \ALT \pi_1 \vee \pi_2 \ALT \pi_2 \Rightarrow \pi_2 \\
\psi & \in & {\tt Contract} & := & \lambda e.\pi
\end{array}
\]
</div>

# Execution

An execution is a $E := \Exec$ where

- $A \subseteq \Effect$ is the set of effects drawn from the universe
  $\Effect$,
- $\CtrtMap \subseteq E \to {\tt Contract}$ be the function that maps each effect
  to its contract,
- $vis \subseteq E \times E$ be the acyclic visibility relation,
- $so \subseteq E \times E$ be the session order, which is a disjoin union of
  the total order of all effects in each session,
- $sort \subseteq E \to {\tt Sort}$ be the sort function that maps each effect
  to its sort.

For perspecuity, given an execution $E := \Exec$, we write $E.A$, $E.vis$, etc,
to denote $A$, $vis$ and so on.

# Well-formedness

The execution is said to be well-formed if

- the happens-before relation $hb = (vis \cup so)^+$ is acyclic
- for all $e \in E.A$, $E$ satisfies the contract $E.\CtrtMap(e)(e)$.
  Formally, $E \models E.\CtrtMap(e)(e)$. Alternatively, we say
  $E.\CtrtMap(e)(e)$ is true under $E$.

The definition of $\models$ is given below.

# Execution satisfies a specification

We provide an inductive definition of $E \models \pi$ as follows.

- If $\pi$ is $true$, then $E \models \pi$.
- If $\pi$ is $false$, then $E \not\models \pi$.
- If $\pi$ is $e_1 = e_2$, then $E \models \pi$ if $e_1 = e_2$ under $E.A$.
- If $\pi$ is $\neg\pi_1$, then $E \models \pi$ if $E \not\models \pi_1$.
- If $\pi$ is $(\pi_1 \wedge \pi_2)$, then $E \models \pi$ if $E \models \pi_1$
  and $E \models \pi_2$.
- If $\pi$ is $(\pi_1 \vee \pi_2)$, then $E \models \pi$ if $E \models \pi_1$
  or $E \models \pi_2$.
- If $\pi$ is $\forall x. \pi_1$, then $E \models \pi$ if for all $e \in E.A$,
  $E \models \pi_1[x/e]$.
- If $\pi$ is $\exists x. \pi_1$, then $E \models \pi$ if there exists an $e
  \in E.A$, such that $E \models \pi_1[x/e]$.
- If $\pi$ is $vis(a,b)$, then $E \models \pi$ if $(a,b) \in E.vis$.
- If $\pi$ is $so(a,b)$, then $E \models \pi$ if $(a,b) \in E.so$.
- If $\pi$ is $sort(e,k)$, then $E \models \pi$ if $E.sort(e) = k$.
- If $\pi$ is $(r_1 \cup r_2)(a,b)$, then $E \models \pi$ if $E \models
  r_1(a,b) ~\vee~ r_2(a,b)$.
- If $\pi$ is $(r_1 \cap r_2)(a,b)$, then $E \models \pi$ if $E \models
  r_1(a,b) ~\wedge~ r_2(a,b)$.
- If $\pi$ is $r^+(a,b)$, then $E \models r(a,b)$ or there exists a $c \in E.A$
  such that $E \models r^+(a,c) ~\wedge~ r(c,b)$.

We can use the defintion of modelling relation to compare contracts, as we will
see next.

# Comparing contracts

Let $\Mod{\psi}{x}$ define the equivalence class of all executions under which
the contract $\psi$ is satisfied for $x$. Formally, $\Mod{\psi}{x} = \\{E
~\mid~ x \in E.A. ~\wedge~ E.\CtrtMap(x) = \psi ~\wedge~ E \models \psi(x)\\}$.

We can now compare two contracts. Given two contracts $\psi_1$ and $\psi_2$,
$\psi_1$ is said to be (non-strictly) stronger than $\psi_2$ if
$\Mod{\psi_1}{x} \subseteq \Mod{\psi_2}{x}$. This relation expresses that every
execution that is a model of $\psi_1(x)$ is also a model for $\psi_2(x)$. This
is the [model-theoretic consequence relation][ModelTheory] written as
$\psi_1(x) \models_{m} \psi_2(x)$. The subscript $m$ is simply there to
distinguish the consequence relation from the modelling relation $\models$
described earlier.

Since $\psi(x)$ is first-order, due to completeness theorem $\psi_1(x)
\models_{m} \psi_2(x)$ holds if and only if there is a proof of $\psi_2(x)$
from $\psi_1(x)$. Formally, $\psi_1(x) \vdash \psi_2(x)$. This is equivalent to
$\vdash \psi_1(x) \Rightarrow \psi_2(x)$ ([Rule of implication][RoI]). This check
is discharged to the SMT solver, where $vis$, $so$ and $sort$ are encoded as
uninterpreted functions. Is this check decidable?


[ModelTheory]: http://plato.stanford.edu/entries/model-theory/#Cons
[RoI]: https://proofwiki.org/wiki/Extended_Rule_of_Implication
