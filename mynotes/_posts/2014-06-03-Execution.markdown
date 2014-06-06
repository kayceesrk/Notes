---
layout: post
title: "Execution and Contracts"
date: 2014-06-03 17:15:00
categories: Research Notes
---

In this article, we will precisely define the relationship of execution and
contracts. $
\newcommand{\Effect}{ {\sf Effect}}
\newcommand{\CtrtMap}{\Psi}
\newcommand{\Exec}{({\sf A},{\sf \CtrtMap},vis,so,sort)}
\newcommand{\Mod}[1]{ {\sf Mod}(#1)}
\newcommand{\cureff}{\eta}
\newcommand{\Effect}{ {\tt Effect}}
\newcommand{\Sort}{ {\tt Sort}}
\newcommand{\Bool}{ {\tt Bool}}
$

Let the contract language be:

<div>
\[
\newcommand{\ALT}{~\mid~}
\begin{array}{cclcl}
e,\cureff & \in & {\tt Effect} \\
k & \in & {\tt Sort} \\
r & \in & {\tt Relation} & := & vis \ALT so \ALT r^+ \ALT r_1 \cup r_2 \ALT r_1 \cap r_2 \\
\psi & \in & {\tt Contract} & := & true \ALT \forall e.\psi \ALT \neg \psi \ALT r(e_1,e_2) \ALT e_1 = e_2 \\
  &		&			 & \ALT & \psi_1 \wedge \psi_2 \ALT \psi_1 \vee \psi_2 \ALT \psi_2 \Rightarrow \psi_2 \ALT sort(e,k) \\
\end{array}
\]
</div>

The term $\cureff$ is a special variable of type effect that represents the
current effect. $\cureff$ may appear free in the contract.

# Execution

An execution is a $E := \Exec$ where

- $A \subseteq \Effect$ is the set of effects drawn from the universe
  $\Effect$,
- $\CtrtMap \subseteq {\tt Sort} \to {\tt Contract}$ be the function that maps
  each sort to its contract,
- $vis \subseteq E \times E$ be the acyclic visibility relation,
- $so \subseteq E \times E$ be the session order, which is a disjoint union of
  the total order of all effects in each session,
- $sort \subseteq E \to {\tt Sort}$ be the sort function that maps each effect
  to its sort.

For perspicuity, given an execution $E := \Exec$, we write $E.A$, $E.vis$, etc,
to denote $A$, $vis$ and so on.

# Well-formedness

A contract $\psi$ is said to be well-formed if:

- $\psi$ is prenex quantified. That is, $\psi = \overline{\forall e}.\psi_1$ and
  $\psi_1$ is quantifier-free.
- $freeVariables(\psi) \subseteq \\{\cureff\\}$
- $\psi$ is [well-typed][#welltyped].

The execution is said to be well-formed if

- the happens-before relation $hb = (vis \cup so)^+$ is acyclic.
- for all $\psi \in range(\CtrtMap)$, $\psi$ is well-formed.
- for all $e \in E.A$, $E$ satisfies the contract $\psi =
  E.\CtrtMap(E.sort(e))[\cureff/e]$. Alternatively, we say $\psi$ is true under
  $E$. Formally, we write $E \models \psi$.

The definition of $\models$ is given below.

# Execution satisfies a specification

We provide an inductive definition of $E \models \psi$ as follows.

- If $\psi$ is $e_1 = e_2$, then $E \models \psi$ if $e_1 = e_2$.
- If $\psi$ is $\neg\psi_1$, then $E \models \psi$ if $E \not\models \psi_1$.
- If $\psi$ is $(\psi_1 \wedge \psi_2)$, then $E \models \psi$ if $E \models \psi_1$
  and $E \models \psi_2$.
- If $\psi$ is $(\psi_1 \vee \psi_2)$, then $E \models \psi$ if $E \models \psi_1$
  or $E \models \psi_2$.
- If $\psi$ is $\forall x. \psi_1$, then $E \models \psi$ if for all $e \in E.A$,
  $E \models \psi_1[x/e]$.
- If $\psi$ is $\exists x. \psi_1$, then $E \models \psi$ if there exists an $e
  \in E.A$, such that $E \models \psi_1[x/e]$.
- If $\psi$ is $vis(a,b)$, then $E \models \psi$ if $(a,b) \in E.vis$.
- If $\psi$ is $so(a,b)$, then $E \models \psi$ if $(a,b) \in E.so$.
- If $\psi$ is $sort(e,k)$, then $E \models \psi$ if $E.sort(e) = k$.
- If $\psi$ is $(r_1 \cup r_2)(a,b)$, then $E \models \psi$ if $E \models
  r_1(a,b) ~\vee~ r_2(a,b)$.
- If $\psi$ is $(r_1 \cap r_2)(a,b)$, then $E \models \psi$ if $E \models
  r_1(a,b) ~\wedge~ r_2(a,b)$.
- If $\psi$ is $r^+(a,b)$, then $E \models r(a,b)$ or there exists a $c \in E.A$
  such that $E \models r^+(a,c) ~\wedge~ r(c,b)$.

We can use the definition of modeling relation to compare contracts, as we will
see next.

# Comparing contracts

Let $\Mod{\psi}$ define the equivalence class of all executions under which the
contract $\psi$ is satisfied. Formally, $\Mod{\psi} = \\{E ~\mid~ \exists e
\in E.A ~\wedge~ E \models \psi[\cureff/e] \\}$.

We can now **statically** compare two contracts. Given two contracts $\psi_1$
and $\psi_2$, $\psi_1$ is said to be (non-strictly) stronger than $\psi_2$ if
$\Mod{\psi_1} \subseteq \Mod{\psi_2}$. This relation expresses that every
execution that is a model of $\psi_1$ is also a model for $\psi_2$. This is the
[model-theoretic consequence relation][ModelTheory] written as $\psi_1
\models_{m} \psi_2$. The subscript $m$ is simply there to distinguish the
consequence relation from the modeling relation $\models$ described earlier.

Since $\psi$ is first-order, due to completeness theorem, $\psi_1 \models_{m}
\psi_2$ holds if and only if there is a proof of $\psi_2$ from $\psi_1$.
Formally, $\psi_1 \vdash \psi_2$. This is equivalent to $\vdash \psi_1
\Rightarrow \psi_2$ ([Rule of implication][RoI]). This check is discharged
through the SMT solver, where $\cureff$ is encoded as a constant of an SMT type
$\Effect$, and $vis :: \Effect \to \Effect \to \Bool$, $so :: \Effect \to
\Effect \to \Bool$ and $sort :: \Effect \to \Sort \to \Bool$ are encoded as
uninterpreted functions, where $\Sort$ is an SMT type for sorts.

[ModelTheory]: http://plato.stanford.edu/entries/model-theory/#Cons
[RoI]: https://proofwiki.org/wiki/Extended_Rule_of_Implication

# Contract classes

Typically the contract system monitors program execution, checks whether the
assertions hold, and, if not, blames the guilty component. Unlike this, we view
contracts as a declarative specification of visibility obligations that are
meant to be **enforced** by the runtime system, such that the resultant
execution is always well-formed. Since the strength of contracts vary, our aim
is to derive highly-scalable implementations for weaker contracts with the
intention of improving scalability without compromising correctness.
