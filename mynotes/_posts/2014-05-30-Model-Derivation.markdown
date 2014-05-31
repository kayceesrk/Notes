---
layout: post
title: "Model Derivation from Sticky-available Specifications"
date: 2014-05-30 16:03:00
categories: Research Notes
---

This article is a followup of the [article][Model] on the necessity and utility
of models. In this article, we will focus on the mechanics of model derivation
and runtime use of the models.

# Specification Language

We will go for a modified specification language that is different from the
language used in previous articles. The two main differenences are:

- The specification only relates effects on the same object.
- Specification provides relational operators: union, intersection and
  transitive closure.

Restricting the specification to relations on the same object is a pragmatic
decision, which avoids the necessecity to track dependencies across objects and
simplifies the system for the purpose of formal description. Ideally, once we
are happy with per-object relations, we should expand to include cross object
relations as well. The specification language is given below:

<div>
\[
\newcommand{\ALT}{~\mid~}
\begin{array}{cclcl}
a & \in & {\tt Effect} \\
k & \in & {\tt Cons} & := & \bigcup_{\tau \in {\tt ObjType}} {\tt Con}_{~\tau} \\
r & \in & {\tt Relation} & := & vis \ALT so \ALT r^+ \ALT r_1 \cup r_2 \ALT r_1 \cap r_2 \\
p & \in & {\tt Prop} & := & true \ALT false \ALT \forall a.p \ALT \exists a. p \ALT \neg p \ALT r(a_1,a_2) \ALT sort(a,k) \\
  &		&			 & \ALT & p_1 \wedge p_2 \ALT p_1 \vee p_2 \ALT p_2 \Rightarrow p_2 \\
\psi & \in & {\tt Spec} & := & \lambda a.p
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
  \subseteq {a | a = SOE \vee a = TVISE} which qualifies the transitions from
  state $S$ to some state $S'$ such that $(S,S',prop) \in T$. $SOE$ models a
  transition which models a session order relation. $TVISE$ models a transition
  which models a $vis^+$ relation. The utility of $tk$ will become clear when
  we discuss the runtime check.
- $s\_0$ is the initial state.

[Model]: http://multimlton.cs.purdue.edu/mML/Notes/research/notes/2014/05/29/Checking-Coordination-Freedom.html
