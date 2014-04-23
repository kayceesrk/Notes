---
layout: post
title:  "Coordination-freedom analysis through Z3 SMT solver"
date:   2014-04-21 14:33:00
categories: Research Notes
---

This article illustrates that [coordination freedom analysis][CoordFree]
analysis can be recast as a decision procedure that can be automatically
discharged through the SMT solver.

Informally, coordination freedom allows an operations to be peformed on one
replica, and ensures that even in the presence of concurrent updates on other
replicas, the execution conforms to the specification. A coordination free
operation does not impose any restriction on operations that can occur
concurrently, and in turn cannot make any assumptions about either concurrent
operations or operations that happen-after it.

The key intuition is this: if assuming that all operations that happened-before
an operation $a$ is visible to $a$ is enough to satisfy the pre-condition for
$a$, then $a$ is said to be coordination-free. This can be formally captured
as:

<div>
\[
\frac{
\begin{array}{c}
visIrr, visAnSym, soIrr, soAnSym, soTrans, soTot, soDis, hbVis \vdash p
\end{array}}
{CoordFree(p)}
\]
</div>

where

<div>
\[
\begin{array}{lrcl}
\text{(Vis is irreflexive)} 		& visIrr   & = & \forall a. \neg vis(a,a)\\
\text{(Vis is anti-symmetric)} 		& visAnSym & = & \forall a,b. vis (a,b) \Rightarrow \neg vis(b,a)\\
\text{(So is irreflexive)} 			& soIrr    & = & \forall a. \neg so(a,a)\\
\text{(So is anti-symmetric)} 		& soAnSym  & = & \forall a,b. so(a,b) \Rightarrow \neg so(b,a)\\
\text{(So is transitive)} 			& soTrans  & = & \forall a,b,b. so(a,b) \wedge so(b,c) \Rightarrow so(a,c)\\
\text{(So relates all actions} 		& soTot    & = & \forall a,b. a \neq b \wedge sess(a) = sess(b) \Rightarrow \\
\text{ in the same session)}   		&          &   & so(a,b) \vee so(b,a)\\
\text{(So does not relate actions} 	& soDis    & = & \forall a,b. sess(a) \neq sess(b) \Rightarrow \\
\text{ from different sessions)}	&		   &   & \neg(so(a,b) \vee so(b,a))\\
\text{(All action that happened-}	& hbVis    & = & \forall a,b.~(so \cup vis)^+(a,b) \Rightarrow vis(a,b)\\
\text{ before are visible)}			&		   &   & \\
\end{array}
\]
</div>

This proof obligation can be automatically discharged by Z3 as shown
[here][z3-coordfree].

[CoordFree]: http://multimlton.cs.purdue.edu/mML/Notes/research/notes/2014/04/16/Local-Specification.html
[z3-coordfree]: http://rise4fun.com/Z3/Vtc6
