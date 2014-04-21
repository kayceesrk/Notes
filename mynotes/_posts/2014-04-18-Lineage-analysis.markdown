---
layout: 	post
title:  	"Lineage Analysis"
date:   	2014-04-18 12:57:00
categories: Research Notes
---

Our goal with the lineage analysis is to determine, given a [coordination
free][CoordFree] specification, what are the minimal edges that need to be
tracked in order to check when a particular coordination-free operation can be
discharged. For example, consider the example of read-my-writes visibility.

<div>
\[
\newcommand{\k}[1]{k#1}
\newcommand{\curAct}{\bullet}
\newcommand{\edgeSo}[2]{\langle \text{so}, #1, #2 \rangle}
\newcommand{\edgeVis}[2]{\langle \text{vis}, #1, #2 \rangle}
\text{Read my writes :} ~~\forall a. inSo(a) \Rightarrow inVis(a)
\]
</div>

This specification says that any operation for which we need to enforce
read-my-writes visibility, we need to keep track of the session order relation
for all the actions that preceded the current operation in session order. Let
$\k{\langle E, a, b \rangle}$ indicate that an edge $a
\overset{E}{\longrightarrow} b$ is in the set of known edges. In the case of
read my writes, $\forall a. \k{\edgeSo{a}{\curAct}}$ holds, where $\curAct$ is
the current action. Similarly, consider the monotonic writes specification,

<div>
\[
\text{Monotonic writes :} ~~\forall a,b. so(a,b) \wedge inVis(b) \Rightarrow inVis(a)
\]
</div>

In this case, we need to track two types of edges; (1) $\forall a. \k{\edgeVis{a}{\curAct}}$
and (2) $\forall a,b. \k{\edgeVis{b}{\curAct}} \Rightarrow \k{\edgeVis{a}{b}}$.

[CoordFree]: http://multimlton.cs.purdue.edu/mML/Notes/research/notes/2014/04/16/Local-Specification.html
