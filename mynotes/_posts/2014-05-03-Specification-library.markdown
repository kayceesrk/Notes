---
layout: post
title: "Codeec Specifications"
date: 2014-05-03 14:37:00
categories: Research Notes
---

In this post, I hope to collect the library for the consistency specification
as well as collect examples. The intention is to derive a Catalyst style API
for this library.

# Specification Library

{% highlight haskell %}
class Sort a
class Attr a -- Attributes. Examples: Key, ForeignKey, value, etc,.
data Effect
data Prop
type Spec = Effect -> Prop

∀            :: (Effect -> Prop) -> Prop
∃            :: (Effect -> Prop) -> Prop
true         :: Prop
false        :: Prop
¬            :: Prop -> Prop
∨            :: Prop -> Prop -> Prop
∧            :: Prop -> Prop -> Prop
⇒            :: Prop -> Prop -> Prop
sameAct      :: Effect -> Effect -> Prop
vis          :: Effect -> Effect -> Prop
so           :: Effect -> Effect -> Prop
sortOf       :: Sort a => Effect -> a -> Prop
ite          :: Prop -> Prop -> Prop -> Prop
sameAttr     :: Attr a => a -> Effect -> Effect -> Prop
distinctActs :: [Effect] -> Prop
isInSameSess :: Effect -> Effect -> Prop
{% endhighlight %}

# Analyses

* **Coordination Freedom** -- Can a specification be safely discharged without
  coordination such that the DB state converges? Might require locally delaying
  the operation until the necesary context is available.
* **Availability** -- There is no need to even locally delay the operation. All
  available operations are coordination-free, where as there are some
  coordination-free operations which are not available.
* **Minimum edge set** -- What are the edges that need to be added to the
  visibility set?
* **Useless effects** -- Example: GetBalance in BankAccount since the GetBalance
  effects are never utilized in any other procedures.

While the first three analyses can be performed only with the specification,
the useless effect analysis need to analyse the source code.

# Complete Specification for Bank Account

GetBalance
----------
{% highlight haskell %}
\a ->  -- Ensures that pervious deposits and withdraws in the same session are
       -- visible.
       ∀b. sortOf(a, GetBalance) ∧ ¬sortOf(b, GetBalance) ∧ so(b,a) ⇒ vis(b,a)
       -- Ensures that the balance is never incorrectly determined as 0 due to
       -- missing deposits.
       ∧ ∀a,b,c. sortOf(a, GetBalance) ∧ sortOf(b, Withdraw) ∧ sortOf(c, Deposit) ∧ vis(b,a) ∧ vis(c,b) ⇒ vis(c,a)
{% endhighlight %}

Withdraw
--------
{% highlight haskell %}
\a ->  -- Ensures that previous deposits and withdraw operations from the same
       -- sessiona are visible.
       ∀b. sortOf(a, Withdraw) ∧ ¬sortOf(b, GetBalance) ∧ so(b,a) ⇒ vis(b,a)
       -- Withdraw operations are totally ordered in order to ensure that withdraw
       -- operations are strongly consistent -> balance does not go below zero.
       ∧ ∀b. sortOf(a, Withdraw) ∧ sortOf(b, Withdraw) ⇒ vis(a,b) ∨ vis(b,a)
       -- Withdraw calculates the current balance first. So, ensure that the
       -- balance is never incorrectly determined as 0 due to missing deposits.
       ∧ ∀b,c. sortOf(a, Withdraw) ∧ sortOf(b, Withdraw) ∧ ¬sortOf(c, GetBalance) ∧ vis(b,a) ∧ vis(c,b) ⇒ vis(c,a)
{% endhighlight %}

It is important to notice that the pre-conditions for withdraw operation has to
be satisfied before performing the operation. Since the withdraw operation will
be applied to every replica, does it mean that the precondition has to be
satisfied on each replica? How do we do this on Cassandra?

For this issue, I believe a read consistency level [ALL][CassandraConsistency]
should work. The idea is that an ALL consisteny level for read returns the
record with the most recent timestamp after all the replicas have responded.
Since there are no updates or conflicting updates on the records in our tables
(every Codeec level effect is a record insertion), the result of the select
query should return all the records from every replica, which by definition,
should contain all the effects that happened before the current effect.

Deposit
-------
{% highlight haskell %}
\_ -> true
{% endhighlight %}

[CassandraConsistency]: http://www.datastax.com/docs/1.1/dml/data_consistency
