---
layout: post
title: "Specification library"
date: 2014-05-03 14:37:00
categories: Research Notes
---

In this post, I hope to collect the library for the consistency specification
as well as collect examples. The intention is to derive a Catalyst style API
for this library.

{% highlight haskell %}
class Sort a
class Attr a -- Attributes. Examples: Key, ForeignKey, value, etc,.
data Effect
data Prop
type Spec = Action -> Prop

∀       :: (Effect -> Prop) -> Prop
∃       :: (Effect -> Prop) -> Prop
true    :: Prop
false   :: Prop
¬       :: Prop -> Prop
∨       :: Prop -> Prop -> Prop
∧       :: Prop -> Prop -> Prop
⇒       :: Prop -> Prop -> Prop
sameAct :: Effect -> Effect -> Prop
vis     :: Effect -> Effect -> Prop
so      :: Effect -> Effect -> Prop
sortOf  :: Sort a => Effect -> a -> Prop
ite     :: Prop -> Prop -> Prop -> Prop
sameAttr :: Attr a => a -> Effect -> Effect -> Prop
distinctActs :: [Effect] -> Prop
isInSameSess :: Effect -> Effect -> Prop
{% endhighlight %}

</br>
# Complete Specification for Bank Account

GetBalance
----------
{% highlight haskell %}
\a -> sortOf(a, GetBalance)
       -- Ensures that pervious deposits and withdraws in the same session are
       -- visible.
       ∧ ∀b. ¬sortOf(b, GetBalance) ∧ so(b,a) ⇒ vis(b,a)
       -- Ensures that the balance is never incorrectly determined as 0 due to
       -- missing deposits.
       ∧ ∀b,c. sortOf(b, Withdraw) ∧ sortOf(c, Deposit) ∧ vis(b,a) ∧ vis(c,b) ⇒ vis(c,a)
{% endhighlight %}

Withdraw
--------
{% highlight haskell %}
\a -> sortOf(a, Withdraw)
       -- Ensures that previous deposits and withdraw operations from the same
       -- sessiona are visible.
       ∧ ∀b. ¬sortOf(b, GetBalance) ∧ so(b,a) ⇒ vis(b,a)
       -- Withdraw operations are totally ordered in order to ensure that withdraw
       -- operations are strongly consistent -> balance does not go below zero.
       ∧ ∀b. sortOf(b, Withdraw) ⇒ vis(a,b) ∨ vis(b,a)
       -- Withdraw calculates the current balance first. So, ensure that the
       -- balance is never incorrectly determined as 0 due to missing deposits.
       ∧ ∀b,c. sortOf(b, Withdraw) ∧ ¬sortOf(c, GetBalance) ∧ vis(b,a) ∧ vis(c,b) ⇒ vis(c,a)
{% endhighlight %}

Deposit
-------
{% highlight haskell %}
\_ -> true
{% endhighlight %}
