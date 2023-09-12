---
title: Tactics
layout: default
nav_order: 6
---

# Tactics

In a nutshell, tactics can be used to construct a term of a type.
In practice, the terms that we construct using tactics are usually proofs of propositions, but this is not a strict restriction.

Tactic blocks can be seen as scripts which are used to construct terms.
We use the `by` keyword to indicate that we are entering a tactic block.

```lean
example : 1 + 1 = 2 := by
  rfl
```

## Sorry

The `sorry` keyword is both a tactic and a term.
When using it as a term, it can be used as a term of any type/proposition.
When using it as a tactic, it can be used to construct a term of any type/proposition.

For example with the example above, we can use `sorry` as a tactic:
```lean
example : 1 + 1 = 2 := by
  sorry
```
Or we can use `sorry` as a term:
```lean
example : 1 + 1 = 2 :=
  sorry
```

We can also use `sorry` as terms of types which are not propositions:
```lean
def foo : Nat := sorry
```

## Exact

The `exact` tactic can be used to construct a term of a type which is *definitionally equal* to the goal type.
For example, we can use `exact rfl` to construct a term of `1 + 1 = 2`:
```lean
example : 1 + 1 = 2 := by
  exact rfl
```

If we have the following goal context:
```lean
n m : Nat
h : n = m
```
then we can use `exact h` to construct a term of `n = m`:
```lean
example (n m : Nat) (h : n = m) : n = m := by
  -- Context here should be as above.
  exact h
```

## Intro

The `intro` tactic can be used to construct a term of a type which is a function type.
It `intro`duces a new variable into the context and changes the goal type to the codomain of the function type.
For example, we can use `intro n` to construct a term of `Nat -> Nat`:
```lean
example : Nat -> Nat := by
  intro n
  exact n + 19
```

## Apply

The `apply` tactic can be used to reduce the goal to another.
Explicitly, if `f : A1 -> ... -> An -> B` is a n-ary function, and the goal is `B`, then `apply f` will change the goal `n` goals of type `A1`, ..., `An`.

For example:
```lean
example (P Q R : Prop) (h : P -> Q -> R) : R := by
  -- One goal here: `R`.
  apply h
  -- Two goals: `P` and `Q`.
  sorry
```

Think of it as applying a lemma to the goal.
The lemma may have a number of hypotheses, and applying the lemma will reduce the goal to proving those hypotheses.

## Induction

The `induction` tactic is used to argue inductively.
It is used when working with so-called "inductive types", which we will see later.
The natural numbers is an example of an inductive type.
It is defined as
```lean
inductive Nat where
  | zero : Nat
  | succ : Nat -> Nat
```

If we want to induct on a natural number `n`, then we can use `induction n` to reduce the goal to two goals:
1. The base case, where `n` is `zero`.
2. The inductive case, where `n` is `succ m` for some `m : Nat`, along with the inductively hypothesis that the assertion being proved holds for `m`.

Let's see an example:
```lean
example (n : Nat) : n + 0 = n := by
  induction n with
  | zero =>
    -- Goal here is `0 + 0 = 0`.
    -- Context here is empty.
    sorry
  | succ m ih =>
    -- Goal here is `succ m + 0 = succ m`.
    -- Context here is `m : Nat` and `ih : m + 0 = m`. 
    -- This `ih` is our "inductive hypothesis".
    sorry
```

## Cases

The `cases` tactic is used to argue by cases.
It is similar to `induction`, but it does not give us an inductive hypothesis.

Let's see an example:
```lean
example (n : Nat) : n + 0 = n := by
  cases n with
  | zero =>
    -- Goal here is `0 + 0 = 0`.
    -- Context here is empty.
    sorry
  | succ n =>
    -- Goal here is `succ n + 0 = succ n`.
    -- Context here is `n : Nat`.
    sorry
```

## Assumption

The `assumption` tactic is used to prove a goal which is *definitionally equal* to a hypothesis in the context.
For example:
```lean

example (n : Nat) (h : n = 0) : n = 0 := by
  assumption
```

## Rewrite

The `rw` (rewrite) tactic is used to rewrite the goal using a hypothesis.
For example:
```lean
example (n : Nat) (h : n = 0) : n + 1 = 1 := by
  rw [h]
```

## The Simplifier

The simplifier is a tactic which is used to simplify terms.
It is one of the most important tactics in Lean4, besides the basic ones above.
It is extremely powerful and useful.
It is used to simplify terms using theorems in the library, and we can even control which theorems it uses.

For example:
```lean
example (n : Nat) : n + 0 = n := by
  simp
```

We can tag certain lemmas in the library with the `@[simp]` attribute, and the simplifier will use them when simplifying terms.
We will see explicit examples of this during lecture.

## Other tactics

Lean has many MANY tactics, and more are being introduced all the time.
We will not be able to cover all of them in this course, but we will cover the most important ones.
Whenever we encounter a new tactic, I will try to explain how to use it.
When in doubt, use the `#help` command to get more information about a tactic, or the online documentation.

