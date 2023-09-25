---
title: Binders
layout: default
nav_order: 8
---

# Binders

Binders are a way to introduce variables in a definition.
Lean has the following kinds of binders:
1. Explicit binders: `( ... )`
2. Implicit binders: `{ ... }`
3. Strict implicit binders: `{{ ... }}`
4. Instanced binders: `[ ... ]`. 

## Explicit Binders

We have already seen this kind of binder.
It lets you introduce a variable in a definition which must be mentiond explicitly when using the definition.

For example:
```lean
def foo (n : Nat) : Nat := n + 1

#eval foo 5
```

## Implicit Binders

This kind of binder lets you introduce a variable in a definition which can be inferred by Lean.
When using the definition, the user does not need to explicitly mention the variable.
If Lean cannot infer the value of an implicit variable, it will complain.

For example:
```lean
def foo' {n : Nat} : Nat := n + 1

#eval foo' -- Lean complains
```

Compare that to the following example:
```lean
def bar {n : Nat} (i : Fin n) : Nat := n + 1

variable (i : Fin 5)

#eval bar i -- 5
```

In the second example, Lean is able to infer the value of `n` from the type of `i`, whereas in the first, Lean has no way of inferring the value of `n`.

Implicit binders are used frequently to introduce type variables in certain definitions.

For instance:
```lean
def baz {α : Type} (a : α) : α := a
```

Lean can infer the value of `α` from the type of `a`, so we don't need to mention it when using the definition, as long as `a` is mentioned explicitly.


## Strict Implicit Binders

This kind of binder is similar to an implicit binder.
The difference is quite subtle and has to do with elaboration order.
Specifically, this kind of binder tells Lean to only add the value before a subsequence explicit variable. 
This subtle point goes beyond the scope of this course, but you can read more about it [here](https://lean-lang.org/theorem_proving_in_lean4/interacting_with_lean.html?highlight=binder#more-on-implicit-arguments).
We may revisit this concept later in the course.

## Making implicit binders explicit

We can use `@` to make implicit binders explicit, if necessary.
For example:
```lean
def thing {n : Nat} (m : Nat) : Nat := n + m

#eval @thing 5 10
```

Lean4 has a new feature which allows you to specify the value of variables (whether implicit or explicit) by directly using the name of the variable in the declaration.

For example, with `thing` as above, the following works as well:
```lean
#eval thing (m := 5) 10
```

## Instanced Binders

This kind of binder is used to introduce a class instance.
We will talk more about classes in the following lecture note.
For now, you can think of a class instance as a way to attach additional data to a type.

For example, if we wish to talk about a group, meaning that we need to specify that a given type `G` has a group structure, we could do it as follows:

```lean
variable (G : Type) [Group G]
```

Here, `G` is a type and `[Group G]` is a class instance.
Naming the term of `Group G` is optional -- we could have written
```lean
variable (G : Type) [e : Group G]
```

With such a variable declaration, we could write
```lean
example (a b c : G) : (a * b) * c = a * (b * c) := mul_assoc _ _ _
```

Here is a full example with the necessary imports:
```lean
import Mathlib.Algebra.Group.Defs

variable (G : Type) [Group G]

example (a b c : G) : (a * b) * c = a * (b * c) := 
  mul_assoc _ _ _
```
