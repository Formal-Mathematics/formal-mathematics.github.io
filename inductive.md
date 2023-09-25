---
title: Inductive Types
layout: default
nav_order: 10
---

# Inductive Types

Inductive types are types that satisfy a certain universal property that tells you how to map *out* of them.
There is a [purely categorical characterization](https://ncatlab.org/nlab/show/inductive+type) which you can look at, if you are so inclined.

In Lean, we declare inductive types with the `inductive` keyword, following by a number of so-called *constructors*.
The constructors are the various ways in which you can build terms of the given inductive type.

The key thing to keep in mind is that the universal property of inductive types explain how to map *out* of them.
So, whenever you have a type which such a universal property, it can often be modeled with an inductive type. 

## Examples of inductive types

We will look at various examples of inductive types, of increasing complexity.

### Single term types
Let's start with the most basic example.

```lean
inductive Foo where
  | foo : Foo
```

This defines a type `Foo` with a single term called `Foo.foo`.
In fact, the built-in type `PUnit` is defined in a similar way:
```lean
inductive PUnit : Sort u where
  | unit : PUnit
```

How can we argue about terms of `Foo`? 
Well, whenever we define an inductive type, Lean automatically creates the type itself, as well as a number of auxiliary lemmas and constructions.
I'll mention a few below.
For now, let's see how we can prove that any term of `Foo` is equal to `Foo.foo`.

```lean
example (a b : Foo) : a = b := by
  cases a
  cases b
  rfl
```

The use of `cases` indicates that some *pattern matching* has taken place.
In fact, we can use pattern matching explicitly to prove the same thing, as follows:

```lean
example (a b : Foo) : a = b := 
  match a, b with 
    | .foo, .foo => rfl
```

### Two term types

We can have multiple constructors.
```lean
inductive Bar where
  | a : Bar 
  | b : Bar
```

Again, this is similar to something from the library, name the type `Bool` of booleans, defined as follows:
```lean
inductive Bool : Type where
  | false : Bool
  | true : Bool
```

Let's now see how to define functions from inductive types in a number of ways.
First, we can use pattern matching similar to the example above to construct such a function.

```lean
example (x : Bar) : Nat := 
  match x with 
    | .a => 0
    | .b => 1
```

This is a bit verbose, and we can compress it with the so-called *equation compiler*, as follows:
```lean
example : Bar → Nat 
  | .a => 0
  | .b => 1
```

As I mentioned above, when declaring an inductive type a number of declarations are added automatically.
In this case, the relevant one is called `Bar.rec`, and its type is:
```lean
Bar.rec.{u} {motive : Bar → Sort u} (a : motive Bar.a) (b : motive Bar.b) (t : Bar) : motive t
```

What this gives us is a way to construct arbitrary dependent functions out of `Bar`.
The "motive" here refers to the family of types (really, sorts, since we want to be able to construct maps to propositions or types) which is the "codomain" of our desired dependent function.
In this case, if `motive : Bar -> Type` is such a family (to Types, for simplicity), this says that in order to obtain a dependent function to `motive` from `Bar`, it suffices to provide a term of `motive .a` (the image of `.a`) and a term of `motive .b` (the image of `.b`).

Here I am using a Lean4 trick which allows me to write `.a` or `.b` instead of `Bar.a` or `Bar.b` as long as Lean knows to expect a term of `Bar`.

Here is the above example constructed using `Bar.rec`:
```lean
example : Bar → Nat :=  
  Bar.rec 0 1
```

This will result in an error in Lean4, saying 
```lean
code generator does not support recursor 'Bar.rec' yet, consider using 'match ... with' and/or structural recursion
```
but this is just because compiler support for explicitly using `.rec` functions has not been implemented yet.
In terms of the underlying type theory, the three functions above are equivalent.

### The Natural Numbers

So far we have talked about inductive types whose terms do not involve other terms of the given type.
But the power of inductive types, as the name suggests, comes from the fact that they are related to *induction*.
There are some technical conditions on where terms of an inductive type can appear in its own definition, and Lean will give you errors if you try to use such a term where it cannot be used.

Let's look at an example:
```lean
inductive MyNat where
  | zero : MyNat
  | succ : MyNat → MyNat 
```

In this case, `MyNat` (my version of the naturals) is an inductive type with two constructors, `zero` which is just a term of `MyNat`, and `succ` which takes a term of `MyNat` and produces a new term of `MyNat`.

We can use pattern matching to define "addition" of terms of `MyNat` reflecting the usual addition of natural numbers:
```lean
def MyNat.add : MyNat → MyNat → MyNat 
  | .zero, b => b
  | (.succ a), b => .succ (MyNat.add a b)
```
So, `zero.add b` is defined to be `b`, while `(succ a).add b` is defined to be `succ (a.add b)`.
This is a *recursive* definition.

The same definition can be given using `match` as follows:
```lean
def MyNat.add (a b : MyNat) : MyNat :=
  match a, b with
    | .zero, b => b
    | (.succ a), b => .succ (MyNat.add a b) 
```

Here is another common example of an inductive type:
```lean
inductive MyList (α : Type) where
  | nil : MyList α 
  | cons : α → MyList α → MyList α 
```
This is the type of lists of terms of `α`.
Such a list is either empty (`nil`), or has the form `cons x xs` where `x : α` and `xs : MyList α`.
Think of `cons x xs` as sticking `x` on the left of `xs` to obtain a list whose length is increased by one.

We can construct the length function on `MyList` by recursion as follows:
```lean
def MyList.length {α : Type} : MyList α → MyNat 
  | .nil => .zero
  | .cons _ xs => .succ (MyList.length xs)
```

Similarly, we can define the function which takes a natural number `n` and returns the constant list all of whose terms are `zero`, of length `n`:

```lean
def MyList.constant : MyNat → MyList MyNat 
  | .zero => .nil
  | .succ n => .cons .zero (MyList.constant n)
```

The word `My` in the names of `MyNat` and `MyList` are just there to avoid name clashes.
In the rest of this note I will use the built-in types `Nat` and `List` for natural numbers and lists.