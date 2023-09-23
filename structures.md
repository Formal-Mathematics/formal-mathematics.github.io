---
title: Structures
layout: default
nav_order: 7
---

A structure is a way to bundle together (possibly interrelated) data.
For example, the sigma type associated to a family `X : A -> Type` is an example of a structure, defined as follows:

```lean
structure Sigma (X : A -> Type) where
  fst : A
  snd : X fst
```

The two fields, `fst` and `snd` are called "projections".
This terminology comes from products, which can also be defined as structures:

```lean
structure Prod (X Y : Type) where
  fst : X
  snd : Y
```
 
To access the projections, we can use dot notation:

```lean
variable (x : Prod X Y) 
#check x.fst
#check x.snd
```

Recall that this is just syntactic sugar for the following:
```lean
variable (x : Prod X Y) 
#check Prod.fst x
#check Prod.fst x
```

The *functions* `Prod.fst` and `Prod.snd` here are the actual projections while writing `x.fst` resp. `x.snd` applies these functions to the term `x : Prod X Y`.

## Parameterizing Structures

Structures are often parameterized, as we saw in the examples above.
Let's look at another example from algebra.
Recall that in algebra a monoid is just a set with an associative binary operation and two-sided identity for the operation.

We can model this as a "bundled structure" in Lean as follows

```lean
structure BundledMonoid where
  carrier : Type
  op : carrier → carrier → carrier 
  identity : carrier
  associativity : 
    ∀ (a b c : carrier), op (op a b) c = op a (op b c)
  left_identity :
    ∀ (a : carrier), op identity a = a
  right_identity :
    ∀ (a : carrier), op a identity = a
```

The word "bundled" here comes from the fact that the underlying type of the monoid is "bundled" as part of the structure itself.
We will revisit this approach later on when we discuss categories appearing in algebra.
You can think of `BundledMonoid` as the type of all monoids.

However, when doing algebra in the usual way, it's more common to talk about a monoid structure on a particular type `M : Type`, as opposed to the type of all monoids.

```lean
structure Monoid (M : Type) where
  op : M → M → M 
  identity : M
  associativity : 
    ∀ (a b c : M), op (op a b) c = op a (op b c)
  left_identity :
    ∀ (a : M), op identity a = a
  right_identity :
    ∀ (a : M), op a identity = a
```

We often introduce structures of this sort not as plain structures, but as so-called *type classes* (see the next lecture notes for more about this).

## Extending Structures

We can use the `extends` keyword to extend existing structures with additional fields.

For example, suppose we want to consider the type of commutative bundled monoids.
Instead of defining this from scratch, we can "extend" the structure `BundledMonoid` above with an additional field ensuring commutativity:

```lean
structure BundledCommMonoid extends BundledMonoid where
  commutativity : ∀ (a b : carrier), op a b = op b a
```

Here is the unbundled variant of the same concept:

```lean
structure BundledCommMonoid extends BundledMonoid where
  commutativity : ∀ (a b : carrier), op a b = op b a
```

Of course, the additional fields you write when using `extends` don't need to be propositions, and can rather be arbitrary sorts.

When you extend a structure, a field `toFoo` is automatically added whose type is that of the structure you extended.

For example, in the two examples above, you have
```lean
#check BundledCommMonoid.toBundledMonoid
-- BundledCommMonoid.toBundledMonoid (self : BundledCommMonoid) : BundledMonoid

#check CommMonoid.toMonoid
-- CommMonoid.toMonoid {M : Type} (self : CommMonoid M) : Monoid M

```

Using these automatically generated projections you can access the projections from the structure you extended.

It's also possible to extend multiple structures:
```lean
structure A where
  n : Nat

structure B where
  m : Nat

structure C extends A, B where
  q : Int

#check C.toA
#check C.toB
#check C.q
```

Note that you don't need to write the `toFoo` when using dot notation.
For example, this works, with `C` as above:

```lean
def foo : C where
  n := 0
  m := 1
  q := 2

#check foo.m
#check foo.n
#check foo.q
```

This also gives an example of how one can construct a term of a structure.
Here is a shortcut which can be useful in some cases:

```lean
def bar : B where
  m := 5

def baz : C := { 
  bar with 
  n := 6 
  q := -1
}

#eval baz.m
#eval baz.n
#eval baz.q
```

Using `with` is useful when you previously constructed a term of some structure that your current structure extends, as in the example above, but it's also useful when you want to update a certain field:

```lean

def foo' : C := {
  foo with 
  n := 37
}

#eval foo'.n
#eval foo'.m
#eval foo'.q
#eval foo.n
#eval foo.m
#eval foo.q
```

## Subtypes

Subtypes are one of the most important examples of structures used in mathematics. 
This concept lets you consider a subset of a type, i.e. a term `S : Set X`, as a type.
Recall that `Set X` is *defined* as `X -> Prop`.

Here is how one defines a subtype associated to a set:
```lean
structure Subtype {X : Type} (S : Set X) where
  val : X
  cond : val ∈ S
```

Thus a term of `Subtype S`, for `S : Set X`, consists of a term `val : X` together with a proof that `val ∈ S`.
To obtain the "inclusion" from this type to `X`, one just uses the `val` projection.

Note: This kind of structure is part of Lean itself, so if you try to redefine it with the name `Subtype`, lean will complain.