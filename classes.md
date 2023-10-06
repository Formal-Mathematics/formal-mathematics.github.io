---
title: Classes
layout: default
nav_order: 9
---

# Classes

A Class (or typeclass) is a special kind of structure terms of which can be found by what's called the "typeclass system."
We use classes extensively to attach additional data to types, often also providing an *interface* for working with this additional data.

Typeclass parameters are declared with square brackets `[...]`.
Terms of typeclasses can either be defined with `def/lemma/theorem` as usual, or with the `instance` keyword.
By using `instance` instead of `def` we instruct Lean's typeclass framework that the given term should be discoverable by the system during typeclass instance synthesis.

Instances of typeclasses can depend on instances of other classes.
This allows us to build *hierarchies*, such as the order hierarchy, the algebra hierarchy, etc.

Let's look at some examples to illustrate these concepts more clearly.

## Monoids

Recall that we have defined the concept of a monoid structure on a type `M` as the following structure (modulo some renaming):
```lean
structure Monoid (M : Type) where
  mul : M → M → M
  one : M 
  mul_assoc : ∀ a b c : M, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a : M, mul one a = a
  mul_one : ∀ a : M, mul a one = a
```

We would like to work with terms, say `e`, of this structure without writing `e.mul`, `e.one`, for the multiplicaton, identity, etc.
Ideally, we would like to just write `mul` and have Lean automatically find the right monoid structure and use the multiplication obtained from that.
Even better would be to introduce notation for `mul` so we could write `a * b` instead of `mul a b`.
This can all be accomplished with typeclasses, as follows.

First, let's replace `structure` by `class`:
```lean
class Monoid (M : Type) where
  mul : M → M → M
  one : M 
  mul_assoc : ∀ a b c : M, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a : M, mul one a = a
  mul_one : ∀ a : M, mul a one = a
```

Note: classes are structures which are tagged with a `@[class]` atrribute, so we could have written
```lean
@[class]
structure ...
```
to obtain an essentially equivalent behavior.
However, using `class` as opposed to `structure` has other more subtle differences in how lean introduces certain binders when elaborating the declaration, so it's usually best to just use the `class` command when introducing a class.

Now, instead of writing `e.mul a b` for `e : Monoid M`, we can write `Monoid.mul a b` given that we have some term of `Monoid M` in context.
If we open the `Monoid` namespace, we can just write `mul`.
Here is an example, complete with the class declaration:

```lean
class Monoid (M : Type) where
  mul : M → M →M  
  one : M 
  mul_assoc : ∀ a b c : M, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a : M, mul one a = a
  mul_one : ∀ a : M, mul a one = a

variable (M : Type) [Monoid M]

open Monoid

example (a b : M) : M := mul a b
```

## Notation Classes

Lean has a few standard classes which exist only to allow for convenient notation. 
The relevant one for our monoid example is `Mul`, which is a class that provides multiplciative notation.
Similarly, `One` provides `1` as notation.

Let's modify our monoid class above to use this.
```lean
import Mathlib.Init.ZeroOne

class Monoid (M : Type) extends Mul M, One M where
  mul_assoc : ∀ a b c : M, (a * b) * c = a * (b * c)
  one_mul : ∀ a : M, 1 * a = a
  mul_one : ∀ a : M, a * 1 = a

variable (M : Type) [Monoid M]

open Monoid

example (a b : M) : M := a * b
example : M := 1
```

The `One` typeclass is defined in `Mathlib.Init.ZeroOne`, hence the import.
Note also that classes can extend other classes, just like structures can extend structures.
The example `Monoid` above now extends `Mul` and `One`, which allows us to write `a * b` instead of `mul a b` and `1 : M` instead of `one : M`.

We can now state and prove theorems about arbitrary monoids, as the following example indicates:
```lean
example (N : Type) [Monoid N] (a b c d : N) : 
    (a * b) * (d * c) = a * b * d * c := 
  by simp only [Monoid.mul_assoc]
```

## Extending the Hierarchy

Let's see how we can build on top of this monoid class and extend the hierarchy, by defining the notion of a group.

```lean
class Inv (α : Type u) where
  inv : α → α

postfix:max "⁻¹" => Inv.inv

class Group (G : Type) extends Monoid G, Inv G where
  mul_inv : ∀ (g : G), g * g⁻¹ = 1
  inv_mul : ∀ (g : G), g⁻¹ * g = 1
```

The `Inv` class above and subsequent `postfix` declaration introduces a class for inversion notation, and the notation itself, allowing us to write `g⁻¹` for the inverse of `g`.

We can now talk about groups, just like we were able to talk about monoids before:

```lean
example (G : Type) [Group G] (g h : G) : 
    g * g⁻¹ * h = h := by 
  simp [Group.mul_inv, Monoid.one_mul]
```

Note that Lean is automatically able to infer that `G` has a monoid instance provided that it has a group instance.
Otherwise, we would not have been able to use `Monoid.one_mul`.
We can see this explicitly by asking Lean to infer this instance given a group instance, as follows:

```lean
example (G : Type) [Group G] : Monoid G := inferInstance
```

What's actually going on here is that Lean automatically introduced an instance of a monoid for every type which has an instance of a group.
We can see this explicitly with the following:
```lean
#check Group.toMonoid
-- Group.toMonoid {G : Type} [self : Group G] : Monoid G
```

This is an example of an *instance*.
When using `[...]`, lean's typeclass system tries to syntesize an instance of the typeclass in question by looking at instances declared inthe current environment, as well as various implications among classes, all of which are also declared as instances similar to `Group.toMonoid` above.

## Instance

Now that we have some classes to work with, let's see how we can declare an instance.
For example, let's introduce the additive monoid structure on the natural numbers.

```lean
instance : Monoid ℕ where 
  mul_assoc := Nat.mul_assoc
  mul_one := Nat.mul_one
  one_mul := Nat.one_mul
```

Note that we did not have to provide instances of `Mul ℕ` or `One ℕ` because Lean was able to find such an instance from the library. 

When declaring an instance, providing a name is optional.
In this case, Lean introduced the name `instMonoidNat`.
If we wanted to control the name explicitly, we could have written
```lean
instance Nat.monoid : Monoid ℕ where 
  mul_assoc := Nat.mul_assoc
  mul_one := Nat.mul_one
  one_mul := Nat.one_mul
```

## Chaining Instances

To illustrate how to chain instances, let's look at another example from `Mathlib`: the concept of an *inhabited* type:
```lean
class Inhabited' (X : Type) where
  default' : X
export Inhabited' (default')
```

Here I use `Inhabited'` because `Inhabited` already exists in the library.
The `export` command tells lean to allow users to write `default'` without opening the `Inhabited'` namespace, just for convenience.

If `X Y : Type` are both inhabited, then so is their product.
We can put this fact into the typeclass system with the following instance:
```lean
instance (X Y : Type) [Inhabited' X] [Inhabited' Y] : Inhabited' (X × Y) where
  default' := (default', default')
```
And similarly for disjoint unions:
```lean
instance (X Y : Type) [Inhabited' X] : Inhabited' (X ⊕ Y) where
  default' := Sum.inl default'

instance (X Y : Type) [Inhabited' Y] : Inhabited' (X ⊕ Y) where
  default' := Sum.inr default'
```

Typeclass inference should now be able to deduce that various expressions involving disjoint unions and products are also inhabited, given that some/all of their components are inhabited.
For example:
```lean
example (X Y Z W : Type) [Inhabited' X] [Inhabited' W] :
    Inhabited' ((X ⊕ Y) × (Z ⊕ W)) := 
  inferInstance
```

In this case, Lean is looking for an instance of `Inhabited' ((X ⊕ Y) × (Z ⊕ W))`. 
It applies the fact that a product is inhabited if each of its components is inhabited, reducing the problem to providing inhabited instances for `(X ⊕ Y)` and `(Z ⊕ W)`.
In the first case, it uses the fact that `X` is inhabited and in the second case it uses the fact that `Z` is inhabited.
In other words, all three `Inhabited'` instances are used, in a completely automatic way, to infer an inhabited instance for `((X ⊕ Y) × (Z ⊕ W))`.

By using the option `set_option trace.Meta.synthInstance true` we can trace the steps that Lean's typeclass system took to find instances.
The output in this case is too complicated to display, so please try this out in your own editor, for example as follows:
```lean
set_option trace.Meta.synthInstance true
example (X Y Z W : Type) [Inhabited' X] [Inhabited' W] :
    Inhabited' ((X ⊕ Y) × (Z ⊕ W)) := 
  inferInstance
```

By placing the cursor over the `inferInstance` line, it will be possible to see the trace in the infoview. 

## `outParam`s

When a typeclass has a parameter, we generally think of this as an "input" for the typeclass system.
This is usually fine, as long as the typeclass system can infer the parameter from context.
For example, if the typeclass system is looking for a monoid instance on some type `M`, then it can infer `M` from since it is a parameter of the `Monoid` class.
Expliitly, a monoid structure on `M` is a term of `Monoid M`, so the type of this term tells the typeclass sytem what `M` is.

But there are some situations where it's impossible for the typeclass system to infer the parameter.
This usually happens when there is more than one parameter for the typeclass.

Consider the following class:
```lean
class F (A B : Type) where
  f : A → B
```
Let's suppose that we instantiate an instance as follows:
```lean
instance : F ℕ ℕ where
  f := id
```
If we want to use an instance of `F A B`, Lean would have to know what both `A` and `B` are.
For example, the following will *fail*:
```lean
example (n : ℕ) := F.f n
```
The reason is that when Lean sees `F.f n`, it knows that it should look for a typeclass instance of the form `F ℕ _`, but it has no way of knowing what the second parameter (`_`) should be.
We can fix the example above by telling Lean explicitly what to expect, using one of the following approaches:
```lean
example (n : ℕ) : ℕ := F.f n
example (n : ℕ) := (F.f n : ℕ) 
```

But niether is ideal.
It's certainly not ideal to always tell Lean the output type of `F.f n`, and we may want to use `F.f n` as a subterm of some more complicated expression.

The solution to this is to use an `outParam`. 
Replace the class above with this:
```lean
class F (A : Type) (B : outParam Type) where
  f : A → B
```
The `outParam` keyword only affects typeclass inference.
What it does is tell Lean to immediately infer the second parameter of `F` when it has found an instance.
So now when we write
```lean
example (n : ℕ) := F.f n
```
Lean will find the instance `F ℕ ℕ` and then immediately infer that the second parameter should also be `ℕ`.

The example above is quite contrived, but there are many situations where `outParam` is useful.
As an explicit example from `mathlib`, lets consider the `Valued` class which is used to define valued rings/fields.
```lean
class Valued (R : Type u) [Ring R] (Γ₀ : outParam (Type v)) [LinearOrderedCommGroupWithZero Γ₀] 
...
```
Note that `Γ₀`, which is the underlying type of the value group associated to the valuation in question, is an `outParam`.
In this way, we can write `Valued.v r` for `r : R` without any further hints, assuming there is some instance of the form `Valued R Γ₀` for some `Γ₀`.

Another example from `mathlib`:
```lean
class AddTorsor (G : outParam (Type*)) (P : Type*) [outParam <| AddGroup G]
...
```
This class is used to say that a type `P` is an additive torsor under an additive group `G`.
Note that `G` and its additive group structure are both `outParam`s here.
That means that if we fix `P`, and Lean is able to find an instance of `AddTorsor G P` for some `G` and some additive group structure on `G`, then Lean will immediately use that instance.
This means that we can write `p -ᵥ q` for `p q : P` without having to provide any additional information.
Similarly, we can write `g +ᵥ p` for `p : P` and `g : G` without having to provide any additional information.

Many other examples of uses of `outParam` can be found in `mathlib`.
We will discuss several more in the section about the various hierarchies in `mathlib`.