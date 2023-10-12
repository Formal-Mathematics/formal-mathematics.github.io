---
title: Algebra in Lean
layout: default
nav_order: 11
---

# Algebra in Lean

Algebraic structures in `mathlib` are organized in a *hierarchy* of typeclasses. 
In this section we will discuss the main classes in this hierarchy, their implementation, and how to use them.

## Generalities

First, let's discuss a few generalities about the algebraic hierarchy overall.
As we saw in the section about classes, typeclasses are organized in a hierarchy.
One can think of the typeclass hierarchy as a directed graph, where the vertices are *typeclasses* and the edges are *instances*. 
When we declare that a class extends another class, an instance is automatically added.

One issue that arises when organizing the hierarchy is the issue of *diamonds*.
This happens when there are two paths from a class `A` to a class `B` in this graph.
This is not a problem in itself, but it causes issues when the two paths result in instances that are not *definitionally equal*.
Since Lean has proof irrelevance, such problematic diamons only arise for classes that involve data.

We will see how this issue can be handeled using a technique called *forgetful inheritance*.
The key idea is that implications between classes should only ever *forget* data, and not add new data.
In some situations this means that the classes we consider will involve additional data that a priori does not seem necessary.

Let's look at a simplistic example of this issue and how it is resolved with forgetful inheritance.

```lean
import Mathlib.Init.ZeroOne
import Mathlib.Data.Prod.Basic

class Monoid (X : Type) extends Mul X, One X where
  assoc : ∀ (x y z : X), x * y * z = x * (y * z)
  mul_one : ∀ (x : X), x * 1 = x
  one_mul : ∀ (x : X), 1 * x = x

instance MonoidToPow {X : Type} [Monoid X] : Pow X Nat where
  pow := aux
    where aux
    | _, 0 => 1
    | x, n + 1 => x * aux x n

variable (X Y : Type) [Monoid X] [Monoid Y]

instance : Monoid (X × Y) where
  mul := fun (a,b) (c,d) => (a * c, b * d)
  one := (1,1)
  assoc := sorry
  mul_one := sorry
  one_mul := sorry


def foo : Pow (X × Y) Nat := inferInstance

def bar : Pow (X × Y) Nat where
  pow := fun (x,y) n => {
    fst := 
      letI : Pow X Nat := MonoidToPow
      x^n
    snd := 
      letI : Pow Y Nat := MonoidToPow
      y^n
  }

attribute [ext] Pow

example : foo = bar := by
  ext A B _ _ ⟨x,y⟩ n
  · show ((x,y)^n).fst = x^n
    sorry
  · show ((x,y)^n).snd = y^n
    sorry
```

In this example, we define a class representing monoids in the usual way: a type with an associative multiplication and a two-sided unit.
Given a monoid `M`, we can define the power operation `M → ℕ → M` in the usual way by recursion on the second variable.
This is done in the instance `MonoidToPow`.
Now given two monoids `X` and `Y`, we can define a monoid structure on `X × Y` in the obvious way.
But now we have two ways to construct a `Pow (X × Y) Nat` instance: we can either use the instance `MonoidToPow` on `X × Y`, or we can define it directly by exponentiating each component.
The two are *not* definitionally equal, and so we would have a diamond if `bar` was declared as an instance.

The way to resolve this is to bundle the data of `Pow` as part of the monoid class itself.
```lean
import Mathlib.Init.ZeroOne
import Mathlib.Data.Prod.Basic

class Monoid (X : Type) extends Mul X, One X, Pow X Nat where
  assoc : ∀ (x y z : X), x * y * z = x * (y * z)
  mul_one : ∀ (x : X), x * 1 = x
  one_mul : ∀ (x : X), 1 * x = x
  pow_zero : ∀ (x : X), x^0 = 1
  pow_succ : ∀ (x : X) (n : Nat), x^(n+1) = x^n * x
```

Now, the `MonnoidToPow` instance is obtained simply by "forgetting" everything except for the `Pow` data.
And since we have declared `Monoid` to extend `Pow`, the relevant instance is registered automatically.
We can now declare the `Monoid (X × Y)` instance without any issues, by using the concrete definition of `pow` we wanted from `bar` above:
```lean
variable (X Y : Type) [Monoid X] [Monoid Y]

instance : Monoid (X × Y) where
  mul := fun (a,b) (c,d) => (a * c, b * d)
  one := (1,1)
  pow := fun (x,y) n => (x^n, y^n)
  assoc := sorry
  mul_one := sorry
  one_mul := sorry
  pow_zero := sorry
  pow_succ := sorry
```

And finally, we can see that the analogues of `foo` and `bar` will not pose an issue since they are equal by definition:
```lean
def foo : Pow (X × Y) Nat := inferInstance

def bar : Pow (X × Y) Nat where
  pow := fun (x,y) n => (x^n, y^n)

example : foo = bar := rfl
```
## Subobjects, Morphisms, Quotients, Universal properties.

When working with algebraic objects, there are a few things we might want to do.
At an elementary level, we may want to actually do *algebra* with our algebraic objects, referring to manipulating equations involving elements of our algebraic structures.

At a higher level we may want to *compare* algebraic objects.
For example, we may want to know if two groups are *isomorphic*, and to talk about isomorphisms we need to talk about *morphisms*.

We may also want to talk about *subobjects* and *quotients* of algebraic objects, and study the collection of all such subobjects resp. quotients as an object in its own right.
We may also want to compare subobjects and quotients, and talk about morphisms between them, compare subobjects with their underlying subsets, etc.

Finally, we may want to construct new algebraic objects from old ones, for example by taking the product of two groups, or the direct sum of two modules.
These objects satisfy *universal properties* that pin them down uniquely up to isomorphism.

## Calculations

Let's now discuss how to do calculations with algebraic objects.
We'll use groups as an example, but the same techniques apply to other algebraic objects as well.

For example, we may want to solve for `x` in the equation `a * x = b` where `a x b : G` and `G` is a group.
We need to formulate this as a "theorem" and so we need to figure out what `x` should be ahead of time.
We can then formulate a theorem in lean and prove it.
Of course, in this case we know that `x = a⁻¹ * b`, so we can formulate the theorem as follows:
```lean
import Mathlib.Algebra.Group.Basic

variable (G : Type) [Group G]

example (a b x : G) (h : a * x = b) : x = a⁻¹ * b := by
  sorry
```
We can prove this in a few ways.
First, we can multiply both sides of the equation `h` by `a⁻¹` on the left.
This can be done with `congr_arg`, or with the `apply_fun` tactic.
This gives us a hypothesis of the form `a⁻¹ * (a * x) = a⁻¹ * b`, which we can simplify in one of various ways to reduce to our goal.
Alternatively, we can rewrite the goal using `h` (backwards) and simplify the goal directly.
Both approaches will be discussed in more detail during lecture.

To illustrate another example of a calculation in lean, let's consider the following example.
```lean
example (a b c d e f : G) (h1 : a * b = c * d) (h2 : c * e = f) :
  sorry
```

We will show how to prove this in class using the `conv` and/or `calc` environments.

For certain kinds of algebraic objects we have specialized tactics that can be used to do such calculations.
The main tactics here are:

- `linarith` for linear (in)equalities
- `group` for groups
- `abel` for abelian groups
- `ring` for commutative rings
- `field_simp` for fields

I'll give a few examples which illustrate how to use these tactics during lecture.
Here are a few additional, more powerful tactics which you may want to explore:

- `nlinarith` for some nonlinear (in)equalities
- `polyrith` for proving some polynomial equalities
- `gcongr` for "generalized congruence"
- `congrm` a congruence-like tactic for proving certain relations

Recall that you can use the `#help tactic foo` command to get the documentation on a tactic `foo`.

In genreal, we can also train lean's simplifier and use `simp` to effectively simplify expressions in algebraic objects.
I'll illustrate how to do this in class by implementing a variant of the `group` tactic using `simp`.