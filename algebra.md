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

## Morphisms and Isomorphisms

We have already discussed briefly how morphisms work in `mathlib`.
Let's do a quick recap.
First, just like the algebraic objects themselves, morphisms are organized in a hierarchy of typeclasses.
For example, morphisms of monoids are defined as a structure extending `MulHom` and `OneHom`, and are endowed with an instance of the type class `MonoidHomClass`.
Similarly, morphisms of rings are again a structure called `RingHom` which is endowed with an instance of `RingHomClass`, while `RingHomClass` extends `MonoidHomClass`.
The `MonoidHomClass` encapsulates the API for monoid morphisms, which means that we can use this API for both `RingHom` and `MonoidHom` (and indeed any type that has an instance of `MonoidHomClass`).

In practice, it's possible to *use* morphisms between algebraic objects without worrying about the details of the morphism typeclass hierarchy.
One only needs to think about this if one wants to *define* a type of morphism between algebraic objects.
In this case, one needs to decide which typeclass to extend, and which typeclass to use for the API, possibly even defining new typeclasses if necessary.

For now I'll focus just on the types of morphisms and isomorphisms themselves.
Let's focus on the case of groups.
A group is a monoid, and a morphism of groups is just a morphism of monoids.
Given two monoids `M` and `N`, a morphism of monoids is a function `M → N` which preserves the multiplication and the unit.
In mathlib, this is essentially defined as a structure:

```lean
structure MonoidHom (M N : Type) [Mul M] [Mul N] [One M] [One N] where
  toFun : M → N
  map_mul : ∀ (x y : M), toFun (x * y) = toFun x * toFun y
  map_one : toFun 1 = 1
```
If we look at the actual definition from mathlib, we see the following:
```lean
structure MonoidHom (M : Type*) (N : Type*) [MulOneClass M] [MulOneClass N] extends
  OneHom M N, M →ₙ* N
```
Namely, we already have a structure `OneHom` for functions which preserve the unit.
We also have a structure `MulHom` with notation `M →ₙ* N` for functions which preserve multiplication.

We provide instances for `MonoidHom` of the class `MonoidHomClass`, which implies `FunLike`.
The `MonoidHomClass` is a class that encapsulates the API for monoid morphisms, including lemmas such as `map_mul` and `map_one`.
The `FunLike` class is a class that encapsulates the API for types which can be considered as functions in a faithful way, introducing the relevant extensionality lemmas, etc.
This particular class also provides a `CoeFun` instance, which will allow us to write `f m` when `f` is a morphism from `M` to `N` and `m : M`.
The type `MonoidHom M N` has the notation `M →* N`.

Now what about isomorphisms?
An isomorphism of monoids is a morphism which has an inverse.
Well, it turns out that it suffices to just check that the map in the forward direction preserves multiplication.
If `f` is a bijection between monoids which preserves multiplication then the fact that `f 1 * n = f 1 * f (f⁻¹ n) = f(1 * f⁻¹ n) = f(f⁻¹ n) = n` along with the injectivity of `f`, ensures that `f 1 = 1`.
Because of this, an isomorphism between monoids is defined, in mathlib, as follows:
```lean
structure MulEquiv (M N : Type*) [Mul M] [Mul N] extends M ≃ N, M →ₙ* N
```
In other words, it's an equivalence between the underlying types whose underlying function preserves multiplication.
The type of such multiplicative equivalences is denoted with the notation `M ≃* N`.
This structure is endowed with an instance of `MulEquivClass`, which extends `MonoidHomClass` and `EquivClass`, allowing us to consider such equivalences as morphisms and as equivalences on the type level.

If `f : M ≃* N` is a multiplicative equivalence, then `f.symm` is the inverse of `f` in the usual sense.
This will be a term of `N ≃* M`.
To compose such equivalences, we can use `f.trans g`.
To obtain the identity as an equvialence, we can use `MulEquiv.refl`.

## Subobjects

Let's now focus on the notion of subobjects, again taking groups as our primary example.
A subgroup of a group `G` is defined in mathlib essentially as follows:
```lean
structure Subgroup (G : Type*) [Group G] where
  carrier : Set G
  mul_mem : ∀ a b, a ∈ carrier → b ∈ carrier → a * b ∈ carrier
  one_mem : 1 ∈ carrier
  inv_mem : ∀ a, a ∈ carrier → a⁻¹ ∈ carrier 
```
Namely, a subgroup of `G` consists of a subset `carrier : Set G` of `G` which is closed under multiplication, contains the unit, and is closed under inverses.
In mathlib, this construction is again part of a hierarchy, and is thus rather defined as follows:
```lean
structure Subgroup (G : Type*) [Group G] extends Submonoid G where
  /-- `G` is closed under inverses -/
  inv_mem' {x} : x ∈ carrier → x⁻¹ ∈ carrier
```
I.e. a subgropu is a submonoid which is closed under multiplication.

Just like in the case of morphisms where we have classes such as `MonoiHomClass` and `FunLike`, for subobjects, we have analogous classes such as `SubgroupClass` and `SetLike`.
The `SubgroupClass` class extends `SubmonoidClass` which provides the API for being closed under multiplication and containing the unit, while `SubgroupClass` provides the API for being closed under inverses.
The class `SetLike` provides a way to think about terms of `Subgroup G` and similar structures as subsets of `G`, and provides the API for this.
For example, an instance of this class allows us to write 
```lean
example (G : Type*) [Group G] (H : Subgroup G) (g : G) : Prop := g ∈ H
```
Recall that subsets as defined as predicates, and that `g ∈ H` is notation for `H g`.

The `SetLike` class also provides an instance of `CoeSort`, allowing us to consider terms of types with an instance of this class as types themselves.
For example:
```lean
example (G : Type*) [Group G] (H : Subgroup G) (g : G) : Type _ := H
```
In general, if `H : Set G` for some type `G`, we can consider the *subtype* associated to `H`, which is defined essentially as a structure with two fields:
```lean
structure Subtype {G : Type*} (H : Set G) where
  val : G
  cond : val ∈ H
```

## Complete lattices and the order hierarchy

The type of subobjects of an algebraic object is naturally a partial order, where the inequality is given by the associated inequality for the underlying sets.
In fact, this is not just a partial order, but rather a *complete lattice*, which is a partial order where infima and suprema exist for any subset.
This brings us into the so-called *order hierarchy* in mathlib, which is a hierarchy of typeclasses for partial orders, lattices, etc.
Please feel free to dig around looking at the various classes in this hierarchy, but we will only discuss these as necessary in our class.

For now, let's look at the definition of a complete lattice:
```lean
/-- A complete lattice is a bounded lattice which has suprema and infima for every subset. -/
class CompleteLattice (α : Type*) extends Lattice α, CompleteSemilatticeSup α,
  CompleteSemilatticeInf α, Top α, Bot α where
  /-- Any element is less than the top one. -/
  le_top : ∀ x : α, x ≤ ⊤
  /-- Any element is more than the bottom one. -/
  bot_le : ∀ x : α, ⊥ ≤ x
```
This extends two classes: `Lattice` and `CompleteSemilatticeSup`, which are defined as 
```lean
class CompleteSemilatticeSup (α : Type*) extends PartialOrder α, SupSet α where
  /-- Any element of a set is less than the set supremum. -/
  le_sSup : ∀ s, ∀ a ∈ s, a ≤ sSup s
  /-- Any upper bound is more than the set supremum. -/
  sSup_le : ∀ s a, (∀ b ∈ s, b ≤ a) → sSup s ≤ a

class Lattice (α : Type u) extends SemilatticeSup α, SemilatticeInf α
```
Digging further, the classes appearing above are defined as
```lean
class PartialOrder (α : Type u) extends Preorder α where
  le_antisymm : ∀ a b : α, a ≤ b → b ≤ a → a = b

class SupSet (α : Type*) where
  sSup : Set α → α

class SemilatticeSup (α : Type u) extends Sup α, PartialOrder α where
  /-- The supremum is an upper bound on the first argument -/
  le_sup_left : ∀ a b : α, a ≤ a ⊔ b
  /-- The supremum is an upper bound on the second argument -/
  le_sup_right : ∀ a b : α, b ≤ a ⊔ b
  /-- The supremum is the *least* upper bound -/
  sup_le : ∀ a b c : α, a ≤ c → b ≤ c → a ⊔ b ≤ c

class SemilatticeInf (α : Type u) extends Inf α, PartialOrder α where
  /-- The infimum is a lower bound on the first argument -/
  inf_le_left : ∀ a b : α, a ⊓ b ≤ a
  /-- The infimum is a lower bound on the second argument -/
  inf_le_right : ∀ a b : α, a ⊓ b ≤ b
  /-- The infimum is the *greatest* lower bound -/
  le_inf : ∀ a b c : α, a ≤ b → a ≤ c → a ≤ b ⊓ c
```
and digging further:
```lean
class Inf (α : Type u) where
  /-- Greatest lower bound (`\glb` notation) -/
  inf : α → α → α

class Sup (α : Type u) where
  /-- Least upper bound (`\lub` notation) -/
  sup : α → α → α

class Preorder (α : Type u) extends LE α, LT α where
  le_refl : ∀ a : α, a ≤ a
  le_trans : ∀ a b c : α, a ≤ b → b ≤ c → a ≤ c
  lt := fun a b => a ≤ b ∧ ¬b ≤ a
  lt_iff_le_not_le : ∀ a b : α, a < b ↔ a ≤ b ∧ ¬b ≤ a := by intros; rfl

class LE (α : Type u) where
  /-- The less-equal relation: `x ≤ y` -/
  le : α → α → Prop

class LT (α : Type u) where
  /-- The less-than relation: `x < y` -/
  lt : α → α → Prop
```

## The complete lattice structure on subobjects

Let's go back to the algebraic objects and their subobjects, and look at the complete lattice structure on the type of subobjects, again focusing on subgroups.
Here is how this instance is defined in mathlib:
```lean
instance : CompleteLattice (Subgroup G) :=
  { completeLatticeOfInf (Subgroup G) fun _s =>
      IsGLB.of_image SetLike.coe_subset_coe isGLB_biInf with
    bot := ⊥
    bot_le := fun S _x hx => (mem_bot.1 hx).symm ▸ S.one_mem
    top := ⊤
    le_top := fun _S x _hx => mem_top x
    inf := (· ⊓ ·)
    le_inf := fun _a _b _c ha hb _x hx => ⟨ha hx, hb hx⟩
    inf_le_left := fun _a _b _x => And.left
    inf_le_right := fun _a _b _x => And.right }
```
Here we use a trick: `completeLatticeOfInf`. 
This construction has the following definition:
```lean
def completeLatticeOfInf (α : Type*) [H1 : PartialOrder α] [H2 : InfSet α]
    (isGLB_sInf : ∀ s : Set α, IsGLB s (sInf s)) : CompleteLattice α :=
  { H1, H2 with
    bot := sInf univ
    bot_le := fun x => (isGLB_sInf univ).1 trivial
    top := sInf ∅
    le_top := fun a => (isGLB_sInf ∅).2 <| by simp
    sup := fun a b => sInf { x : α | a ≤ x ∧ b ≤ x }
    inf := fun a b => sInf {a, b}
    le_inf := fun a b c hab hac => by
      apply (isGLB_sInf _).2
      simp [*]
    inf_le_right := fun a b => (isGLB_sInf _).1 <| mem_insert_of_mem _ <| mem_singleton _
    inf_le_left := fun a b => (isGLB_sInf _).1 <| mem_insert _ _
    sup_le := fun a b c hac hbc => (isGLB_sInf _).1 <| by simp [*]
    le_sup_left := fun a b => (isGLB_sInf _).2 fun x => And.left
    le_sup_right := fun a b => (isGLB_sInf _).2 fun x => And.right
    le_sInf := fun s a ha => (isGLB_sInf s).2 ha
    sInf_le := fun s a ha => (isGLB_sInf s).1 ha
    sSup := fun s => sInf (upperBounds s)
    le_sSup := fun s a ha => (isGLB_sInf (upperBounds s)).2 fun b hb => hb ha
    sSup_le := fun s a ha => (isGLB_sInf (upperBounds s)).1 ha }
```
This is essentialy a way to construct a complete lattice structure on a type given just the data of infimums satisfying certain axioms.
The *supremum* is then defined in terms of the infimum by saying that the supremum of a set `S` is the infimum of the set of upper bounds of `S`.
In the case of subgroups, this is saying that we *define* the supremum of a collection of subgroups by taking the infimum (i.e. the intersection) of the family of all subgroups which contain all the subgroups in the collection.