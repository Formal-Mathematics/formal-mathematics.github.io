---
title: Categories 
layout: default
nav_order: 13
--- 

# Category Theory

In Mathlib, categories are modeled using the typeclass system, as follows.
Given a type `C` which is meant to be considered as the "type of objects" of a category `C`, the class `CategoryTheory.Category C` includes the following data:
1. A type of morphisms `X ⟶ Y` for any `X Y : C`.
2. An identity morphism `𝟙 X : X ⟶ X` for any `X : C`.
3. A composition law `(X ⟶ Y) -> (Y ⟶ Z) -> (X ⟶ Z)` for objects `X Y Z : C`, denoted `f ≫ g` for `f : X ⟶ Y` and `g : Y ⟶ Z`.
4. The axioms of a category: associativity of composition and the left/right identity axioms for the identity morphisms.

In mathlib's category theory library, many objects are constructed using structures (this includes isomorphisms functors, natural transformations, adjunctions, etc.). 
In almost all cases, the proof obligations in such structures have a default value of `by aesop_cat`.
The tactic `aesop_cat`, which is built using the general purpose automation system called `aesop`, is a tactic which should be able to solve various "obvious" categorical assertions (checking certain diagrams commute, naturality assertions, etc.).
When `aesop_cat` succeeds in solving such a goal, the field itself can be omitted -- we'll see some examples below.

# Universes

It is often important to have precise control over universe parameters when doing category theory.
We can control the universe level of the type of objects in the usual way:
```lean
open CategoryTheory
universe u
variable (C : Type u) [Category C]
```
But to contol the universe level of the type of morphisms in a category instance, we would write
```lean
open CategoryTheory
universe v u
variable (C : Type u) [Category.{v} C]
```
This means that the type of objects has universe level `u`, while for `X Y : C`, the type of morphisms from `X` to `Y` has universe level `v`.

We also have some abbreviations: `SmallCategory C` means that the level of morphisms is the same as the level of `C`.
Namely, 
```lean
universe u
variable (C : Type u) [SmallCategory C]
```
is the same thing as 
```lean
universe u
variable (C : Type u) [Category.{u} C]
```

More common are *large categories*, written as `LargeCategory`, where
```lean
universe u
variable (C : Type (u + 1)) [LargeCategory C]
```
means
```lean
universe u
variable (C : Type (u + 1)) [Category.{u} C]
```
For example the category `Type u` of types is such a large category (note that `Type u : Type (u+1)`).
Similarly, the category `GroupCat.{u}` of groups whose underlying type `G` is a term of `Type u` is also a large category, with `GroupCat.{u} : Type (u+1)`.

# Examples

## The empty category
Here is the "ovbious" category instance on the empty type:
```lean
instance : SmallCategory Empty where
  Hom X := X.elim
  id X := X.elim
  comp {X} := X.elim
```
Note that the three additional fields 
```
  id_comp := _
  comp_id := _
  assoc := _
```
have been omitted since they can be solved with `aesop_cat`.
We could have alternatively written
```lean
instance : SmallCategory Empty where
  Hom X := X.elim
  id X := X.elim
  comp {X} := X.elim
  id_comp := by aesop_cat
  comp_id := by aesop_cat
  assoc := by aesop_cat
```

## `Type u`.
The category of types `Type u` is a category.
Its instance is in mathlib -- find by importing `Mathlib.CategoryTheory.Types`.
The type of morphisms `X ⟶ Y` in this case is just the type of usual (type-theoretic) functions `X -> Y`.

## Unit

Just as the empty category is the inital category (in a sense that can be made precise, see later), the terminal category is the category with one object and one morphism.
We can model it as a category instance on the `Unit` type, as follows:
```lean
instance : SmallCategory Unit where
  Hom _ _ := Unit
  id _ := .unit
  comp _ _ := .unit
```
Again, the proof obligations are "trivial" and can be solved automatically.

## Preorders
Given a preorder on `X`, the type `X` has a natural category structure where the morphisms encode the preorder.
We can model this in lean as follows:
```lean
instance (X : Type u) [Preorder X] : SmallCategory X where
  Hom a b := ULift (PLift (a ≤ b))
  id a := .up <| .up <| le_refl a
  comp {a b c} f g := .up <| .up <| le_trans f.down.down g.down.down
```
The functions `ULift` lifts the universe level of a type to a higher level, while `PLift` lifts a proposition to `Type`.
Together, these lift the proposition `a ≤ b` to a type in the same universe level as `X` (due to the fact that we're defining a "small category" instance).

This instance exists in mathlib in the import `Mathlib.CategoryTheory.Category.Preorder`.
This also has some convenience functions that lets us go back and forth between the inequality proposition and morphisms in the category instance, as illustrated in the following examples: 
```lean
variable (X : Type u) [Preorder X]
example (a b : X) (h : a ≤ b) : a ⟶ b := h.hom
example (a b : X) (h : a ≤ b) : h.hom = .up (.up h) := rfl

example (a b : X) (f : a ⟶ b) : a ≤ b := f.le
example (a b : X) (f : a ⟶ b) : f.le = f.down.down := rfl
```

# Functors

A functor `F : C ⟶ D` between categories `C` and `D` consists of the following data:
1. A function `F.obj : C -> D` which assigns to each object `X : C` an object `F.obj X : D`.
2. A function `F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y)` for any `X Y : C`.
this data must satisfy the following axioms:
3. `F.map (𝟙 X) = 𝟙 (F.obj X)` for any `X : C`.
4. `F.map (f ≫ g) = F.map f ≫ F.map g` for any `f : X ⟶ Y` and `g : Y ⟶ Z`.

In mathlib, functors are modeled as structures, as follows:
```lean
structure Functor (C : Type u) [Category C] (D : Type u') [Category D] where
  obj : C -> D
  map : {X Y : C} -> (X ⟶ Y) -> (obj X ⟶ obj Y)
  map_id : ∀ X : C, map (𝟙 X) = 𝟙 (obj X)
  map_comp : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), map (f ≫ g) = map f ≫ map g
```
The two fields `map_id` and `map_comp` are have a default value of `by aesop_cat`, so they can often be omitted when constructing a functor.
The notation for the type of functors from `C` to `D` is `C ⥤ D`.
And composition of two functors `F : C ⥤ D` and `G : D ⥤ E` is written `F ⋙ G`.
The identity functor on `C` is written `𝟭 C`.

## Examples

During lecture we saw several examples of functors. 
Please refer to the course repository for those examples.

# Natural Transofmrations

Given two functors `F G : C ⥤ D`, a natural transformation `α : F ⟶ G` consists of the following data:
1. For each object `X : C`, a morphism `α.app X : F.obj X ⟶ G.obj X`.
2. For each morphism `f : X ⟶ Y` in `C`, a naturality condition `α.naturality f : α.app X ≫ G.map f = F.map f ≫ α.app Y`.

We again model natural transformations in Lean using structures:
```lean
structure NatTrans {C : Type u} [Category C] {D : Type u'} [Category D] (F G : C ⥤ D) where
  app : ∀ X : C, F.obj X ⟶ G.obj X
  naturality : ∀ {X Y : C} (f : X ⟶ Y), app X ≫ G.map f = F.map f ≫ app Y
```
As before, `naturality` has a default value of `by aesop_cat`, so it can often be omitted when constructing a natural transformation.
The collection of all functors from `C` to `D` forms a category whose morphisms are natural transformations. 
Thus, we usually use the standard "hom" notation for the type of natural transofmrations from `F` to `G`.
That is, we write `F ⟶ G` for the type of natural transformations from `F` to `G` when `F` and `G` are functors.

# Adjunctions

In class we also talked about adjunctions between categories which consists of two functors `F : C ⥤ D` and `G : D ⥤ C` together natural transformations `η : 𝟭 C ⟶ F ⋙ G` and `ε : G ⋙ F ⟶ 𝟭 D` satisfying certain triangle conditions.
Mathematically speaking, an adjunction between `F` and `G` consists of equivalences of types:
```lean
(F X ⟶ Y) ≃ (X ⟶ G Y)
```
for all `X : C` and `Y : D` which is *natural* in `X` and `Y`.

In mathlib, adjunctions are defined slightly differently, but we can construct adjunctions from such equivalences using the constructor `CategoryTheory.Adjunction.mkOfHomEquiv`.
This is the most convenient way to construct adjunctions in practice.

In class we discussed an extended example showing that the forgetful functor from the category of monoids to the category of types is a right-adjoint whose left adjoint sends a type `X` to the free monoid on `X`.
Please refer to the course repository for details about this example.