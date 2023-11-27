---
title: Quotients 
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