---
title: Basics
layout: default
nav_order: 4
---

# Types

Lean4 is based on *dependent type theory*, as opposed to *set theory*, which is usually used as the foundation of mathematics.
I won't go into all of the technical details of dependent type theory here, but I will try to give a brief overview of the main ideas.
Also, I will use the words "dependent type theory" to refer to "Lean4's dependent type theory".
This is an egregious abuse of terminology, but since we're only going to use Lean4 in this course, it shouldn't cause any confusion.

Here is the gist: In dependent type theory, everything is a *term*, and every term has a *type*.
We write `t : T` to indicate that `t` is a term of type `T`.

Examples of types include the natural numbers $$\mathbb{N}$$, the rational numbers $$\mathbb{Q}$$, the type $$\mathbb{N} \to \mathbb{Q}$$ of functions from $$\mathbb{N}$$ to $$\mathbb{Q}$$, the type $$\mathbb{N} \times \mathbb{Q}$$ of pairs of natural numbers and rational numbers, etc.
For example, we have 

1. $$0 : \mathbb{N}$$, $$1/5 : \mathbb{N}$$, $$\pi : \mathbb{R}$$, etc.
3. $$n \mapsto n^2 : \mathbb{N} \to \mathbb{N}$$, $$n \mapsto 1/n : \mathbb{N} \to \mathbb{Q}$$, $$n \mapsto \sqrt{n} : \mathbb{N} \to \mathbb{R}$$, etc.
4. $$(1, 2) : \mathbb{N} \times \mathbb{N}$$, $$(1, 1/2) : \mathbb{N} \times \mathbb{Q}$$, etc.

In Lean4, we have a countable hierarchy of universes for types, denoted `Type 0`, `Type 1`, `Type 2`, etc., satisfying `Type n : Type (n+1)`.
Universes of this sort are introduced in order to avoid inconsistency arising essentially from Russell's paradox.
In practice, most types `T` that we will encounter will be in universe level `0`, meaning `T : Type 0`.
Since it's most common, there is an abbreviation of the notation `Type === Type 0`.
For example, we have `Nat : Type 0`, `Int : Type 0`, `Nat -> Rat : Type 0`, etc.
You can think of the types `T` in `Type 0` as analogous to "sets" in usual set theory, while types in `Type 1` are analogous to "classes".

We will see various ways of constructing types soon, but I'll mention a few here: 
1. Products: if `T : Type u` and `U : Type v`, then `T × U : Type (max u v)` is the type of pairs `(t, u)` where `t : T` and `u : U`. 
2. Disjoint unions: if `T : Type u` and `U : Type v`, then `T ⊕ U : Type (max u v)` is the type of pairs `(t, u)` where `t : T` and `u : U`.
3. Functions: if `T : Type u` and `U : Type v`, then `T -> U` is the type of functions from `T` to `U`.
4. Dependent functions: if `T : Type u` and `U : T -> Type v`, then `(t : T) -> U t` is the type of functions which send `t : T` to a term of `U t`.
5. Sigma types: if `T : Type u` and `U : T -> Type v`, then `Σ t : T, U t` is the type of pairs `(t, u)` where `t : T` and `u : U t`.

# Propositions

Lean4 also has the notion of a `Sort`, which is also organized into a hierarchy `Sort 0`, `Sort 1`, `Sort 2`, etc., satisfying `Sort n : Sort (n+1)`.
In fact, `Type u` is *defined* as `Sort (u+1)`, so, for example, `Type === Type 0 === Sort 1`. 
The sort `Sort 0` is special and is denoted by `Prop`; this is the type of *propositions*.

We write `p : Prop` to indicate that `p` is a proposition.
Just like we can talk about `t : T` for `T : Type`, we can talk about `h : P` for `P : Prop`. 
The key distinction is that for `P : Prop`, any two `h1, h2 : P` are *equal*.
This is a property of Lean4's dependent type theory called *proof irrelevance*.

The logical foundations of Lean4 are thus based on the *Curry-Howard correspondence*, which says that propositions should be considered as types and proofs of propositions should be considered as terms of the corresponding type.
In other words, if `P : Prop`, then you should think about `h : P` as a *proof* of `P`.
In a naive sense, if a proposition has a proof, then we say that it is *true*, and if it does not have a proof, then we say that it is *false*.

With the Curry-Howard correspondence in mind, we can view the usual logical operations in terms of type theory, as follows:

1. Conjunction: `P ∧ Q` is the type of pairs `(p, q)` where `p : P` and `q : Q`, i.e. this is just the type-theoretic *product*.
2. Disjunction: `P ∨ Q` is the type of pairs `(b, p)` where `b : Bool` and `p : if b then P else Q`, i.e. this is just the type-theoretic *disjoint union*. 
3. Implication: `P → Q` is the type of functions `f : P → Q`, i.e. this is just the type-theoretic *function type*.
4. Universal quantification: `∀ x : T, P x` is the type of functions `f : (x : T) → P x`, i.e. this is just the type-theoretic *dependent function type*.
5. Existential quantification: `∃ x : T, P x` is the type of pairs `(t, p)` where `t : T` and `p : P t`, i.e. this is just the type-theoretic *sigma type*.
6. Negation: `¬ P` is defined as `P → False`, where `False` is the proposition with no proofs. 

In item 6 we mentioned the proposition `False`, which is false by construction.
There is also a proposition `True` which is true by construction.
We will come back to the actual definitions of `True` and `False` later on.

# Functions

Functions in dependent type theory include the usual functions from set theory, such as $$n \mapsto n^2 : \mathbb{N} \to \mathbb{N}$$.
But since everything is a term, we can also have functions which take terms of a type as inputs and return types as outputs.
This is where the word *dependent* in *dependent type theory* comes from.

We have already seen an example of this in the notion of a dependent function and the notion of a sigma type above.
Let me expand on those examples a bit.

Fix a type `T : Type u`, and consider a *function* `U : T -> Type v`.
You can think of `U` as a *family of types* indexed by `T`.
Namely, given any `t : T`, we have a type `U t : Type v`.

We can then consider the sigma type associated to this type family.
Explicitly, it is the type `Σ t : T, U t`, which is the type of pairs `(t, u)` where `t : T` and `u : U t`.
Mathematically speaking, you can think of this as the disjoint union $$\bigcoprod_{t : T} U t$$ of all the types `U t` for `t : T`.

Note that there is a well-defined map `p : Σ t : T, U t -> T` sending `(t, u)` to `t`.
Sections of this map are precisely the dependent functions `f : (t : T) -> U t`.
Indeed, a section `s` is a function `s : T -> Σ t : T, U t` such that `p (s t) = t` for all `t : T`.
In other words, `s t = (t,u)` for some `u : U t`.
We can thus think of `s` as a rule which sends `t : T` to a term `s t : U t`.
Slogan: Sigma types are disjoint unions of families of types, and sections of the projection map are dependent functions.

In Lean4, the function arrow `->` is right associative, so `T -> U -> V` is the same as `T -> (U -> V)`.
This is actually quite convenient.
Indeed, suppose that `f : T -> U -> V`, `t : T` and `u : U` are given. 
Then `f t` is a function `U -> V`, and `f t u` is a term of `V`.
We can thus think of `f` as a function taking two inputs `t : T` and `u : U` and returning a term `f t u : V`.

This is related to the notion of *currying* in functional programming.
There is a one-to-one correspondence between the type `T -> U -> V` and the type `(T × U) -> V`.

# Predicates and Relations

Now that we are equipped with the knowledge above, we can think about how to formulate the notion of a predicate and a relation in this language.
A predicate on a type `T` is just a function `P : T -> Prop`.
This means that for every `t : T`, we obtain a proposition `P t : Prop`, which may or may not be true.
In other words, such a predicate defines a *subset* of `T`, consisting of those `t : T` for which `P t` is true.

We can play a similar game to model relations.
A relation on a type `T` is just a function `R : T -> T -> Prop`.
Given `t1, t2 : T`, we obtain a proposition `R t1 t2 : Prop`, which may or may not be true.
If `R t1 t2` is true, then we say that `t1` is *related* to `t2` by `R`, and say that `t1` is *unrelated* to `t2` by `R` if `R t1 t2` is false.