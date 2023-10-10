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
TODO
```

## Subobjects, Morphisms, Quotients, Universal properties.

When working with algebraic objects, there are a few things we might want to do.
At an elementary level, we may want to actually do *algebra* with our algebraic objects.
For example, we may want to solve for `x` in the equation `a * x = b` where `a x b : G` and `G` is a group.

At a higher level we may want to *compare* algebraic objects.
For example, we may want to know if two groups are *isomorphic*, and to talk about isomorphisms we need to talk about *morphisms*.

We may also want to talk about *subobjects* and *quotients* of algebraic objects, and study the collection of all such subobjects resp. quotients as an object in its own right.
We may also want to compare subobjects and quotients, and talk about morphisms between them, compare subobjects with their underlying subsets, etc.

Finally, we may want to construct new algebraic objects from old ones, for example by taking the product of two groups, or the direct sum of two modules.
These objects satisfy *universal properties* that pin them down uniquely up to isomorphism.

