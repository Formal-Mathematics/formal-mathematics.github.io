---
title: Introduction
layout: default
nav_order: 3
---

# Introduction

Welcome! 
This course is an introduction to *formal mathematics* using the [Lean4](https://leanprover.github.io/) interactive theorem prover (ITP).

## What is formal mathematics?

Formal mathematics is the practice of writing mathematics in a *formal language*, as opposed to a *natural language*.
This may or may not be done using the help of a computer.
However, by using a computer, we can rely on the computer to check the validity of our mathematics and ensure consistency.

## Why formalize mathematics?

There are various reasons to formalize mathematics using an ITP. 
As mentioned above, formalizing mathematics allows us to rely on the computer to check the validity of our mathematics and ensure consistency.
This can help facilitate large collaborations where each contributor can be sure that their contributions are correct and consistent with the project as a whole.

The formalization process encourages the use of *abstractions* which has numerous benefits for mathematics itself.
In fact, coming up with useful abstractions can be seen as one of the main driving forces of progress in mathematics.

There are various other reasons to formalize mathematics, which have both research and pedagogical benefits.
We will not spend too much time discussing these dhere, but we refer the reader to [this paper](https://www.imo.universite-paris-saclay.fr/~patrick.massot/files/exposition/why_formalize.pdf) by P. Massot for a detailed discussion.

## What is Lean4?

Lean4 is both a general purpose functional programming language with dependent types, as well as an ITP.
It is being actively developed by Leonardo de Moura and Sebastian Ullrich, originally as part of Microsoft Research. 
Lean4 is now backed by the [Lean FRO](https://lean-fro.org/) and supported by a large [community](https://leanprover-community.github.io/) of mathematicians and computer scientists.

Lean4 has a sophisticated metaprogramming framework which allows users to extend the language with new features.
It also allows users to write *tactics* which are used to help with and even automate some parts of the theorem proving process.

## What is Mathlib4?

[Mathlib4](https://github.com/leanprover-community/mathlib4) is the main library of formalized mathematics written in Lean4.
It has over 300 contributors, over 1 million lines of code, and is still growing rapidly.
Mathlib4 is maintained and developed by the Lean community.

# Course Structure

This course has lectures, homework assignments and a final project. 

## Lectures

Lectures will take place on Tuesday and Thursday, 11am to 12:20pm Edmonton time.
All lectures will be conducted using zoom.
While this is an *online* course, there is a room reserved for the course which students may use in order to attend lectures while on campus.
I will also be physically present and lecture from this room, at least once a week.

## Assignments

Homework assignments will be assigned periodically throughout the term, using github classroom.
All assignments will require writing Lean4 code and will be *automatically graded*.
While you are working on a homework assignment, you can push to github periodically to check whether your solution is valid.
Note that automaticaly graded assignments will be graded only for *successful completion.*

The assignments will not have any predefined deadline, but they must all be completed by 24h59 on the last day of classes for the term, which is 2023-12-08.
Even though there are no deadlines throughout the term, you should do your best to complete assignments in a timely manner as they will get progressively harder and build on previous knowledge as the term progresses.
Please do not wait until the last minute to start working on the assignments!

## Final Project

In addition to the assignments, students will submit a final project at the end of the term.
This project should be a formalization of a piece of mathematics that interests the student. 
You should start thinking about potential topics for the project as early as possible.
Details about the project will be discussed in class.

## Grade distrubtion

The final grade for this course will be based on the homework assignments (50%) and the final project (50%).

# Getting Started

Please refer to the [setup](setup) page for help in getting set up with Lean4 and the related tooling.