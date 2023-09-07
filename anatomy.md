---
title: Anatomy
layout: default
nav_order: 5
---

# The Anatomy of a Lean Project

In this section, we will discuss the basic structure of a Lean project, and that of a Lean file.

## Lean Projects

A Lean project is a collection of Lean files which are all located in the same directory.
It must contain a few special files, including:

1. A `lakefile.lean` file.
2. A `lean-toolchain` file.

The `lakefile.lean` file is used to manage the Lean project, declaring dependencies, specifying how to build the project, etc.
The `lean-toolchain` file is used to specify the version of Lean that the project uses; this file is used by the `elan` tool to determine which version of Lean to use when building the project.
We will see explicit examples of such files during lecture.

To create a bare bones Lean project, you can run the following commands in a terminal:

```bash
lake new my_project
```

This will create a new Lean project called `my_project` in the current directory, with the necessary files (as well as some others).
In this case, this is a bare project meant to eventually compile a Lean executable.
To create a "library" project, you can use `lake new foo lib` and to create one which has `mathlib` as a dependency use `lake new foo math`.

## Mathlib

We should spend a few minutes talking about `mathlib`, which is the main library of formalized mathematics written in Lean.
It is maintained and developed by the Lean community, and has over 300 contributors and over 1 million lines of code.
It is still growing rapidly.
Here is a [link](https://github.com/leanprover-community/mathlib4) to the GitHub repository.

It is important to note that `mathlib` takes a very long time to compile, and that it must be compiled in order to be used (see the discussion about `import`s below). 
You definitely do not want to spend time compiling `mathlib` on your own machine.
Instead, you can download a precompiled cache for the version of `mathlib` that you are using.
This is done using `lake`, with the command `lake exe cache get`.
Again, we will see examples during lecture.
Note that after updating `mathlib` in a project, the cache must be updated as well.

## Lake

Let me also say a few additional words about `lake`, which is the build system used by Lean projects: `lake` = `lean` + `make`.
It is a tool which is used to manage Lean projects, and is used to compile Lean files.
It is also used to manage dependencies, and to download precompiled caches of Lean projects.

To build a project, you use `lake build` in the root directory of the project (the same location which contains the `lakefile.lean` of your project).
The lakefile can also specify lake executables which can be run with `lake exe ...` (`cache` is such an executable which is part of `mathlib` itself).
This tool has various other capabilities as well, and we will discuss them as necessary.

## Opening a project

When working with a Lean project in an editor (such as VScode) it is crucial that you open the project's root directory (the one containing the lakefile).
*DO NOT OPEN A SINGLE LEAN FILE ON ITS OWN*.

# The Anatomy of a Lean File

Let's take a closer look at what goes on in an individual lean file.

## Copyright and comments
At the top of the file we usually have a copyright notice as a multiline comment.
This looks like this:
```lean
/-
Copyright (c) 2023 Joe Shmoe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joe Shmoe, Jane Doe
-/
```
Note that multiline comments in Lean are delimited by `/-` and `-/`, while single line comments are delimited by `--`:
```lean
/-
A multiline comment.
Another line.
-/

-- A single line comment.
```
There are two other kinds of comment blocks which we will discuss later.

## Imports

Right after the copyright notice, we have a collection of import commands.
For example:

```lean
import Mathlib.Data.Nat.Basic
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Lean.Data.Json.Parser
```

These import commands are used to import Lean files from other Lean projects, or other files from within the current project.

After the imports, we have the main body of the file, which contains definitions, theorems, etc.

## Docstrings

As mentioned above, there are two additional kinds of comment blocks in Lean.
They are delimited by `/-!` and `-/`, and `/--` and `-/`.
The first one, `/-! ... -/` is commonly used for the module docstring.
This comment block accepts markdown, and is used to describe the contents of the file.
It usually comes right after the imports, and looks like this:

```lean
/-!

# Markdown Title

Markdown text.

## Subheading

Etc.

-/
```

The other kind of comment block, `/-- ... -/` is used for docstrings for definitions, theorems, etc.
For example:
```lean
/-- The meaning of life. -/
def theMeaningOfLife : Nat := 42
```

We use these two kinds of comment blocks to generate documentation for our code.
You can find the automatically generated documentation for `mathlib` at [this link](https://leanprover-community.github.io/mathlib4_docs/).