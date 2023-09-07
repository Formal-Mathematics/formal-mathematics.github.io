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

