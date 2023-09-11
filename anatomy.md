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

# What happens in a Lean File?

Let's take a closer look at what happens in an actual lean file.
When we open a lean file in an editor like VSCode, a language server is spawned which lets us interact with the code in the given file in real time (this assumes that the Lean4 package has been properly installed).
At the top (after a copyright header) we have the imports of the file.
The server then uses these imports to obtain an `Environment`, which contains all the information (definitions, lemmas, etc.) from the imports.

We can interact with this environment explicitly using metaprogramming. 
I will demonstrate this in class.

After the import portion of the file, we start writing commands.
At the end of the day, these commands all define terms which have some names, and which are added to the environment in question.
After each command, the environment could be different!

But what actually happens when Lean (or the Lean Language Server) processes a file?
Well, first it looks at the imports and obtains an initial environment (along with messages, etc.).
It does this by first parsing the import lines, and using a precompiled version of the files in question.
If there is no precompiled version, then it compiles the imports (which amounts to recursively doing what I describe below).

Next, it parses the actual code into `Syntax` objects.
Here `Syntax` is a built-in type in Lean that we can work with as a first-class citizen in the language.
This is a formal representation of the code itself that Lean can work with.

After that, there is a macro expansion step.
In Lean4, we can write macros that convert `Syntax` into `Syntax`.
Custom notation is an example of a macro.

After that comes the main step, which is called "elaboration."
In this step, Lean tried to fill in missing information, such as implicit variables, typeclass parameters, etc.
It also does some "unification," checking that certain things are definitionally equal.
This step also converts tactics into actual terms -- you can think of tactics as scripts that instruct Lean in constructing actual terms.
It also tries to detect and report all possible errors. 
At the end of this step, the `Syntax` objects mentioned above are converted into "fully elaborated terms" which are elements of an expression type called `Expr`. 
Again, this is a built-in Lean type that can be handled as a first-class citizen.

From here, the fully elaborated terms of `Expr` are passed to the kernel of the language for typechecking.
The kernel is actually responsible for checking that definitions and proofs are correct.

The Lean kernel is purposefully kept as small as possible, so that it is easier to verify the correctness of the program.
On the other hand, the elaboration process is much more complex, and may have bugs. 
It does happen (infrequently) that a fully elaborated term is passed to the kernel, only to be rejected. 
This indicates that there is a bug in some elaborator which should be fixed. 

We wont't have to worry about all these internals for this course.
However, if you plan to do any metaprogramming in Lean (and I recommend that you do), such as writing custom tactics, etc., then understanding the internals is quite important.



