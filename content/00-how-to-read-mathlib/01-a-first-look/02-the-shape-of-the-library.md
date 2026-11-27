---
title: The shape of the library
kind: guide
modules: []
explains: {}
families: []
requires: []
reads_with: ["MIL Ch. 1", "MSG"]
lean:
  - MathlibHandbook/V00/C01/Examples.lean
  - MathlibHandbook/V00/C01/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The shape of the library

### Overview

A reader who opens Mathlib for the first time sees about 8,700 files in a tree of folders. This section gives the map of that tree. It explains what a module is, how a file starts, and the kinds of declarations that a file contains: definitions, theorems, structures, classes and instances. It then reads one definition of Mathlib in full, the definition of a prime number, and proves on paper that it agrees with the definition of a textbook. After this section the reader can open a file of Mathlib, find its main statements, and tell a definition from a theorem.

### Folders and modules

Each file of Mathlib is a *module*. The name of the module is the path of the file, with dots in place of the slashes and without the extension `.lean`. So the file `Mathlib/Data/Nat/Prime/Defs.lean` is the module `Mathlib.Data.Nat.Prime.Defs`. The Mathlib box of each section of the handbook gives the module of the declaration in its first line.

The folders below `Mathlib/` follow the areas of mathematics. The main ones are these.

| Folder | Content |
|---|---|
| `Logic`, `Order`, `Data` | logic, orders and lattices, the basic types: `ℕ`, `ℤ`, `ℚ`, lists, finite sets |
| `Algebra`, `GroupTheory`, `RingTheory`, `FieldTheory`, `LinearAlgebra` | algebraic structures and their theory |
| `Topology`, `Analysis`, `MeasureTheory`, `Probability` | topology, analysis, measure and integration, probability |
| `NumberTheory`, `Combinatorics`, `SetTheory` | number theory, combinatorics, ordinals and cardinals |
| `AlgebraicGeometry`, `AlgebraicTopology`, `CategoryTheory`, `Geometry` | schemes, homotopy, categories, manifolds |
| `Tactic` | the tactics of Mathlib, which are Lean programs |

Inside a folder, the file names follow a habit. A file `Defs.lean` has the definitions of an area with the first few lemmas. A file `Basic.lean` has the basic theory. Other files have a name for their topic: `Infinite.lean` in `Mathlib/Data/Nat/Prime/` has the theorem of Euclid on the infinitude of the primes. The habit keeps the first files small, so that a file which needs only the definition of a prime imports little.

A module can use a declaration of another module only after it imports that module. The first lines of a file list the imports. A file of the user usually starts with `import Mathlib`, which imports all of Mathlib. That is simple, and it makes the start of Lean slower. The files of Mathlib itself import only what they need.

### How a file starts

Here is the start of the file `Mathlib/Data/Nat/Prime/Infinite.lean` at the commit of this edition, quoted from the source.

```lean
/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
module

public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Order.Bounds.Basic

import Mathlib.Data.Nat.Factorial.Basic

/-!
# Infinitude of the primes

## Main statements

- `Nat.exists_infinite_primes`: Euclid's theorem that there exist infinitely many prime numbers.
-/
```

Read it in order. The first comment gives the copyright, the licence and the authors. The keyword `module` says that the file uses the module system of Lean, which separates the public part of a file from its private part. The lines with `import` give the imports. The comment that starts with `/-!` is the documentation of the module. It has a title, and usually a part *Main definitions* and a part *Main statements*. A reader who looks for the main result of a file reads this comment first. The documentation pages of Mathlib show it at the top of the page of the module.

After the header, a file usually opens a namespace with `namespace Nat`. Each declaration up to `end Nat` gets the prefix `Nat.`, so the theorem written `exists_infinite_primes` in the file has the full name `Nat.exists_infinite_primes`. The line `open Nat` lets the file write `Prime` for `Nat.Prime`. Section 4.1 explains how the namespace is part of the name.

### The kinds of declarations

Each declaration starts with a keyword. The keyword tells the reader what the declaration is.

1. `def` gives a definition: a name for a term. Example: `Nat.Prime` is a definition of a predicate on `ℕ`, and `Nat.factorial` is a definition of a function from `ℕ` to `ℕ`.
2. `theorem` and `lemma` give a statement with a proof. The two words mean the same thing to Lean. Example: `Nat.exists_infinite_primes`.
3. `structure` gives a new type whose terms are records with named fields. Example: the type `Real` of real numbers is a structure with one field, a Cauchy completion of `ℚ`.
4. `class` gives a structure that Lean can find on its own, by the instance search. Example: `Group` is a class. Section 2.2 explains classes.
5. `instance` gives a term of a class that the instance search can use. Example: `Real.instField` is the statement, with its proof, that `ℝ` is a field.
6. `abbrev` gives a definition that Lean unfolds freely, and `inductive` gives a type by constructors, as `ℕ` is built from `0` and the successor.

A declaration often has an *attribute* in `@[...]` before the keyword. The attribute `@[simp]` makes a lemma a rule of the tactic `simp`. The attribute `@[to_additive]` makes Lean write the additive version of a multiplicative lemma. Section 4.1 and Section 3.3 explain these attributes.

::: mathlib
`Nat.exists_infinite_primes` · `Mathlib.Data.Nat.Prime.Infinite`

The theorem of Euclid in Mathlib: for each natural number $n$, there is a prime $p$ with $n \le p$. Section 1.3 explains why this form, and Section 5.3 reads its proof term.

<?decl Nat.exists_infinite_primes?>
:::

### The definition of a prime number

A textbook defines a prime number as a natural number $p \ge 2$ whose only divisors are $1$ and $p$. Mathlib takes a definition from algebra.

**Definition (Unit).** Let $M$ be a monoid, written multiplicatively. An element $u \in M$ is a *unit* if there is $v \in M$ with $uv = vu = 1$.

**Definition (Irreducible element).** Let $M$ be a monoid. An element $p \in M$ is *irreducible* if $p$ is not a unit, and for all $a, b \in M$ with $p = ab$, $a$ is a unit or $b$ is a unit.

**Definition (Prime number, Mathlib form).** A natural number $p$ is *prime* if $p$ is irreducible in the monoid $(\mathbb{N}, \cdot, 1)$.

::: mathlib
`Irreducible` · `Mathlib.Algebra.Group.Irreducible.Defs`

The predicate `Irreducible` is a structure with two fields: `not_isUnit`, the proof that $p$ is not a unit, and `isUnit_or_isUnit`, the proof that each factorization has a unit factor. A structure whose type is `Prop` is a statement with named parts. The definition does not ask that $p \ne 0$: the documentation of the file says that this needs a semiring, and the definition is for monoids.

<?decl Irreducible?>
:::

::: mathlib
`Nat.Prime` · `Mathlib.Data.Nat.Prime.Defs`

The definition is `def Prime (p : ℕ) := Irreducible p`, in the namespace `Nat`. The signature shows only the type `ℕ → Prop`: a prime is a predicate on `ℕ`. The full name `Nat.Prime` is different from the name `Prime`, which is the general notion of a prime element of a monoid with zero.

<?decl Nat.Prime?>
:::

The two definitions agree. To prove it, first find the units of $\mathbb{N}$.

**Lemma (The units of ℕ).** The only unit of the monoid $(\mathbb{N}, \cdot, 1)$ is $1$.

*Proof.* The element $1$ is a unit, since $1 \cdot 1 = 1$. Let $u$ be a unit, with $uv = 1$. Then $u \ne 0$ and $v \ne 0$, since $0 \cdot v = 0 \ne 1$ and $u \cdot 0 = 0 \ne 1$. So $u \ge 1$ and $v \ge 1$. Then $u = u \cdot 1 \le u v = 1$. So $1 \le u \le 1$, and $u = 1$. $\square$

**Theorem (Two definitions of a prime).** Let $p \in \mathbb{N}$. Then $p$ is irreducible in $(\mathbb{N}, \cdot, 1)$ if and only if $p \ge 2$ and each $m < p$ that divides $p$ is equal to $1$.

*Proof.* First suppose that $p$ is irreducible. By the lemma, $p \ne 1$, because $p$ is not a unit. Also $p \ne 0$: indeed $0 = 0 \cdot 0$, and $0$ is not a unit, so $0$ has a factorization with no unit factor. So $p \ge 2$. Now let $m < p$ with $m \mid p$, so $p = mk$ for some $k \in \mathbb{N}$. Since $p$ is irreducible, $m$ is a unit or $k$ is a unit, so $m = 1$ or $k = 1$ by the lemma. If $k = 1$, then $m = p$, which contradicts $m < p$. So $m = 1$.

Now suppose that $p \ge 2$ and each divisor $m < p$ of $p$ is $1$. Then $p \ne 1$, so $p$ is not a unit. Let $p = ab$. Since $p \ne 0$, also $a \ne 0$ and $b \ne 0$, so $a \ge 1$ and $b \ge 1$. Then $a = a \cdot 1 \le ab = p$. There are two cases. If $a < p$, then $a$ divides $p$, so $a = 1$, and $a$ is a unit. If $a = p$, then $p = pb$, and $p \cdot 1 = p \cdot b$ with $p \ne 0$ gives $b = 1$ by cancellation in $\mathbb{N}$. Then $b$ is a unit. In both cases a factor is a unit, so $p$ is irreducible. $\square$

::: mathlib
`Nat.prime_def_lt` · `Mathlib.Data.Nat.Prime.Defs`

The theorem of this subsection, in Mathlib. The binder `∀ m < p` means "for all $m$ with $m < p$". The statement is an equivalence `↔`, so it can rewrite `Nat.Prime p` into the textbook form, and back. The lemma `Nat.prime_def` gives the other textbook form: $p \ge 2$, and each divisor is $1$ or $p$.

<?decl Nat.prime_def_lt?>
:::

### Why Mathlib takes the algebraic definition

The algebraic definition looks less direct. It has two advantages. First, the lemmas about irreducible elements of any monoid apply to `Nat.Prime` at once, with no new proof. Second, the same notion works in $\mathbb{Z}$, in the Gaussian integers and in polynomial rings, where "divisors $1$ and $p$" is not the right notion because of the units $-1$, $\pm i$ and the nonzero constants. Mathlib defines a notion once, in the most general setting in which it makes sense, and proves the textbook forms as theorems.

A second notion, *prime element*, asks that $p$ is not zero and not a unit, and that $p \mid ab$ implies $p \mid a$ or $p \mid b$. In $\mathbb{N}$ the two notions agree. That is the lemma of Euclid, and in Mathlib it is the theorem `Nat.Prime.prime`.

::: mathlib
`Nat.Prime.prime` · `Mathlib.Data.Nat.Prime.Defs`

From a proof of `Nat.Prime p`, the theorem gives a proof of `Prime p`, the general notion of a prime element. The name has the form `Nat.Prime.prime`: the namespace `Nat.Prime` holds the lemmas whose main hypothesis is `Nat.Prime p`.

<?decl Nat.Prime.prime?>
:::

### Dot notation

The name `Nat.Prime.two_le` is the lemma that a prime is at least $2$. When `hp` is a proof of `Nat.Prime p`, the term `hp.two_le` means `Nat.Prime.two_le hp`. Lean sees that the type of `hp` is `Nat.Prime p`, so it looks for `two_le` in the namespace `Nat.Prime`, and it gives `hp` as the first explicit argument of the right type. This is *dot notation*. It is everywhere in Mathlib proofs. For example, the proof of `irrational_sqrt_two` in Mathlib is `simpa using Nat.prime_two.irrational_sqrt`: the term `Nat.prime_two` is a proof of `Nat.Prime 2`, so `Nat.prime_two.irrational_sqrt` means `Nat.Prime.irrational_sqrt Nat.prime_two`.

::: mathlib
`Nat.Prime.two_le` · `Mathlib.Data.Nat.Prime.Defs`

The hypothesis `Nat.Prime p` is the only explicit argument. The number `p` is implicit, because Lean reads it from the type of the hypothesis.

<?decl Nat.Prime.two_le?>
:::

### Examples

**Example (Small primes).** The number $2$ is prime: its only divisor less than $2$ that divides it is $1$, since $0$ does not divide $2$. The number $1$ is not prime, because it is a unit. The number $0$ is not prime, because $0 = 0 \cdot 0$ and $0$ is not a unit. Mathlib has these facts as `Nat.prime_two`, `Nat.not_prime_one` and `Nat.not_prime_zero`.

**Example (A composite number).** The number $6$ is not prime: $6 = 2 \cdot 3$, and neither $2$ nor $3$ is a unit. In the textbook form, $2 < 6$ and $2 \mid 6$, but $2 \ne 1$.

::: mathlib
`Nat.not_prime_one` · `Mathlib.Data.Nat.Prime.Defs`

The statement is a negation, `¬Nat.Prime 1`. A negation `¬P` in Lean is the statement `P → False`. Section 3.1 explains this.

<?decl Nat.not_prime_one?>
:::

### Common errors

1. Confusing `Prime` with `Nat.Prime`. After `open Nat`, the name `Prime` can mean either one. Write the full name when in doubt.
2. Looking for a theorem in `Defs.lean` when it is in `Basic.lean` or in a file of its own. Use the search of Section 4.2, not the file names.
3. Reading `theorem` as more important than `lemma`. Lean treats the two words the same.
4. Forgetting an import. The error `unknown identifier` often means that the module of the declaration is not imported.

### Exercises

1. (A) Give the module of the file `Mathlib/Topology/Order/IntermediateValue.lean`. Give the file of the module `Mathlib.Analysis.Real.Sqrt`.
2. (A) Find the units of the monoid $(\mathbb{Z}, \cdot, 1)$. Prove the answer.
3. (A) Use the theorem of this section to show that $7$ is prime and $9$ is not.
4. (B) Show that $-3$ is irreducible in $\mathbb{Z}$, and explain why the textbook definition of a prime does not apply to it.
5. (B) In the monoid $(\mathbb{N}, +, 0)$, find the units and the irreducible elements. Hint: the additive form of a unit is an element with an additive inverse.
6. (C) Prove that each irreducible element of $\mathbb{N}$ is a prime element, that is, that $p \mid ab$ implies $p \mid a$ or $p \mid b$. Hint: use the theorem of Bézout on $\gcd(p, a)$.

### Notes and history

The definition of `Nat.Prime` as `Irreducible` dates from the Lean 3 period of Mathlib. Older versions of the library defined a prime by the textbook condition, and the algebraic form was a theorem. The file `Mathlib/Data/Nat/Prime/Infinite.lean` names Leonardo de Moura, Jeremy Avigad and Mario Carneiro as authors, and its copyright line of 2015 shows that its content goes back to the first libraries of Lean. The Mathlib style guide gives the rules for the header and for the module documentation of a file.
