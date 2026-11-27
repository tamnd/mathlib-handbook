---
title: Search tools and the source
kind: guide
modules: []
explains: {}
families: []
requires: [V00.C02, V00.C03]
reads_with: ["MIL Ch. 2", "MSG"]
lean:
  - MathlibHandbook/V00/C04/Examples.lean
  - MathlibHandbook/V00/C04/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Search tools and the source

### Overview

When the name of a lemma is not clear from the convention of Section 4.1, a tool finds it. There are three kinds of tools: tactics that search for a lemma that fits the goal, search engines that search by the form or the words of a statement, and commands that show a declaration once its name is known. This section describes each tool, gives two searches in full, and then reads a file of Mathlib, so that the reader can find a declaration and read its proof in the source.

### Tactics that search

**Definition (Search tactic).** A *search tactic* looks at the current goal, tries the lemmas of the imported modules, and prints a line `Try this: ...` with a proof that works.

1. `exact?` searches for a lemma that closes the goal, with the hypotheses of the goal as arguments. It prints `Try this: exact name args`.
2. `apply?` searches for a lemma whose conclusion matches the goal. It prints the lemma and the goals that remain.
3. `rw?` searches for an equation or an equivalence that rewrites the goal, and prints the rewrite and the new goal.
4. `simp?` runs `simp` and prints the lemmas that it used.

The search tactics are tools for the editor. A finished proof uses the line that they print, and not the tactic, because the search is slow and its result can change with the version of Mathlib. Mathlib itself has no call to `exact?`.

The search uses only the imported modules. If the file imports only `Mathlib.Data.Nat.Basic`, then `exact?` cannot find a lemma on real numbers. For a search over the whole library, import `Mathlib`.

**Example (Searching with exact?).** The goal is

```text
n : ℕ
⊢ 0 < n.factorial
```

The call `exact?` prints `Try this: exact Nat.factorial_pos n`. The name follows the convention: the namespace `Nat`, the object `factorial`, the sign `pos`.

::: mathlib
`Nat.factorial_pos` · `Mathlib.Data.Nat.Factorial.Basic`

The factorial of each natural number is positive. The argument `n` is explicit, because no hypothesis names it. The lemma `Nat.factorial_ne_zero` follows from it.

<?decl Nat.factorial_pos?>
:::

### Search engines

The search engines search the whole library, with no import.

1. Loogle, at loogle.lean-lang.org, searches by the form of the statement. A query is a list of patterns separated by commas. The pattern `?a * 2 = ?a + ?a` finds lemmas with that statement up to the names of the variables, and finds `mul_two`. The pattern `Nat.factorial, Nat.Prime` finds the lemmas whose statements use both constants. A pattern `|- _ < _ * _` finds lemmas with a conclusion of that form.
2. LeanSearch and Moogle search by a sentence in words, as "the factorial is positive". They use a model of language, and the result is a list of candidates to check.
3. The documentation of Mathlib, at the site of the project, has a page for each module, with the docstrings and the signatures. Its search box searches the names.
4. The search of mathlib.tamnd.com searches the names and the statements in words of the handbook.

**Example (Searching with Loogle).** The task is to find the cast of a difference of natural numbers to the integers. The query `((?n - ?m : ℕ) : ℤ)` is the form of the left side. Loogle answers with `Nat.cast_sub`, with the signature of Section 2.3, and with some variants for special targets. The hypothesis `m ≤ n` is in the signature and not in the query. A search by form finds lemmas with hypotheses, and the reader must check that the hypotheses hold.

**Theorem (Cast of a difference).** Let $R$ be a ring and $m \le n$ natural numbers. Then $\overline{n - m} = \bar n - \bar m$ in $R$.

*Proof.* Write $k = n - m$. Since $m \le n$, the truncated difference is the true difference, and $n = k + m$. By the law of the cast for addition, $\bar n = \bar k + \bar m$. Subtracting $\bar m$ in the ring $R$ gives $\bar k = \bar n - \bar m$. $\square$

::: mathlib
`Nat.cast_sub` · `Mathlib.Data.Int.Cast.Basic`

The proof above is the proof in Mathlib, in a few lines. The hypothesis `m ≤ n` is explicit, and the numbers `m` and `n` are implicit because the hypothesis names them. So the call is `Nat.cast_sub h` for `h : m ≤ n`.

<?decl Nat.cast_sub?>
:::

### Commands that show a declaration

Once the name is known, four commands show it.

1. `#check name` prints the signature, with the implicit arguments in braces.
2. `#print name` prints the full definition or the proof term.
3. `#synth C` searches for an instance of the class `C`, as `#synth Field ℝ`, and prints it or fails. It answers the question of Section 2.2: does this type have this structure?
4. `#print axioms name` prints the axioms of Section 3.1.

In the editor, the pointer over a name shows its signature and docstring, and the command *go to definition* opens the source at the declaration. Go to definition is the fastest way from a name to its proof.

**Example (The output of #check).** The command `#check @Nat.cast_le` prints the full signature with all arguments explicit. The mark `@` turns off the implicit arguments, so the output shows the type `α` and each instance in the order of the signature. Without `@`, `#check Nat.cast_le` prints `Nat.cast_le {α : Type u_1} ... : ↑m ≤ ↑n ↔ m ≤ n`.

### Reading a file of Mathlib

A file of Mathlib has a fixed structure. The file `Mathlib/Data/Nat/Factorial/Basic.lean` is an example. It starts with a header.

```lean
/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Chris Hughes, Floris van Doorn, Yaël Dillies
-/
module

public import Mathlib.Data.Nat.Basic
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Common
```

The header gives the authors and the imports. The word `module` and the marks `public` are part of the module system of recent Lean: a `public import` is visible to the files that import this one. After the imports comes a docstring of the module, between `/-!` and `-/`, with the title and the main declarations. Then the declarations.

```lean
namespace Nat

/-- `Nat.factorial n` is the factorial of `n`. -/
def factorial : ℕ → ℕ
  | 0 => 1
  | succ n => succ n * factorial n

scoped notation:10000 n "!" => Nat.factorial n

section Factorial

variable {m n : ℕ}

@[simp] theorem factorial_zero : 0! = 1 :=
  rfl

theorem factorial_succ (n : ℕ) : (n + 1)! = (n + 1) * n ! :=
  rfl

theorem factorial_pos : ∀ n, 0 < n !
  | 0 => Nat.zero_lt_one
  | succ n => Nat.mul_pos (succ_pos _) (factorial_pos n)
```

The text above is a part of the source, with the docstring of the notation and some lemmas left out. Each line has a reading.

1. `namespace Nat` puts each name of the file in the namespace `Nat`, so `factorial` is `Nat.factorial`.
2. The definition is by recursion on the two cases of a natural number: $0! = 1$ and $(n+1)! = (n+1) \cdot n!$.
3. The notation `n !` is `scoped`: it is active only after `open Nat`. That is why other files write `n.factorial` or `(n)!`.
4. The line `variable {m n : ℕ}` adds the implicit arguments `m` and `n` to each lemma of the section that uses them.
5. The proofs `rfl` say that the two sides are equal by the definition: Lean computes them to the same term.
6. The proof of `factorial_pos` is a definition by recursion of a proof: for $0$, it gives $0 < 1$, and for $n + 1$, it gives the product of the proofs of $0 < n + 1$ and of $0 < n!$. It is a proof by induction, written as a recursive function.

**Theorem (Factorials are positive).** For each $n \in \mathbb{N}$, $n! > 0$.

*Proof.* By induction on $n$. For $n = 0$, $0! = 1 > 0$. Suppose $n! > 0$. Then $(n+1)! = (n+1) \cdot n!$ is a product of two positive natural numbers, so it is positive. $\square$

The two proofs have the same structure. The term `factorial_pos n` in the step is the hypothesis of the induction: in Lean, a recursive call is an induction.

### Common errors

1. Leaving `exact?` in a proof. The proof works, but it is slow, and the line it prints is the proof to keep.
2. Searching with Loogle for `0 < a + b` with `a b` and not `?a ?b`. Without the mark `?`, Loogle looks for constants named `a` and `b`.
3. Concluding that a lemma does not exist because `exact?` fails. The search uses only the imports, and the goal can need a rewrite first.
4. Reading `n !` as `n` followed by a Boolean negation. In Lean the notation needs the space or the parentheses, and the source explains this in the docstring of the notation.

### Exercises

1. (A) Write a Loogle query for lemmas of the form `a ^ 2 = a * a`. Guess the name of the result.
2. (A) Give the output of `#check Nat.factorial_succ` from its signature in the source above.
3. (A) Explain why `factorial_zero` has the proof `rfl`.
4. (B) Use the source above to prove on paper that $n \cdot (n-1)! = n!$ for $n \ne 0$. Then find the name of this lemma in the same file, from the naming convention.
5. (B) The lemma `Nat.cast_div` of Section 2.3 has two hypotheses. Write a Loogle query that finds it, and explain why a query on the left side alone finds also lemmas without these hypotheses.
6. (B) Find the module of `Finset.sum_range_id_mul_two` from its name, and check with the documentation. Hint: sums over intervals.
7. (C) Prove that $n! \ge 2^{n-1}$ for $n \ge 1$, on paper. Write the proof as a recursive function in the style of `factorial_pos`, with the two cases $1$ and $n + 2$.

### Notes and history

Loogle was written by Joachim Breitner in 2023, on the model of the search tool Hoogle for Haskell. The tactic `exact?` replaces the tactic `library_search` of Lean 3, written by Scott Morrison. The documentation of Mathlib is made by the tool `doc-gen4`, by Henrik Böving.
