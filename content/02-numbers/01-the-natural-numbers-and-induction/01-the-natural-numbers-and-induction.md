---
title: The natural numbers and induction
kind: theory
modules:
  - Mathlib.Data.Nat.Init
  - Mathlib.Data.Nat.Find
explains:
  E3: [Nat.le_induction, Nat.find]
  E2: [Nat.strong_induction_on, Nat.twoStepInduction, Nat.decreasingInduction, Nat.find_spec, Nat.find_min']
  E1: auto
families: []
requires: [V01.C05]
reads_with: ["MIL", "TPIL"]
lean:
  - MathlibHandbook/V02/C01/Examples.lean
  - MathlibHandbook/V02/C01/Exercises.lean
  - MathlibHandbook/V02/C01/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The natural numbers and induction

### Overview

Lean defines the natural numbers as an inductive type with two constructors, `Nat.zero` and `Nat.succ`. So each natural number is $0$ or the successor of a natural number, and a proof by induction is the eliminator of the type. The core of Lean gives the type and its arithmetic. Mathlib adds the forms of induction that a mathematician uses, and the function `Nat.find`, which gives the least number with a property. This section shows these tools and the tactics that use them.

### Definitions

**Definition (The natural numbers).** The type `ℕ` is the inductive type with the constructors `Nat.zero : ℕ` and `Nat.succ : ℕ → ℕ`. Lean writes `n + 1` for `Nat.succ n`, and the kernel computes with a binary representation, so a large literal costs little.

**Definition (Induction from a start value).** For $m \in \mathbb{N}$ and a property $P$ of the numbers $n \geq m$, the principle `Nat.le_induction` says: if $P(m)$ holds, and $P(n)$ gives $P(n + 1)$ for each $n \geq m$, then $P(n)$ holds for each $n \geq m$.

**Definition (Strong induction).** The principle `Nat.strong_induction_on` says: if $P(n)$ follows from $P(k)$ for all $k < n$, then $P(n)$ holds for each $n$.

**Definition (The least number with a property).** Let $P$ be a decidable property of natural numbers, and let `h` be a proof that some number has $P$. Then `Nat.find h` is the least number with $P$.

### Theorems and proofs

**Theorem (Induction from a start value).** Let $m \in \mathbb{N}$. If $P(m)$ holds and $P(n)$ implies $P(n + 1)$ for each $n \geq m$, then $P(n)$ holds for each $n \geq m$.

*Proof.* Let $Q(k)$ be the statement $P(m + k)$. Then $Q(0)$ is $P(m)$, and $Q(k)$ gives $Q(k + 1)$ by the hypothesis. So $Q(k)$ holds for each $k$ by ordinary induction. Each $n \geq m$ is $m + k$ for $k = n - m$, so $P(n)$ holds. $\square$

**Theorem (Strong induction).** If $P(n)$ follows from $P(k)$ for all $k < n$, then $P(n)$ holds for each $n$.

*Proof.* Let $Q(n)$ be the statement that $P(k)$ holds for each $k < n$. The statement $Q(0)$ is true because no $k$ is less than $0$. If $Q(n)$ holds, then the hypothesis gives $P(n)$, and so $Q(n + 1)$ holds. Thus $Q(n + 1)$ holds for each $n$, and it contains $P(n)$. $\square$

**Theorem (The well ordering of ℕ).** If some natural number has the property $P$, then there is a least number with $P$.

*Proof.* Suppose that no number with $P$ is the least. By strong induction, no number $n$ has $P$: a number $n$ with $P$ is not the least, so some $k < n$ has $P$, and this is false by the hypothesis of the induction. This contradicts the hypothesis. $\square$

### Mathlib boxes

::: mathlib
`Nat.le_induction` · `Mathlib.Data.Nat.Init`

The property `P` takes the number and the proof of `m ≤ n`. Use it with `induction n, hn using Nat.le_induction`. The goal of the case `base` is `P m`, and the case `succ` gives the hypothesis of the induction.

<?decl Nat.le_induction?>
:::

::: mathlib
`Nat.find` · `Mathlib.Data.Nat.Find`

The function needs a `DecidablePred` instance for `P`, because its definition searches the numbers in order. The lemmas `Nat.find_spec` and `Nat.find_min'` give the two properties of the value, and `Nat.find_eq_iff` gives the value from both.

<?decl Nat.find?>
:::

::: mathlib
`Nat.strong_induction_on` · `Mathlib.Data.Nat.Init`

The tactic form is `induction n using Nat.strong_induction_on`. The hypothesis of the induction applies to each `k < n`.

<?decl Nat.strong_induction_on?>
:::

### Examples

**Example (Induction from 1).** The inequality $n + 1 \leq 2^n$ holds for each $n \geq 1$. The case `succ` uses `pow_succ` and `omega`.

<?lean MathlibHandbook/V02/C01/Examples.lean#le_induction?>

**Example (Strong induction).** The tactic gives the hypothesis `ih` for each smaller number. This proof does not use it.

<?lean MathlibHandbook/V02/C01/Examples.lean#strong_induction?>

**Example (A value of Nat.find).** The least $n$ with $5 < 2n$ is $3$.

<?lean MathlibHandbook/V02/C01/Examples.lean#find?>

**Example (The two properties of Nat.find).**

<?lean MathlibHandbook/V02/C01/Examples.lean#find_spec?>

**Example (The factorial).** The factorial `Nat.factorial n` is positive for each `n`.

<?lean MathlibHandbook/V02/C01/Examples.lean#factorial?>

### The library around it

The file `Mathlib.Data.Nat.Init` has the forms of induction: `Nat.le_induction`, `Nat.strong_induction_on`, `Nat.twoStepInduction` for a property that uses the two numbers before $n$, and `Nat.decreasingInduction` for a property that goes down from a bound. The definition `Nat.leRec` is the recursor behind `Nat.le_induction`. The file `Mathlib.Data.Nat.Find` has `Nat.find` and its lemmas, for example `Nat.find_le`. The tactic `omega` proves most goals of linear arithmetic on `ℕ` and `ℤ`, so a proof by induction often ends with it. The subtraction on `ℕ` is truncated, as Chapter 5 of Volume 1 shows. The factorial is `Nat.factorial`, with the notation `n !` in the namespace `Nat`. The binomial coefficients and the theory of order on `ℕ` are in other files of `Mathlib/Data/Nat`.

### Exercises

1. (A) Give the value of `Nat.find h`, where `h` says that some $n$ has $n^2 > 10$.
2. (A) Explain why `Nat.find` needs a `DecidablePred` instance.
3. (B) Show that strong induction follows from ordinary induction, and that ordinary induction follows from strong induction.
4. (B) Show that each $n \geq 2$ is a product of primes, with strong induction.
5. (L) Prove that $2n \leq 2^n$ for each $n \geq 2$. The solution is `le_pow_self`.
6. (L) Prove that for each $k$ there is a least $n$ with $k < n^2$. The solution is `exists_least_square_gt`.
7. (L) Prove that $2 \leq n!$ for each $n \geq 2$. The solution is `two_le_factorial`.

### Notes and history

Dedekind gave the axioms of the natural numbers in 1888, and Peano gave them in a different form in 1889. In type theory, the natural numbers are the simplest inductive type, and the principle of induction is its eliminator. Lean 4 adds a fast representation in the kernel, so `decide` and `norm_num` can compute with large numbers.

### Reference

<?reference?>
