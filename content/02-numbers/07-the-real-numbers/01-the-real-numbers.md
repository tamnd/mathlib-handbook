---
title: The real numbers
kind: theory
modules:
  - Mathlib.Basic.Real.Basic
  - Mathlib.Algebra.Order.CauSeq.Basic
  - Mathlib.Algebra.Order.CauSeq.Completion
explains:
  E3: [Real, CauSeq]
  E2: [Real.ofCauchy, Real.mk, Real.mk_le, Real.ind_mk, CauSeq.lim]
  E1: auto
families: []
requires: [V02.C04, V02.C05]
reads_with: ["MIL"]
lean:
  - MathlibHandbook/V02/C07/Examples.lean
  - MathlibHandbook/V02/C07/Exercises.lean
  - MathlibHandbook/V02/C07/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The real numbers

### Overview

There are two common constructions of $\mathbb{R}$: Dedekind cuts and Cauchy sequences. Mathlib uses Cauchy sequences. A real number is a class of Cauchy sequences of rational numbers, and two sequences are in the same class if their difference goes to $0$. Mathlib wraps the quotient in a structure, so the type `ℝ` is not a quotient type, and its definition does not unfold in a proof. A user of `ℝ` almost never sees the construction. The instances say that `ℝ` is a field, a linear order and a complete metric space, and the lemmas of these structures do the work. This section shows the construction and the few functions that open it.

### Definitions

**Definition (Cauchy sequence).** Let $\alpha$ be an ordered field, $\beta$ a ring and $v : \beta \to \alpha$ an absolute value. A sequence $f : \mathbb{N} \to \beta$ is a Cauchy sequence if for each $\varepsilon > 0$ there is $N$ with $v(f_j - f_i) < \varepsilon$ for all $j \geq i \geq N$. The type `CauSeq β v` is the subtype of the Cauchy sequences.

**Definition (Equivalence of sequences).** Two Cauchy sequences $f$ and $g$ are equivalent, $f \approx g$, if $v(f_i - g_i)$ goes to $0$.

**Definition (The real numbers).** Let `Cauchy` be the quotient of `CauSeq ℚ abs` by the equivalence. The type `ℝ` is the structure with one field `Real.cauchy : Cauchy`. The constructor is `Real.ofCauchy`, and `Real.mk f` is the real number of the sequence $f$.

**Definition (The limit).** In a complete space, `CauSeq.lim f` is the limit of the Cauchy sequence $f$. The class `CauSeq.IsComplete` says that each Cauchy sequence has a limit.

### Theorems and proofs

**Theorem (Each real number has a sequence).** For each $x \in \mathbb{R}$ there is a Cauchy sequence $f$ of rational numbers with $x = \operatorname{mk}(f)$.

*Proof.* The field `x.cauchy` is a class of the quotient, so it has a representative $f$. Then $x = \operatorname{mk}(f)$, because a structure with one field is equal to the structure of its field. $\square$

**Theorem (Equality and order).** $\operatorname{mk}(f) = \operatorname{mk}(g)$ if and only if $f \approx g$, and $\operatorname{mk}(f) \leq \operatorname{mk}(g)$ if and only if $f \leq g$, where $f \leq g$ means that $f \approx g$ or $g - f$ is positive.

*Proof.* The first statement is the property of a quotient. For the second, the order on `ℝ` is defined from the order on the representatives, and the definition does not depend on the choice of representatives. $\square$

**Theorem (Completeness).** Each set of real numbers that is not empty and is bounded above has a least upper bound.

*Proof.* Let $s$ be the set and $b$ an upper bound. For each $n$, let $q_n$ be the least multiple of $2^{-n}$ that is an upper bound of $s$. The sequence $q_n$ goes down, and $q_n - 2^{-n}$ is not an upper bound. So $|q_m - q_n| \leq 2^{-n}$ for $m \geq n$, and the sequence is a Cauchy sequence. Its class is the least upper bound of $s$. $\square$

### Mathlib boxes

::: mathlib
`Real` · `Mathlib.Basic.Real.Basic`

The definition is a structure with one field, and the field is a quotient. So the definition of `ℝ` and of its operations do not unfold. The instances `Real.instField` and `Real.instIsStrictOrderedRing` make the general lemmas apply.

<?decl Real?>
:::

::: mathlib
`CauSeq` · `Mathlib.Algebra.Order.CauSeq.Basic`

The type takes the absolute value as an argument. The real numbers use `CauSeq ℚ abs`. The $p$ adic numbers use the same type with the $p$ adic absolute value, so the two constructions share their lemmas.

<?decl CauSeq?>
:::

::: mathlib
`Real.mk` · `Mathlib.Basic.Real.Basic`

The lemmas `Real.mk_add`, `Real.mk_mul`, `Real.mk_le`, `Real.mk_eq` and `Real.mk_const` say that `Real.mk` is compatible with the structure. A proof that opens the construction starts with `Real.ind_mk`.

<?decl Real.mk?>
:::

### Examples

**Example (A field).**

<?lean MathlibHandbook/V02/C07/Examples.lean#field?>

**Example (Tactics on ℝ).** The tactics `ring` and `linarith` use the instances, not the construction.

<?lean MathlibHandbook/V02/C07/Examples.lean#ring_linarith?>

**Example (A constant sequence).**

<?lean MathlibHandbook/V02/C07/Examples.lean#mk_const?>

**Example (The sum).**

<?lean MathlibHandbook/V02/C07/Examples.lean#mk_add?>

**Example (A representative).**

<?lean MathlibHandbook/V02/C07/Examples.lean#ind_mk?>

**Example (The order on the rational numbers).**

<?lean MathlibHandbook/V02/C07/Examples.lean#ratCast_lt?>

### The library around it

The file `Mathlib.Basic.Real.Basic` has the construction and the instances, with `Real.ext_cauchy`, `Real.mk_mul` and `Real.mk_pos`. The completeness is in `Mathlib.Algebra.Order.Archimedean.Real.Basic`: `Real.exists_isLUB` gives a least upper bound, `Real.sSup_le` is a lemma about `sSup`, and `Real.instArchimedean` says that `ℝ` is archimedean. The lemma `exists_rat_btwn` gives a rational number between two real numbers. The file `Mathlib.Algebra.Order.CauSeq.Completion` has the general completion, with `CauSeq.Completion.Cauchy`, `CauSeq.IsComplete` and `CauSeq.equiv_lim`. The square root, the exponential and the logarithm are in the volumes on analysis. The topology of `ℝ` is in the volume on general topology.

### Exercises

1. (A) Give the value of `sSup ∅` for a set of real numbers in Mathlib, and explain why `Real.sSup_le` needs `0 ≤ a`.
2. (A) Explain why the structure with one field makes the definition of `ℝ` opaque in a proof.
3. (B) Show that the sequences $1/n$ and $0$ give the same real number.
4. (B) Show that `ℝ` with the order is archimedean, from the construction.
5. (L) Prove that $(x - y)^2 = x^2 - 2 x y + y^2$ in `ℝ`. The solution is `sub_sq_real`.
6. (L) Prove that each real number is the class of a Cauchy sequence. The solution is `exists_cauSeq_mk`.
7. (L) Prove that `Real.mk` keeps the order. The solution is `mk_le_mk_of_le`.
8. (L) Prove that the cast from `ℚ` to `ℝ` keeps the strict order. The solution is `ratCast_lt_ratCast`.

### Notes and history

Dedekind published his cuts in 1872, and Cantor published his construction with Cauchy sequences in the same year. Mathlib uses the construction of Cantor because the same code builds the completions of other fields, for example the $p$ adic numbers. Lean 3 Mathlib had the same construction, and the port to Lean 4 kept it.

### Reference

<?reference?>
