---
title: "Extended numbers: NNReal, ENNReal and ENat"
kind: theory
modules:
  - Mathlib.Basic.NNReal.Defs
  - Mathlib.Basic.ENNReal.Basic
  - Mathlib.Basic.ENNReal.Operations
  - Mathlib.Data.ENat.Basic
explains:
  E3: [NNReal, ENNReal]
  E2: [ENNReal.toReal, ENNReal.ofReal, ENNReal.mul_top, ENNReal.coe_ne_top, ENat.toNat]
  E1: auto
families: []
requires: [V02.C05, V02.C07]
reads_with: ["MIL"]
lean:
  - MathlibHandbook/V02/C08/Examples.lean
  - MathlibHandbook/V02/C08/Exercises.lean
  - MathlibHandbook/V02/C08/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Extended numbers: NNReal, ENNReal and ENat

### Overview

A measure takes values in $[0, \infty]$, and the dimension of a vector space can be infinite. Mathlib has a type for each of these sets. `NNReal` is the set $[0, \infty)$ of the real numbers that are not negative, with the notation `ℝ≥0`. `ENNReal` is $[0, \infty]$, with the notation `ℝ≥0∞`. `ENat` is $\mathbb{N} \cup \{\infty\}$, with the notation `ℕ∞`. The value $\infty$ is the top element `⊤` of the order. The arithmetic with `⊤` has rules that a reader must know, and the casts back to `ℝ` and `ℕ` have junk values at `⊤`. This section shows the three types, the rules and the casts.

### Definitions

**Definition (NNReal).** `NNReal` is the subtype `{r : ℝ // 0 ≤ r}`. The cast `(x : ℝ)` gives the value of `x`, and `Real.toNNReal r` is $\max(r, 0)$.

**Definition (ENNReal).** `ENNReal` is `WithTop NNReal`: a term is the cast of a term of `NNReal`, or `⊤`. The function `ENNReal.ofReal r` is the cast of $\max(r, 0)$, and `ENNReal.toReal a` is the value of $a$ for $a \neq \top$, with the junk value $0$ at `⊤`.

**Definition (ENat).** `ENat` is `WithTop ℕ`. The function `ENat.toNat` is the identity on `ℕ`, with the junk value $0$ at `⊤`.

**Definition (Arithmetic with ⊤).** In `ENNReal`, $a + \top = \top$ for each $a$, $a \cdot \top = \top$ for $a \neq 0$, and $0 \cdot \top = 0$. The inverse has $0^{-1} = \top$ and $\top^{-1} = 0$. Subtraction is truncated: $a - b = 0$ for $a \leq b$, and $\top - b = \top$ for $b \neq \top$.

### Theorems and proofs

**Theorem (Sums with ⊤).** For $a, b \in [0, \infty]$, $a + b = \top$ if and only if $a = \top$ or $b = \top$.

*Proof.* If $a = \top$ or $b = \top$, then $a + b = \top$ by the rule. If $a$ and $b$ are finite, they are casts of $x, y \in [0, \infty)$, and $a + b$ is the cast of $x + y$, which is finite. $\square$

**Theorem (Products with ⊤).** If $a \neq 0$, then $a \cdot \top = \top$.

*Proof.* If $a = \top$, the product is $\top$ by definition. If $a$ is the cast of $x > 0$, then for each finite $c$ there is $n$ with $c < x n$, so the product is above each finite value. $\square$

**Theorem (Casts back to ℝ).** For $r \geq 0$, $\operatorname{toReal}(\operatorname{ofReal}(r)) = r$. For $a \neq \top$, $\operatorname{ofReal}(\operatorname{toReal}(a)) = a$.

*Proof.* For $r \geq 0$, $\max(r, 0) = r$, and the value of its cast is $r$. For finite $a$, $a$ is the cast of some $x$, and $\operatorname{toReal}(a) = x \geq 0$, so $\operatorname{ofReal}(x)$ is the cast of $x$. $\square$

### Mathlib boxes

::: mathlib
`NNReal` · `Mathlib.Basic.NNReal.Defs`

The notation `ℝ≥0` needs `open NNReal`. The lemmas about the cast to `ℝ` have the prefix `NNReal.coe_`: `NNReal.coe_add`, `NNReal.coe_mul`, `NNReal.coe_le_coe` and `NNReal.coe_nonneg`. The tactic `norm_cast` uses them.

<?decl NNReal?>
:::

::: mathlib
`ENNReal` · `Mathlib.Basic.ENNReal.Basic`

The notation `ℝ≥0∞` needs `open ENNReal`. The type is a complete linear order, so each set has a supremum, and a sum of a family of terms is always defined. This is why measure theory uses it.

<?decl ENNReal?>
:::

::: mathlib
`ENNReal.mul_top` · `Mathlib.Basic.ENNReal.Operations`

The hypothesis `a ≠ 0` is necessary, because $0 \cdot \top = 0$. The lemma `ENNReal.top_mul` is the form with `⊤` on the left, and `ENNReal.mul_eq_top` gives the two cases.

<?decl ENNReal.mul_top?>
:::

::: mathlib
`ENNReal.toReal` · `Mathlib.Basic.ENNReal.Basic`

The junk value at `⊤` is $0$, so a lemma such as `ENNReal.toReal_add` needs the hypotheses `a ≠ ⊤` and `b ≠ ⊤`.

<?decl ENNReal.toReal?>
:::

### Examples

**Example (The cast of NNReal).**

<?lean MathlibHandbook/V02/C08/Examples.lean#nnreal?>

**Example (Truncated subtraction).**

<?lean MathlibHandbook/V02/C08/Examples.lean#nnreal_sub?>

**Example (Arithmetic with ⊤).** The lemma `add_top` is the general lemma of an ordered monoid with a top element.

<?lean MathlibHandbook/V02/C08/Examples.lean#ennreal_top?>

**Example (A finite value).**

<?lean MathlibHandbook/V02/C08/Examples.lean#coe_ne_top?>

**Example (The cast to ℝ).**

<?lean MathlibHandbook/V02/C08/Examples.lean#toReal?>

**Example (ENat).**

<?lean MathlibHandbook/V02/C08/Examples.lean#enat?>

### The library around it

The file `Mathlib.Basic.ENNReal.Basic` has the casts: `ENNReal.ofNNReal`, `ENNReal.toNNReal`, `ENNReal.coe_ne_top`, `ENNReal.coe_lt_top`, `ENNReal.zero_lt_top`, `ENNReal.toReal_ofReal` and `ENNReal.ofReal_toReal`. The file `Mathlib.Basic.ENNReal.Operations` has the arithmetic: `ENNReal.add_eq_top`, `ENNReal.top_mul` and `ENNReal.top_sub_coe`. The inverse and the division are in `Mathlib.Basic.ENNReal.Inv`, with `ENNReal.inv_zero`, `ENNReal.inv_top` and `ENNReal.div_zero`. The lemmas with `ENNReal.toReal` and `ENNReal.ofReal` are in `Mathlib.Basic.ENNReal.Real`, for example `ENNReal.ofReal_add` and `ENNReal.ofReal_of_nonpos`. The file `Mathlib.Data.ENat.Basic` has `ENat.coe_lt_top`, `ENat.top_ne_coe`, `ENat.toNat_natCast` and `ENat.natCast_toNat`. The type `EReal` of the extended real numbers $[-\infty, \infty]$ is in `Mathlib/Data/EReal`.

### Exercises

1. (A) Give the values of `(⊤ : ENNReal).toReal`, `ENNReal.ofReal (-2)` and `(0 : ENNReal)⁻¹` in Mathlib.
2. (A) Explain why measure theory uses `ENNReal` and not `ℝ`.
3. (B) Show that the multiplication of `ENNReal` is not cancellative: find $a \neq 0$ and $b \neq c$ with $a b = a c$.
4. (B) Show that `ENNReal.toReal` does not keep addition in general.
5. (L) Prove that $\top \cdot \top = \top$ in `ENNReal`. The solution is `top_mul_top_ennreal`.
6. (L) Prove that a sum in `ENNReal` is `⊤` if and only if a term is `⊤`. The solution is `add_eq_top_iff_ennreal`.
7. (L) Prove that the value of `ENNReal.ofReal 2` is $2$. The solution is `toReal_ofReal_two`.
8. (L) Prove that the cast of `ENat.toNat n` is $n$ for $n \neq \top$. The solution is `enat_coe_toNat`.
9. (L) Prove that the cast from `NNReal` to `ℝ` keeps products. The solution is `nnreal_coe_mul`.

### Notes and history

The convention $0 \cdot \infty = 0$ is the convention of measure theory: the integral of the zero function on a set of infinite measure is $0$. Mathlib defines the extended types with `WithTop`, so the general lemmas about a top element apply to `ENNReal` and to `ENat`.

### Reference

<?reference?>
