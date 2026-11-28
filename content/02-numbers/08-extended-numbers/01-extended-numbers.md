---
title: "NNReal and ENNReal"
kind: theory
modules:
  - Mathlib.Basic.NNReal.Defs
  - Mathlib.Basic.ENNReal.Basic
  - Mathlib.Basic.ENNReal.Operations
  - Mathlib.Basic.NNReal.Basic
  - Mathlib.Basic.NNReal.Star
  - Mathlib.Data.ENNReal.Basic
  - Mathlib.Data.ENNReal.Operations
  - Mathlib.Data.NNReal.Defs
  - Mathlib.Data.NNReal.Basic
  - Mathlib.Data.NNReal.Star
explains:
  E3: [NNReal, ENNReal]
  E2: [ENNReal.toReal, ENNReal.ofReal, ENNReal.mul_top, ENNReal.coe_ne_top, ENNReal.add_eq_top, ENNReal.iSup_add]
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

## NNReal and ENNReal

### Overview

A length is a real number that is not negative, or infinite. So measure theory needs the set $[0, \infty]$ with an arithmetic for $\infty$. Mathlib has the type `NNReal` (notation `ℝ≥0`) for $[0, \infty)$ and the type `ENNReal` (notation `ℝ≥0∞`) for $[0, \infty]$, where $\infty$ is the top element `⊤`. This section proves the rules for $\infty$ and the main theorem: each subset of $[0, \infty]$ has a supremum, so each series in $[0, \infty]$ has a sum.

### Definitions

**Definition (Nonnegative reals).** The set $[0, \infty) = \{x \in \mathbb{R} : x \geq 0\}$ with the operations and the order of $\mathbb{R}$, and the truncated subtraction $x \mathbin{\dot -} y = \max(x - y, 0)$.

::: mathlib
`NNReal` · `Mathlib.Basic.NNReal.Defs`

`NNReal` is the subtype `{r : ℝ // 0 ≤ r}`, a linear ordered semifield. The cast lemmas have the prefix `NNReal.coe_`, for example `NNReal.coe_add` and `NNReal.coe_mul`. The lemma `NNReal.coe_sub` needs `r₂ ≤ r₁`. The map `Real.toNNReal` sends $r$ to $\max(r, 0)$.

<?decl NNReal?>
:::

**Definition (Extended nonnegative reals).** The set $[0, \infty] = [0, \infty) \cup \{\infty\}$, with $x < \infty$ for each finite $x$. For each $a$:

1. $a + \infty = \infty + a = \infty$;
2. $a \cdot \infty = \infty \cdot a = \infty$ if $a \neq 0$, and $0 \cdot \infty = \infty \cdot 0 = 0$;
3. $a \mathbin{\dot -} b = 0$ if $a \leq b$, and $\infty \mathbin{\dot -} b = \infty$ if $b \neq \infty$;
4. $0^{-1} = \infty$ and $\infty^{-1} = 0$.

::: mathlib
`ENNReal` · `Mathlib.Basic.ENNReal.Basic`

`ENNReal` is `WithTop ℝ≥0`: a term is a cast `↑r` with `r : ℝ≥0`, or `⊤`. It is an ordered commutative semiring and a complete linear order. A proof by cases uses `cases a` or `WithTop.recTopCoe`, and the general lemmas `add_top` and `top_add` apply.

<?decl ENNReal?>
:::

**Definition (Casts to and from ℝ).** For $r \in \mathbb{R}$, $\operatorname{ofReal}(r) = \max(r, 0)$. For $a \in [0, \infty]$, $\operatorname{toReal}(a) = a$ if $a \neq \infty$, and $\operatorname{toReal}(\infty) = 0$.

::: mathlib
`ENNReal.ofReal` · `Mathlib.Basic.ENNReal.Basic`

`ENNReal.ofReal r` is the cast of `Real.toNNReal r`, so `ENNReal.ofReal_of_nonpos` gives $0$ for $r \leq 0$.

<?decl ENNReal.ofReal?>
:::

::: mathlib
`ENNReal.toReal` · `Mathlib.Basic.ENNReal.Basic`

The junk value at `⊤` is $0$. So `ENNReal.toReal_add` needs `a ≠ ⊤` and `b ≠ ⊤`. The lemma `ENNReal.toReal_mul` needs no hypothesis, because both sides are $0$ when a factor is `⊤`.

<?decl ENNReal.toReal?>
:::

### Theorems and proofs

**Theorem (Sums with ∞).** $a + b = \infty$ if and only if $a = \infty$ or $b = \infty$.

*Proof.* If $a = \infty$ or $b = \infty$, rule 1 gives $a + b = \infty$. If $a$ and $b$ are finite, $a + b$ is a real number, so it is not $\infty$. $\square$

::: mathlib
`ENNReal.add_eq_top` · `Mathlib.Basic.ENNReal.Operations`

A `simp` lemma. The strict form is `ENNReal.add_lt_top`.

<?decl ENNReal.add_eq_top?>
:::

**Theorem (Products with ∞).** $a b = \infty$ if and only if $a \neq 0$ and $b = \infty$, or $a = \infty$ and $b \neq 0$.

*Proof.* If $a$ and $b$ are finite, $a b$ is a real number. If $b = \infty$, rule 2 gives $a b = \infty$ for $a \neq 0$ and $a b = 0$ for $a = 0$. The case $a = \infty$ is the same. $\square$

::: mathlib
`ENNReal.mul_top` · `Mathlib.Basic.ENNReal.Operations`

The hypothesis `a ≠ 0` is necessary because $0 \cdot \infty = 0$. The theorem above is `ENNReal.mul_eq_top`.

<?decl ENNReal.mul_top?>
:::

**Remark.** The convention $0 \cdot \infty = 0$ is forced. A semiring needs $a \cdot 0 = 0$ for each $a$, and $a = \infty$ gives it. With this rule, distributivity holds in all cases, and a case check proves that $[0, \infty]$ is a commutative semiring.

**Theorem (Suprema in [0, ∞]).** Each subset $S$ of $[0, \infty]$ has a supremum.

*Proof.* If $S$ is empty, the supremum is $0$. If $\infty \in S$, or if $S$ has no real upper bound, the only upper bound is $\infty$, and it is the supremum. Otherwise $S$ is a nonempty subset of $[0, \infty)$ that is bounded above in $\mathbb{R}$. The least upper bound property (Chapter 7) gives a supremum $s \geq 0$ in $\mathbb{R}$. Each upper bound in $[0, \infty]$ is $\infty$ or a real upper bound, so it is $\geq s$. $\square$

**Lemma (Sums and suprema).** For a nonempty family $(x_i)$ in $[0, \infty]$ and $c \in [0, \infty]$, $(\sup_i x_i) + c = \sup_i (x_i + c)$.

*Proof.* Let $s = \sup_i x_i$ and $u = \sup_i (x_i + c)$. Each $x_i + c \leq s + c$, so $u \leq s + c$. If $c = \infty$ or $u = \infty$, both sides are $\infty$. Otherwise $u \geq c$ is finite and $x_i \leq u - c$ for each $i$. So $s \leq u - c$ and $s + c \leq u$. $\square$

::: mathlib
`ENNReal.iSup_add` · `Mathlib.Basic.ENNReal.Operations`

The hypothesis `[Nonempty ι]` is necessary: for the empty family the left side is $c$ and the right side is $0$.

<?decl ENNReal.iSup_add?>
:::

**Corollary (Series in [0, ∞]).** Define $\sum_n a_n = \sup_N \sum_{n < N} a_n$. This sum exists for each sequence in $[0, \infty]$, and $\sum_n (a_n + b_n) = \sum_n a_n + \sum_n b_n$.

*Proof.* The sum exists by the theorem on suprema. Let $s_N$ and $t_N$ be the partial sums of $a$ and $b$. They increase because the terms are $\geq 0$. Each $s_N + t_N \leq \sup s + \sup t$, which gives one inequality. For all $M, N$ and $K = \max(M, N)$, $s_M + t_N \leq s_K + t_K$. Take the supremum over $M$ and then over $N$ with the lemma. This gives $\sup s + \sup t \leq \sup_K (s_K + t_K)$. $\square$

No hypothesis of convergence appears, so countable additivity $\mu(\bigcup_n A_n) = \sum_n \mu(A_n)$ makes sense for each sequence of disjoint sets. This is why measures in Mathlib take values in `ℝ≥0∞`.

**Theorem (Casts back to ℝ).** For $r \geq 0$, $\operatorname{toReal}(\operatorname{ofReal}(r)) = r$. For $a \neq \infty$, $\operatorname{ofReal}(\operatorname{toReal}(a)) = a$.

*Proof.* For $r \geq 0$, $\operatorname{ofReal}(r) = r$ is finite, and toReal gives $r$. For a finite $a = x \geq 0$, $\operatorname{toReal}(a) = x$ and $\operatorname{ofReal}(x) = x$. $\square$

::: mathlib
`ENNReal.coe_ne_top` · `Mathlib.Basic.ENNReal.Basic`

A hypothesis `h : a ≠ ⊤` lets a proof lift `a` to `ℝ≥0` with `lift a to ℝ≥0 using h`. The theorem above is `ENNReal.toReal_ofReal` and `ENNReal.ofReal_toReal`.

<?decl ENNReal.coe_ne_top?>
:::

### Examples

**Example (A divergent series).** The partial sums of $\sum 1/(n+1)$ are not bounded, so the sum is $\infty$ in $[0, \infty]$. In `ℝ`, `∑'` of a series that is not summable has the junk value $0$.

**Counterexample (Cancellation).** $\infty + 1 = \infty + 2$ but $1 \neq 2$, so $[0, \infty]$ is not a group. The lemma `ENNReal.add_right_inj` needs `a ≠ ⊤`. Also $\operatorname{toReal}(\infty + 1) = 0 \neq 0 + 1$, so `ENNReal.toReal_add` needs its hypotheses.

**Example (Inverses).** $a \cdot a^{-1} = 1$ for $a \notin \{0, \infty\}$, but $0 \cdot 0^{-1} = 0 \cdot \infty = 0$. So `ENNReal.mul_inv_cancel` needs `a ≠ 0` and `a ≠ ⊤`.

**Example (Lean).** The cast of `ℝ≥0`, the truncated subtraction $3 - 5 = 0$, the rules for `⊤`, a finite value, and the junk value of `toReal`.

<?lean MathlibHandbook/V02/C08/Examples.lean#nnreal?>

<?lean MathlibHandbook/V02/C08/Examples.lean#nnreal_sub?>

<?lean MathlibHandbook/V02/C08/Examples.lean#ennreal_top?>

<?lean MathlibHandbook/V02/C08/Examples.lean#coe_ne_top?>

<?lean MathlibHandbook/V02/C08/Examples.lean#toReal?>

### The library around it

`Mathlib.Basic.NNReal.Defs` has `NNReal` and `Real.toNNReal`. `Mathlib.Basic.ENNReal.Basic` has the casts `ENNReal.ofNNReal`, `ENNReal.toNNReal`, `ENNReal.ofReal` and `ENNReal.toReal` with their lemmas, such as `ENNReal.coe_lt_top` and `ENNReal.toReal_top`. `Mathlib.Basic.ENNReal.Operations` has the arithmetic, for example `ENNReal.mul_eq_top`, `ENNReal.sub_top` and `ENNReal.top_sub_coe`. `Mathlib.Basic.ENNReal.Inv` has `ENNReal.inv_zero`, `ENNReal.inv_top` and `ENNReal.div_zero`, and `Mathlib.Basic.ENNReal.Real` has `ENNReal.ofReal_add` and `ENNReal.toReal_add`. A lemma states `≠ ⊤` when the junk value matters.

`Mathlib.Basic.NNReal.Basic` collects the results on `ℝ≥0` that need more of the library. The cast to `ℝ` commutes with finite sums and products: `NNReal.coe_sum`, `NNReal.coe_prod`, `NNReal.coe_multiset_sum`, `NNReal.coe_list_sum` and `NNReal.coe_expect`, all `norm_cast` lemmas. In the other direction, `Real.toNNReal_sum_of_nonneg` needs nonnegative terms. The multiplication distributes over suprema and infima, as in `NNReal.mul_iSup`, `NNReal.iInf_mul` and `NNReal.mul_finset_sup`. Because the subtraction of `ℝ≥0` is truncated, `NNReal.sub_div` gives $(a - b) / c = a / c - b / c$ with no hypothesis, and `NNReal.coe_sub_of_lt` gives the cast of $b - a$ for $a < b$. The lemmas `NNReal.toReal_le` and `NNReal.toReal_lt` move an order statement to `ℝ`. The image of an interval under the cast is an interval: for example `NNReal.image_coe_Icc`, and `NNReal.range_coe` says that the range of the cast is $[0, \infty)$.

`Mathlib.Basic.NNReal.Star` makes `ℝ≥0` a `StarRing` with the trivial star, and gives the instance `StarModule` of `ℝ≥0` on each star module over `ℝ`.

`Mathlib.Data.ENNReal.Basic` and `Mathlib.Data.ENNReal.Operations` are deprecated redirects to `Mathlib.Basic.ENNReal.Basic` and `Mathlib.Basic.ENNReal.Operations`. Division, the maps to `ℝ` and finite sums have their own section in this chapter.

### Exercises

1. (A) Give the values of `(⊤ : ℝ≥0∞).toReal`, `ENNReal.ofReal (-2)` and `(0 : ℝ≥0∞)⁻¹`. *Hint.* Use the definitions and rule 4.
2. (B) Show that the multiplication of $[0, \infty]$ is associative. *Hint.* If a factor is $0$, both sides are $0$. Otherwise use the theorem on products.
3. (B) Show that $\sum_n 2^{-n} = 2$ in $[0, \infty]$. *Hint.* The partial sums are $2 - 2^{1 - N}$.
4. (C) Show that $x \mapsto x^{-1}$ is an order reversing bijection of $[0, \infty]$. *Hint.* Treat $0$ and $\infty$ apart.
5. (L) Prove that $\top \cdot \top = \top$ in `ℝ≥0∞`. The solution is `top_mul_top_ennreal`.
6. (L) Prove that a sum in `ℝ≥0∞` is `⊤` if and only if a term is `⊤`. The solution is `add_eq_top_iff_ennreal`.
7. (L) Prove that `(ENNReal.ofReal 2).toReal = 2`. The solution is `toReal_ofReal_two`.
8. (L) Prove that the cast from `ℝ≥0` to `ℝ` keeps products. The solution is `nnreal_coe_mul`.

### Notes and history

The half line $[0, \infty]$ with $0 \cdot \infty = 0$ is the value set of the measures of Lebesgue (1902) and Carathéodory (1914). Rudin, *Real and Complex Analysis*, Section 1.22, explains the convention. In Mathlib, `ENNReal` came from the measure theory library of Johannes Hölzl, and `NNReal` from Johan Commelin.

### Reference

<?reference?>
