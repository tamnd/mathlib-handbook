---
title: The complete ordered field
kind: theory
modules:
  - Mathlib.Basic.Real.Pointwise
  - Mathlib.Basic.Real.Embedding
explains:
  E3: []
  E2: [Real.sSup_smul_of_nonneg, Real.mul_iSup_of_nonneg, Archimedean.embedReal, Archimedean.exists_orderAddMonoidHom_real_injective]
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

## The complete ordered field

### Overview

The ordered fields $\mathbb{Q}$ and $\mathbb{R}$ differ in completeness: in $\mathbb{Q}$ the set $\{x : x^2 < 2\}$ is bounded above and has no least upper bound, and in $\mathbb{R}$ each nonempty set that is bounded above has one. This section proves the least upper bound property from the construction of the previous section. Then it derives from the axioms the archimedean property, the density of $\mathbb{Q}$, the existence of $\sqrt 2$ and the monotone convergence theorem.

### Definitions

Let $F$ be an ordered field and $S \subseteq F$.

**Definition (Upper bound and supremum).** An element $u$ is an *upper bound* of $S$ if $x \leq u$ for each $x \in S$, and $S$ is *bounded above* if it has one. An upper bound $s$ is the *supremum* of $S$ if $s \leq u$ for each upper bound $u$. The *infimum* is the greatest lower bound.

A supremum is unique, and it need not be in $S$. An upper bound $s$ is the supremum if and only if for each $\varepsilon > 0$ there is $x \in S$ with $x > s - \varepsilon$.

::: mathlib
`Real.sSup_smul_of_nonneg` · `Mathlib.Basic.Real.Pointwise`

Mathlib uses the predicate `IsLUB s x` and the total function `sSup s`. On `ℝ`, `sSup` of a set that is empty or not bounded above is the junk value $0$ (`Real.sSup_empty`, `Real.sSup_of_not_bddAbove`). The lemma says $\sup (a \cdot S) = a \cdot \sup S$ for $a \geq 0$, with no hypothesis on $S$, because $a \cdot 0 = 0$. The form for indexed suprema is `Real.mul_iSup_of_nonneg`.

<?decl Real.sSup_smul_of_nonneg?>
:::

**Definition (Complete and archimedean).** $F$ is *complete* if each nonempty subset that is bounded above has a supremum. $F$ is *archimedean* if for each $x \in F$ there is $n \in \mathbb{N}$ with $x < n$.

::: mathlib
`Real.instConditionallyCompleteLinearOrder` · `Mathlib.Algebra.Order.Archimedean.Real.Basic`

Mathlib has no single class for a complete ordered field. It combines `Field`, `IsStrictOrderedRing` and `ConditionallyCompleteLinearOrder`, whose axioms hold only for the sets that are nonempty and bounded.

<?decl Real.instConditionallyCompleteLinearOrder?>
:::

### Theorems and proofs

The first two lemmas use the construction. After them, each proof uses only the axioms.

**Lemma (Integer bounds).** For each $x \in \mathbb{R}$ there is an integer $M$ with $-M \leq x \leq M$.

*Proof.* Let $x = [a]$ and $|a_n| \leq B$ for each $n$. Let $M \geq B$ be an integer. The sequence $M - a_n$ has terms $\geq 0$. If $[M - a] < 0$, then $a_n - M \geq \delta > 0$ for large $n$, a contradiction. So $x \leq M$, and $x \geq -M$ in the same way. $\square$

Since $2^n \geq n + 1$, the lemma gives $n$ with $2^{-n} < \varepsilon$ for each real $\varepsilon > 0$.

**Lemma (A sequence approaches its class).** Let $a$ be a Cauchy sequence with $|a_n - a_m| \leq \varepsilon$ for all $n \geq m \geq N$. Then $|[a] - a_m| \leq \varepsilon$ for each $m \geq N$.

*Proof.* Fix $m \geq N$. The sequences $n \mapsto \varepsilon \mp (a_n - a_m)$ have terms $\geq 0$ for $n \geq N$, so their classes are $\geq 0$ by the argument of the previous proof. These classes are $\varepsilon \mp ([a] - a_m)$. $\square$

**Theorem (Least upper bound property).** Each nonempty $S \subseteq \mathbb{R}$ that is bounded above has a supremum.

*Proof.* Step 1. Fix $n$. Let $K_n$ be the set of the integers $k$ such that $k/2^n$ is an upper bound of $S$. By the lemma, $K_n$ is nonempty (above $2^n b$ for an upper bound $b$) and bounded below (by an integer below $2^n x_0$ for some $x_0 \in S$). Let $k_n$ be its least element and $q_n = k_n / 2^n$. Then (i) $q_n$ is an upper bound, and (ii) $q_n - 2^{-n}$ is not.

Step 2. Let $m \geq n$. The point $q_n = 2^{m-n} k_n / 2^m$ is on the finer grid and is an upper bound, so $q_m \leq q_n$. By (ii) some $x \in S$ has $x > q_n - 2^{-n}$, and $q_m \geq x$ by (i). So
$$q_n - 2^{-n} < q_m \leq q_n \quad \text{for all } m \geq n. \qquad (1)$$
So $(q_n)$ is a Cauchy sequence. Let $L = [q]$.

Step 3. By (1) and the second lemma, $|L - q_n| \leq 2^{-n}$. For $x \in S$, $x \leq q_n \leq L + 2^{-n}$ for each $n$, so $x \leq L$.

Step 4. Let $u < L$ and choose $n$ with $2 \cdot 2^{-n} < L - u$. By (ii) some $x \in S$ has $x > q_n - 2^{-n} \geq L - 2 \cdot 2^{-n} > u$. So $u$ is not an upper bound, and $L$ is the supremum. $\square$

::: mathlib
`Real.exists_isLUB` · `Mathlib.Algebra.Order.Archimedean.Real.Basic`

The statement is `s.Nonempty → BddAbove s → ∃ x, IsLUB s x`. The Mathlib proof uses a similar grid argument with a Cauchy sequence of rational numbers. From it Mathlib defines `sSup` by choice.

<?decl Real.exists_isLUB?>
:::

::: mathlib
`Real.sSup_le` · `Mathlib.Algebra.Order.Archimedean.Real.Basic`

If each element of $S$ is $\leq a$ and $0 \leq a$, then $\sup S \leq a$. It needs no hypothesis that $S$ is nonempty, at the price of $0 \leq a$, because $\sup \emptyset = 0$. The general lemma `csSup_le` asks for `s.Nonempty` instead.

<?decl Real.sSup_le?>
:::

**Theorem (A complete ordered field is archimedean).** In a complete ordered field $F$, for each $x$ there is $n \in \mathbb{N}$ with $x < n$.

*Proof.* Otherwise $\mathbb{N} \subseteq F$ is bounded above by $x$ and has a supremum $s$. Since $s - 1$ is not an upper bound, some $n > s - 1$. Then $n + 1 > s$, a contradiction. $\square$

::: mathlib
`Real.instArchimedean` · `Mathlib.Algebra.Order.Archimedean.Real.Basic`

`Archimedean R` says that for $y > 0$ and each $x$ there is $n$ with $x \leq n \cdot y$. The lemma `exists_nat_gt` gives the form above.

<?decl Real.instArchimedean?>
:::

**Theorem (Density of ℚ).** In an archimedean ordered field, between $x < y$ there is a rational $q$.

*Proof.* Choose $n \geq 1$ with $1/n < y - x$. The integers $k > n x$ form a nonempty set that is bounded below, by the archimedean property. Let $m$ be its least element. Then $n x < m \leq n x + 1 < n y$, so $x < m/n < y$. $\square$

::: mathlib
`exists_rat_btwn` · `Mathlib.Algebra.Order.Archimedean.Basic`

The statement holds for each archimedean ordered field `K`, with the cast `↑q : K`. The Mathlib proof uses the floor function.

<?decl exists_rat_btwn?>
:::

**Theorem (Square root of 2).** In a complete ordered field there is $s > 0$ with $s^2 = 2$.

*Proof.* Let $S = \{x \geq 0 : x^2 < 2\}$. Then $1 \in S$ and $2$ is an upper bound. Let $s = \sup S$, so $1 \leq s \leq 2$.

If $s^2 < 2$, let $h = \min\left(1, \frac{2 - s^2}{2(2s + 1)}\right)$. Then $h^2 \leq h$ and $(s + h)^2 \leq s^2 + h(2s + 1) \leq s^2 + \frac{2 - s^2}{2} < 2$, so $s + h \in S$, a contradiction.

If $s^2 > 2$, let $h = \frac{s^2 - 2}{2s}$, so $0 < h < s$ and $(s - h)^2 > s^2 - 2sh = 2$. Each $x > s - h$ has $x^2 > 2$, so $s - h$ is a smaller upper bound, a contradiction. So $s^2 = 2$. $\square$

In $\mathbb{Q}$ the proof shows that a supremum would satisfy $s^2 = 2$, so $S \cap \mathbb{Q}$ has no supremum in $\mathbb{Q}$.

::: mathlib
`Real.sq_sqrt` · `Mathlib.Analysis.Real.Sqrt`

`Real.sqrt x`, notation `√x`, has the junk value $0$ for $x < 0$, so `Real.sq_sqrt` needs `0 ≤ x`.

<?decl Real.sq_sqrt?>
:::

**Theorem (Monotone convergence).** In a complete ordered field, an increasing sequence $(a_n)$ that is bounded above converges to $L = \sup_n a_n$.

*Proof.* Let $\varepsilon > 0$. Since $L - \varepsilon$ is not an upper bound, some $a_N > L - \varepsilon$. For $n \geq N$, $L - \varepsilon < a_N \leq a_n \leq L$. $\square$

::: mathlib
`tendsto_atTop_ciSup` · `Mathlib.Topology.Order.MonotoneConvergence`

Mathlib states it with filters: `Tendsto f atTop (𝓝 (⨆ i, f i))` for a monotone `f` with `BddAbove (Set.range f)`.

<?decl tendsto_atTop_ciSup?>
:::

**Remark (Nested intervals).** If $a_n \leq a_{n+1} \leq b_{n+1} \leq b_n$, then $a_n \leq b_m$ for all $n, m$, so $c = \sup_n a_n$ lies in each $[a_n, b_n]$. In $\mathbb{Q}$ the decimal intervals around $\sqrt 2$ have an empty intersection.

**Remark (Uniqueness).** Each complete ordered field $F$ is isomorphic to $\mathbb{R}$ by a unique map that keeps the operations and the order: it sends $x$ to the supremum in $F$ of the rationals below $x$. So the choice of the construction does not change the theorems.

::: mathlib
`Archimedean.exists_orderAddMonoidHom_real_injective` · `Mathlib.Basic.Real.Embedding`

This is the theorem of Hölder: each archimedean linearly ordered abelian group embeds in `ℝ`. The map `Archimedean.embedReal` is the construction of the remark. The uniqueness of the complete ordered field is `ConditionallyCompleteLinearOrderedField.inducedOrderRingIso` in `Mathlib.Algebra.Order.CompleteField`.

<?decl Archimedean.exists_orderAddMonoidHom_real_injective?>
:::

### Examples

**Example (A supremum that is not in the set).** For $S = \{1 - 1/n : n \geq 1\}$, $1$ is an upper bound, and for $\varepsilon > 0$ and $n > 1/\varepsilon$, $1 - 1/n > 1 - \varepsilon$. So $\sup S = 1 \notin S$.

**Example (A field that is not archimedean).** In $\mathbb{Q}(t)$, let $f > 0$ if the leading coefficients of the numerator and the denominator have the same sign. Then $t > n$ for each $n$, so this ordered field is not archimedean, and $\mathbb{N}$ is bounded above by $t$ with no supremum.

**Example (Junk values of sSup).** In Mathlib, `sSup ∅ = 0` and `sSup (Set.range (fun n : ℕ => (n : ℝ))) = 0`. So $\sup S \leq a$ fails for $S = \emptyset$ and $a = -1$, which is why `Real.sSup_le` needs $0 \leq a$.

**Example (Lean).** The cast from `ℚ` to `ℝ` keeps the strict order.

<?lean MathlibHandbook/V02/C07/Examples.lean#ratCast_lt?>

### The library around it

`Mathlib.Algebra.Order.Archimedean.Real.Basic` has `Real.exists_isLUB`, `Real.sSup_def`, the junk values `Real.sSup_empty` and `Real.sSup_of_not_bddAbove`, the lemmas `Real.sSup_le` and `Real.sSup_nonneg`, `Real.add_neg_lt_sSup`, `Real.instArchimedean` and `Real.cauSeq_converges`. The general lemmas `le_csSup` and `csSup_le` apply through the instance. `Mathlib.Basic.Real.Pointwise` has `Real.sSup_smul_of_nonneg` and `Real.mul_iSup_of_nonneg`, and `Mathlib.Basic.Real.Embedding` has the embedding of Hölder.

### Exercises

1. (A) Find $\sup S$ and $\inf S$ for $S = \{(-1)^n / n : n \geq 1\}$. *Hint.* Compute the first terms.
2. (A) Give the values of `sSup (∅ : Set ℝ)`, `sSup (Set.univ : Set ℝ)` and `Real.sqrt (-4)`. *Hint.* `Set.univ` is not bounded above.
3. (B) Show that $\inf S = -\sup(-S)$ for a nonempty $S$ that is bounded below. *Hint.* $u$ is a lower bound of $S$ if and only if $-u$ is an upper bound of $-S$.
4. (B) Show that between $x < y$ there is an irrational number. *Hint.* Use the density of $\mathbb{Q}$ between $x/\sqrt 2$ and $y/\sqrt 2$.
5. (B) Show that each $a \geq 0$ has a square root in a complete ordered field. *Hint.* Use $S = \{x \geq 0 : x^2 < a\}$ and the upper bound $a + 1$.
6. (C) Show that each Cauchy sequence of real numbers converges. *Hint.* Apply monotone convergence to $b_n = \sup_{k \geq n} a_k$.
7. (C) Show that $\mathbb{R}$ is not countable. *Hint.* Given $x_1, x_2, \dots$, choose nested intervals $I_n$ of positive length with $x_n \notin I_n$.

### Notes and history

The least upper bound property is the completeness of Dedekind (1872). The archimedean axiom goes back to Eudoxus and Book V of Euclid. Hilbert gave the axioms of a complete ordered field in 1900, and Hölder proved the embedding theorem in 1901. In Mathlib, the completeness of `ℝ` is by Mario Carneiro, and the uniqueness of the complete ordered field by Alex J. Best and Yaël Dillies.

### Reference

<?reference?>
