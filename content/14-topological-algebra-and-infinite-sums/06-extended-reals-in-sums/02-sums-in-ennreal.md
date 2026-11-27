---
title: Sums in the extended nonnegative reals
kind: theory
modules:
  - Mathlib.Topology.Algebra.InfiniteSum.ENNReal
explains:
  E3: [ENNReal.tsum_coe_ne_top_iff_summable, ENNReal.ofReal_tsum_of_nonneg, ENNReal.tsum_eq_iSup_nat, ENNReal.tsum_mul_left, hasSum_iff_tendsto_nat_of_nonneg]
  E2: [ENNReal.hasSum_coe, ENNReal.coe_tsum, ENNReal.tsum_coe_eq, ENNReal.tsum_coe_eq_top_iff_not_summable_coe, ENNReal.tendsto_nat_tsum, ENNReal.hasSum_iff_tendsto_nat, ENNReal.tsum_le_of_sum_range_le, ENNReal.tsum_mul_right, ENNReal.tsum_const, ENNReal.tsum_const_eq_top_of_ne_zero, ENNReal.tsum_set_const, ENNReal.tsum_top, ENNReal.tsum_sub, ENNReal.tsum_toReal_eq, ENNReal.summable_toReal, ENNReal.summable_toNNReal_of_tsum_ne_top, ENNReal.finite_const_le_of_tsum_ne_top, ENNReal.tendsto_cofinite_zero_of_tsum_ne_top, ENNReal.tendsto_tsum_compl_atTop_zero, Summable.countable_support_ennreal, ENNReal.tsum_lt_tsum, ENNReal.tsum_eq_liminf_sum_nat, ENNReal.tsum_apply, Summable.of_nonneg_of_le, NNReal.summable_of_le, Summable.toNNReal, Summable.tsum_ofReal_lt_top, cauchySeq_of_edist_le_of_tsum_ne_top]
  E1: auto
families: []
requires: [V04, V13, V14.C04, V14.C05]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Sums in the extended nonnegative reals

### Overview

In `ℝ≥0∞` every family has a sum. A family that diverges in $\mathbb{R}$ has the sum $\infty$, and the sum of a family is the supremum of its finite sums. Two summations can be exchanged with no condition, as in the theorem of Tonelli for integrals. Scalars come out of a sum with no condition. These facts make `ℝ≥0∞` the natural home of sums in measure theory, where the measure of a countable disjoint union is the sum of the measures, finite or not.

This section proves these facts and relates sums in `ℝ≥0∞` to sums in `ℝ≥0` and $\mathbb{R}$. The main link is simple: a family of finite values has a finite sum in `ℝ≥0∞` exactly when it is summable in `ℝ≥0`. It also proves that for a nonnegative real sequence the unconditional sum and the limit of the partial sums agree, so that the classical tests for series of positive terms apply directly to `HasSum`.

### Definitions

The type `ℝ≥0∞` is a complete lattice. Its addition is canonically ordered: $a \le b$ holds exactly when $b = a + c$ for some $c$. Its topology is the order topology of a linear order, so monotone nets converge to their suprema. These are the hypotheses of the theorem on sums in a complete lattice of Section 5.1. So every family $f : I \to [0, \infty]$ has the sum
$$\sum' f = \sup_{F \text{ finite}} \sum_{i \in F} f_i .$$
The older names `ENNReal.summable`, `ENNReal.hasSum`, `ENNReal.tsum_eq_iSup_sum`, `ENNReal.tsum_comm` and `ENNReal.tsum_sigma` are deprecated. Their replacements are the lattice lemmas `CompleteLattice.summable`, `CompleteLattice.hasSum`, `tsum_eq_iSup_sum`, `tsum_comm` and `tsum_sigma`, with no namespace.

The inclusions $\mathbb{R}_{\ge 0} \to [0, \infty]$, $r \mapsto \uparrow r$, and $\mathbb{R} \to [0, \infty]$, $x \mapsto \mathrm{ofReal}(x) = \uparrow \max(x, 0)$, and the maps `toNNReal` and `toReal` back, with $\infty \mapsto 0$, are those of Section 1.

::: mathlib
`CompleteLattice.summable` · `Mathlib.Topology.Algebra.InfiniteSum.Order`

The statement `Summable f` for every `f : ι → α`, with `CompleteLattice α`, `CanonicallyOrderedAdd α` and `SupConvergenceClass α`. For `α = ℝ≥0∞` the instances are found automatically. The formula `tsum_eq_iSup_sum` is `∑' x, f x = ⨆ s, ∑ a ∈ s, f a`.

<?decl CompleteLattice.summable?>
<?decl tsum_eq_iSup_sum?>
:::

### Theorems and proofs

**Theorem (Sums over ℕ).** For $f : \mathbb{N} \to [0, \infty]$, $\sum' f = \sup_n \sum_{i < n} f_i$, and the partial sums tend to $\sum' f$.

*Proof.* Every partial sum is a finite sum, so it is at most the supremum of all finite sums. Conversely every finite $F \subseteq \mathbb{N}$ lies in some $\{0, \dots, n-1\}$, and $S_F \le s_n$ since the terms are nonnegative. So the two suprema agree. The partial sums form a monotone sequence, which converges to its supremum in the order topology. $\square$

::: mathlib
`ENNReal.tsum_eq_iSup_nat` · `Mathlib.Topology.Algebra.InfiniteSum.ENNReal`

The statement `∑' i, f i = ⨆ i, ∑ a ∈ Finset.range i, f a`. The limit form is `ENNReal.tendsto_nat_tsum`, the criterion `ENNReal.hasSum_iff_tendsto_nat`, and the bound `ENNReal.tsum_le_of_sum_range_le`. The value is also a `liminf`, `ENNReal.tsum_eq_liminf_sum_nat`.

<?decl ENNReal.tsum_eq_iSup_nat?>
:::

**Theorem (Exchange of summations).** For $f : \Sigma_{i \in I} J_i \to [0, \infty]$, $\sum'_{(i, j)} f(i, j) = \sum'_i \sum'_j f(i, j)$. In particular $\sum'_i \sum'_j g(i, j) = \sum'_j \sum'_i g(i, j)$ for $g : I \times J \to [0, \infty]$.

*Proof.* Write $T_i = \sum'_j f(i, j)$. For the inequality $\le$, let $F$ be a finite subset of the sigma type. Let $A$ be the finite set of first coordinates of $F$, and for $i \in A$ let $G_i$ be the set of $j$ with $(i, j) \in F$. Then
$$S_F = \sum_{i \in A} \sum_{j \in G_i} f(i, j) \le \sum_{i \in A} T_i \le \sum'_i T_i .$$
Take the supremum over $F$. For the inequality $\ge$, fix a finite $A \subseteq I$. For each $i \in A$, $T_i$ is the supremum of the directed family of finite sums over $G \subseteq J_i$. Addition on `ℝ≥0∞` is continuous and monotone, so a finite sum of suprema of directed families is the supremum of the sums: $\sum_{i \in A} T_i = \sup_{(G_i)} \sum_{i \in A} \sum_{j \in G_i} f(i, j)$, over the tuples of finite sets. Each sum on the right is the finite sum of $f$ over $\bigcup_{i \in A} \{i\} \times G_i$, so it is at most $\sum' f$. Take the supremum over $A$. The statement for $I \times J$ follows by applying the first to the two ways of writing $I \times J$ as a sigma type. $\square$

The comparison with Chapter 4 is instructive. In a group the same exchange needs the summability of $f$, and Section 4.2 gave a family of reals whose iterated sums differ. In `ℝ≥0∞` no such hypothesis is needed.

::: mathlib
`tsum_sigma` · `Mathlib.Topology.Algebra.InfiniteSum.Order`

The lattice form `∑' p : Σ i, β i, f p.1 p.2 = ∑' i, ∑' j, f i j`, with `ContinuousAdd α` and `T3Space α`. The exchange of two summations is `tsum_comm`, and the form over a product is `tsum_prod`. These replace the deprecated `ENNReal.tsum_sigma`, `ENNReal.tsum_comm` and `ENNReal.tsum_prod`.

<?decl tsum_sigma?>
<?decl tsum_comm?>
:::

**Theorem (Scalars).** For $a \in [0, \infty]$ and $f : I \to [0, \infty]$, $\sum' a f_i = a \sum' f$.

*Proof.* For each finite $F$, $\sum_{i \in F} a f_i = a S_F$. Multiplication by $a$ is monotone. If $a$ is finite, it is continuous, so it commutes with the supremum of the directed family $(S_F)$. If $a = \infty$, both sides are $0$ when all $f_i = 0$, and both are $\infty$ otherwise, since a single term $a f_i = \infty$ with $f_i \ne 0$ makes the left side infinite. $\square$

**Theorem (Finite sums and summability).** Let $f : I \to \mathbb{R}_{\ge 0}$. Then $\sum' \uparrow f_i \ne \infty$ in `ℝ≥0∞` exactly when $f$ is summable in `ℝ≥0`. Then $\uparrow \sum' f = \sum' \uparrow f$.

*Proof.* If $f$ has the sum $r$ in `ℝ≥0`, the inclusion is continuous and additive, so $\uparrow f$ has the sum $\uparrow r$, which is finite. Conversely let $\sum' \uparrow f = a \ne \infty$, and write $a = \uparrow c$. Every finite sum satisfies $\uparrow S_F \le a$, so $S_F \le c$ in `ℝ≥0`. Then the reals $f_i$ have bounded finite sums, so they are summable in $\mathbb{R}$ by Section 5.1, and $f$ is summable in `ℝ≥0` by Section 1. The formula follows from the first part and the uniqueness of sums. $\square$

::: mathlib
`ENNReal.tsum_coe_ne_top_iff_summable` · `Mathlib.Topology.Algebra.InfiniteSum.ENNReal`

The statement `∑' b, (f b : ℝ≥0∞) ≠ ⊤ ↔ Summable f`, for `f : β → ℝ≥0`. The other forms are `ENNReal.tsum_coe_eq_top_iff_not_summable_coe`, `ENNReal.hasSum_coe` and `ENNReal.coe_tsum`. For a family with values in `ℝ≥0∞`, a finite sum gives summability of the real parts, `ENNReal.summable_toReal` and `ENNReal.summable_toNNReal_of_tsum_ne_top`.

<?decl ENNReal.tsum_coe_ne_top_iff_summable?>
:::

**Theorem (Real sums).** Let $f : I \to \mathbb{R}$ be nonnegative and summable. Then $\mathrm{ofReal}(\sum' f) = \sum' \mathrm{ofReal}(f_i)$.

*Proof.* Let $g_i = \max(f_i, 0) = f_i$ in `ℝ≥0`, so that $\mathrm{ofReal}(f_i) = \uparrow g_i$. The family $g$ is summable in `ℝ≥0` by Section 1, with $\uparrow \sum' g = \sum' f$ in $\mathbb{R}$. By the previous theorem $\sum' \uparrow g = \uparrow \sum' g = \mathrm{ofReal}(\sum' f)$. $\square$

::: mathlib
`ENNReal.ofReal_tsum_of_nonneg` · `Mathlib.Topology.Algebra.InfiniteSum.ENNReal`

The hypotheses `∀ n, 0 ≤ f n` and `Summable f`. The reverse transfer is `ENNReal.tsum_toReal_eq`, `(∑' a, f a).toReal = ∑' a, (f a).toReal`, under `∀ a, f a ≠ ⊤`. A nonnegative summable real family has a finite sum in `ℝ≥0∞`, `Summable.tsum_ofReal_lt_top`.

<?decl ENNReal.ofReal_tsum_of_nonneg?>
:::

**Theorem (Nonnegative real sequences).** Let $f : \mathbb{N} \to \mathbb{R}$ be nonnegative and $r \in \mathbb{R}$. Then $f$ has the sum $r$ exactly when $\sum_{i < n} f_i \to r$.

*Proof.* The forward direction holds for every family, by Section 4.3. Conversely, suppose $s_n \to r$. The sequence $(s_n)$ is monotone, so $s_n \le r$ for all $n$. Each finite $F$ lies in some $\{0, \dots, n-1\}$, so $S_F \le s_n \le r$. By Section 5.1 the family $f$ is summable, and its sum is the limit of $(s_n)$ by Section 4.3, that is, $r$. $\square$

So for nonnegative real terms the series of a first course and the unconditional sum of Mathlib agree, and every test of Volume 15, Chapter 1, for series of positive terms gives a statement about `HasSum`.

::: mathlib
`hasSum_iff_tendsto_nat_of_nonneg` · `Mathlib.Topology.Algebra.InfiniteSum.ENNReal`

The statement `HasSum f r ↔ Tendsto (fun n ↦ ∑ i ∈ Finset.range n, f i) atTop (𝓝 r)`, for `f : ℕ → ℝ` with `∀ i, 0 ≤ f i`. The comparison test `Summable.of_nonneg_of_le` and its form `NNReal.summable_of_le` in `ℝ≥0` live in the same module.

<?decl hasSum_iff_tendsto_nat_of_nonneg?>
:::

### Examples

**Example (The harmonic sum).** In `ℝ≥0∞`, $\sum_{n \ge 1} 1/n = \infty$. By Section 5.1 the partial sums are unbounded, and by the theorem on sums over $\mathbb{N}$ the sum is their supremum. In $\mathbb{R}$ the same family has the junk sum $0$. The value $\infty$ carries the information that the real `tsum` loses.

**Example (Constant families).** For $c \in [0, \infty]$, $\sum'_{x \in I} c = |I| \cdot c$, where $|I| \in \mathbb{N} \cup \{\infty\}$ is the cardinality (`ENNReal.tsum_const`). For a set $s$ the form is `ENNReal.tsum_set_const`. In particular a nonzero constant has the sum $\infty$ on an infinite type (`ENNReal.tsum_const_eq_top_of_ne_zero`). The function $s \mapsto \sum'_{x \in s} 1$ is the counting measure of Volume 18.

**Example (A counterexample: transfer from ℝ).** The theorem on real sums needs both hypotheses. Let $f(n) = 1$ for all $n$. Then $f$ is not summable in $\mathbb{R}$, so $\mathrm{ofReal}(\sum' f) = \mathrm{ofReal}(0) = 0$, while $\sum' \mathrm{ofReal}(f_n) = \infty$. Let $g = (1, -1, 0, 0, \dots)$. Then $g$ is summable with $\sum' g = 0$, while $\sum' \mathrm{ofReal}(g_n) = 1$, since $\mathrm{ofReal}(-1) = 0$.

**Remark (Common errors).** The subtraction of sums `ENNReal.tsum_sub` needs $\sum' g \ne \infty$ and $g \le f$. The strict inequality `ENNReal.tsum_lt_tsum` needs $\sum' f \ne \infty$: if both sums are $\infty$, a strict inequality of one term gives no strict inequality of sums. A proof that moves between `ℝ≥0∞` and $\mathbb{R}$ must check finiteness at each step, since `toReal` sends $\infty$ to $0$.

### The library around it

The module `Mathlib.Topology.Algebra.InfiniteSum.ENNReal` has three groups of results. The first treats sums in `ℝ≥0∞`. Many older lemmas of this group are deprecated in favour of the lattice lemmas of `Mathlib.Topology.Algebra.InfiniteSum.Order`. The second treats `ℝ≥0`: comparison, strict monotonicity, and sums over sigma types. The third returns to $\mathbb{R}$: the comparison test `Summable.of_nonneg_of_le`, the criterion `hasSum_iff_tendsto_nat_of_nonneg` and the transfers to `ℝ≥0∞`. The module also proves that products of factors at most $1$ are multipliable in `ℝ≥0∞`, which Chapter 7 uses.

### Exercises

1. (A) Compute $\sum_{n \ge 0} 2^{-n}$ and $\sum_{n \ge 0} 2^n$ in `ℝ≥0∞`.
2. (A) Show that $\sum'_{x \in I} 0 = 0$ and $\sum'_{x \in I} \infty = \infty$ for $I$ nonempty.
3. (A) Let $f, g : I \to [0, \infty]$. Show that $\sum' (f + g) = \sum' f + \sum' g$ with no hypothesis.
4. (B) Let $a : \mathbb{N} \times \mathbb{N} \to [0, \infty]$, $a(m, n) = 2^{-m-n}$. Compute $\sum' a$ by exchange of summations. *Hint:* the answer is $4$.
5. (B) Show that if $\sum' f \ne \infty$ in `ℝ≥0∞`, then $f_i \ne \infty$ for every $i$, and $f_i \to 0$ along the cofinite filter.
6. (B) Give $f, g : \mathbb{N} \to [0, \infty]$ with $f \le g$, $f_0 < g_0$, and $\sum' f = \sum' g$.
7. (C) Let $(A_n)$ be subsets of a set $X$ and $c(s) = \sum'_{x \in s} 1$ in `ℝ≥0∞`. Show that $c(\bigcup_n A_n) \le \sum'_n c(A_n)$, with equality when the $A_n$ are pairwise disjoint. *Hint:* the exchange of summations for the indicator functions.

### Notes and history

The use of $[0, \infty]$ as the range of a measure goes back to the founders of measure theory at the start of the twentieth century. In this setting the interchange of two sums of nonnegative terms is the discrete case of the theorem of Tonelli. Mathlib first stated these results in the namespace `ENNReal` and later moved them to complete lattices, which explains the deprecated names.

### Reference

<?reference?>
