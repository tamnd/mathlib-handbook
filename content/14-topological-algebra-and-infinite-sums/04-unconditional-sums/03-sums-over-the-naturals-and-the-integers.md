---
title: Sums over ℕ and ℤ
kind: theory
modules:
  - Mathlib.Topology.Algebra.InfiniteSum.NatInt
  - Mathlib.Topology.Algebra.InfiniteSum.ConditionalInt
explains:
  E3: [HasSum.tendsto_sum_nat, hasSum_nat_add_iff, HasSum.of_nat_of_neg_add_one, SummationFilter.symmetricIcc]
  E2: [Summable.hasSum_iff_tendsto_nat, Summable.tendsto_sum_tsum_nat, summable_nat_add_iff, Summable.sum_add_tsum_nat_add, Summable.tsum_eq_zero_add, HasSum.zero_add, HasSum.sum_range_add, tendsto_sum_nat_add, Summable.tendsto_atTop_zero, summable_iff_nat_tsum_vanishing, HasSum.even_add_odd, tsum_even_add_odd, HasSum.int_rec, HasSum.nat_add_neg, Summable.of_nat_of_neg, summable_int_iff_summable_nat_and_neg, tsum_of_nat_of_neg_add_one, tsum_int_eq_zero_add_tsum_pnat, Summable.alternating, SummationFilter.hasSum_symmetricIcc_iff, Summable.tendsto_zero_of_even_summable_symmetricIcc]
  E1: auto
families: []
requires: [V03, V13.C02, V15.C01, V14.C01]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Sums over ℕ and ℤ

### Overview

Most sums of analysis are indexed by $\mathbb{N}$ or by $\mathbb{Z}$. For these index types a reader wants the familiar tools: the partial sums $s_n = f(0) + \cdots + f(n-1)$, the first terms split off from the rest, the tails $\sum_{i \ge k} f(i)$, the terms that tend to $0$, and the sums over $\mathbb{Z}$ written as a sum over $n \ge 0$ and a sum over $n < 0$. This section proves these tools for the unconditional sum of Section 1 and the rules of Section 2.

The main results are three. An unconditional sum over $\mathbb{N}$ is the limit of the partial sums. Splitting off finitely many terms preserves summability in a topological group, and the tails of a sum tend to $0$. A family on $\mathbb{Z}$ is summable exactly when its restrictions to the nonnegative and to the negative integers are summable, in a complete group. The section ends with the symmetric sums $\lim_N \sum_{n=-N}^{N} f(n)$, which Mathlib treats as the sums for a summation filter.

### Definitions

The section introduces no new notion of sum. It names two classical objects in the language of Section 1.

**Definition (Partial sums and tails).** Let $f : \mathbb{N} \to M$. The $n$-th *partial sum* is $s_n = \sum_{i < n} f(i)$, the sum over the finite set $\{0, \dots, n-1\}$, written `Finset.range n` in Mathlib. For $k \in \mathbb{N}$ the *shifted family* is $n \mapsto f(n + k)$, and its sum $\sum'_{n} f(n + k)$ is the $k$-th *tail*.

**Definition (Symmetric sum over ℤ).** Let $f : \mathbb{Z} \to M$. The family has the *symmetric sum* $a$ if $\sum_{n=-N}^{N} f(n) \to a$ as $N \to \infty$. This is the sum for the summation filter on the finite subsets of $\mathbb{Z}$ that is the image of $\mathrm{atTop}$ under $N \mapsto [-N, N]$.

::: mathlib
`SummationFilter.symmetricIcc` · `Mathlib.Topology.Algebra.InfiniteSum.ConditionalInt`

The filter of symmetric intervals `Finset.Icc (-N) N`, defined on any locally finite order with a negation. The lemma `SummationFilter.hasSum_symmetricIcc_iff` turns `HasSum f a (SummationFilter.symmetricIcc ℤ)` into the limit of the sums over `Finset.Icc (-N) N`. The module has the variants `symmetricIco`, `symmetricIoc` and `symmetricIoo`, with lemmas that compare them.

<?decl SummationFilter.symmetricIcc?>
:::

### Theorems and proofs

**Theorem (Partial sums).** Let $M$ be a commutative topological monoid and $f : \mathbb{N} \to M$ with the sum $a$. Then $s_n \to a$.

*Proof.* The map $n \mapsto \{0, \dots, n-1\}$ from $\mathbb{N}$ to the finite subsets of $\mathbb{N}$ tends to $\mathrm{atTop}$: for each finite $F_0$ choose $N$ larger than all elements of $F_0$; then $\{0, \dots, n-1\} \supseteq F_0$ for all $n \ge N$. The function $F \mapsto S_F$ tends to $a$ along $\mathrm{atTop}$. The composition of the two limits gives $s_n \to a$. $\square$

The converse is false: the alternating harmonic series of Section 1 has convergent partial sums and no sum. It holds for a family that is already known to be summable, if $M$ is Hausdorff: if $f$ is summable and $s_n \to b$, then $s_n \to \sum' f$ by the theorem, so $b = \sum' f$.

::: mathlib
`HasSum.tendsto_sum_nat` · `Mathlib.Topology.Algebra.InfiniteSum.NatInt`

The conclusion is `Tendsto (fun n ↦ ∑ i ∈ Finset.range n, f i) atTop (𝓝 m)`, with no hypothesis on `M` beyond a topology and a commutative monoid. The equivalence for a summable family is `Summable.hasSum_iff_tendsto_nat`, and the form with `tsum` is `Summable.tendsto_sum_tsum_nat`.

<?decl HasSum.tendsto_sum_nat?>
:::

**Theorem (Splitting off the first terms).** Let $G$ be a commutative topological group, $f : \mathbb{N} \to G$, $k \in \mathbb{N}$ and $g \in G$. Then $n \mapsto f(n + k)$ has the sum $g$ if and only if $f$ has the sum $g + s_k$. In particular $f$ is summable if and only if $n \mapsto f(n + k)$ is summable, and then
$$\sum'_{n} f(n) = \sum_{i < k} f(i) + \sum'_{n} f(n + k).$$

*Proof.* Let $h(n) = f(n)$ for $n \ge k$ and $h(n) = 0$ for $n < k$. The map $\tau(n) = n + k$ is injective, its image is $\{n : n \ge k\}$, and $h$ vanishes outside the image. By the reindexing theorem of Section 1, $h \circ \tau$ has the sum $g$ if and only if $h$ has the sum $g$. But $h \circ \tau$ is the shifted family $n \mapsto f(n + k)$.

The family $f - h$ is $f(i)$ for $i < k$ and $0$ for $i \ge k$. It has finite support, so it has the sum $s_k$. If $h$ has the sum $g$, then $f = h + (f - h)$ has the sum $g + s_k$ by additivity. If $f$ has the sum $g + s_k$, then $h = f - (f - h)$ has the sum $g$, by the rule for differences in a topological group. The statement on `tsum` follows by uniqueness. $\square$

In a monoid without subtraction only one direction remains: if the shifted family has the sum $g$, then $f$ has the sum $s_k + g$. Mathlib calls it `HasSum.sum_range_add`, and for $k = 1$ `HasSum.zero_add`.

::: mathlib
`hasSum_nat_add_iff` · `Mathlib.Topology.Algebra.InfiniteSum.NatInt`

The statement `HasSum (fun n ↦ f (n + k)) g ↔ HasSum f (g + ∑ i ∈ range k, f i)` for `[IsTopologicalAddGroup G]`. The summability form is `summable_nat_add_iff`, and the equation of `tsum` is `Summable.sum_add_tsum_nat_add`, which needs `[T2Space G]`. The case $k = 1$ is `Summable.tsum_eq_zero_add`: `∑' b, f b = f 0 + ∑' b, f (b + 1)`.

<?decl hasSum_nat_add_iff?>
:::

**Corollary (Tails and terms).** Let $G$ be a Hausdorff commutative topological group and $f : \mathbb{N} \to G$.

1. The tails tend to $0$: $\sum'_{n} f(n + k) \to 0$ as $k \to \infty$.
2. If $f$ is summable, then $f(n) \to 0$ as $n \to \infty$.

*Proof.* (1) If $f$ is summable, the theorem gives $\sum'_n f(n + k) = \sum' f - s_k$, and $s_k \to \sum' f$, so the difference tends to $0$. If $f$ is not summable, then no shifted family is summable, by the theorem, so each tail is the junk value $0$, and the sequence of tails is constant $0$.

(2) By Section 2 the terms tend to $0$ along the cofinite filter. On $\mathbb{N}$ the cofinite filter is $\mathrm{atTop}$, since a set contains all but finitely many $n$ exactly when it contains a tail $\{n : n \ge N\}$. $\square$

Part 1 shows how the junk value works. The statement is true for every $f$, and for a family that is not summable it is true for a reason that says nothing about $f$.

::: mathlib
`tendsto_sum_nat_add` · `Mathlib.Topology.Algebra.InfiniteSum.NatInt`

Part 1, with no summability hypothesis, exactly as in the proof. Part 2 is `Summable.tendsto_atTop_zero`. The criterion of Cauchy in terms of tails is `summable_iff_nat_tsum_vanishing`.

<?decl tendsto_sum_nat_add?>
:::

**Theorem (Sums over ℤ).** Let $M$ be a commutative topological monoid with continuous addition and $f : \mathbb{Z} \to M$. If $n \mapsto f(n)$, for $n \in \mathbb{N}$, has the sum $m$, and $n \mapsto f(-(n+1))$, for $n \in \mathbb{N}$, has the sum $m'$, then $f$ has the sum $m + m'$. If $M$ is a complete group, then $f$ is summable if and only if both restrictions are summable.

*Proof.* Let $P = \{n \in \mathbb{Z} : n \ge 0\}$ and $Q = \{n : n < 0\}$, so $Q$ is the complement of $P$. The maps $\iota(n) = n$ and $\kappa(n) = -(n+1)$ from $\mathbb{N}$ are bijections onto $P$ and onto $Q$. By reindexing (Section 1), the restriction $f|_P$ has the sum $m$ and $f|_Q$ has the sum $m'$. By the rule for a set and its complement (Section 2), $f$ has the sum $m + m'$.

For the second claim, assume that $f$ is summable in a complete group. The restrictions to $P$ and to $Q$ are summable by the corollary on subfamilies of Section 2, and so are their reindexed forms. The converse is the first part. $\square$

::: mathlib
`HasSum.of_nat_of_neg_add_one` · `Mathlib.Topology.Algebra.InfiniteSum.NatInt`

The first part. The `tsum` form is `tsum_of_nat_of_neg_add_one`. The forms with $n \mapsto f(-n)$ in place of $f(-(n+1))$ count $f(0)$ twice: `HasSum.nat_add_neg` gives the sum `m + f 0` for the family `f n + f (-n)`. The equivalence in a complete group is `summable_int_iff_summable_nat_and_neg`, and `tsum_int_eq_zero_add_tsum_pnat` writes the sum as `f 0` plus two sums over the positive integers `ℕ+`.

<?decl HasSum.of_nat_of_neg_add_one?>
:::

### Examples

**Example (A two-sided geometric sum).** Let $f(n) = 2^{-|n|}$ on $\mathbb{Z}$. On $n \ge 0$ the family is $2^{-n}$, with the sum $2$ (Volume 15, Chapter 1). On the negative integers, $f(-(n+1)) = 2^{-(n+1)}$, with the sum $1$. The theorem on sums over $\mathbb{Z}$ gives $\sum'_{n \in \mathbb{Z}} 2^{-|n|} = 3$.

**Example (Even and odd terms).** The value $\sum_{n \ge 1} 1/n^2 = \pi^2/6$ is proved in Mathlib (`hasSum_zeta_two`). Split $\mathbb{N}$ into the even and the odd numbers. The even terms are $\frac{1}{(2k)^2} = \frac14 \cdot \frac{1}{k^2}$, with the sum $\frac14 \cdot \frac{\pi^2}{6} = \frac{\pi^2}{24}$. The odd terms are summable, as a subfamily of a summable family in the complete group $\mathbb{R}$. By the rule for even and odd terms,
$$\sum_{k \ge 0} \frac{1}{(2k+1)^2} = \frac{\pi^2}{6} - \frac{\pi^2}{24} = \frac{\pi^2}{8}.$$

::: mathlib
`hasSum_zeta_two` · `Mathlib.NumberTheory.ZetaValues`

The statement `HasSum (fun n : ℕ ↦ 1 / (n : ℝ) ^ 2) (π ^ 2 / 6)`. The family starts at $n = 0$, where $1 / 0^2 = 0$ by the convention $x / 0 = 0$ of Mathlib, so the junk term adds nothing. The rule for even and odd terms is `HasSum.even_add_odd`, with `tsum_even_add_odd`.

<?decl hasSum_zeta_two?>
<?decl HasSum.even_add_odd?>
:::

**Example (A symmetric sum that is not a sum).** Let $f(n) = n$ on $\mathbb{Z}$. For each $N$, $\sum_{n=-N}^{N} n = 0$, so the symmetric sum is $0$. The family is not summable, since its terms do not tend to $0$, and its restriction to $\mathbb{N}$ has no sum. So the hypothesis of the theorem on $\mathbb{Z}$ is needed: a symmetric sum gives no information on the two halves. For an even family, $f(-n) = f(n)$, the symmetric sums are $f(0) + 2 \sum_{n=1}^{N} f(n)$, and their convergence forces $f(n) \to 0$; this is `Summable.tendsto_zero_of_even_summable_symmetricIcc` for normed groups.

**Remark (Common errors).** The partial sum `∑ i ∈ Finset.range n, f i` stops at $n - 1$, not at $n$. A reader who expects $s_n = f(0) + \cdots + f(n)$ makes an error of one term in each formula with tails. A second error is to apply `hasSum_nat_add_iff` in a monoid such as $[0, \infty]$: the lemma needs a group, and the monoid form is `HasSum.sum_range_add`, which has only one direction. A third error is to treat the integers $-n$ for $n \in \mathbb{N}$ as the negative integers: they include $0$.

### The library around it

The module `Mathlib.Topology.Algebra.InfiniteSum.NatInt` has four groups of lemmas. The first relates sums over `ℕ` to partial sums over `Finset.range`. The second shifts the index: `hasSum_nat_add_iff`, `summable_nat_add_iff`, `Summable.sum_add_tsum_nat_add`, the tails `tendsto_sum_nat_add`, and the versions over the positive integers `ℕ+` such as `tsum_pnat_eq_tsum_succ`. The third splits `ℕ` into even and odd numbers. The fourth treats `ℤ`, with the pairs of names `of_nat_of_neg_add_one` (the halves $n \ge 0$ and $n < 0$) and `of_nat_of_neg` (the halves $n \ge 0$ and $n \le 0$). The module `Mathlib.Topology.Algebra.InfiniteSum.ConditionalInt` defines the symmetric summation filters on `ℤ` and compares the sums over $[-N, N]$, $[-N, N)$, $(-N, N]$ and $(-N, N)$. Each lemma has a multiplicative twin for products.

The reference table at the end of the section lists the declarations of the two modules.

### Exercises

1. (A) Compute $\sum'_{n \in \mathbb{Z}} 3^{-|n|}$. *Hint:* the answer is $2$.
2. (A) Let $f : \mathbb{N} \to \mathbb{R}$ be summable. Show that $\sum'_n f(n+1) = \sum'_n f(n) - f(0)$.
3. (A) Show that $\sum_{k \ge 0} \frac{1}{(2k+2)^2} = \frac{\pi^2}{24}$ from `hasSum_zeta_two`, and say where the term $n = 0$ goes.
4. (B) Let $f : \mathbb{N} \to \mathbb{R}$ be summable. Show that $\sum'_{n} (f(n) - f(n+1)) = f(0)$. *Hint:* the rule for differences and the shift theorem.
5. (B) Show that the symmetric sum of $f(n) = 1/n$ for $n \ne 0$, $f(0) = 0$, is $0$, and that the family is not summable.
6. (B) Let $G$ be a commutative topological group and $f : \mathbb{N} \to G$. Show that if $n \mapsto f(2n)$ and $n \mapsto f(2n+1)$ are summable, then $f$ is summable. Is the converse true in $\mathbb{R}$? In $\mathbb{Q}$?
7. (B) Compute $\sum_{n \ge 1} \frac{(-1)^{n+1}}{n^2}$ from $\zeta(2) = \pi^2/6$. *Hint:* odd minus even terms; the answer is $\pi^2/12$.
8. (C) Show that the conditional summation filter on $\mathbb{Z}$ of Section 1, with independent ends, and the symmetric filter of this section give different sums for $f(n) = \operatorname{sign}(n)$, and that the first gives no sum at all.

### Notes and history

Two-sided sums over $\mathbb{Z}$ appear in the theory of Fourier series and of theta functions. Symmetric sums over $[-N, N]$ give a meaning to some sums over $\mathbb{Z}$ that do not converge absolutely.

### Reference

<?reference?>
