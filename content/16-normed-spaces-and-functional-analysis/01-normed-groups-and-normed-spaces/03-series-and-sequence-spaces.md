---
title: Series and the sequence spaces
kind: theory
modules:
  - Mathlib.Analysis.Normed.Group.InfiniteSum
  - Mathlib.Analysis.Normed.Group.Completeness
  - Mathlib.Analysis.Normed.Lp.lpSpace
explains:
  E3: [Summable.of_norm, NormedAddCommGroup.completeSpace_of_summable_imp_tendsto, Memℓp, lp, lp.completeSpace]
  E2: [Summable.of_norm_bounded, norm_tsum_le_tsum_norm, NormedAddCommGroup.summable_imp_tendsto_iff_completeSpace, memℓp_infty_iff, memℓp_gen_iff, lp.norm_eq_tsum_rpow, lp.norm_eq_ciSup, lp.norm_apply_le_norm, lp.single]
  E1: auto
families: []
requires: [V02, V07, V13, V15]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Series and the sequence spaces

### Overview

Volume 15 proves that an absolutely convergent series of real numbers converges. The proof uses only two facts: the triangle inequality and the completeness of $\mathbb{R}$. So the theorem holds in any complete normed group, and it characterizes completeness: a normed group is complete if and only if each absolutely convergent series in it converges. This criterion is the standard way to prove that a normed space is complete, and Chapter 2 uses it for the space of bounded operators. The section then builds the sequence spaces $\ell^p$ for $1 \le p \le \infty$, the first examples of infinite dimensional complete normed spaces, and shows that the space of finitely supported sequences is not complete.

### Definitions

**Definition (Convergent and absolutely convergent series).** Let $(x_n)_{n \ge 0}$ be a sequence in a seminormed group $E$, and $s_N = \sum_{n < N} x_n$ its partial sums. The series $\sum x_n$ *converges* to $s$ if $s_N \to s$. It *converges absolutely* if $\sum \|x_n\| < \infty$, that is, the real series of the norms converges.

Mathlib uses a different notion as the default: unconditional summation. The family $(x_i)_{i \in I}$ has the sum $s$ if the finite partial sums $\sum_{i \in F} x_i$ tend to $s$ along the filter of finite subsets $F$ of $I$, ordered by inclusion (Volume 13, Chapter 2). For a sequence this means that each rearrangement converges to $s$. In $\mathbb{R}$ and in each finite dimensional space, unconditional convergence is the same as absolute convergence, by the theorem of Riemann on rearrangements (Volume 15, Chapter 1). In infinite dimension it is weaker: in $\ell^2$ the series $\sum_n e_n / n$ of Example 3 below converges unconditionally but not absolutely.

::: mathlib
`Summable.of_norm` · `Mathlib.Analysis.Normed.Group.InfiniteSum`

In a complete seminormed group, `(Summable fun a ↦ ‖f a‖) → Summable f`, for a family `f : ι → E` over any index type. The predicates `Summable f` and `HasSum f a` of `Mathlib.Topology.Algebra.InfiniteSum.Defs` (Volume 14) have an optional argument, a `SummationFilter`, whose default value is the unconditional one. So `Summable f` without this argument is the unconditional notion of the text.

<?decl Summable.of_norm?>
:::

**Definition (The spaces $\ell^p$).** Let $I$ be a set and $1 \le p < \infty$. The space $\ell^p(I)$ is the set of functions $f : I \to \mathbb{K}$ (with $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$) with $\sum_{i \in I} |f(i)|^p < \infty$, with the norm
$$\|f\|_p = \Bigl(\sum_{i \in I} |f(i)|^p\Bigr)^{1/p}.$$
The space $\ell^\infty(I)$ is the set of bounded functions with $\|f\|_\infty = \sup_i |f(i)|$. For $I = \mathbb{N}$ write $\ell^p$.

A sum over a set $I$ of nonnegative terms is the supremum of its finite partial sums, so the definition needs no order on $I$. For finite $I$ this is $K^n$ with the $p$-norm of Section 2. The Minkowski inequality for finite sums (Section 2) gives the triangle inequality: for each finite $F \subseteq I$,
$$\Bigl(\sum_{i \in F} |f(i) + g(i)|^p\Bigr)^{1/p} \le \Bigl(\sum_{i \in F} |f(i)|^p\Bigr)^{1/p} + \Bigl(\sum_{i \in F} |g(i)|^p\Bigr)^{1/p} \le \|f\|_p + \|g\|_p,$$
and the supremum over $F$ gives $f + g \in \ell^p$ with $\|f + g\|_p \le \|f\|_p + \|g\|_p$. Homogeneity is clear. So $\ell^p(I)$ is a normed space.

::: mathlib
`Memℓp` · `Mathlib.Analysis.Normed.Lp.lpSpace`

`Memℓp f p` for `f : (i : α) → E i` and `p : ℝ≥0∞` is defined by three cases: for `p = 0` the support of `f` is finite, for `p = ∞` the norms are bounded above, and otherwise `Summable fun i ↦ ‖f i‖ ^ p.toReal`. The lemmas `memℓp_infty_iff` and `memℓp_gen_iff` unfold the last two cases. The values `E i` may be any normed groups, not only scalars, so `ℓ^p` of a family of normed spaces is covered.

<?decl Memℓp?>
:::

::: mathlib
`lp` · `Mathlib.Analysis.Normed.Lp.lpSpace`

`lp E p` is the `AddSubgroup` of the functions with `Memℓp f p`, so an element is a subtype element `f : lp E p` with a coercion to a function. The norm is given by `lp.norm_eq_tsum_rpow` for `0 < p.toReal` and by `lp.norm_eq_ciSup` for `p = ∞`. The instance `lp.normedAddCommGroup` needs `[Fact (1 ≤ p)]`. The unit vectors are `lp.single p i a`, the function with value `a` at `i` and `0` elsewhere.

<?decl lp?>
:::

### Theorems and proofs

**Theorem (Absolute convergence).** Let $E$ be a complete seminormed group. If $\sum \|x_n\| < \infty$, then $\sum x_n$ converges, and
$$\Bigl\|\sum_{n=0}^\infty x_n\Bigr\| \le \sum_{n=0}^\infty \|x_n\|.$$

*Proof.* Let $s_N$ be the partial sums and $t_N = \sum_{n < N} \|x_n\|$. For $M < N$ the triangle inequality gives
$$\|s_N - s_M\| = \Bigl\|\sum_{M \le n < N} x_n\Bigr\| \le \sum_{M \le n < N} \|x_n\| = t_N - t_M.$$
The sequence $(t_N)$ converges in $\mathbb{R}$, so it is Cauchy, and the inequality shows that $(s_N)$ is Cauchy in $E$. Since $E$ is complete, $s_N \to s$ for some $s$. Finally $\|s_N\| \le t_N$ for each $N$, and the limit $N \to \infty$ gives $\|s\| \le \sum \|x_n\|$, since the norm is continuous. $\square$

::: mathlib
`norm_tsum_le_tsum_norm` · `Mathlib.Analysis.Normed.Group.InfiniteSum`

`(Summable fun i ↦ ‖f i‖) → ‖∑' i, f i‖ ≤ ∑' i, ‖f i‖`. The comparison test is `Summable.of_norm_bounded`: a summable real `g` with `‖f i‖ ≤ g i` gives `Summable f`. Mathlib proves both through the Cauchy criterion for the filter of finite sets, `cauchySeq_finset_of_norm_bounded`.

<?decl norm_tsum_le_tsum_norm?>
:::

**Theorem (Completeness criterion).** A normed group $E$ is complete if and only if each absolutely convergent series in $E$ converges.

*Proof.* One direction is the last theorem. For the other, assume that each absolutely convergent series converges, and let $(y_k)$ be a Cauchy sequence. It suffices to find a convergent subsequence, since a Cauchy sequence with a convergent subsequence converges to the same limit (Volume 13, Chapter 3).

Choose indices $k_1 < k_2 < \dots$ with $\|y_m - y_l\| < 2^{-j}$ for all $m, l \ge k_j$. This is possible by the Cauchy property, applied with $\varepsilon = 2^{-j}$, and taking $k_j$ larger than $k_{j-1}$. Put $x_0 = y_{k_1}$ and $x_j = y_{k_{j+1}} - y_{k_j}$ for $j \ge 1$. Then $\|x_j\| < 2^{-j}$ for $j \ge 1$, so $\sum \|x_j\| \le \|x_0\| + 1 < \infty$. By the hypothesis $\sum x_j$ converges. Its partial sums telescope:
$$x_0 + x_1 + \dots + x_{J} = y_{k_{J+1}}.$$
So the subsequence $(y_{k_J})$ converges, and $(y_k)$ converges. $\square$

The proof shows the typical use of the criterion. To prove that a normed space is complete, take an absolutely convergent series, build its sum by hand, and prove that the partial sums converge to it.

::: mathlib
`NormedAddCommGroup.completeSpace_of_summable_imp_tendsto` · `Mathlib.Analysis.Normed.Group.Completeness`

The hypothesis is stated for sequences `u : ℕ → E` and partial sums over `Finset.range n`, not with `Summable u`, so it is the criterion of the text with ordinary convergence. The equivalence is `NormedAddCommGroup.summable_imp_tendsto_iff_completeSpace`.

<?decl NormedAddCommGroup.completeSpace_of_summable_imp_tendsto?>
:::

**Theorem (Completeness of $\ell^p$).** For $1 \le p \le \infty$ and any set $I$, the space $\ell^p(I)$ is complete.

*Proof.* Let $1 \le p < \infty$ and let $(f_k)$ be a Cauchy sequence in $\ell^p(I)$. The proof has three steps.

*Step 1: a pointwise limit.* For each $i$, $|f_k(i) - f_l(i)| \le \|f_k - f_l\|_p$, since one term of a sum of nonnegative terms is at most the sum. So $(f_k(i))_k$ is Cauchy in $\mathbb{K}$, and it has a limit $f(i)$.

*Step 2: $f \in \ell^p$ and the tail estimate.* Let $\varepsilon > 0$ and choose $N$ with $\|f_k - f_l\|_p < \varepsilon$ for $k, l \ge N$. For a finite set $F \subseteq I$ and $k, l \ge N$,
$$\sum_{i \in F} |f_k(i) - f_l(i)|^p \le \|f_k - f_l\|_p^p < \varepsilon^p.$$
Let $l \to \infty$ in this finite sum: $\sum_{i \in F} |f_k(i) - f(i)|^p \le \varepsilon^p$. Since $F$ is arbitrary, $f_k - f \in \ell^p$ with $\|f_k - f\|_p \le \varepsilon$ for $k \ge N$. Then $f = f_N - (f_N - f)$ is in $\ell^p$, since $\ell^p$ is a group.

*Step 3: convergence.* Step 2 says $\|f_k - f\|_p \le \varepsilon$ for all $k \ge N$, so $f_k \to f$ in $\ell^p$.

For $p = \infty$ the same three steps work with $|f_k(i) - f_l(i)| \le \|f_k - f_l\|_\infty$ for each $i$ in place of the finite sums. $\square$

The order of the limits in Step 2 matters. The limit $l \to \infty$ is taken in a finite sum, where it is a limit of finitely many real sequences. Taking it in the infinite sum directly would need an interchange of a limit and a series, which is the point to be proved.

::: mathlib
`lp.completeSpace` · `Mathlib.Analysis.Normed.Lp.lpSpace`

The instance `CompleteSpace (lp E p)` under `[Fact (1 ≤ p)]` and `[∀ a, CompleteSpace (E a)]`. The values may be any complete normed groups. Mathlib proves it with the same pointwise limit, through the lemmas `lp.memℓp_of_tendsto` and `lp.norm_le_of_tendsto`, which say that a pointwise limit of a bounded sequence in `lp E p` is in `lp E p`, with the norm bound.

<?decl lp.completeSpace?>
:::

### Examples

**Example (A series in $\ell^1$).** Let $e_n \in \ell^1$ be the sequence with $1$ at place $n$ and $0$ elsewhere. The series $\sum_n 2^{-n} e_n$ converges absolutely, since $\|2^{-n} e_n\|_1 = 2^{-n}$. Its sum is the sequence $f = (1, \tfrac12, \tfrac14, \dots)$, with $\|f\|_1 = 2$. Here the bound of the theorem is an equality.

**Example (A Cauchy sequence in $\ell^2$).** Let $f_k = (1, \tfrac12, \dots, \tfrac1k, 0, 0, \dots)$. For $k < l$,
$$\|f_l - f_k\|_2^2 = \sum_{n = k+1}^{l} \frac{1}{n^2} \le \sum_{n > k} \frac{1}{n(n-1)} = \frac1k,$$
so $(f_k)$ is Cauchy, and its limit in $\ell^2$ is $f = (1/n)_{n \ge 1}$, with $\|f\|_2^2 = \pi^2/6$. The same sequence is not Cauchy in $\ell^1$: $\|f_l - f_k\|_1 = \sum_{n=k+1}^l 1/n$, which is unbounded in $l$, and $f \notin \ell^1$.

**Example (Unconditional but not absolute convergence).** In $\ell^2$ the series $\sum_{n \ge 1} e_n / n$ converges to $f = (1/n)$ in any order of its terms, by the last computation applied to a rearrangement: the tail of any rearrangement has norm squared at most $\sum_{n > k} 1/n^2$ once it contains $e_1, \dots, e_k$. But $\sum \|e_n / n\|_2 = \sum 1/n = \infty$. In $\mathbb{R}^n$ this cannot happen.

**Counterexample (The finitely supported sequences).** Let $c_{00} \subseteq \ell^\infty$ be the subspace of sequences with finitely many nonzero terms, with the norm $\|\cdot\|_\infty$. The series $\sum_n 2^{-n} e_n$ converges absolutely in $c_{00}$, since $\|2^{-n} e_n\|_\infty = 2^{-n}$. Its partial sums $s_N = (1, \tfrac12, \dots, 2^{-(N-1)}, 0, \dots)$ converge in $\ell^\infty$ to $(2^{-n})_n$, which is not finitely supported. A limit in $c_{00}$ would also be a limit in $\ell^\infty$, so it would be this sequence, which is not in $c_{00}$. So the series does not converge in $c_{00}$, and by the criterion $c_{00}$ is not complete. Its closure in $\ell^\infty$ is the space $c_0$ of sequences that tend to $0$ (Exercise 5). In Mathlib, $c_{00}$ is `lp E 0`, whose elements have finite support.

### The library around it

The lemmas on series in normed groups are in `Mathlib.Analysis.Normed.Group.InfiniteSum`: the comparison tests `Summable.of_norm_bounded` and `Summable.of_norm_bounded_eventually`, the Cauchy criteria `cauchySeq_finset_of_norm_bounded`, and the bound `tsum_of_norm_bounded`. The general theory of `HasSum`, `Summable` and `tsum` is in `Mathlib.Topology.Algebra.InfiniteSum`, the home of Volume 14. The junk value matters: `∑' i, f i = 0` when `f` is not summable, so a lemma about `tsum` usually has a hypothesis `Summable f`. The file `Mathlib.Analysis.Normed.Lp.lpSpace` also gives `lp E ∞` the structure of a normed ring (`lp.inftyNormedRing`) when the values are normed rings, and the file `Mathlib.Analysis.Normed.Lp.lpHolder` the inequality of Hölder for `lp`. The space $L^p$ of integrable functions is in `Mathlib.MeasureTheory`, the subject of Volume 18.

Common errors of a learner:

- Reading `Summable f` as "the series converges in the order of $\mathbb{N}$". It is unconditional summability.
- Using `∑' i, f i` without a proof of `Summable f`, and getting the junk value $0$.
- Taking a limit inside an infinite sum in the proof of completeness of $\ell^p$, in place of a finite sum.
- Forgetting the instance `Fact (1 ≤ p)` in a statement about `lp E p`.

### Exercises

1. (A) Show that $(1/n)_{n \ge 1} \in \ell^p$ if and only if $p > 1$, and compute $\|(2^{-n})_{n \ge 0}\|_2$.
2. (A) Show that $\ell^1 \subseteq \ell^2 \subseteq \ell^\infty$ with $\|f\|_\infty \le \|f\|_2 \le \|f\|_1$.
3. (A) In a complete normed space, let $\|x_n\| \le 3^{-n}$. Show that $\|\sum_n x_n\| \le 3/2$.
4. (B) Show that the inclusions of Exercise 2 are strict, and that $\ell^1$ is not closed in $\ell^2$.
5. (B) Let $c_0 \subseteq \ell^\infty$ be the sequences with limit $0$. Show that $c_0$ is closed in $\ell^\infty$, so complete, and that $c_{00}$ is dense in $c_0$.
6. (B) Show that the space of continuous functions $[0, 1] \to \mathbb{R}$ with the norm $\|f\|_1 = \int_0^1 |f|$ is not complete. Hint: functions that rise from $0$ to $1$ on $[\tfrac12, \tfrac12 + \tfrac1n]$.
7. (C) Let $E$ be a normed space in which each series with $\|x_n\| \le 2^{-n}$ converges. Show that $E$ is complete.

### Notes and history

The space $\ell^2$ appears in the work of Hilbert on integral equations, from 1904 to 1910, and in that of Schmidt (1908), who wrote it with the geometric language of length and orthogonality. The spaces $\ell^p$ were studied by F. Riesz in 1913. The criterion by absolutely convergent series is the standard tool of the textbooks to prove completeness. The file `Mathlib.Analysis.Normed.Lp.lpSpace` has the authors Heather Macbeth and Jireh Loreaux, and `Mathlib.Analysis.Normed.Group.Completeness` the author Frédéric Dupuis.

### Reference

<?reference?>
