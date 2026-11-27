---
title: The lemma of Riesz and compactness
kind: theory
modules:
  - Mathlib.Analysis.Normed.Module.RieszLemma
  - Mathlib.Analysis.Normed.Module.FiniteDimension
explains:
  E3: [riesz_lemma, FiniteDimensional.of_isCompact_closedBall, FiniteDimensional.proper]
  E2: [riesz_lemma_of_lt_one, riesz_lemma_of_norm_lt, exists_seq_norm_le_one_le_norm_sub, FiniteDimensional.of_isCompact_closedBall₀, FiniteDimensional.proper_real, ProperSpace.of_locallyCompactSpace]
  E1: auto
families: []
requires: [V07, V13, V16.C01, V16.C02]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The lemma of Riesz and compactness

### Overview

In $\mathbb{R}^n$ the closed bounded sets are compact. In an infinite dimensional normed space this fails already for the closed unit ball: in $\ell^2$ the basis vectors $e_n$ lie in the unit ball and $\|e_m - e_n\|_2 = \sqrt2$ for $m \ne n$, so no subsequence is Cauchy. This section proves that the example is typical. The tool is the lemma of Riesz: in a normed space, for each closed proper subspace there are unit vectors almost at distance $1$ from it. It replaces the orthogonal complement, which a general normed space does not have. With it each infinite dimensional normed space contains a sequence in the unit ball with no convergent subsequence. So the closed unit ball is compact if and only if the dimension is finite. The section ends with the class `ProperSpace` of Mathlib for spaces where closed balls are compact.

### Definitions

**Definition (Distance to a set).** For a subset $M$ of a normed space $E$ and $x \in E$, the distance of $x$ to $M$ is $d(x, M) = \inf_{y \in M}\|x - y\|$. If $M$ is closed, then $d(x, M) = 0$ if and only if $x \in M$ (Volume 13).

**Definition (Proper metric space).** A metric space is *proper* if each closed ball is compact. A proper space is locally compact, and it is complete: a Cauchy sequence is bounded, so it lies in a compact closed ball, and a Cauchy sequence with a convergent subsequence converges.

::: mathlib
`ProperSpace` · `Mathlib.Topology.MetricSpace.ProperSpace`

`ProperSpace α` is a class on a pseudometric space with the field `isCompact_closedBall : ∀ x r, IsCompact (closedBall x r)`. Instances derive `CompleteSpace α`, `LocallyCompactSpace α` and `SecondCountableTopology α` from it. The real line, the complex plane and finite products of proper spaces are proper by instances. The compactness of closed bounded sets is `Metric.isCompact_of_isClosed_isBounded`. The class is part of the metric topology of Volume 13.

<?decl ProperSpace?>
:::

### Theorems and proofs

**Theorem (Lemma of Riesz).** Let $M$ be a closed subspace of a normed space $E$ with $M \ne E$, and let $0 < r < 1$. Then there is $x \in E$ with $\|x\| = 1$ and $\|x - y\| \ge r$ for all $y \in M$.

*Proof.* Choose $z \in E \setminus M$. Since $M$ is closed, $d = d(z, M) > 0$. Since $d/r > d$, there is $y_0 \in M$ with $\|z - y_0\| < d/r$. Put
$$x = \frac{z - y_0}{\|z - y_0\|}.$$
Then $\|x\| = 1$. For $y \in M$, the vector $y_0 + \|z - y_0\|\,y$ lies in $M$, so
$$\|x - y\| = \frac{\big\|z - (y_0 + \|z - y_0\|\,y)\big\|}{\|z - y_0\|} \ge \frac{d}{\|z - y_0\|} > \frac{d}{d/r} = r. \qquad \square$$

The lemma does not give $r = 1$ in general. In a Hilbert space, a unit vector orthogonal to $M$ has distance exactly $1$ (Chapter 7). In the space $c_0$ of sequences that tend to $0$, there is a closed hyperplane with no unit vector at distance $1$ (Exercise 7). In finite dimension $r = 1$ is always possible (Exercise 5).

::: mathlib
`riesz_lemma` · `Mathlib.Analysis.Normed.Module.RieszLemma`

`riesz_lemma (hFc : IsClosed (F : Set E)) (hF : ∃ x, x ∉ F) (hr : r < 1) : ∃ x₀ ∉ F, ∀ y ∈ F, r * ‖x₀‖ ≤ ‖x₀ - y‖` over any normed field. The vector `x₀` is not normalized, since over a general field a vector need not have a multiple of norm $1$. For `RCLike` scalars, `riesz_lemma_of_lt_one` adds `‖x₀‖ = 1`. The form `riesz_lemma_of_norm_lt` uses a scalar `c` with `1 < ‖c‖` and gives `‖x₀‖ ≤ R` and `1 ≤ ‖x₀ - y‖` for `y ∈ F`.

<?decl riesz_lemma?>
:::

**Theorem (A separated sequence in infinite dimension).** Let $E$ be an infinite dimensional normed space over $\mathbb{K}$. Then there is a sequence $(x_n)$ with $\|x_n\| = 1$ and $\|x_m - x_n\| \ge \frac12$ for all $m \ne n$.

*Proof.* Choose $x_1$ with $\|x_1\| = 1$. Suppose $x_1, \dots, x_n$ are chosen. The span $M_n$ of $x_1, \dots, x_n$ is finite dimensional, so it is closed by Section 1, and $M_n \ne E$ since $E$ has infinite dimension. The lemma of Riesz with $r = \frac12$ gives $x_{n+1}$ with $\|x_{n+1}\| = 1$ and $\|x_{n+1} - y\| \ge \frac12$ for all $y \in M_n$, in particular for $y = x_1, \dots, x_n$. $\square$

::: mathlib
`exists_seq_norm_le_one_le_norm_sub` · `Mathlib.Analysis.Normed.Module.FiniteDimension`

From `¬FiniteDimensional 𝕜 E` over a complete nontrivially normed field: `∃ R f, 1 < R ∧ (∀ n, ‖f n‖ ≤ R) ∧ Pairwise fun m n ↦ 1 ≤ ‖f m - f n‖`. This is the theorem after scaling by $2$, with a bound $R$ in place of the exact norm, so that it holds over every such field.

<?decl exists_seq_norm_le_one_le_norm_sub?>
:::

**Theorem (Compactness of the ball).** Let $E$ be a normed space over $\mathbb{K}$. The following are equivalent.

1. $E$ is finite dimensional.
2. The closed unit ball of $E$ is compact.
3. Some closed ball $\bar B(c, r)$ with $r > 0$ is compact.
4. $E$ is locally compact.
5. $E$ is proper.

*Proof.* (1) ⇒ (5). By Section 1 there is a linear homeomorphism $\varphi : \mathbb{K}^n \to E$ that is Lipschitz in both directions. A closed ball of $E$ is closed and bounded, so its image under $\varphi^{-1}$ is closed and bounded in $\mathbb{K}^n$, hence compact by Heine-Borel, and the ball is its image under the continuous map $\varphi$.

(5) ⇒ (2) ⇒ (3) are clear, and (3) ⇒ (4) holds since each point $x$ has the compact neighbourhood $\bar B(c, r) + (x - c) = \bar B(x, r)$, the image of $\bar B(c, r)$ under a translation, which is a homeomorphism.

(4) ⇒ (1). Let $\bar B(0, r)$ be a compact neighbourhood of $0$, with $r > 0$; a closed ball inside a compact neighbourhood is compact, as a closed subset. Suppose $E$ has infinite dimension. The last theorem gives $(x_n)$ with $\|x_n\| = 1$ and $\|x_m - x_n\| \ge \frac12$. Then $(rx_n)$ lies in $\bar B(0, r)$ and $\|rx_m - rx_n\| \ge \frac r2$ for $m \ne n$. No subsequence is Cauchy, which contradicts the sequential compactness of the compact metric space $\bar B(0, r)$ (Volume 13). $\square$

::: mathlib
`FiniteDimensional.of_isCompact_closedBall` · `Mathlib.Analysis.Normed.Module.FiniteDimension`

`FiniteDimensional.of_isCompact_closedBall 𝕜 (hr : 0 < r) (h : IsCompact (closedBall c r)) : FiniteDimensional 𝕜 V`, the step (3) ⇒ (1), and `FiniteDimensional.of_isCompact_closedBall₀` for the ball around `0`. The form for locally compact spaces is `FiniteDimensional.of_locallyCompactSpace` in `Mathlib.Topology.Algebra.Module.FiniteDimension`, and `ProperSpace.of_locallyCompactSpace` makes a locally compact normed space proper.

<?decl FiniteDimensional.of_isCompact_closedBall?>
:::

::: mathlib
`FiniteDimensional.proper` · `Mathlib.Analysis.Normed.Module.FiniteDimension`

`FiniteDimensional.proper 𝕜 E : ProperSpace E` for a finite dimensional normed space over a locally compact nontrivially normed field, the step (1) ⇒ (5). It is not an instance, since `𝕜` cannot be found from `E`. The real case is the instance `FiniteDimensional.proper_real`, so instance search knows that each finite dimensional real normed space is proper, hence complete and locally compact.

<?decl FiniteDimensional.proper?>
:::

**Corollary (Heine-Borel in finite dimension).** In a finite dimensional normed space over $\mathbb{R}$ or $\mathbb{C}$, a set is compact if and only if it is closed and bounded.

*Proof.* A compact subset of a metric space is closed and bounded (Volume 13). Conversely a closed bounded set lies in a closed ball, which is compact by the theorem, and a closed subset of a compact set is compact. $\square$

### Examples

**Example (The basis of $\ell^p$).** In $\ell^p$ with $1 \le p < \infty$ the vectors $e_n$ satisfy $\|e_n\|_p = 1$ and $\|e_m - e_n\|_p = 2^{1/p}$ for $m \ne n$. In $\ell^\infty$ the distance is $1$. In each case $(e_n)$ is a sequence in the closed unit ball with no Cauchy subsequence, and the ball is not compact. For $p = 2$ the distance is $\sqrt2$, larger than the $\frac12$ of the theorem, since the $e_n$ are orthogonal.

**Example (Functions with disjoint supports).** In $C[0,1]$ with $\|\cdot\|_\infty$ let $f_n$ be the tent function that is $0$ outside $[2^{-n-1}, 2^{-n}]$ and $1$ at the midpoint, linear on the two halves. The supports are disjoint except for end points, where both functions vanish. So $\|f_n\|_\infty = 1$ and $\|f_m - f_n\|_\infty = 1$ for $m \ne n$. The unit ball of $C[0,1]$ is not compact, and $C[0,1]$ has infinite dimension.

**Example (A step of the lemma of Riesz).** In $E = \mathbb{R}^2$ with $\|\cdot\|_\infty$ let $M = \{(t, 0)\}$ and $z = (3, 1)$. Then $d(z, M) = \inf_t\max(|3 - t|, 1) = 1$, attained at each $t \in [2, 4]$. With $y_0 = (3, 0)$, $x = (0, 1)$ has $\|x\| = 1$ and $\|x - (t, 0)\|_\infty = \max(|t|, 1) \ge 1$ for each $t$. So in this finite dimensional case $r = 1$ is attained. The vector $(\frac12, 1)$ also has norm $1$ and distance $1$ to $M$: the vector of the lemma is not unique.

**Counterexample (Bounded closed sets in $\ell^2$).** The set $\{e_n : n \ge 1\}$ in $\ell^2$ is closed, since a convergent sequence in it is eventually constant, and it is bounded. It is not compact, since the open balls $B(e_n, 1)$ cover it and each ball contains only one $e_n$. So the theorem of Heine-Borel fails in each infinite dimensional normed space.

### The library around it

The file `Mathlib.Analysis.Normed.Module.RieszLemma` has the three forms of the lemma, and the lemma `Metric.closedBall_infDist_compl_subset_closure` that is used for it. The file `Mathlib.Analysis.Normed.Module.FiniteDimension` has the criteria of compactness and the proper instances, including an instance that makes a finite dimensional subspace of a normed space proper. The compactness in the sense of sequences is `IsCompact.tendsto_subseq` in `Mathlib.Topology.Sequences` (Volume 13). In Chapter 5 the weak* topology on the dual gives back a compact unit ball, by the theorem of Banach-Alaoglu, which is `WeakDual.isCompact_polar` in `Mathlib.Analysis.Normed.Module.WeakDual`.

Common errors of a learner:

- Using the theorem of Heine-Borel in a space of functions.
- Taking $r = 1$ in the lemma of Riesz for a general normed space.
- Forgetting the hypothesis that the subspace is closed. For a dense subspace $M$ of $E$ each $x$ has $d(x, M) = 0$.

### Exercises

1. (A) Compute $\|e_m - e_n\|_p$ in $\ell^p$ for $m \ne n$, and show that $(e_n)$ has no convergent subsequence.
2. (A) Show that in a normed space $E \ne 0$, the closed unit ball is compact if and only if the unit sphere is compact.
3. (A) Show that a proper metric space is complete.
4. (B) Show that a compact subset $K$ of an infinite dimensional normed space has empty interior.
5. (B) Let $M$ be a proper subspace of a finite dimensional normed space $E$. Show that there is $x$ with $\|x\| = 1$ and $d(x, M) = 1$. Hint: the lemma of Riesz with $r_n \to 1$ and compactness of the sphere.
6. (B) Show that an infinite dimensional Banach space is not a countable union of compact sets. Hint: use Exercise 4 and the Baire category theorem of Volume 13.
7. (C) Let $c_0$ be the space of real sequences with limit $0$, with $\|\cdot\|_\infty$, and $M = \{x \in c_0 : \sum_n 2^{-n}x_n = 0\}$. Show that $M$ is a closed proper subspace and that no $x \in c_0$ with $\|x\|_\infty = 1$ has $d(x, M) = 1$.
8. (C) Show that a normed space is finite dimensional if and only if each bounded sequence has a convergent subsequence.

### Notes and history

The lemma of almost orthogonal vectors and the characterization of finite dimension by the compactness of the unit ball are in the paper of F. Riesz on linear functional equations in Acta Mathematica of 1918, where they serve the theory of compact operators. The file `Mathlib.Analysis.Normed.Module.RieszLemma` has the authors Jean Lo and Yury Kudryashov, and the file `Mathlib.Analysis.Normed.Module.FiniteDimension` has the author Sébastien Gouëzel.

### Reference

<?reference?>
