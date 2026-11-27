---
title: Birkhoff sums and the ergodic theorems
kind: theory
modules:
  - Mathlib.Dynamics.BirkhoffSum.Basic
  - Mathlib.Dynamics.BirkhoffSum.Average
  - Mathlib.Dynamics.BirkhoffSum.Integrable
  - Mathlib.Dynamics.BirkhoffSum.Maximal
  - Mathlib.Dynamics.BirkhoffSum.NormedSpace
  - Mathlib.Dynamics.Ergodic.EmpiricalMeasure
explains:
  E3: [birkhoffSum, birkhoffSum_add_right, birkhoffAverage, birkhoffMax_le_indicator_add_comp, mul_measureReal_lt_birkhoffAverageSup_le_integral, tendsto_birkhoffAverage_apply_sub_birkhoffAverage, MeasureTheory.empiricalMeasure, MeasureTheory.exists_measurePreserving_probabilityMeasure]
  E2: [birkhoffSum_succ', birkhoffSum_apply_sub_birkhoffSum, birkhoffSum_of_comp_eq, Function.IsFixedPt.birkhoffSum_eq, birkhoffAverage_apply_sub_birkhoffAverage, birkhoffAverage_of_comp_eq, Function.IsFixedPt.tendsto_birkhoffAverage, integrable_birkhoffSum, integrable_birkhoffAverage, birkhoffMax, birkhoffMax_succ, birkhoffSumSup, birkhoffAverageSup, setIntegral_support_birkhoffMax_nonneg, setIntegral_birkhoffSumSup_nonneg, lt_birkhoffAverageSup_iff_lt_birkhoffSumSup, mul_measureReal_lt_birkhoffAverageSup_le_norm, dist_birkhoffAverage_apply_birkhoffAverage, uniformEquicontinuous_birkhoffAverage, isClosed_setOfPred_tendsto_birkhoffAverage, MeasureTheory.integral_empiricalMeasure_eq_birkhoffaverage, MeasureTheory.tendsto_integral_comp_sub_integral_empiricalMeasure_of_isBoundedUnder, MeasureTheory.ProbabilityMeasure.integral_comp_eq_integral_of_mapClusterPt, MeasureTheory.exists_measurePreserving_probabilityMeasure_of_compact_forwardInvariant]
  E1: auto
families: []
requires: [V16, V18, V20, V21.C05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Birkhoff sums and the ergodic theorems

### Overview

The time average of an observable $g$ along the orbit of $x$ is $\frac1n\sum_{k<n} g(f^k x)$. The ergodic theorems say that these averages converge, in $L^2$ (von Neumann) and almost everywhere (Birkhoff), and that the limit is the space average when $f$ is ergodic. This section defines Birkhoff sums and averages, proves the maximal inequality by the argument of Garsia, proves both ergodic theorems, and constructs invariant measures for continuous maps of compact spaces from averages of Dirac measures.

### Definitions

Let $f : X \to X$ and $g : X \to M$ with $M$ an additive commutative monoid.

**Definition (Birkhoff sum and average).** The *Birkhoff sum* is $S_n g(x) = \sum_{k<n} g(f^k x)$. If $M$ is a module over a division semiring $R$, the *Birkhoff average* is $A_n g = \frac1n S_n g$, with $A_0 g = 0$.

::: mathlib
`birkhoffSum` · `Mathlib.Dynamics.BirkhoffSum.Basic`

`birkhoffSum f g n x = ∑ k ∈ Finset.range n, g (f^[k] x)`, of type `(α → α) → (α → M) → ℕ → α → M`. The recursions are `birkhoffSum_succ'`, `birkhoffSum f g (n + 1) = g + birkhoffSum f g n ∘ f`, and `birkhoffSum_succ`. An invariant `g` gives `birkhoffSum_of_comp_eq : g ∘ f = g → birkhoffSum f g n = n • g`, and a fixed point gives `Function.IsFixedPt.birkhoffSum_eq`.

<?decl birkhoffSum?>
:::

::: mathlib
`birkhoffAverage` · `Mathlib.Dynamics.BirkhoffSum.Average`

`birkhoffAverage R f g n x = (n : R)⁻¹ • birkhoffSum f g n x`. The ring `R` is explicit; `birkhoffAverage_congr_ring` shows that it does not change the value. Invariant functions are fixed by `birkhoffAverage_of_comp_eq`, which needs `(n : R) ≠ 0`.

<?decl birkhoffAverage?>
:::

For real $g$, the *maximal sums* are $M_n g = \max(0, S_1 g, \dots, S_n g)$, so $M_0 g = 0$ and $M_{n+1}g = \max(0, g + M_n g \circ f)$.

### Theorems and proofs

**Proposition (Cocycle identity).** $S_{m+n}g = S_m g + S_n g \circ f^m$. For $g$ with values in a group, $S_n g \circ f - S_n g = g \circ f^n - g$.

*Proof.* Split the sum over $k < m + n$ into $k < m$ and $k = m + j$ with $j < n$, and use $g(f^{m+j}x) = g(f^j(f^m x))$. For the second claim, the cases $(m, n) = (1, n)$ and $(n, 1)$ give $g + S_n g \circ f = S_{n+1}g = S_n g + g \circ f^n$. $\square$

As a consequence, $A_n g(fx) - A_n g(x) = \frac1n(g(f^n x) - g(x))$, which tends to $0$ when $g$ is bounded along the orbit of $x$.

**Lemma (Garsia).** For real $g$ and all $x$, $M_n g(x) \le 1_{\{M_n g > 0\}}(x)\,g(x) + M_n g(fx)$. If $f$ preserves a measure $\mu$ and $g \in L^1(\mu)$, then $\int_{\{M_n g > 0\}} g\,d\mu \ge 0$.

*Proof.* Write $M_n = M_n g$ and $E = \{M_n > 0\}$. If $x \notin E$, then $M_n(x) = 0 \le M_n(fx)$. If $x \in E$, then $M_n(x) = S_k g(x)$ for some $1 \le k \le n$, and $S_k g(x) = g(x) + S_{k-1}g(fx) \le g(x) + M_n(fx)$, since $k - 1 \le n$ and $S_0 g = 0$.

Each $M_n$ is integrable, since $|M_n| \le \sum_{k<n}|g \circ f^k|$. Integrate the inequality over $E$:
$$\int_E M_n \le \int_E g + \int_E M_n \circ f \le \int_E g + \int_X M_n \circ f = \int_E g + \int_X M_n = \int_E g + \int_E M_n.$$
The second step uses $M_n \ge 0$, the third uses that $f$ preserves $\mu$, and the last uses $M_n = 0$ off $E$. $\square$

**Theorem (Maximal inequality).** Let $f$ preserve a finite $\mu$, let $g \in L^1(\mu)$ be real and $a \ge 0$, and let $B = \{x : \sup_n A_n g(x) > a\}$. Then $a\,\mu(B) \le \int_B g\,d\mu$.

*Proof.* Since $a \ge 0$ and $A_0 g = 0$, $x \in B$ if and only if $S_n(g - a)(x) > 0$ for some $n \ge 1$, that is, $M_n(g - a)(x) > 0$ for some $n$. The sets $E_n = \{M_n(g - a) > 0\}$ increase with union $B$. Garsia's lemma gives $a\,\mu(E_n) \le \int_{E_n} g$. Let $n \to \infty$, using dominated convergence with the bound $|g|$. $\square$

Apply the theorem to $|g|$. Since $|A_n g| \le A_n|g|$, the set $\{\sup_n |A_n g| > a\}$ has measure at most $\|g\|_1 / a$.

**Theorem (Mean ergodic theorem).** Let $T$ be a linear operator with $\|T\| \le 1$ on a Hilbert space $H$, and $P$ the orthogonal projection onto $\ker(T - 1)$. For every $v \in H$, $\frac1n\sum_{k<n}T^k v \to Pv$.

*Proof.* Let $A_n = \frac1n\sum_{k<n}T^k$, so $\|A_n\| \le 1$. First, $Tv = v$ implies $T^*v = v$:
$$\|T^*v - v\|^2 = \|T^*v\|^2 - 2\operatorname{Re}\langle v, Tv\rangle + \|v\|^2 \le \|v\|^2 - 2\|v\|^2 + \|v\|^2 = 0.$$
By symmetry, $\ker(T - 1) = \ker(T^* - 1) = \operatorname{range}(T - 1)^\perp$, so $H = \ker(T - 1) \oplus \overline{\operatorname{range}(T - 1)}$. On the first summand $A_n v = v = Pv$. For $v = Tw - w$, $A_n v = \frac1n(T^n w - w)$, of norm at most $\frac2n\|w\|$, and $Pv = 0$. For $v$ in the closure, take $v'$ in the range with $\|v - v'\| < \varepsilon$; then $\|A_n v\| \le \varepsilon + \|A_n v'\|$. $\square$

If $f$ preserves $\mu$, then $Tg = g \circ f$ is an isometry of $L^2(\mu)$, and the theorem gives $A_n g \to Pg$ in $L^2$. If $f$ is ergodic and $\mu$ a probability, the invariant functions are constants and $Pg = \int g\,d\mu$.

**Theorem (Pointwise ergodic theorem).** Let $f$ preserve a probability $\mu$ and $g \in L^1(\mu)$ be real. Then $A_n g$ converges a.e. and in $L^1$ to an invariant $g^* \in L^1$ with $\int_C g^* = \int_C g$ for every invariant measurable $C$. If $f$ is ergodic, then $g^* = \int g\,d\mu$ a.e.

*Proof.* Let $\overline g = \limsup A_n g$ and $\underline g = \liminf A_n g$, with values in $[-\infty, \infty]$. From $A_n g(fx) = \frac{n+1}{n}A_{n+1}g(x) - \frac1n g(x)$ follow $\overline g \circ f = \overline g$ and $\underline g \circ f = \underline g$ everywhere.

For rationals $a < b$, let $C = \{\underline g < a < b < \overline g\}$. Then $f^{-1}(C) = C$, so $1_C \circ f^k = 1_C$ and $S_n(1_C h) = 1_C S_n h$ for every $h$. Put $h = 1_C(g - b)$. On $C$, some $A_n g > b$, so some $S_n(g - b) > 0$; off $C$, all $S_n h = 0$. So $C = \bigcup_n\{M_n h > 0\}$, and Garsia's lemma with dominated convergence gives $\int_C (g - b) \ge 0$. The same argument with $1_C(a - g)$ gives $\int_C (a - g) \ge 0$. Adding, $(a - b)\mu(C) \ge 0$, so $\mu(C) = 0$. The union over rational pairs is null, so $\underline g = \overline g$ a.e., and $A_n g \to g^*$ a.e. By Fatou, $\int |g^*| \le \liminf \int |A_n g| \le \|g\|_1$, so $g^*$ is integrable and finite a.e.

For $L^1$ convergence, first let $g$ be bounded. Then $|A_n g| \le \sup|g|$, and dominated convergence applies. For general $g$ and $\varepsilon > 0$, take bounded $g'$ with $\|g - g'\|_1 < \varepsilon$. Then $\|A_n g - A_n g'\|_1 \le \varepsilon$, and by Fatou $\|g^* - g'^*\|_1 \le \varepsilon$. So $\limsup_n \|A_n g - g^*\|_1 \le 2\varepsilon$.

For invariant $C$, $\int_C g \circ f^k = \int (1_C\, g) \circ f^k = \int_C g$, so $\int_C A_n g = \int_C g$, and $L^1$ convergence gives $\int_C g^* = \int_C g$. If $f$ is ergodic, the invariant function $g^*$ is a.e. a constant $c$ (Section 1), and $C = X$ gives $c = \int g$. $\square$

**Theorem (Krylov and Bogolyubov).** A continuous map $f$ of a nonempty compact metric space $X$ has an invariant Borel probability measure.

*Proof.* Fix $x$ and let $\mu_n = \frac1{n+1}\sum_{k \le n}\delta_{f^k x}$. Then $\int g\,d\mu_n = A_{n+1}g(x)$, and by the cocycle identity, for continuous $g$,
$$\Big|\int g \circ f\,d\mu_n - \int g\,d\mu_n\Big| = \frac{|g(f^{n+1}x) - g(x)|}{n+1} \le \frac{2\sup|g|}{n+1}.$$
By the Riesz theorem and the Banach and Alaoglu theorem (Volume 16), the probability measures on $X$ form a compact set in the weak topology, so $(\mu_n)$ has a cluster point $\mu$. The functions $g$ and $g \circ f$ are continuous, so $\int g \circ f\,d\mu = \int g\,d\mu$. The measures $f_*\mu$ and $\mu$ have the same integrals of continuous functions, so they are equal. $\square$

### Examples

**Example (Weyl equidistribution).** Let $f(x) = x + a$ on $\mathbb{T}$ with $a$ irrational and $e_k(x) = e^{2\pi i k x}$. For $k \ne 0$,
$$A_n e_k(x) = \frac{e_k(x)}{n}\cdot\frac{e^{2\pi i k n a} - 1}{e^{2\pi i k a} - 1} \to 0.$$
Trigonometric polynomials are uniformly dense in $C(\mathbb{T})$ and $\|A_n\| \le 1$ for the sup norm, so $A_n g(x) \to \int g$ for every continuous $g$ and every $x$, not only almost every $x$. Every invariant probability then has $\int g\,d\nu = \int g$, so Lebesgue measure is the only one.

**Example (Normal numbers).** The doubling map $D$ is ergodic (Section 1). For a binary word $w$ of length $m$, let $I_w$ be the interval of the points whose expansion starts with $w$, of length $2^{-m}$. The pointwise theorem for $1_{I_w}$ shows that for a.e. $x$, the word $w$ occurs in the binary expansion of $x$ with frequency $2^{-m}$. A countable intersection over all $w$ gives this for all $w$ at once.

**Example (A point mass).** For $f(x) = x^2$ on $[0, 1]$ and $x < 1$, $f^k x \to 0$, so $\mu_n \to \delta_0$ in the proof of Krylov and Bogolyubov. For $x = 1$ the limit is $\delta_1$.

**Counterexample (Divergent averages).** Let $x \in [0, 1)$ have binary digits in blocks of lengths $1, 2, 4, 8, \dots$, with digits $0$ in the first block, $1$ in the second, and so on. After the block of length $2^k$, $2^{k+1} - 1$ digits are written, and the number of digits $1$ is $(2^{k+2} - 2)/3$ for odd $k$ and $(2^{k+1} - 2)/3$ for even $k$. With $g = 1_{[1/2, 1)}$, $A_n g(x)$ counts the digits $1$, and its liminf is $1/3$ and its limsup $2/3$. So $x$ is in the null set where the pointwise theorem fails for $D$.

### The library around it

::: mathlib
`birkhoffSum_add_right` · `Mathlib.Dynamics.BirkhoffSum.Basic`

`birkhoffSum f g (m + n) = birkhoffSum f g m + birkhoffSum f g n ∘ f^[m]`. For groups, `birkhoffSum_apply_sub_birkhoffSum` is `birkhoffSum f g n (f x) - birkhoffSum f g n x = g (f^[n] x) - g x`, and `birkhoffAverage_apply_sub_birkhoffAverage` divides it by `n`. With a measure preserving `f`, `integrable_birkhoffSum` and `integrable_birkhoffAverage` keep integrability.

<?decl birkhoffSum_add_right?>
:::

::: mathlib
`birkhoffMax_le_indicator_add_comp` · `Mathlib.Dynamics.BirkhoffSum.Maximal`

`birkhoffMax f g n x ≤ (support (birkhoffMax f g n)).indicator g x + birkhoffMax f g n (f x)`, in a linearly ordered additive group. The function `birkhoffMax f g : ℕ →o α → M` is monotone in `n`, with `birkhoffMax_succ` the recursion of the definitions. The integral form is `setIntegral_support_birkhoffMax_nonneg`, and `setIntegral_birkhoffSumSup_nonneg` passes to the supremum `birkhoffSumSup f g : α → EReal`.

<?decl birkhoffMax_le_indicator_add_comp?>
:::

::: mathlib
`mul_measureReal_lt_birkhoffAverageSup_le_integral` · `Mathlib.Dynamics.BirkhoffSum.Maximal`

For finite `μ`, `MeasurePreserving f μ μ → Integrable g μ → ∀ a, 0 ≤ a → a * μ.real {x | ↑a < birkhoffAverageSup f g x} ≤ ∫ x in {x | ↑a < birkhoffAverageSup f g x}, g x ∂μ`. Here `birkhoffAverageSup f g x : EReal` is the supremum of the averages, and `lt_birkhoffAverageSup_iff_lt_birkhoffSumSup` is the first step of the proof. The form `mul_measureReal_lt_birkhoffAverageSup_le_norm` takes `‖g x‖` for `g` with values in a normed group.

<?decl mul_measureReal_lt_birkhoffAverageSup_le_integral?>
:::

::: mathlib
`tendsto_birkhoffAverage_apply_sub_birkhoffAverage` · `Mathlib.Dynamics.BirkhoffSum.NormedSpace`

If the orbit values `g (f^[n] x)` form a bounded set, then `birkhoffAverage 𝕜 f g n (f x) - birkhoffAverage 𝕜 f g n x → 0`. The exact distance is `dist_birkhoffAverage_apply_birkhoffAverage`. For `LipschitzWith 1 f` and uniformly continuous `g`, `uniformEquicontinuous_birkhoffAverage` holds, and `isClosed_setOfPred_tendsto_birkhoffAverage` shows that, for continuous `l`, the set of `x` with averages tending to `l x` is closed.

<?decl tendsto_birkhoffAverage_apply_sub_birkhoffAverage?>
:::

::: mathlib
`ContinuousLinearMap.tendsto_birkhoffAverage_orthogonalProjection` · `Mathlib.Analysis.InnerProductSpace.MeanErgodic`

For `f : E →L[𝕜] E` on a complete inner product space with `‖f‖ ≤ 1`, `birkhoffAverage 𝕜 f id n x` tends to the orthogonal projection of `x` onto `(f : E →ₗ[𝕜] E).eqLocus 1`. This is the mean ergodic theorem.

<?decl ContinuousLinearMap.tendsto_birkhoffAverage_orthogonalProjection?>
:::

::: mathlib
`MeasureTheory.exists_measurePreserving_probabilityMeasure` · `Mathlib.Dynamics.Ergodic.EmpiricalMeasure`

On a nonempty compact Hausdorff space with the Borel structure, `Continuous f → ∃ μ, MeasurePreserving f μ μ ∧ μ.Regular ∧ IsProbabilityMeasure μ`. The empirical measure `MeasureTheory.empiricalMeasure f x n` satisfies `MeasureTheory.integral_empiricalMeasure_eq_birkhoffaverage`, `∫ g ∂empiricalMeasure f x n = birkhoffAverage NNReal f g (n + 1) x`, so it has `n + 1` atoms. The key steps are `MeasureTheory.tendsto_integral_comp_sub_integral_empiricalMeasure_of_isBoundedUnder` and `MeasureTheory.ProbabilityMeasure.integral_comp_eq_integral_of_mapClusterPt`. The version for a compact `K` with `MapsTo f K K` is `MeasureTheory.exists_measurePreserving_probabilityMeasure_of_compact_forwardInvariant`.

<?decl MeasureTheory.exists_measurePreserving_probabilityMeasure?>
<?decl MeasureTheory.empiricalMeasure?>
:::

Common errors of a learner:

- `birkhoffAverage R f g 0 = 0`, so statements about all `n` often need `n ≠ 0`.
- `empiricalMeasure f x n` averages over $n + 1$ points, not $n$.
- The suprema `birkhoffSumSup` and `birkhoffAverageSup` take values in `EReal`. The lemmas on `birkhoffAverageSup` ask for `0 ≤ a`, because the average for `n = 0` is `0`.

### Exercises

1. (A) Let $g = h \circ f - h$ with $h$ bounded. Show that $|A_n g| \le 2\sup|h|/n$ everywhere.
2. (A) Let $x$ have period $p$. Compute $\lim_n A_n g(x)$, and show that the empirical measures of $x$ converge to $\frac1p\sum_{j<p}\delta_{f^j x}$.
3. (A) Let $f$ be ergodic for a probability $\mu$ and $\mu(B) > 0$. Show that a.e. orbit enters $B$ with frequency $\mu(B)$, and in particular infinitely often.
4. (B) Let $T(u, v) = (u + v, v)$ on $\mathbb{R}^2$. Show that $A_n(0, 1)$ is unbounded, so the mean ergodic theorem needs $\|T\| \le 1$.
5. (B) Let $a$ be irrational and $I \subseteq \mathbb{T}$ an interval. Show that for every $x$, the frequency of $k < n$ with $x + ka \in I$ tends to the length of $I$. Hint: bound $1_I$ above and below by continuous functions with integrals close to the length.
6. (C) Show that the proportion of $n < N$ for which the first decimal digit of $2^n$ is $d$ tends to $\log_{10}(1 + 1/d)$. Hint: $\log_{10}2$ is irrational; use Exercise 5.
7. (C) Show that a continuous map of a compact metric space has an ergodic invariant probability. Hint: the invariant probabilities form a nonempty convex weakly compact set; use the Krein and Milman theorem and the characterization of ergodic measures as extreme points in Section 1.

### Notes and history

Birkhoff proved the pointwise theorem in 1931, and von Neumann the mean theorem in 1932. The short proof of the maximal lemma is due to Garsia (1965). Krylov and Bogolyubov published their construction of invariant measures in 1937. Weyl proved equidistribution of $na \bmod 1$ in 1916, and Borel proved that almost every number is normal in 1909. The index of this edition has no declaration for the pointwise ergodic theorem.

### Reference

<?reference?>
