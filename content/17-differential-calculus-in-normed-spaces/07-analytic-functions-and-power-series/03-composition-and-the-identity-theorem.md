---
title: Sums, products, composition and the identity theorem
kind: theory
modules:
  - Mathlib.Analysis.Analytic.Constructions
  - Mathlib.Analysis.Analytic.Composition
  - Mathlib.Analysis.Analytic.IsolatedZeros
  - Mathlib.Analysis.Analytic.Uniqueness
  - Mathlib.Analysis.Analytic.Inverse
  - Mathlib.Analysis.Analytic.Order
  - Mathlib.Analysis.Analytic.WithLp
  - Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
explains:
  E3: [AnalyticAt.comp, AnalyticAt.mul, AnalyticAt.eventually_eq_zero_or_eventually_ne_zero, AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq]
  E2: [AnalyticAt.add, AnalyticAt.pow, AnalyticAt.inv, AnalyticAt.div, analyticAt_inverse, HasFPowerSeriesAt.comp, FormalMultilinearSeries.comp, HasFPowerSeriesAt.locally_ne_zero, AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq, AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero, AnalyticAt.exists_eventuallyEq_pow_smul_ne_zero_iff, AnalyticAt.frequently_zero_iff_eventually_zero, HasFPowerSeriesAt.apply_eq_zero, OpenPartialHomeomorph.hasFPowerSeriesAt_symm, FormalMultilinearSeries.leftInv]
  E1: auto
families: []
requires: [V17.C04, V17.C05, V17.C06, V13.C06]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Sums, products, composition and the identity theorem

### Overview

This section shows that the class of analytic functions is closed under sums, products, composition and inversion. The proofs multiply and substitute power series, and they rest on one principle: an absolutely convergent double series can be summed in any order.

The second half proves the isolated zeros and the identity theorem, which separate analytic functions from smooth ones. The section ends with the analytic inverse function theorem.

$E$, $F$ and $G$ are normed spaces over $\mathbb{K}$, complete when a sum must exist, and $\mathcal{A}$ is a Banach algebra with $\|1\| = 1$.

### Definitions

Recall from Volume 13 that a subset $U$ of a topological space is *preconnected* if it is not the union of two disjoint nonempty sets that are open in $U$. An open interval and an open ball are preconnected.

**Definition (Order of a zero).** Let $f : \mathbb{K} \to F$ be analytic at $z_0$, with $f(z_0 + t) = \sum_n a_n t^n$ near $t = 0$, and let some $a_n$ be nonzero. The *order* of $f$ at $z_0$ is the least $k$ with $a_k \ne 0$. The point $z_0$ is a zero of $f$ if and only if the order is at least $1$.

### Theorems and proofs

**Theorem (Sums and products).** Let $f, g : E \to \mathcal{A}$ be analytic at $x$. Then $f + g$ and $f g$ are analytic at $x$.

*Proof in one variable.* Let $E = \mathbb{K}$ and $x = 0$, with $f(t) = \sum_n a_n t^n$ and $g(t) = \sum_m b_m t^m$ for $|t| < \rho$, where $\rho$ is less than both radii. The sum is the series $\sum_n (a_n + b_n)t^n$. For the product, the double family $a_n t^n\, b_m t^m$ satisfies
$$\sum_{n, m}\|a_n\|\,\|b_m\|\,|t|^{n+m} = \Big(\sum_n \|a_n\|\,|t|^n\Big)\Big(\sum_m \|b_m\|\,|t|^m\Big) < \infty.$$
So it can be summed in any order. Summing over $n$ and $m$ separately gives $f(t)g(t)$. Summing over the diagonals $n + m = k$ gives
$$f(t)g(t) = \sum_k c_k t^k, \qquad c_k = \sum_{n + m = k} a_n b_m.$$
The same bound gives $\sum_k \|c_k\|\rho'^k < \infty$ for each $\rho' < \rho$, so the radius of $\sum c_k t^k$ is at least $\rho$. $\square$

::: mathlib
`AnalyticAt.mul` · `Mathlib.Analysis.Analytic.Constructions`

For `f g : E → A` with `A` a normed algebra over `𝕜`, `hf.mul hg : AnalyticAt 𝕜 (f * g) z`. Its proof is `hf.smul hg`: Mathlib proves the case of a scalar action once and deduces the product. The sum is `AnalyticAt.add`, the powers are `AnalyticAt.pow`, and for values in a normed field there are `AnalyticAt.inv` (with `f x ≠ 0`) and `AnalyticAt.div`.

<?decl AnalyticAt.mul?>
:::

**Theorem (Composition).** Let $f : E \to F$ be analytic at $x$ and $g : F \to G$ analytic at $f(x)$. Then $g \circ f$ is analytic at $x$.

*Proof in one variable.* Let $E = F = \mathbb{K}$ and $x = 0$. Write $f(t) = f(0) + \sum_{n \ge 1} a_n t^n$ and $g(f(0) + s) = \sum_m b_m s^m$ for $|s| < \rho$. The function $\sigma(\tau) = \sum_{n \ge 1}|a_n|\tau^n$ is finite for small $\tau > 0$ and tends to $0$ with $\tau$, by the estimate of Section 1. Choose $\tau > 0$ with $\sigma(\tau) < \rho$, and let $|t| < \tau$.

Put $s(t) = \sum_{n \ge 1} a_n t^n$. By the product rule above, $s(t)^m = \sum_k c_{m,k}t^k$, where $c_{m,k}$ is a sum of products of the $a_n$, and $\sum_k |c_{m,k}|\,|t|^k \le \sigma(|t|)^m$. Since $s(t)$ has no constant term, $c_{m,k} = 0$ for $k < m$. Now
$$\sum_m \sum_k \|b_m\|\,|c_{m,k}|\,|t|^k \le \sum_m \|b_m\|\,\sigma(\tau)^m < \infty,$$
because $\sigma(\tau) < \rho$ is inside the radius of $g$. So the double family $b_m c_{m,k}t^k$ is absolutely summable. Summing over $k$ first gives $\sum_m b_m s(t)^m = g(f(t))$. Summing over $m$ first gives
$$g(f(t)) = \sum_k \Big(\sum_{m \le k} b_m c_{m,k}\Big) t^k,$$
a power series that converges for $|t| < \tau$, with finite inner sums. $\square$

::: mathlib
`AnalyticAt.comp` · `Mathlib.Analysis.Analytic.Composition`

The statement is `AnalyticAt 𝕜 g (f x) → AnalyticAt 𝕜 f x → AnalyticAt 𝕜 (g ∘ f) x`. The series is `HasFPowerSeriesAt.comp`, with the composite series `q.comp p`. The definition `FormalMultilinearSeries.comp` sums over the type `Composition n` of ordered decompositions $n = n_1 + \dots + n_m$ with $n_i \ge 1$, which are the blocks above.

<?decl AnalyticAt.comp?>
:::

**Corollary (Inverses).** Let $f : E \to \mathcal{A}$ be analytic at $x$ with $f(x)$ invertible. Then $y \mapsto f(y)^{-1}$ is analytic at $x$.

*Proof.* By the composition theorem it suffices that $\mathrm{Inv}$ is analytic at each invertible $u$. For $\|h\| < \|u^{-1}\|^{-1}$,
$$(u + h)^{-1} = \big(u(1 + u^{-1}h)\big)^{-1} = (1 + u^{-1}h)^{-1}u^{-1} = \sum_n (-u^{-1}h)^n\,u^{-1},$$
by the geometric series of Section 1. The $n$-th term is the value on $h^n$ of the continuous $n$-linear map $(h_1, \dots, h_n) \mapsto (-1)^n u^{-1}h_1 u^{-1}h_2 \cdots u^{-1}h_n u^{-1}$, so this is a power series in $h$ with a positive radius. $\square$

The statement in Mathlib is `analyticAt_inverse (z : Aˣ) : AnalyticAt 𝕜 Ring.inverse z`, where `Ring.inverse` is the inverse extended by $0$ to the non-invertible elements.

**Theorem (Isolated zeros).** Let $f : \mathbb{K} \to F$ be analytic at $z_0$. Then either $f = 0$ on a neighbourhood of $z_0$, or $f(z) \ne 0$ for all $z \ne z_0$ in a neighbourhood of $z_0$.

*Proof.* Write $f(z_0 + t) = \sum_n a_n t^n$ for $|t| < r$. If every $a_n$ is $0$, then $f = 0$ on $B(z_0, r)$. Otherwise let $k$ be the order. Then
$$f(z_0 + t) = t^k g(t), \qquad g(t) = \sum_n a_{n+k}t^n.$$
The series of $g$ converges for $|t| < r$: if $\|a_n\|s^n \le C$, then $\|a_{n+k}\|s^n \le C s^{-k}$. So $g$ is analytic at $0$ and continuous there by Section 1, and $g(0) = a_k \ne 0$. Hence $g(t) \ne 0$ for $|t| < \delta$, for some $\delta > 0$, and $f(z_0 + t) = t^k g(t) \ne 0$ for $0 < |t| < \delta$. $\square$

::: mathlib
`AnalyticAt.eventually_eq_zero_or_eventually_ne_zero` · `Mathlib.Analysis.Analytic.IsolatedZeros`

For `f : 𝕜 → E` with `hf : AnalyticAt 𝕜 f z₀`, it gives `(∀ᶠ z in 𝓝 z₀, f z = 0) ∨ ∀ᶠ z in 𝓝[≠] z₀, f z ≠ 0`. The factorization is `AnalyticAt.exists_eventuallyEq_pow_smul_ne_zero_iff`: $f = (z - z_0)^n \cdot g$ near $z_0$ with $g(z_0) \ne 0$ if and only if $f$ is not eventually zero. The form with frequent zeros is `AnalyticAt.frequently_zero_iff_eventually_zero`, and the form for a series is `HasFPowerSeriesAt.locally_ne_zero`.

<?decl AnalyticAt.eventually_eq_zero_or_eventually_ne_zero?>
:::

**Theorem (Identity theorem).** Let $U \subseteq E$ be open and preconnected, and let $f : E \to F$ be analytic on $U$. If $f = 0$ on a neighbourhood of a point $z_0 \in U$, then $f = 0$ on $U$.

*Proof.* Let $S$ be the set of $z \in U$ such that $f = 0$ on a neighbourhood of $z$. It contains $z_0$ and it is open. The set $U \setminus S$ is open too, as follows. Since $U$ is preconnected and $S \ne \emptyset$, this gives $U \setminus S = \emptyset$, so $S = U$.

Let $z \in U$ be a limit of points of $S$. Choose $r > 0$ such that $f$ has an expansion $p$ on $B(z, r)$. Choose $w \in S$ with $\|w - z\| < r/2$. By the change of origin of Section 2, $f$ has an expansion $q$ on $B(w, r')$ with $r' = r - \|w - z\| > r/2$. Since $f = 0$ near $w$, every $q_k$ vanishes on the diagonal: for each $y$, the function $t \mapsto f(w + ty) = \sum_k q_k(y^k)t^k$ is $0$ near $t = 0$, and the coefficients of a power series in one variable are unique by Section 1. So $f(w + y) = \sum_k q_k(y^k) = 0$ for $\|y\| < r'$. The ball $B(w, r')$ is open and contains $z$, because $\|z - w\| < r/2 < r'$. So $z \in S$.

This shows that the points of $U$ that are limits of $S$ lie in $S$. Each $z \in U \setminus S$ therefore has a neighbourhood in $U$ that does not meet $S$, so $U \setminus S$ is open. $\square$

**Corollary (Identity theorem in one variable).** Let $U \subseteq \mathbb{K}$ be open and preconnected, let $f, g$ be analytic on $U$, and let $z_0 \in U$ be a limit of points $z \ne z_0$ with $f(z) = g(z)$. Then $f = g$ on $U$.

*Proof.* The function $f - g$ is analytic at $z_0$ and vanishes at points $z \ne z_0$ arbitrarily close to $z_0$. By the isolated zeros, it vanishes on a neighbourhood of $z_0$. By the identity theorem, $f - g = 0$ on $U$. $\square$

::: mathlib
`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq` · `Mathlib.Analysis.Analytic.Uniqueness`

From `hf : AnalyticOnNhd 𝕜 f U`, `hg : AnalyticOnNhd 𝕜 g U`, `hU : IsPreconnected U`, `h₀ : z₀ ∈ U` and `hfg : f =ᶠ[𝓝 z₀] g`, it gives `EqOn f g U`. It is deduced from `AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero` applied to `f - g`. The step on the vanishing coefficients is `HasFPowerSeriesAt.apply_eq_zero`. The corollary in one variable is `AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq`, with the hypothesis `∃ᶠ z in 𝓝[≠] z₀, f z = g z`.

<?decl AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq?>
:::

**Theorem (Analytic inverse function theorem).** Let $E$ and $F$ be Banach spaces, let $f$ be analytic at $a$, and let $Df(a)$ be invertible. Then the local inverse of $f$ from Chapter 6 is analytic at $f(a)$.

This section does not prove the theorem. One proof solves $q \circ p = \mathrm{id}$ for the coefficients of $q$ degree by degree and then bounds them. For $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, it also follows from the smooth inverse function theorem of Chapter 6 with $n = \omega$, because Mathlib defines $C^\omega$ as analytic.

::: mathlib
`OpenPartialHomeomorph.hasFPowerSeriesAt_symm` · `Mathlib.Analysis.Analytic.Inverse`

For an open partial homeomorphism `f`, `h : HasFPowerSeriesAt f p a` with `a ∈ f.source` and `hp : p 1 = (continuousMultilinearCurryFin1 𝕜 E F).symm i` for an equivalence `i`, it gives `HasFPowerSeriesAt f.symm (p.leftInv i a) (f a)`. The series `FormalMultilinearSeries.leftInv p i a` is the formal inverse, defined by the recursion on the degree. The form with `AnalyticAt` is `OpenPartialHomeomorph.analyticAt_symm`, and the one-variable form is `AnalyticAt.analyticAt_localInverse` in `Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic`.

<?decl OpenPartialHomeomorph.hasFPowerSeriesAt_symm?>
:::

### Examples

**Example (Inverting $x + x^2$).** Let $f(x) = x + x^2$ on $\mathbb{R}$, with $f'(0) = 1$. Solving $y = x + x^2$ near $0$ gives
$$x = \frac{-1 + \sqrt{1 + 4y}}{2} = y - y^2 + 2y^3 - 5y^4 + \cdots.$$
The coefficients come from the binomial series of $\sqrt{1 + 4y}$, and up to sign they are the Catalan numbers $1, 1, 2, 5, 14, \dots$. The radius is $\frac14$: the binomial series of $\sqrt{1 + u}$ has radius $1$, and $u = 4y$. Section 1 of Chapter 6 found a preimage for $|y| \le \frac18$; the analytic theory gives the larger disc.

**Example (The zeros of the sine).** Over $\mathbb{C}$, $\sin z = \sum_n (-1)^n z^{2n+1}/(2n+1)!$. So $\sin z = z\,g(z)$ with $g(z) = \sum_n (-1)^n z^{2n}/(2n+1)!$ and $g(0) = 1$, and the zero at $0$ has order $1$. Since $\sin(z + \pi k) = \pm\sin z$, every zero $\pi k$ has order $1$.

**Counterexample (Connectedness is needed).** On $U = (-1, 0) \cup (0, 1)$, let $f = 0$ on $(-1, 0)$ and $f = 1$ on $(0, 1)$. It is analytic on $U$, since it is locally constant, and it vanishes on an open set, but not on $U$. The set $U$ is not preconnected.

### The library around it

In practice `fun_prop` proves analyticity from `AnalyticAt.add`, `AnalyticAt.mul`, `AnalyticAt.comp` and the basic functions. The uniqueness results are in `Mathlib.Analysis.Analytic.Uniqueness` for any `E`, and in `Mathlib.Analysis.Analytic.IsolatedZeros` for `𝕜 → E`.

The order of a zero is `analyticOrderAt f z₀ : ℕ∞`, in `Mathlib.Analysis.Analytic.Order`, for $f : 𝕜 \to E$. It is $\top$ when $f$ vanishes near $z_0$ (`analyticOrderAt_eq_top`), $0$ when $f$ is not analytic at $z_0$ or $f(z_0) \ne 0$ (`analyticOrderAt_eq_zero`), and otherwise the $n$ of the definition above: `AnalyticAt.analyticOrderAt_eq_natCast` states $f(z) = (z - z_0)^n g(z)$ with $g(z_0) \ne 0$. The version `analyticOrderNatAt` takes values in `ℕ`, with $0$ for the order $\top$. The order is additive on products (`analyticOrderAt_mul`, `analyticOrderAt_smul`), at least the minimum on sums (`le_analyticOrderAt_add`), and it drops by one under the derivative at a zero (`analyticOrderAt_deriv_of_pos`). The lemma `analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero` reads it from the iterated derivatives, and `AnalyticAt.analyticOrderAt_comp` gives the order of a composition. On a connected open set, the order is either finite at every point or $\top$ at every point (`AnalyticOnNhd.exists_analyticOrderAt_ne_top_iff_forall`), and the points of order $0$ or $\top$ form a codiscrete set (`AnalyticOnNhd.codiscrete_setOfPred_analyticOrderAt_eq_zero_or_top`).

The module `Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic` gives the inverse function theorem in one variable: if $f : 𝕜 \to 𝕜$ is analytic at $x$ and $f'(x) \ne 0$, the local inverse is analytic at $f(x)$ (`AnalyticAt.analyticAt_localInverse`), and $g \circ f$ is analytic at $x$ if and only if $g$ is analytic at $f(x)$ (`analyticAt_comp_iff_of_deriv_ne_zero`). The module `Mathlib.Analysis.Analytic.WithLp` proves that the identifications `WithLp.toLp` and `WithLp.ofLp` between a product or a product of a family and its $L^p$ version are analytic (`WithLp.analyticOn_toLp`, `PiLp.analyticOn_ofLp`), so analyticity passes to the spaces `WithLp p (E × F)` and `PiLp p E`.

Common errors of a learner:

- Applying the identity theorem with `AnalyticOn` in place of `AnalyticOnNhd`.
- Applying the one-variable corollary in several variables. In $\mathbb{R}^2$ the function $xy$ vanishes on the two axes, which accumulate at $0$, but it is not zero.

### Exercises

1. (A) Show that $x \mapsto e^x/(1 + x^2)$ is analytic on $\mathbb{R}$.
2. (A) Compute the series of $e^{\sin z}$ at $0$ up to the term in $z^3$. Hint: the coefficient of $z^3$ is $0$.
3. (B) Let $f$ be analytic on $\mathbb{R}$ with $f(1/n) = 0$ for every $n \ge 1$. Show that $f = 0$.
4. (B) Show that no analytic $f$ on $(-1, 1)$ satisfies $f(1/n) = (-1)^n/n$ for every $n \ge 2$.
5. (B) Verify the coefficient $-5$ of $y^4$ in the inverse of $x + x^2$. Hint: iterate $x \mapsto y - x^2$ from $x = y$.
6. (C) Let $U \subseteq \mathbb{K}$ be open and preconnected, and let $f$ be analytic on $U$ and not identically $0$. Show that the zeros of $f$ in $U$ have no limit point in $U$, and that a compact subset of $U$ contains finitely many zeros.

### Notes and history

The isolated zeros and the identity theorem are classical results of the theory of functions of a complex variable. The proofs above use only power series, so they hold over $\mathbb{R}$, over $\mathbb{C}$ and in Banach spaces.

### Reference

<?reference?>
