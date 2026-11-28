---
title: Topology, evaluation and Gauss norms of power series
kind: api
modules:
  - Mathlib.RingTheory.MvPowerSeries.PiTopology
  - Mathlib.RingTheory.PowerSeries.PiTopology
  - Mathlib.RingTheory.MvPowerSeries.Evaluation
  - Mathlib.RingTheory.PowerSeries.Evaluation
  - Mathlib.RingTheory.MvPowerSeries.GaussNorm
  - Mathlib.RingTheory.PowerSeries.GaussNorm
  - Mathlib.RingTheory.Polynomial.GaussNorm
explains:
  E2: [MvPowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto, MvPowerSeries.WithPiTopology.as_tsum, MvPowerSeries.WithPiTopology.isTopologicallyNilpotent_iff_constantCoeff_isNilpotent, MvPowerSeries.HasEval, MvPowerSeries.eval₂, MvPowerSeries.aeval_unique, PowerSeries.aeval, MvPowerSeries.gaussNorm, Polynomial.gaussNorm_mul]
  E1: auto
families: []
requires: [V06.C05, V09.C06]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Topology, evaluation and Gauss norms of power series

### Overview

A power series $\sum_n a_n X^n$ is the limit of its partial sums, but only in a suitable topology. The natural one is the product topology: a sequence of power series converges when each coefficient converges, so the partial sums converge to the series when the coefficients of $R$ carry the discrete topology. In this topology the ring of power series is complete, the polynomials are dense, and a series $f$ with $f(0)$ nilpotent has powers that tend to $0$. These facts are the base for the evaluation of a power series at an element of a complete topological ring, and for the substitution of one power series into another in the next section.

The evaluation $f(a)$ of a power series at $a$ makes sense when the powers of $a$ tend to $0$. For example, in the ring $\mathbb{Z}_p$ of $p$-adic integers the series $\sum_n X^n$ can be evaluated at $p$, and its value is $1/(1 - p)$. The library builds evaluation by extension of the evaluation of polynomials by continuity, and proves that it is the unique continuous algebra map with given values on the variables.

The Gauss norm of a power series $f$ with respect to an absolute value $v$ on the coefficients and a real number $c$ is the supremum of $v(a_n) c^n$. For polynomials and a nonarchimedean absolute value it is multiplicative, and so it extends $v$ to $R[X]$. This section is a guide to the seven modules on the product topology, on evaluation and on Gauss norms.

### The library around it

**The product topology.** The ring of power series is a function type, so a topology on it is not an instance by default: the library offers several topologies. The module `Mathlib.RingTheory.MvPowerSeries.PiTopology` puts the product topology in the namespace MvPowerSeries.WithPiTopology. After `open MvPowerSeries.WithPiTopology` the instances `MvPowerSeries.WithPiTopology.instTopologicalSpace` and `MvPowerSeries.WithPiTopology.instUniformSpace` are active. A family converges exactly when each coefficient converges:
$$f_i \to g \iff \operatorname{coeff}_d f_i \to \operatorname{coeff}_d g \text{ for all } d,$$
which is `MvPowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto`. The coefficient maps are continuous, `MvPowerSeries.WithPiTopology.continuous_coeff`, and so is the constant coefficient, `MvPowerSeries.WithPiTopology.continuous_constantCoeff`. With a topological ring of coefficients the series form a topological ring, `MvPowerSeries.WithPiTopology.instIsTopologicalRing`, which is complete when $R$ is complete, `MvPowerSeries.WithPiTopology.instCompleteSpace`, and Hausdorff when $R$ is Hausdorff, `MvPowerSeries.WithPiTopology.instT2Space`.

**Sums and products.** For a Hausdorff ring of coefficients a series is the sum of its monomials,
$$f = \sum_d \operatorname{coeff}_d(f) \, X^d,$$
which is `MvPowerSeries.WithPiTopology.as_tsum`, and the polynomials are dense, `MvPowerSeries.WithPiTopology.denseRange_toMvPowerSeries`. The truncations of $f$ tend to $f$, `MvPowerSeries.WithPiTopology.tendsto_trunc_atTop`. A family is summable when the orders of its members tend to infinity, `MvPowerSeries.WithPiTopology.summable_of_tendsto_order_atTop_nhds_top`, and a product $\prod_i (1 + f_i)$ is multipliable under the same condition, `MvPowerSeries.WithPiTopology.multipliable_one_add_of_tendsto_order_atTop_nhds_top`. The geometric series is an inverse: if the constant coefficient of $f$ is $0$, then
$$(1 - f) \sum_{i \ge 0} f^i = 1,$$
which is `MvPowerSeries.WithPiTopology.one_sub_mul_tsum_pow_of_constantCoeff_eq_zero`. For a discrete ring of coefficients, the powers of $f$ tend to $0$ exactly when the constant coefficient of $f$ is nilpotent, `MvPowerSeries.WithPiTopology.isTopologicallyNilpotent_iff_constantCoeff_isNilpotent`.

The module `Mathlib.RingTheory.PowerSeries.PiTopology` states the same results for one variable, in the namespace PowerSeries.WithPiTopology: `PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto`, `PowerSeries.as_tsum`, `PowerSeries.WithPiTopology.summable_of_tendsto_order_atTop_nhds_top` and the others. It adds the Euler product of the theory of partitions: the product $\prod_{n \ge 1} (1 - X^n)$ exists, `PowerSeries.WithPiTopology.multipliable_one_sub_X_pow`, and it is nonzero over a nontrivial Hausdorff ring, `PowerSeries.WithPiTopology.tprod_one_sub_X_pow_ne_zero`.

**Evaluation.** The module `Mathlib.RingTheory.MvPowerSeries.Evaluation` takes a family $a$ of elements of a topological ring $S$. The predicate `MvPowerSeries.HasEval a` holds when each $a_s$ is topologically nilpotent, that is, its powers tend to $0$, and when $a_s$ tends to $0$ along the cofinite filter. For finitely many variables the second condition is automatic. Such families form an ideal, `MvPowerSeries.hasEvalIdeal`, in a ring with a linear topology. For a ring homomorphism $\varphi : R \to S$ the evaluation `MvPowerSeries.eval₂ φ a` is defined by extension by continuity of the evaluation of polynomials. It agrees with `MvPolynomial.eval₂` on polynomials, `MvPowerSeries.eval₂_coe`, and under `MvPowerSeries.HasEval a` with the right completeness and topology hypotheses it is a sum:
$$\operatorname{eval}_2(\varphi, a)(f) = \sum_d \varphi(\operatorname{coeff}_d f) \, a^d,$$
which is `MvPowerSeries.eval₂_eq_tsum`. It is continuous, `MvPowerSeries.continuous_eval₂`, and it is a ring map `MvPowerSeries.eval₂Hom`. For an $R$-algebra $S$ the algebra map is `MvPowerSeries.aeval`, with `MvPowerSeries.aeval_coe` for polynomials and `MvPowerSeries.continuous_aeval`. It is the only continuous algebra map that sends $X_s$ to $a_s$, `MvPowerSeries.aeval_unique`. The module `Mathlib.RingTheory.PowerSeries.Evaluation` gives the same objects in one variable: `PowerSeries.HasEval a`, `PowerSeries.eval₂`, `PowerSeries.aeval`, `PowerSeries.aeval_eq_sum` and `PowerSeries.aeval_unique`, with `PowerSeries.hasEval_iff` to pass to the multivariate form.

**Gauss norms.** The module `Mathlib.RingTheory.MvPowerSeries.GaussNorm` takes a function $v : R \to \mathbb{R}$ and real numbers $c_s$, one for each variable, and defines
$$\|f\| = \sup_d v(\operatorname{coeff}_d f) \prod_s c_s^{d_s},$$
which is `MvPowerSeries.gaussNorm v c f`. The supremum is a real supremum, so it is meaningful only when the set is bounded above, the predicate `MvPowerSeries.HasGaussNorm v c f`. Each term is below the norm, `MvPowerSeries.le_gaussNorm`. For a nonnegative nonarchimedean $v$ the norm satisfies the strong triangle inequality, `MvPowerSeries.gaussNorm_add_le_max`. For a submultiplicative $v$ it is submultiplicative, `MvPowerSeries.gaussNorm_mul_le`, and `MvPowerSeries.gaussNorm_mul_eq_mul` gives equality under a hypothesis on the coefficients that reach the norm, `MvPowerSeries.AchievesGaussNorm`. The module `Mathlib.RingTheory.PowerSeries.GaussNorm` specializes to one variable, with `PowerSeries.gaussNorm_eq`: the norm is $\sup_i v(a_i) c^i$.

**The Gauss norm of a polynomial.** The module `Mathlib.RingTheory.Polynomial.GaussNorm` defines `Polynomial.gaussNorm v c p` as the maximum of $v(p_i) c^i$, which exists because $p$ has finitely many coefficients, `Polynomial.exists_eq_gaussNorm`. On a monomial it is $v(r) c^n$, `Polynomial.gaussNorm_monomial`, and it agrees with the norm of $p$ as a power series, `Polynomial.gaussNorm_coe_powerSeries`. The main result is the lemma of Gauss: for a nonarchimedean absolute value $v$ and $c > 0$,
$$\|p q\| = \|p\| \, \|q\|,$$
which is `Polynomial.gaussNorm_mul`. So the Gauss norm is an absolute value on $R[X]$, `Polynomial.gaussNorm_isAbsoluteValue`, and it is nonarchimedean, `Polynomial.isNonarchimedean_gaussNorm`. For $c = 1$ and the $p$-adic absolute value on $\mathbb{Z}$ this is a form of the lemma of Gauss on primitive polynomials of Chapter 5, Section 1.

#### Common errors

1. The product topology is not a global instance. A statement about limits of power series fails to elaborate, or uses the wrong topology, without `open MvPowerSeries.WithPiTopology` or `open PowerSeries.WithPiTopology`. Several lemmas also need the discrete topology on $R$, often given by a local instance.
2. `MvPowerSeries.gaussNorm` is a real supremum. When the set of values is not bounded above, the supremum has the junk value $0$, so most lemmas need `MvPowerSeries.HasGaussNorm` as a hypothesis.
3. `MvPowerSeries.eval₂` is defined for every family $a$, but it is the expected sum only under `MvPowerSeries.HasEval a` and the hypotheses of completeness. Do not apply `MvPowerSeries.eval₂_eq_tsum` without them.

### Exercises

1. (A) With `PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto`, prove that the sequence $X^n$ tends to $0$ in $\mathbb{Z}[[X]]$ for the product topology with discrete coefficients.
2. (A) Use `MvPowerSeries.WithPiTopology.one_sub_mul_tsum_pow_of_constantCoeff_eq_zero` to find the inverse of $1 - X - Y$ in $\mathbb{Z}[[X, Y]]$ as a sum, and compute its coefficient of $X^2 Y$.
3. (B) Let $R$ be discrete. Prove that $1 + X$ is not topologically nilpotent in $R[[X]]$ when $R$ is nontrivial, and that $X$ is.
4. (B) Compute `Polynomial.gaussNorm` for $p = 2 + 6X + 3X^2$ over $\mathbb{Z}$ with the $3$-adic absolute value and $c = 1$, and check `Polynomial.gaussNorm_mul` for $p \cdot (1 + 3X)$.
5. (B) Prove from `MvPowerSeries.aeval_unique` that two continuous algebra maps $R[[X]] \to S$ that agree on $X$ are equal.
6. (C) Let $p$ be a prime number and give $\mathbb{Z}_p$ its $p$-adic topology. Prove that `PowerSeries.HasEval (p : ℤ_[p])` holds, and compute `PowerSeries.aeval` of $\sum_n X^n$ at $p$.

### Reference

<?reference?>
