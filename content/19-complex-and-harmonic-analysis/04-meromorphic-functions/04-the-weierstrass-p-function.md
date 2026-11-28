---
title: The Weierstrass ℘ function
kind: api
modules:
  - Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
explains:
  E2: [PeriodPair, PeriodPair.lattice, PeriodPair.weierstrassP, PeriodPair.hasSumLocallyUniformly_weierstrassP, PeriodPair.weierstrassP_add_coe, PeriodPair.order_weierstrassP, PeriodPair.weierstrassPExcept, PeriodPair.hasFPowerSeriesAt_weierstrassPExcept, PeriodPair.g₂, PeriodPair.derivWeierstrassP_sq]
  E1: auto
families: []
requires: [V19.C02, V19.C03, V17.C07]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The Weierstrass ℘ function

### Overview

An elliptic function is a meromorphic function on $\mathbb{C}$ with two periods $\omega_1, \omega_2$ that are linearly independent over $\mathbb{R}$. An elliptic function without poles is bounded, because it is bounded on the compact parallelogram spanned by the periods. So by Liouville's theorem of Chapter 3 it is constant. A nonconstant elliptic function must have poles, and the simplest one has a double pole at each period. This is the Weierstrass function
$$\wp(z) = \frac{1}{z^2} + \sum_{\ell \in \Lambda \setminus \{0\}} \Big(\frac{1}{(z - \ell)^2} - \frac{1}{\ell^2}\Big),$$
where $\Lambda = \mathbb{Z}\omega_1 + \mathbb{Z}\omega_2$ is the lattice of periods.

The module `Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass` defines $\wp$ and its derivative $\wp'$. It proves that the series converge locally uniformly, that $\wp$ is even, periodic and meromorphic with a double pole at each lattice point, and that it satisfies the differential equation
$$\wp'(z)^2 = 4\wp(z)^3 - g_2\wp(z) - g_3.$$
This section describes that interface. It uses the meromorphic functions and orders of Sections 1 and 2, the power series of Volume 17, and locally uniform limits of Chapter 3.

### The library around it

#### Period pairs and the lattice

The structure `PeriodPair` has two fields `PeriodPair.ω₁` and `PeriodPair.ω₂` of type $\mathbb{C}$ and a proof `PeriodPair.indep` that they are linearly independent over $\mathbb{R}$. The lattice `PeriodPair.lattice L` is the $\mathbb{Z}$-submodule of $\mathbb{C}$ spanned by the two periods. `PeriodPair.mem_lattice` states that $x$ is in the lattice if and only if $x = m\omega_1 + n\omega_2$ for integers $m, n$.

The lattice is a lattice in the real vector space $\mathbb{C}$. It is discrete and closed (`PeriodPair.isClosed_lattice`), it is an instance of `IsZLattice`, it has rank $2$ (`PeriodPair.finrank_lattice`), and `PeriodPair.latticeBasis` and `PeriodPair.latticeEquivProd` identify it with $\mathbb{Z}^2$. Every subset of the lattice is closed (`PeriodPair.isClosed_of_subset_lattice`), so the complement of the lattice minus any set is open (`PeriodPair.isOpen_compl_lattice_sdiff`). Half a period is not a period (`PeriodPair.ω₁_div_two_notMem_lattice`), and more generally `PeriodPair.mul_ω₁_add_mul_ω₂_mem_lattice` decides membership for rational coefficients.

#### The definition and its junk values

The definition is a single sum over the lattice:
$$\texttt{PeriodPair.weierstrassP}\ L\ z = \sum_{\ell \in \Lambda} \Big(\frac{1}{(z - \ell)^2} - \frac{1}{\ell^2}\Big).$$
The term $\ell = 0$ has no special case. In Lean, $1/0 = 0$, so the term for $\ell = 0$ is $1/z^2 - 0$, which is the leading term $1/z^2$ of the classical formula. At a lattice point $z = \ell_0$, the term for $\ell_0$ is $1/0 - 1/\ell_0^2$ in Lean, and the sum gives the junk value $\wp(\ell_0) = 0$ (`PeriodPair.weierstrassP_coe`). The function is not continuous there (`PeriodPair.not_continuousAt_weierstrassP`). The notation `℘[L]` in the namespace `PeriodPair` stands for `PeriodPair.weierstrassP L`.

The convergence comes from a bound on the terms. For $|z| < r$ and $|\ell| \ge 2r$,
$$\Big|\frac{1}{(z - \ell)^2} - \frac{1}{\ell^2}\Big| \le \frac{10r}{|\ell|^3},$$
which is `PeriodPair.weierstrassP_bound`. The sum of $|\ell|^{-3}$ over a lattice in $\mathbb{R}^2$ is finite. So the series converges absolutely, uniformly on the disc $|z| < r$ after the finitely many terms with $|\ell| < 2r$.

**Theorem.** The series of $\wp$ converges locally uniformly on $\mathbb{C}$ to $\wp$, and $\wp$ is differentiable on $\mathbb{C} \setminus \Lambda$.

*Proof.* Fix $r > 0$. Only finitely many lattice points have $|\ell| < 2r$, because the lattice is discrete. The remaining terms satisfy the bound above, and $\sum |\ell|^{-3} < \infty$. So the tail converges uniformly on $|z| < r$ by the Weierstrass M-test. Each term is holomorphic off its pole, and a locally uniform limit of holomorphic functions is holomorphic (Chapter 3). $\square$

These are `PeriodPair.hasSumLocallyUniformly_weierstrassP` and `PeriodPair.differentiableOn_weierstrassP`. The general tool is `PeriodPair.hasSumLocallyUniformly_aux`. The derivative `PeriodPair.derivWeierstrassP L`, with notation `℘'[L]`, is defined as the sum of $-2/(z - \ell)^3$ (`PeriodPair.hasSum_derivWeierstrassP`). It satisfies `PeriodPair.deriv_weierstrassP`, `deriv ℘[L] = ℘'[L]` as functions on all of $\mathbb{C}$. The equation also holds at the lattice points, because both sides have the junk value $0$ there.

#### Symmetry and periodicity

**Theorem.** The function $\wp$ is even, and $\wp(z + \ell) = \wp(z)$ for every $\ell \in \Lambda$.

*Proof.* Evenness: replace $\ell$ by $-\ell$ in the sum, which permutes the lattice. Periodicity: the derivative $\wp'$ is the sum of $-2/(z - \ell)^3$, and translating by $\ell_0$ permutes the terms, so $\wp'$ is periodic. Then $\wp(z + \ell_0) - \wp(z)$ is constant on the connected set $\mathbb{C} \setminus \Lambda$. For $\ell_0 = \omega_1$, put $z = -\omega_1/2$, which is not in $\Lambda$. Evenness gives $\wp(\omega_1/2) - \wp(-\omega_1/2) = 0$. The same argument works for $\omega_2$, and the two periods generate $\Lambda$. $\square$

These are `PeriodPair.weierstrassP_neg` and `PeriodPair.weierstrassP_add_coe`, with the forms `PeriodPair.periodic_weierstrassP` and `PeriodPair.weierstrassP_sub_coe`. For the derivative, `PeriodPair.derivWeierstrassP_neg` states that $\wp'$ is odd, and `PeriodPair.derivWeierstrassP_add_coe` that it is periodic.

#### The sum minus one term, and the Laurent expansion

To study $\wp$ near a lattice point $\ell_0$, Mathlib removes the divergent term. The function `PeriodPair.weierstrassPExcept L l₀`, with notation `℘[L - l₀]`, is the same sum without the term for $\ell_0$. It is analytic at $\ell_0$ (`PeriodPair.analyticAt_weierstrassPExcept`), and
$$\wp(z) = \wp_{\ne \ell_0}(z) + \frac{1}{(z - \ell_0)^2} - \frac{1}{\ell_0^2}$$
by `PeriodPair.weierstrassPExcept_add`. For $\ell_0 \notin \Lambda$ nothing is removed (`PeriodPair.weierstrassPExcept_of_notMem`).

The power series of $\wp_{\ne \ell}$ at $\ell$ has the coefficients
$$a_0 = \wp_{\ne \ell}(\ell), \qquad a_i = (i + 1)\sum_{\lambda \in \Lambda} \frac{1}{(\lambda - \ell)^{i+2}} \quad (i \ge 1),$$
by `PeriodPair.hasFPowerSeriesAt_weierstrassPExcept`. The sum is `PeriodPair.sumInvPow L ℓ (i + 2)`, and in Lean the term $\lambda = \ell$ is $0^{-1} = 0$, so the sum omits it. At $\ell = 0$ the sums are the Eisenstein sums $G_n = \sum_{\lambda \ne 0} \lambda^{-n}$, the function `PeriodPair.G` (`PeriodPair.sumInvPow_zero`). The odd sums vanish by the symmetry $\lambda \mapsto -\lambda$ (`PeriodPair.G_eq_zero_of_odd`). So near $0$,
$$\wp(z) = \frac{1}{z^2} + 3G_4 z^2 + 5G_6 z^4 + O(z^6).$$
The same expansion at $\ell_0$ shows that $\wp$ is meromorphic (`PeriodPair.meromorphic_weierstrassP`) with order $-2$ at each lattice point (`PeriodPair.order_weierstrassP`). Off the lattice, `PeriodPair.hasFPowerSeriesOnBall_weierstrassP` gives the power series on any closed ball that misses the lattice.

#### The differential equation

The invariants of the lattice are `PeriodPair.g₂`, which is $60G_4$, and `PeriodPair.g₃`, which is $140G_6$.

**Theorem.** For $z \notin \Lambda$, $\wp'(z)^2 = 4\wp(z)^3 - g_2\wp(z) - g_3$.

*Proof.* Let $F = \wp'^2 - 4\wp^3 + g_2\wp + g_3$. It is elliptic, and its only possible poles are at the lattice points. From the expansion of $\wp$ at $0$, $\wp'(z) = -2z^{-3} + 6G_4z + 20G_6z^3 + O(z^5)$. Then
$$\wp'^2 = 4z^{-6} - 24G_4z^{-2} - 80G_6 + O(z^2), \qquad 4\wp^3 = 4z^{-6} + 36G_4z^{-2} + 60G_6 + O(z^2).$$
So $F(z) = -60G_4z^{-2} - 140G_6 + g_2z^{-2} + g_3 + O(z^2) = O(z^2)$. Thus $F$ has a removable singularity at $0$ with value $0$, and by periodicity at every lattice point. Then $F$ is an elliptic function without poles, so it is constant by Liouville's theorem, and the constant is $F(0) = 0$. $\square$

This is `PeriodPair.derivWeierstrassP_sq`. The point $(\wp(z), \wp'(z))$ thus lies on the cubic curve $y^2 = 4x^3 - g_2x - g_3$. The module does not prove that this map from $\mathbb{C}/\Lambda$ to the curve is a bijection, and it does not connect `PeriodPair.G` to the Eisenstein series of the modular forms library.

#### Common errors

1. A learner writes the term $\ell = 0$ as a special case, as in the classical formula. In Mathlib, the sum runs over all of `PeriodPair.lattice L`, and the junk value $1/0 = 0$ makes the term for $0$ equal to $1/z^2$. Statements that remove one term use `PeriodPair.weierstrassPExcept`.
2. A learner uses `PeriodPair.weierstrassP_coe` as a fact about the pole. The value $0$ at a lattice point is a junk value. For the pole, use `PeriodPair.order_weierstrassP` or `PeriodPair.not_continuousAt_weierstrassP`.
3. A learner applies `PeriodPair.derivWeierstrassP_sq` at a lattice point. The hypothesis $z \notin \Lambda$ is needed: at a lattice point both sides take junk values, and the equation $0 = -g_3$ is false in general.

### Exercises

1. (A) Show that $\wp'(\omega_1/2) = 0$, from the facts that $\wp'$ is odd and periodic.
2. (A) Prove from `PeriodPair.mem_lattice` that $-\ell \in \Lambda$ for $\ell \in \Lambda$, and use it to show that $G_n = 0$ for odd $n$.
3. (B) Prove the bound of `PeriodPair.weierstrassP_bound`. Write the difference as $z(2\ell - z)/(\ell^2(z - \ell)^2)$ and use $|z - \ell| \ge |\ell|/2$.
4. (B) Compute the coefficient of $z^2$ in the power series of $\wp - 1/z^2$ at $0$ from `PeriodPair.hasFPowerSeriesAt_weierstrassPExcept`, and check that it is $3G_4$.
5. (B) Show that an elliptic function with a single simple pole in a fundamental parallelogram cannot exist. Use the residue theorem on the boundary of the parallelogram.
6. (C) Differentiate the differential equation to prove $\wp'' = 6\wp^2 - g_2/2$ off the lattice.

### Reference

<?reference?>
