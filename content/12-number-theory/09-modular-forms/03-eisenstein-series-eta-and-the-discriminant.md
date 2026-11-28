---
title: Eisenstein series, eta and the discriminant
kind: api
modules:
  - Mathlib.NumberTheory.ModularForms.EisensteinSeries.Defs
  - Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable
  - Mathlib.NumberTheory.ModularForms.EisensteinSeries.UniformConvergence
  - Mathlib.NumberTheory.ModularForms.EisensteinSeries.MDifferentiable
  - Mathlib.NumberTheory.ModularForms.EisensteinSeries.IsBoundedAtImInfty
  - Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
  - Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
  - Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Defs
  - Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Summable
  - Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Transform
  - Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.MDifferentiable
  - Mathlib.NumberTheory.ModularForms.RamanujanFormula
  - Mathlib.NumberTheory.ModularForms.DedekindEta
  - Mathlib.NumberTheory.ModularForms.Discriminant
explains:
  E2: [eisensteinSeries, EisensteinSeries.eisSummand, ModularForm.eisensteinSeriesMF, ModularForm.E, EisensteinSeries.E_qExpansion_coeff, EisensteinSeries.E2, EisensteinSeries.E2_slash_action, Derivative.serreDerivative_E₄, ModularForm.eta, ModularForm.discriminant]
  E1: auto
families: []
requires: [V19.C09, V19]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Eisenstein series, eta and the discriminant

### Overview

The first examples of modular forms are the Eisenstein series
$$G_k(z) = \sum_{(c, d) \neq (0, 0)} \frac{1}{(cz + d)^k}, \qquad k \geq 3.$$
The sum converges absolutely, and a change of variables $(c, d) \mapsto (c, d)\gamma$ gives the transformation law. Their $q$-expansions have the divisor sums $\sigma_{k-1}(n)$ as coefficients. In weight $2$ the sum does not converge absolutely, and the series $E_2$ is only quasimodular. The Dedekind eta function $\eta(z) = q^{1/24} \prod_{n \geq 1} (1 - q^n)$ gives the discriminant $\Delta = \eta^{24}$, the first cusp form.

The modules `Mathlib.NumberTheory.ModularForms.EisensteinSeries.Defs` to `Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic` define the series of weight $k \geq 3$ at level $\Gamma(N)$ and show that they are modular forms. The module `Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion` computes the $q$-expansions at level one. The four modules with E2 in their names treat weight $2$. `Mathlib.NumberTheory.ModularForms.RamanujanFormula` has the Ramanujan equations, and `Mathlib.NumberTheory.ModularForms.DedekindEta` and `Mathlib.NumberTheory.ModularForms.Discriminant` treat $\eta$ and $\Delta$. The definitions of modular forms and $q$-expansions are in Section 2.

### The library around it

#### Eisenstein series of level N

The summand is `EisensteinSeries.eisSummand k v z`, equal to $(v_0 z + v_1)^{-k}$ for $v \in \mathbb{Z}^2$. For $a \in (\mathbb{Z}/N\mathbb{Z})^2$, the set `EisensteinSeries.gammaSet N r a` contains the $v$ with $v \equiv a \pmod N$ and $\gcd(v_0, v_1) = r$. The Eisenstein series `eisensteinSeries a k`, a name in the root namespace, is

$$E_{a,k}(z) = \sum_{v \equiv a,\ \gcd(v_0, v_1) = 1} (v_0 z + v_1)^{-k},$$

a sum over the coprime pairs in the class $a$ only. An element $\gamma$ of $\mathrm{SL}_2(\mathbb{Z})$ permutes these sets, `EisensteinSeries.gammaSetEquiv`, so `EisensteinSeries.eisensteinSeries_slash_apply` gives

$$E_{a,k} \mid_k \gamma = E_{a\gamma,k}.$$

For $\gamma \in \Gamma(N)$, $a\gamma = a$, so the series is a slash invariant form for $\Gamma(N)$, `EisensteinSeries.eisensteinSeriesSIF a k`.

**Theorem.** For $k \geq 3$ and $N \neq 0$, the series is a modular form of weight $k$ and level $\Gamma(N)$.

*Proof.* There is a function $r(z) > 0$, `EisensteinSeries.r`, with $\lvert v_0 z + v_1 \rvert \geq r(z) \lVert v \rVert$ for the max norm, `EisensteinSeries.summand_bound`. The sum $\sum_{v \neq 0} \lVert v \rVert^{-k}$ converges for $k > 2$, `EisensteinSeries.summable_one_div_norm_rpow`, since there are $8n$ vectors of norm $n$. The function $r$ has a positive lower bound on each vertical strip, so the convergence is locally uniform, `EisensteinSeries.eisensteinSeries_tendstoLocallyUniformly`. A locally uniform limit of holomorphic functions is holomorphic, `EisensteinSeries.eisensteinSeriesSIF_mdifferentiable`. The bound at $\infty$, `EisensteinSeries.isBoundedAtImInfty_eisensteinSeriesSIF`, follows from the same estimate after each slash by $\mathrm{SL}_2(\mathbb{Z})$, and this is the condition at each cusp. $\square$

The result is `ModularForm.eisensteinSeriesMF hk a`, of type `ModularForm` for the image of `CongruenceSubgroup.Gamma N`.

#### Level one: E4 and E6

For $N = 1$ and $a = 0$ the set is all the coprime pairs. Since $v$ and $-v$ both appear, the normalized series is half of it:
$$E_k(z) = \frac{1}{2} \sum_{\gcd(c, d) = 1} \frac{1}{(cz + d)^k},$$
the form `ModularForm.E hk` of level $\mathrm{SL}_2(\mathbb{Z})$ for $k \geq 3$, with `ModularForm.E₄` and `ModularForm.E₆` for $k = 4, 6$. The sum over all nonzero pairs is $\zeta(k)$ times the sum over the coprime pairs, so it is $2\zeta(k) E_k$, `tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries`, because each nonzero pair is $r$ times a coprime pair, `EisensteinSeries.gammaSetDivGcdSigmaEquiv`.

**Theorem.** For even $k \geq 4$,
$$E_k(z) = 1 - \frac{2k}{B_k} \sum_{n \geq 1} \sigma_{k-1}(n) \, q^n, \qquad q = e^{2\pi i z}.$$

This is `EisensteinSeries.q_expansion_bernoulli`, with the form `EisensteinSeries.q_expansion_riemannZeta` in terms of $\zeta(k)$. The coefficient form is `EisensteinSeries.E_qExpansion_coeff`: coefficient $0$ is $1$ and coefficient $m \geq 1$ is $-\frac{2k}{B_k}\sigma_{k-1}(m)$. So $E_4 = 1 + 240q + \cdots$ and $E_6 = 1 - 504q - \cdots$. Then `EisensteinSeries.tendsto_E_atImInfty` gives the limit $1$ at $\infty$, and `EisensteinSeries.E_ne_zero` says $E_k \neq 0$.

*Proof idea.* Take the sum over all nonzero pairs. The pairs with $c = 0$ give $2\zeta(k)$. For fixed $c \geq 1$, the Lipschitz formula
$$\sum_{d \in \mathbb{Z}} \frac{1}{(z + d)^k} = \frac{(-2\pi i)^k}{(k-1)!} \sum_{m \geq 1} m^{k-1} e^{2\pi i m z}$$
at $cz$, summed over $c$, gives the divisor sums. Euler's formula for $\zeta(k)$ in terms of $B_k$ gives the first form. $\square$

#### The series of weight 2

In weight $2$ the double sum depends on the order of summation. `EisensteinSeries.G2` sums first over $d$ and then over $c$ along the symmetric intervals $[-N, N]$, and `EisensteinSeries.E2` is $G_2 / (2\zeta(2))$. Its $q$-expansion is
$$E_2(z) = 1 - 24 \sum_{n \geq 1} \sigma_1(n) \, q^n,$$
the statement `EisensteinSeries.E2_eq_tsum_cexp`, with the `HasSum` form `EisensteinSeries.hasSum_qExpansion_E2`. It is periodic, `EisensteinSeries.E2_T_transform`, bounded at $\infty$, `EisensteinSeries.isBoundedAtImInfty_E2`, and holomorphic, `E2_mdifferentiable`.

**Theorem.** For $\gamma \in \mathrm{SL}_2(\mathbb{Z})$ with bottom row $(c, d)$,
$$E_2 \mid_2 \gamma = E_2 - \frac{1}{2\zeta(2)} D_2(\gamma), \qquad D_2(\gamma)(z) = \frac{2\pi i c}{cz + d}.$$

This is `EisensteinSeries.E2_slash_action`, with `EisensteinSeries.D2` for the defect. The defect is a cocycle, `EisensteinSeries.D2_mul`, so it is enough to check the generators: $T$ is the period, and the main step is `EisensteinSeries.G2_S_transform` for $S$, where the change in the order of summation gives the correction term $2\pi i / z$.

#### Ramanujan's equations

With $D = \frac{1}{2\pi i}\frac{d}{dz}$ and the Serre derivative $\partial_k = D - \frac{k}{12}E_2$ of Section 2, the module `Mathlib.NumberTheory.ModularForms.RamanujanFormula` proves:

| Lean name | Identity |
|---|---|
| `Derivative.serreDerivative_E₂` | $\partial_1 E_2 = -E_4/12$ |
| `Derivative.serreDerivative_E₄` | $\partial_4 E_4 = -E_6/3$ |
| `Derivative.serreDerivative_E₆` | $\partial_6 E_6 = -E_4^2/2$ |
| `Derivative.normalizedDerivOfComplex_E₂` | $D E_2 = (E_2^2 - E_4)/12$ |
| `Derivative.normalizedDerivOfComplex_E₄` | $D E_4 = (E_2 E_4 - E_6)/3$ |
| `Derivative.normalizedDerivOfComplex_E₆` | $D E_6 = (E_2 E_6 - E_4^2)/2$ |

*Proof idea.* For $E_4$, the form $\partial_4 E_4$ has weight $6$ and level one. That space is one dimensional (Section 4), so $\partial_4 E_4 = c E_6$, and the constant terms give $c = -1/3$. The other two are similar. $\square$

#### The eta function and the discriminant

`ModularForm.eta` is the function $\eta(z) = e^{2\pi i z/24} \prod_{n \geq 0} (1 - q^{n+1})$ on $\mathbb{C}$, where `ModularForm.eta_q n z` is $q^{n+1}$ (`ModularForm.eta_q_eq_cexp`). The product converges locally uniformly on $\mathbb{H}$, `ModularForm.multipliableLocallyUniformlyOn_eta`, and $\eta$ has no zeros there, `ModularForm.eta_ne_zero`. Its logarithmic derivative is a multiple of $E_2$, `ModularForm.logDeriv_eta_eq_E2`:
$$\frac{\eta'(z)}{\eta(z)} = \frac{\pi i}{12} E_2(z).$$
The transformation law under $S$ is `ModularForm.eta_comp_eq_csqrt_I_inv`: $\eta(-1/z) = \sqrt{z/i}\,\eta(z)$, written with `Complex.sqrt`.

**Definition.** The discriminant is $\Delta = \eta^{24}$, `ModularForm.discriminant`. So $\Delta = q \prod_{n \geq 1} (1 - q^n)^{24}$, `ModularForm.discriminant_eq_q_prod`.

**Theorem.** $\Delta$ is a cusp form of weight $12$ and level $\mathrm{SL}_2(\mathbb{Z})$, it has no zeros on $\mathbb{H}$, and its $q$-expansion starts with $q$.

*Proof.* The invariance under $T$ and $S$ is `ModularForm.discriminant_T_invariant` and `ModularForm.discriminant_S_invariant`; the second one comes from the law for $\eta$ raised to the power $24$. These generate $\mathrm{SL}_2(\mathbb{Z})$. Holomorphy comes from the product, and the factor $q$ gives the limit $0$ at $\infty$, `ModularForm.discriminant_isZeroAtImInfty`. $\square$

The cusp form is `CuspForm.discriminant`, with `CuspForm.coe_discriminant` for its function. The facts `ModularForm.discriminant_ne_zero` and `ModularForm.discriminant_qExpansion_coeff_one` give the other two claims. From the logarithmic derivative of $\eta$, $D\Delta = E_2 \Delta$, `ModularForm.normalizedDerivOfComplex_discriminant`, so $\partial_{12} \Delta = 0$, `ModularForm.serreDerivative_discriminant`. The classical formula $1728\Delta = E_4^3 - E_6^2$ is in Section 4.

#### Common errors

1. `ModularForm.E hk` is normalized with constant term $1$: it is half of the sum over coprime pairs, not the sum $G_k$ over all pairs. The factor between them is `tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries`.
2. `EisensteinSeries.E2` is a function `UpperHalfPlane → ℂ`, not a `ModularForm`. Its transformation law has the extra term `EisensteinSeries.D2`.
3. `ModularForm.eta` is a function on `ℂ`, not on the upper half plane, so its results take the condition `z ∈ UpperHalfPlane.upperHalfPlaneSet` or a coercion from `UpperHalfPlane`. In contrast, `ModularForm.discriminant` takes a point of `UpperHalfPlane`.

### Exercises

1. (A) Use `EisensteinSeries.E_qExpansion_coeff` with $B_4 = -1/30$ and $B_6 = 1/42$ to get the coefficients $240$ and $-504$ of $q$ in $E_4$ and $E_6$.
2. (A) Use `ModularForm.discriminant_eq_q_prod` to show that the coefficient of $q^2$ in $\Delta$ is $-24$.
3. (B) Show from `EisensteinSeries.D2_mul` that $D_2(1) = 0$ and $D_2(\gamma^{-1}) = -D_2(\gamma) \mid_2 \gamma^{-1}$.
4. (B) Deduce $D\Delta = E_2\Delta$ from `ModularForm.logDeriv_eta_eq_E2`.
5. (C) Prove the Lipschitz formula from the partial fraction expansion of $\pi \cot(\pi z)$, and deduce the $q$-expansion of $E_k$ for even $k \geq 4$.
6. (C) Use `EisensteinSeries.E_qExpansion_coeff` and `ModularForm.qExpansion_mul` to show that $E_4^3 - E_6^2$ has zero constant term and coefficient $1728$ of $q$.

### Reference

<?reference?>
