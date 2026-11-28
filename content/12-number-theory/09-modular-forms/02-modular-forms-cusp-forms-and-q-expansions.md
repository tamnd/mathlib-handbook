---
title: Modular forms, cusp forms and q-expansions
kind: api
modules:
  - Mathlib.NumberTheory.ModularForms.SlashActions
  - Mathlib.NumberTheory.ModularForms.SlashInvariantForms
  - Mathlib.NumberTheory.ModularForms.Basic
  - Mathlib.NumberTheory.ModularForms.BoundedAtCusp
  - Mathlib.NumberTheory.ModularForms.CuspFormSubmodule
  - Mathlib.NumberTheory.ModularForms.Bounds
  - Mathlib.NumberTheory.ModularForms.Identities
  - Mathlib.NumberTheory.ModularForms.Petersson
  - Mathlib.NumberTheory.ModularForms.NormTrace
  - Mathlib.NumberTheory.ModularForms.QExpansion
  - Mathlib.NumberTheory.ModularForms.QExpansionInjective
  - Mathlib.NumberTheory.ModularForms.OrderAtInfty
  - Mathlib.NumberTheory.ModularForms.Derivative
explains:
  E2: [SlashAction, SlashInvariantForm, ModularForm, CuspForm, UpperHalfPlane.qExpansion, ModularForm.hasSum_qExpansion, ModularForm.qExpansionAlgHom_injective, CuspFormClass.qExpansion_isBigO, ModularForm.isZero_of_neg_weight, Derivative.serreDerivative]
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

## Modular forms, cusp forms and q-expansions

### Overview

A modular form of weight $k$ for a group $\Gamma$ is a holomorphic function $f$ on the upper half plane $\mathbb{H}$ with $f(\gamma z) = (cz + d)^k f(z)$ for each $\gamma \in \Gamma$, and with growth control at the cusps. A cusp form also tends to $0$ at the cusps. Because $f$ is periodic, it has a Fourier expansion $f(z) = \sum_{n \geq 0} a_n q^n$ in the variable $q = e^{2\pi i z/h}$, its $q$-expansion. Most of the arithmetic of a modular form is in the coefficients $a_n$.

This section covers the definitions and the general results that hold at each level. The slash action and the invariant functions are in `Mathlib.NumberTheory.ModularForms.SlashActions` and `Mathlib.NumberTheory.ModularForms.SlashInvariantForms`. The structures of modular forms and cusp forms are in `Mathlib.NumberTheory.ModularForms.Basic`, with the conditions at the cusps in `Mathlib.NumberTheory.ModularForms.BoundedAtCusp`. The $q$-expansion is in `Mathlib.NumberTheory.ModularForms.QExpansion` and `Mathlib.NumberTheory.ModularForms.QExpansionInjective`, and the order at $\infty$ in `Mathlib.NumberTheory.ModularForms.OrderAtInfty`. Bounds, the Petersson product, the change of level and the Serre derivative are in the other modules of the list. The groups and the cusps are in Section 1.

### The library around it

#### The slash action

The class `SlashAction β G α` gives an action of a monoid $G$ on $\alpha$ for each "weight" in $\beta$, with the notation `f ∣[k] γ` for `SlashAction.map k γ f`. The main instance is for functions $\mathbb{H} \to \mathbb{C}$ and $G = \mathrm{GL}_2(\mathbb{R})$. For $\gamma$ with entries $a, b, c, d$, `ModularForm.slash_def` gives
$$(f \mid_k \gamma)(z) = \sigma_\gamma\bigl(f(\gamma z)\bigr) \, \lvert \det \gamma \rvert^{k-1} \, (cz + d)^{-k},$$
where `UpperHalfPlane.denom` is $cz + d$, and $\sigma_\gamma$, `UpperHalfPlane.σ`, is the identity if $\det \gamma > 0$ and complex conjugation if $\det \gamma < 0$. So the action is defined for all of $\mathrm{GL}_2(\mathbb{R})$, and on $\mathrm{SL}_2(\mathbb{Z})$ it is the usual factor of automorphy. The module also has the rules for sums, scalars and products, for example `ModularForm.mul_slash`.

#### Slash invariant forms, modular forms and cusp forms

**Definition.** Let $\Gamma \leq \mathrm{GL}_2(\mathbb{R})$ and $k \in \mathbb{Z}$.

1. A slash invariant form, `SlashInvariantForm Γ k`, is a function $f$ with $f \mid_k \gamma = f$ for each $\gamma \in \Gamma$.
2. A modular form, `ModularForm Γ k`, is a slash invariant form that is holomorphic on $\mathbb{H}$ and bounded at each cusp of $\Gamma$.
3. A cusp form, `CuspForm Γ k`, is a slash invariant form that is holomorphic and zero at each cusp.

Holomorphy is stated with manifold derivatives, the predicate `MDiff f`. The conditions at a cusp $c$ are `OnePoint.IsBoundedAt c f k` and `OnePoint.IsZeroAt c f k`: move $c$ to $\infty$ by an element of $\mathrm{SL}_2(\mathbb{R})$, slash, and ask for `UpperHalfPlane.IsBoundedAtImInfty` or `UpperHalfPlane.IsZeroAtImInfty`. For a cusp of $\mathrm{SL}_2(\mathbb{Z})$ the test reduces to all $\gamma \in \mathrm{SL}_2(\mathbb{Z})$, `OnePoint.isBoundedAt_iff_forall_SL2Z`.

The classes `SlashInvariantFormClass`, `ModularFormClass` and `CuspFormClass` let a theorem apply to each type of functions with these properties. Each `ModularForm Γ k` and `CuspForm Γ k` is a complex vector space. If $\Gamma$ satisfies `Subgroup.HasDetPlusMinusOne`, `ModularForm.mul` multiplies a form of weight $k_1$ and a form of weight $k_2$ into a form of weight $k_1 + k_2$, and `ModularForm.pow` raises to a power. With `Subgroup.HasDetOne`, `ModularForm.const` gives the constant forms of weight $0$. The weights are part of the type, so the direct sum over $k \in \mathbb{Z}$ is a graded ring. Use `ModularForm.mcast` to move a form along an equality of weights.

To check invariance, generators are enough: `SlashInvariantForm.slash_action_generators` reduces the condition for $\Gamma = \langle s \rangle$ to the elements of $s$. For $\Gamma(N)$, `SlashInvariantForm.T_zpow_width_invariant` gives the period $N$.

#### Cusp forms in the space of modular forms

The linear map `CuspForm.toModularFormₗ` is injective, `CuspForm.toModularFormₗ_injective`. Its image is the submodule `ModularForm.cuspFormSubmodule Γ k`, with the predicate `ModularForm.IsCuspForm`. A modular form is a cusp form if and only if it is zero at each cusp, `ModularForm.isCuspForm_iff`. At level $\mathrm{SL}_2(\mathbb{Z})$ only the cusp $\infty$ is necessary, and `ModularForm.isCuspForm_iff_coeffZero_eq_zero` says that $f$ is a cusp form if and only if $a_0 = 0$. The map `ModularForm.toCuspForm` makes the cusp form from this condition.

#### The q-expansion

Let $h > 0$ be a strict period of $\Gamma$ (Section 1), and let $q_h(z) = e^{2\pi i z/h}$, `Function.Periodic.qParam h z`. A function $f$ with period $h$ is $F \circ q_h$ for a function $F$ on the punctured unit disc. The function `UpperHalfPlane.cuspFunction h f` is $F$, with the limit at $0$ as its value there. If $f$ is holomorphic and bounded at $\infty$, then $F$ is holomorphic at $0$ by the removable singularity theorem. The $q$-expansion `UpperHalfPlane.qExpansion h f` is its Taylor series, a term of `PowerSeries ℂ`, with coefficients
$$a_m = \frac{F^{(m)}(0)}{m!},$$
the statement `UpperHalfPlane.qExpansion_coeff`. The coefficients are also contour integrals, `UpperHalfPlane.qExpansion_coeff_eq_circleIntegral`.

**Theorem.** Let $f$ be a modular form of weight $k$ for $\Gamma$, let $\infty$ be a cusp of $\Gamma$, and let $h > 0$ be a strict period. Then for each $z \in \mathbb{H}$,
$$f(z) = \sum_{m \geq 0} a_m \, q_h(z)^m.$$

This is `ModularForm.hasSum_qExpansion`, in the form of a `HasSum`. The cusp condition enters as the instance `Fact (IsCusp OnePoint.infty Γ)`. The general form for a periodic, holomorphic and bounded function is `UpperHalfPlane.hasSum_qExpansion`. The coefficients are unique: if $\sum c_m q^m$ also sums to $f$, then `UpperHalfPlane.qExpansion_coeff_unique` gives $c_m = a_m$.

The $q$-expansion respects the ring structure. `ModularForm.qExpansion_mul` and `ModularForm.qExpansion_pow` give the products and the powers, and the maps `ModularForm.qExpansionRingHom` and `ModularForm.qExpansionAlgHom` send the graded ring $\bigoplus_k M_k(\Gamma)$ to `PowerSeries ℂ`.

**Theorem.** If $\Gamma$ is arithmetic and has determinant one, then `ModularForm.qExpansionAlgHom h hh hΓ` is injective.

This is `ModularForm.qExpansionAlgHom_injective`. It contains two facts. A form is zero if its $q$-expansion is zero, by the identity theorem. Forms of different weights are linearly independent, and `ModularForm.gradedCoe_injective` states this for the map from the graded ring to functions. So an identity between modular forms can be checked on $q$-expansions.

#### The order at infinity

`UpperHalfPlane.orderAtInfty f` is the order of vanishing of $f$ as $\mathrm{Im}\,z \to \infty$, a term of `EReal`. For a form with period $h$, `UpperHalfPlane.orderAtInfty_eq_qExpansion_order` says that it is the order of the $q$-expansion divided by $h$. The order is $\top$ only for the zero function, `UpperHalfPlane.orderAtInfty_eq_top_iff_eq_zero`, and the order of a product is the sum of the orders, `UpperHalfPlane.orderAtInfty_mul_of_holo`.

#### Bounds

**Theorem.** Let $\Gamma$ be arithmetic and $k \geq 0$. For a modular form $f$ of weight $k$ there is $C$ with $\lvert f(z) \rvert \leq C \max(1, \mathrm{Im}(z)^{-k})$. The coefficients satisfy $a_n = O(n^k)$, and $a_n = O(n^{k/2})$ if $f$ is a cusp form.

These are `ModularFormClass.exists_bound`, `ModularFormClass.qExpansion_isBigO` and `CuspFormClass.qExpansion_isBigO`. The bound for cusp forms is the Hecke bound. The $q$-expansions here are taken at the strict width `Subgroup.strictWidthInfty Γ`.

*Proof idea for cusp forms.* The function $\lvert f(z) \rvert \, \mathrm{Im}(z)^{k/2}$ is invariant under $\Gamma$ and tends to $0$ at the cusps, so it is bounded. The coefficient $a_n$ is an integral of $f$ over a horizontal segment of length $h$ at height $y$. With $y = 1/n$ the bound gives $\lvert a_n \rvert \leq C y^{-k/2} e^{2\pi n y/h} = O(n^{k/2})$. $\square$

#### The Petersson product

The function `UpperHalfPlane.petersson k f f'` is $z \mapsto \overline{f(z)} \, f'(z) \, \mathrm{Im}(z)^k$. For two slash invariant forms of the same weight and level it is invariant under $\Gamma$, `SlashInvariantFormClass.petersson_smul`, and `UpperHalfPlane.petersson_slash` gives the general transformation law. If $f$ is a cusp form, the product with any modular form is bounded, `CuspFormClass.petersson_bounded_left`, and it decays exponentially at $\infty$, `UpperHalfPlane.IsZeroAtImInfty.petersson_exp_decay_left`. These are the inputs for the convergence of the Petersson inner product, which is an integral over a fundamental domain and is not in these modules.

#### Change of level

For $\mathcal{G} \leq \mathcal{H}$, `ModularForm.restrict` views a form for $\mathcal{H}$ as a form for $\mathcal{G}$. For $g \in \mathrm{GL}_2(\mathbb{R})$, `ModularForm.translate f g` is $f \mid_k g$, a form for the conjugate group. If $\mathcal{G} \cap \mathcal{H}$ has finite index in $\mathcal{H}$, the sum and the product of the translates over the cosets give `ModularForm.trace ℋ f`, of weight $k$, and `ModularForm.norm ℋ f`, of weight $k$ times the index. The norm is zero only for the zero form, `ModularForm.norm_eq_zero_iff`.

**Theorem.** If $\Gamma$ is arithmetic and $k < 0$, each modular form of weight $k$ for $\Gamma$ is zero.

*Proof.* The norm of $f$ down to $\mathrm{SL}_2(\mathbb{Z})$ has negative weight, so it is zero by the result at level one in Section 4. So $f = 0$ by `ModularForm.norm_eq_zero_iff`. $\square$

This is `ModularForm.isZero_of_neg_weight`. The same method shows that a form of weight $0$ is constant.

#### The Serre derivative

The derivative of a modular form is not a modular form. Let $D = \frac{1}{2\pi i}\frac{d}{dz}$, `Derivative.normalizedDerivOfComplex`, so that $D$ acts as $q \frac{d}{dq}$ on $q$-expansions. The Serre derivative `Derivative.serreDerivative k F` is $D F - \frac{k}{12} E_2 F$, by `Derivative.serreDerivative_eq`, where $E_2$ is the Eisenstein series of weight $2$ of Section 3. The correction term cancels the defect in the transformation law of $D F$, so `Derivative.serreDerivative_slash_equivariant` holds, and `Derivative.serreDerivativeMF` sends a modular form of weight $k$ for a group $\Gamma \leq \mathrm{SL}_2(\mathbb{Z})$ to a form of weight $k + 2$.

#### Common errors

1. The weight is part of the type. The product of `f : ModularForm Γ 4` and `g : ModularForm Γ 6` is `ModularForm.mul f g` of type `ModularForm Γ (4 + 6)`, and `ModularForm Γ 10` is a different type. Use `ModularForm.mcast` or work in the graded ring.
2. `UpperHalfPlane.qExpansion` takes the period $h$ as an argument. For $\Gamma(N)$ the period $1$ is wrong; use a strict period of the group. The bounds use `Subgroup.strictWidthInfty Γ`.
3. `ModularForm.isCuspForm_iff_coeffZero_eq_zero` is for level $\mathrm{SL}_2(\mathbb{Z})$ only. For a smaller group a form with $a_0 = 0$ can be nonzero at another cusp; use `ModularForm.isCuspForm_iff`.

### Exercises

1. (A) Show from `ModularForm.slash_def` that $f \mid_k (-1) = (-1)^k f$ for $-1 \in \mathrm{SL}_2(\mathbb{Z})$, and deduce that a modular form of odd weight for a group that contains $-1$ is zero.
2. (A) Let $f$ be a modular form for $\mathrm{SL}_2(\mathbb{Z})$. Use `ModularForm.qExpansion_mul` to compute the first two coefficients of the $q$-expansion of $f^2$ from those of $f$.
3. (B) Use `ModularForm.isZero_of_neg_weight` to show that `ModularForm Γ k` is the zero space for each arithmetic $\Gamma$ and $k < 0$.
4. (B) Show that the product of a cusp form and a modular form is a cusp form, with the conditions at the cusps.
5. (C) Prove the bound $a_n = O(n^{k/2})$ for a cusp form of level $\mathrm{SL}_2(\mathbb{Z})$ from `CuspFormClass.petersson_bounded_left` and the integral formula for the coefficients.
6. (C) Show from `Derivative.serreDerivative_eq` that $D$ maps a form with $q$-expansion $\sum a_n q^n$ to the series $\sum n a_n q^n$, and find the first coefficient of the Serre derivative of a cusp form.

### Reference

<?reference?>
