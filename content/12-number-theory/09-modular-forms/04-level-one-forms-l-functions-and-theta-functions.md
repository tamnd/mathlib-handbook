---
title: Level one forms, L-functions and theta functions
kind: api
modules:
  - Mathlib.NumberTheory.ModularForms.LevelOne
  - Mathlib.NumberTheory.ModularForms.LevelOne.Basic
  - Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
  - Mathlib.NumberTheory.ModularForms.DimensionFormulas.LevelOne
  - Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
  - Mathlib.NumberTheory.ModularForms.LFunction
  - Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
  - Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
  - Mathlib.NumberTheory.ModularForms.JacobiTheta.Manifold
  - Mathlib.NumberTheory.ModularForms.JacobiTheta.Bounds
explains:
  E2: [ModularForm.dimension_level_one, ModularForm.sturm_bound_levelOne, CuspForm.discriminantEquiv, ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq, ModularForm.mvPolynomialEquiv, ModularForm.L, ModularForm.hasSum_L, CuspForm.differentiable_Λ, jacobiTheta, jacobiTheta₂_functional_equation]
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

## Level one forms, L-functions and theta functions

### Overview

For the full modular group the spaces of modular forms are known completely. Let $M_k$ and $S_k$ be the spaces of modular forms and cusp forms of weight $k$ for $\mathrm{SL}_2(\mathbb{Z})$. Then $M_k = 0$ for $k < 0$ and for odd $k$, $M_0 = \mathbb{C}$, and division by the discriminant $\Delta$ gives $S_k \cong M_{k-12}$. These facts give the dimension formula, and the graded ring $\bigoplus_k M_k$ is the polynomial ring $\mathbb{C}[E_4, E_6]$. A modular form of any arithmetic level also has an $L$-function, the Mellin transform of $f(it)$, with a functional equation. The theta functions are a second source of modular objects, with their own transformation laws.

The modules `Mathlib.NumberTheory.ModularForms.LevelOne.Basic`, `Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula` and `Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing` have the results at level one. The modules `Mathlib.NumberTheory.ModularForms.LevelOne` and `Mathlib.NumberTheory.ModularForms.DimensionFormulas.LevelOne` contain no declarations: they only import these modules. The module `Mathlib.NumberTheory.ModularForms.LFunction` defines the $L$-function. The four modules with JacobiTheta in their names define the theta functions and give the bounds for the Hurwitz zeta function. The forms $E_4$, $E_6$ and $\Delta$ are in Section 3.

### The library around it

#### Weights at most zero

**Theorem.** A modular form of level $\mathrm{SL}_2(\mathbb{Z})$ and weight $k < 0$ is zero, and one of weight $0$ is constant.

*Proof idea.* For $k \leq 0$, the function $\lvert f(z) \rvert \, \mathrm{Im}(z)^{k/2}$ is invariant. Each orbit meets the fundamental domain, where $\mathrm{Im}(z) \geq 1/2$, `SlashInvariantForm.exists_one_half_le_im_and_norm_le`, and $f$ is bounded there. So $\lvert f \rvert$ has a maximum, and the maximum principle makes $f$ constant. A nonzero constant is invariant only in weight $0$, `SlashInvariantForm.wt_eq_zero_of_eq_const`. $\square$

The results are `ModularFormClass.levelOne_neg_weight_eq_zero` and `ModularFormClass.levelOne_weight_zero_const`, with the ranks `ModularForm.levelOne_neg_weight_rank_zero` and `ModularForm.levelOne_weight_zero_rank_one`. Section 2 extends the first one to each arithmetic group with the norm map. For odd $k$, the element $-1$ gives $f = (-1)^k f$, so $f = 0$, `ModularForm.levelOne_odd_weight_eq_zero`. Invariance under $\mathrm{SL}_2(\mathbb{Z})$ follows from invariance under $S$ and $T$, `SlashInvariantForm.slash_action_generators_SL2Z`.

#### Division by the discriminant and the dimension formula

Since $\Delta$ has no zeros on $\mathbb{H}$ and a simple zero at $\infty$ (`ModularForm.discriminant_qExpansion_order`), a cusp form $f$ of weight $k$ gives a holomorphic function $f/\Delta$ of weight $k - 12$ that is bounded at $\infty$. This gives the linear equivalence `CuspForm.discriminantEquiv` between $S_k$ and $M_{k-12}$, with `CuspForm.discriminantEquiv_apply` for its values and the inverse direction `CuspForm.ofMulDiscriminant`, multiplication by $\Delta$. For $k \geq 3$ even, $M_k = \mathbb{C} E_k \oplus S_k$, so `ModularForm.rank_eq_one_add_rank_cuspForm` gives $\dim M_k = 1 + \dim S_k$.

**Theorem.** For even $k \geq 0$,
$$\dim M_k = \begin{cases} \lfloor k/12 \rfloor & k \equiv 2 \pmod{12}, \\ \lfloor k/12 \rfloor + 1 & \text{otherwise.} \end{cases}$$

*Proof.* Induction on $k$ in steps of $12$. The base cases are $\dim M_0 = 1$, $\dim M_2 = 0$ (`ModularForm.levelOne_weight_two_rank_zero`), and $\dim M_4 = \dim M_6 = \dim M_8 = \dim M_{10} = 1$, since $S_k \cong M_{k-12} = 0$ for $k < 12$ (`CuspForm.rank_eq_zero_of_weight_lt_twelve`). For $k \geq 12$, $\dim M_k = 1 + \dim M_{k-12}$. $\square$

This is `ModularForm.dimension_level_one`, with `Module.rank` as the dimension. The single cases are `ModularForm.levelOne_weight_four_rank_one`, `ModularForm.levelOne_weight_six_rank_one` and `CuspForm.rank_eq_one_of_weight_eq_twelve`; so each cusp form of weight $12$ is a multiple of $\Delta$, `CuspForm.exists_smul_discriminant_of_weight_eq_twelve`. Each `ModularForm` space at level one is finite dimensional, and the instance is in the module.

**Theorem (Sturm bound).** If $f \in M_k$ and the first $\lfloor k/12 \rfloor + 1$ coefficients of its $q$-expansion are zero, then $f = 0$.

This is `ModularForm.sturm_bound_levelOne`, stated with the order of the power series. The classical proof divides by $\Delta$ until the weight is less than $12$. With `ModularForm.qExpansionAlgHom_injective` of Section 2, this bound reduces each identity between level one forms of weight $k$ to a finite computation on coefficients.

#### The graded ring

**Theorem.** The map $\mathbb{C}[X, Y] \to \bigoplus_k M_k$ with $X \mapsto E_4$ and $Y \mapsto E_6$ is an isomorphism of $\mathbb{C}$-algebras. Also $1728\,\Delta = E_4^3 - E_6^2$.

The map is `ModularForm.evalE₄E₆`, on `MvPolynomial (Fin 2) ℂ`, with `ModularForm.evalE₄E₆_injective` and `ModularForm.evalE₄E₆_surjective`, and the isomorphism is `ModularForm.mvPolynomialEquiv`. So $E_4$ and $E_6$ are algebraically independent, `ModularForm.algebraicIndependent_E₄_E₆`, and they generate, `ModularForm.adjoin_E₄_E₆_eq_top`. The formula for $\Delta$ is `ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq`, with the form `ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq_graded` in the graded ring. For a direct check, both sides are cusp forms of weight $12$ with coefficient $1$ of $q$: the values `ModularForm.E₄_qExpansion_coeff_one` and `ModularForm.E₆_qExpansion_coeff_one` are $240$ and $-504$, and $3 \cdot 240 + 2 \cdot 504 = 1728$. The ring is a Noetherian domain of finite type, by instances in the module.

#### L-functions

Let $\Gamma$ be arithmetic, $k > 0$, and $f$ a modular form of weight $k$ with $q$-expansion coefficients $a_n$ at the strict width $h$ of $\Gamma$. The completed $L$-function `ModularForm.Λ hk f` is the $\Lambda$-function of the pair `ModularForm.weakFEPair hk f`: the functions $t \mapsto f(it)$ and $t \mapsto (f \mid_k S)(it)$, with weight $k$ and root number $i^k$. The theory of Mellin transforms and of the pairs `WeakFEPair` is in the analysis library. So $\Lambda$ has a meromorphic continuation and the functional equation that relates $f$ to $f \mid_k S$. The $L$-function `ModularForm.L hk f` is $\Lambda(s) \cdot 2/\Gamma_{\mathbb{C}}(s)$, with the value $-a_0$ at $s = 0$ (`ModularForm.L_apply_zero`).

**Theorem.** For $\mathrm{Re}(s) > k + 1$,
$$\sum_{n \geq 1} \frac{a_n}{n^s} = h^{-s} L(f, s).$$
For a cusp form the same holds for $\mathrm{Re}(s) > k/2 + 1$, and $L(f, s)$ and $\Lambda(f, s)$ are entire.

The statements are `ModularForm.hasSum_L`, `CuspForm.hasSum_L`, `CuspForm.differentiable_L` and `CuspForm.differentiable_Λ`. The half planes come from the bounds on $a_n$ in Section 2. For a cusp form the pair is strong, `CuspForm.isStrongFEPair`, since $f(it)$ decays at both ends, and `CuspForm.Λ_eq_mellin` writes $\Lambda$ as a plain Mellin transform.

#### Theta functions

The Jacobi theta function of two variables is
$$\theta(z, \tau) = \sum_{n \in \mathbb{Z}} e^{2\pi i n z + \pi i n^2 \tau},$$
the function `jacobiTheta₂ z τ` on $\mathbb{C} \times \mathbb{C}$, with the value $0$ for $\mathrm{Im}\,\tau \leq 0$ (`jacobiTheta₂_undef`). The sum converges for $\mathrm{Im}\,\tau > 0$, `hasSum_jacobiTheta₂_term`, and the function is differentiable in both variables there, `hasFDerivAt_jacobiTheta₂`. The function `jacobiTheta₂'` is its derivative in $z$.

| Lean name | Statement |
|---|---|
| `jacobiTheta₂_add_left` | $\theta(z + 1, \tau) = \theta(z, \tau)$ |
| `jacobiTheta₂_add_left'` | $\theta(z + \tau, \tau) = e^{-\pi i(\tau + 2z)}\theta(z, \tau)$ |
| `jacobiTheta₂_add_right` | $\theta(z, \tau + 2) = \theta(z, \tau)$ |
| `jacobiTheta₂_neg_left` | $\theta(-z, \tau) = \theta(z, \tau)$ |
| `jacobiTheta₂_functional_equation` | $\theta(z, \tau) = (-i\tau)^{-1/2} e^{-\pi i z^2/\tau} \theta(z/\tau, -1/\tau)$ |

The functional equation comes from Poisson summation for a Gaussian. The one variable function `jacobiTheta τ` is $\theta(0, \tau) = \sum_n e^{\pi i n^2 \tau}$, `jacobiTheta_eq_jacobiTheta₂`. On the upper half plane it satisfies `jacobiTheta_T_sq_smul` and `jacobiTheta_S_smul`:
$$\theta(\tau + 2) = \theta(\tau), \qquad \theta(-1/\tau) = (-i\tau)^{1/2}\theta(\tau),$$
and it is holomorphic, `mdifferentiable_jacobiTheta`. So $\theta$ is a modular form of weight $1/2$ for the group generated by $S$ and $T^2$, but the library has no type of forms of half integral weight. The bound `norm_jacobiTheta_sub_one_le` gives $\lvert \theta(\tau) - 1 \rvert \leq 2e^{-\pi \mathrm{Im}\,\tau}/(1 - e^{-\pi \mathrm{Im}\,\tau})$.

The module `Mathlib.NumberTheory.ModularForms.JacobiTheta.Bounds` has the bounds for the kernels of the Hurwitz zeta function of Chapter 6. The functions `HurwitzKernelBounds.F_nat k a t` are $\sum_{n \geq 0} (n + a)^k e^{-\pi (n + a)^2 t}$, and `HurwitzKernelBounds.isBigO_atTop_F_nat_one` and `HurwitzKernelBounds.isBigO_atTop_F_int_zero_sub` give exponential decay as $t \to \infty$.

#### Common errors

1. The level one results are stated for `ModularForm (Matrix.SpecialLinearGroup.mapGL ℝ).range k`. A form for a congruence subgroup must be at this level, or be moved to it, before they apply.
2. `ModularForm.dimension_level_one` takes a natural number $k$ and the hypothesis `Even k`, and the value is a `Module.rank`, a cardinal. Use `Module.finrank` lemmas or the finite dimensional instance to get a natural number.
3. `ModularForm.L hk f` is normalized by the strict width: the Dirichlet series $\sum a_n n^{-s}$ equals $h^{-s}L(f, s)$, not $L(f, s)$. For level $\mathrm{SL}_2(\mathbb{Z})$, $h = 1$.

### Exercises

1. (A) Use `ModularForm.dimension_level_one` to compute $\dim M_k$ for $k = 12, 14, 24$ and $26$.
2. (A) Use `jacobiTheta₂_functional_equation` at $z = 0$ to get the transformation law of `jacobiTheta` under $S$.
3. (B) Show that $E_4^2$ and $E_8$ are equal, from $\dim M_8 = 1$ and the constant terms.
4. (B) Show that $\dim S_k = \dim M_k - 1$ for even $k \geq 4$, and list the $k \leq 30$ with $S_k \neq 0$.
5. (C) Prove $E_4 E_6 = E_{10}$ and find the relation that gives $\sigma_9(n)$ as a convolution of $\sigma_3$ and $\sigma_5$.
6. (C) Show that $\Lambda(\Delta, s) = \Lambda(\Delta, 12 - s)$ from the functional equation of `ModularForm.weakFEPair` and the invariance of $\Delta$ under $S$.

### Reference

<?reference?>
