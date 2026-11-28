---
title: The Möbius action, the hyperbolic metric and the cusp
kind: api
modules:
  - Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
  - Mathlib.Analysis.Complex.UpperHalfPlane.FixedPoints
  - Mathlib.Analysis.Complex.UpperHalfPlane.ProperAction
  - Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
  - Mathlib.Analysis.Complex.UpperHalfPlane.Metric
  - Mathlib.Analysis.Complex.UpperHalfPlane.Measure
  - Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
  - Mathlib.Analysis.Complex.UpperHalfPlane.Exp
  - Mathlib.Analysis.Complex.Periodic
explains:
  E2: [UpperHalfPlane.im_smul_eq_div_normSq, UpperHalfPlane.denom_cocycle, UpperHalfPlane.toSL2R_smul_I, UpperHalfPlane.gl_smul_eq_self_iff_eq_fixedPt, UpperHalfPlane.dist_eq, UpperHalfPlane.image_coe_ball, UpperHalfPlane.volume_def, UpperHalfPlane.atImInfty, Function.Periodic.cuspFunction, Function.Periodic.differentiableAt_cuspFunction_zero]
  E1: auto
families: []
requires: [V19.C01, V19.C03, V18, V13]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The Möbius action, the hyperbolic metric and the cusp

### Overview

A real matrix $g = \begin{pmatrix} a & b \\ c & d \end{pmatrix}$ with $\det g > 0$ acts on the upper half-plane by the Möbius map $z \mapsto (az + b)/(cz + d)$. The formula for the imaginary part is the key fact of the theory:
$$\operatorname{Im}\left(\frac{az + b}{cz + d}\right) = \frac{\det g \cdot \operatorname{Im} z}{|cz + d|^2}.$$
It shows that the map preserves $\mathbb{H}$. The denominator $j(g, z) = cz + d$ satisfies the cocycle relation $j(gh, z) = j(g, hz) \, j(h, z)$, and this relation makes the formula an action of the group.

Three structures on $\mathbb{H}$ are invariant under this action. The first is the hyperbolic metric, with $\cosh d(z, w) = 1 + |z - w|^2/(2 \operatorname{Im} z \operatorname{Im} w)$. The second is the measure $dx \, dy / y^2$. The third is the complex structure: each Möbius map is holomorphic, with derivative $\det g/(cz + d)^2$. The group $\mathrm{SL}(2, \mathbb{R})$ acts transitively, with stabilizer $\mathrm{SO}(2)$ at $i$, so $\mathbb{H}$ is the homogeneous space $\mathrm{SL}(2, \mathbb{R})/\mathrm{SO}(2)$.

The point at infinity is not in $\mathbb{H}$, but the filter of points with large imaginary part stands for it. A function $f$ on $\mathbb{H}$ with period $h > 0$ factors through the map $q = e^{2\pi i z/h}$, which sends $\mathbb{H}$ onto the punctured disc. If $f$ is holomorphic and bounded as $\operatorname{Im} z \to \infty$, then the function of $q$ has a removable singularity at $q = 0$ by the theorem of Riemann of Chapter 3. Its Taylor series is the $q$-expansion of $f$. This section gives the Mathlib form of each of these facts.

The section prepares the theory of modular forms in Volume 12. It proves no theorem about a modular group. The only arithmetic objects are the matrices $S$ and $T$, whose action is computed here.

### The library around it

#### The action of the general linear group

The functions `UpperHalfPlane.num` and `UpperHalfPlane.denom` are the numerator $az + b$ and the denominator $cz + d$ of a matrix $g$ in `GL (Fin 2) ℝ`, as functions on $\mathbb{C}$. The denominator does not vanish off the real line, by `UpperHalfPlane.denom_ne_zero`. The formula for the imaginary part is `UpperHalfPlane.moebius_im` on $\mathbb{C}$, and the cocycle relation is `UpperHalfPlane.denom_cocycle`.

Mathlib lets the whole group $\mathrm{GL}(2, \mathbb{R})$ act, and not only the matrices of positive determinant. A matrix of negative determinant sends $\mathbb{H}$ to the lower half-plane, so the action composes it with complex conjugation. The map `UpperHalfPlane.σ` $g$ is the identity if $\det g > 0$ and conjugation otherwise. The action is the instance `UpperHalfPlane.glAction`, with `UpperHalfPlane.coe_smul` for the general formula and `UpperHalfPlane.coe_smul_of_det_pos` for the usual formula when $\det g > 0$. The theorem `UpperHalfPlane.im_smul_eq_div_normSq` gives $\operatorname{Im}(g \cdot z) = |\det g| \operatorname{Im} z / |cz + d|^2$ for all $g$. The scalar matrices act trivially by `UpperHalfPlane.glScalar_smul`, so the action descends to $\mathrm{PGL}(2, \mathbb{R})$.

The standard matrices have their own lemmas. `UpperHalfPlane.modular_S_smul` computes $S \cdot z = -1/z$ and `UpperHalfPlane.modular_T_smul` computes $T \cdot z = z + 1$. The matrix `UpperHalfPlane.J` has determinant $-1$ by `UpperHalfPlane.det_J`, and it acts by $z \mapsto -\bar z$, the reflection in the imaginary axis. The map `UpperHalfPlane.toSL2R` sends $z = x + iy$ to the matrix $\begin{pmatrix} \sqrt y & x/\sqrt y \\ 0 & 1/\sqrt y \end{pmatrix}$ of $\mathrm{SL}(2, \mathbb{R})$, and `UpperHalfPlane.toSL2R_smul_I` says that this matrix sends $i$ to $z$. The instance `UpperHalfPlane.isPretransitiveSL2R` is the transitivity that follows.

#### Fixed points

The module on fixed points classifies the matrices that fix a point. For $\det g > 0$, a point is fixed if and only if it solves a quadratic equation, by `UpperHalfPlane.gl_smul_eq_self_iff_quadratic`. An elliptic matrix, with $(\operatorname{tr} g)^2 < 4 \det g$, has exactly one fixed point `UpperHalfPlane.fixedPt`, and `UpperHalfPlane.gl_smul_eq_self_iff_eq_fixedPt` is the uniqueness. A matrix that fixes every point is a scalar matrix, by `UpperHalfPlane.forall_smul_eq_self_iff_mem_center`. A matrix with $\det g < 0$ has a fixed point if and only if its trace is $0$, by `UpperHalfPlane.exists_gl_smul_eq_self_iff_trace_eq_zero`, and then its fixed points form a geodesic.

#### Properness and smoothness

The action of $\mathrm{SL}(2, \mathbb{R})$ is proper. The theorem `UpperHalfPlane.isProperMap_smul_I` says that the orbit map $g \mapsto g \cdot i$ is proper, and the instance `UpperHalfPlane.instProperSMul` follows. A discrete subgroup of $\mathrm{SL}(2, \mathbb{R})$ then acts properly discontinuously, by `UpperHalfPlane.instProperlyDiscontinuousSL2RSubgroup`. This is the fact that makes the quotient by a modular group a reasonable space.

The manifold module makes $\mathbb{H}$ a complex manifold of dimension $1$, as an open subset of $\mathbb{C}$. The theorem `UpperHalfPlane.mdifferentiable_iff` says that a function $f$ on $\mathbb{H}$ is holomorphic in the manifold sense if and only if $f \circ \mathrm{ofComplex}$ is differentiable on $\{\operatorname{Im} z > 0\}$. So the two definitions of Section 1 agree. Each Möbius map is holomorphic by `UpperHalfPlane.mdifferentiable_smul`, and `UpperHalfPlane.deriv_smul` gives its derivative $\det g/(cz + d)^2$.

#### The hyperbolic metric

The metric space instance on $\mathbb{H}$ uses the distance
$$d(z, w) = 2 \operatorname{arsinh} \frac{|z - w|}{2\sqrt{\operatorname{Im} z \operatorname{Im} w}},$$
which is `UpperHalfPlane.dist_eq`. The theorem `UpperHalfPlane.cosh_dist` gives the classical form with $\cosh$. Mathlib replaces the topology of the metric by the subspace topology of Section 1, so the two topologies are equal by definition. On a vertical line the distance is $|\log y_1 - \log y_2|$, and `UpperHalfPlane.isometry_vertical_line` says that $t \mapsto a + i e^t$ is an isometry from $\mathbb{R}$.

A hyperbolic ball is a Euclidean ball with another center. The point `UpperHalfPlane.center` $z$ $r$ is $\operatorname{Re} z + i \operatorname{Im} z \cosh r$, and `UpperHalfPlane.image_coe_ball` says that the hyperbolic ball of radius $r$ about $z$ is the Euclidean ball of radius $\operatorname{Im} z \sinh r$ about this point. The closed balls are compact by the same argument, so $\mathbb{H}$ is a proper metric space. The translations, the positive dilations and the matrices of $\mathrm{SL}(2, \mathbb{R})$ are isometries, by `UpperHalfPlane.isometry_real_vadd`, `UpperHalfPlane.isometry_pos_mul` and the instance `UpperHalfPlane.instIsIsometricSMulSpecialLinearGroupFinOfNatNatReal`.

#### The invariant measure

The measure on $\mathbb{H}$ is the Lebesgue measure of $\mathbb{C}$ with density $1/y^2$, by `UpperHalfPlane.volume_def`, and `UpperHalfPlane.volume_eq_lintegral` writes the measure of a set as a lower integral over its image in $\mathbb{C}$. The measure is finite on compact sets and $\sigma$-finite. The instance `UpperHalfPlane.instSMulInvariantMeasureGeneralLinearGroupFinOfNatNatRealVolume` says that it is invariant under all of $\mathrm{GL}(2, \mathbb{R})$. The proof uses the change of variables formula of Volume 18.

#### The cusp at infinity

The filter `UpperHalfPlane.atImInfty` is the pullback of `Filter.atTop` by the imaginary part. A set is in it if and only if it contains a region $\{\operatorname{Im} z \ge A\}$, by `UpperHalfPlane.atImInfty_mem`. A function is bounded at infinity, `UpperHalfPlane.IsBoundedAtImInfty`, if it is bounded on such a region, and `UpperHalfPlane.isBoundedAtImInfty_iff` unfolds the definition. The function vanishes at infinity, `UpperHalfPlane.IsZeroAtImInfty`, if it tends to $0$ along the filter. The bounded functions form the subalgebra `UpperHalfPlane.boundedAtImInftySubalgebra`. The theorem `UpperHalfPlane.tendsto_smul_atImInfty` says that a matrix with $c = 0$ maps the filter to itself.

The parameter at the cusp lives in `Mathlib.Analysis.Complex.Periodic`, for functions on all of $\mathbb{C}$. The function `Function.Periodic.qParam` $h$ is $z \mapsto e^{2\pi i z/h}$, and `Function.Periodic.norm_qParam` gives $|q| = e^{-2\pi \operatorname{Im} z/h}$. Its one sided inverse `Function.Periodic.invQParam` uses the principal logarithm, and `Function.Periodic.qParam_right_inv` is the inverse law. For a function $f$ of period $h$, the function `Function.Periodic.cuspFunction` $h$ $f$ is $q \mapsto f(\mathrm{invQParam}(q))$ for $q \ne 0$, by `Function.Periodic.cuspFunction_eq_of_ne_zero`, and it takes the limit value at $q = 0$.

The main theorem is `Function.Periodic.differentiableAt_cuspFunction_zero`. If $f$ has period $h > 0$, is holomorphic near the cusp and is bounded there, then its cusp function is differentiable at $q = 0$. As a consequence, `Function.Periodic.exp_decay_of_zero_at_inf` says that a function that vanishes at the cusp decays like $e^{-2\pi \operatorname{Im} z/h}$. The module `Mathlib.Analysis.Complex.UpperHalfPlane.Exp` connects this to $\mathbb{H}$: `UpperHalfPlane.norm_qParam_lt_one` puts $q$ in the open disc for $z$ in $\mathbb{H}$, and `Function.Periodic.im_invQParam_pos_of_norm_lt_one` goes back.

#### Common errors

1. The action of a matrix of negative determinant includes a complex conjugation. The formula $(az + b)/(cz + d)$ is `UpperHalfPlane.coe_smul_of_det_pos`, and it needs the hypothesis $0 < \det g$.
2. The functions of `Mathlib.Analysis.Complex.Periodic` are functions on $\mathbb{C}$, and its filter at infinity is a filter on $\mathbb{C}$. For a function on $\mathbb{H}$, compose with `UpperHalfPlane.ofComplex` first, and use `UpperHalfPlane.periodic_comp_ofComplex` for the period.
3. The value of `Function.Periodic.cuspFunction` at $0$ is a limit. It is the expected value only when the limit exists, so a lemma about it at $0$ needs continuity or the hypotheses of `Function.Periodic.differentiableAt_cuspFunction_zero`.

### Exercises

1. (A) Prove the formula $\operatorname{Im}((az + b)/(cz + d)) = (ad - bc)\operatorname{Im} z/|cz + d|^2$.
2. (A) Prove the cocycle relation $j(gh, z) = j(g, hz) \, j(h, z)$ for matrices of positive determinant.
3. (B) Show that the stabilizer of $i$ in $\mathrm{SL}(2, \mathbb{R})$ is $\mathrm{SO}(2)$, with `UpperHalfPlane.gl_smul_I_eq_I_iff_of_pos`.
4. (B) Show that $d(iy_1, iy_2) = |\log(y_1/y_2)|$ from `UpperHalfPlane.cosh_dist`, and that the vertical line is a geodesic.
5. (B) Show that the measure $dx \, dy/y^2$ is invariant under $z \mapsto -1/z$, with the derivative formula and the change of variables formula.
6. (C) Let $f$ be holomorphic on $\mathbb{H}$, of period $1$ and bounded on $\{\operatorname{Im} z \ge 1\}$. Show that $f(z) = \sum_{n \ge 0} a_n e^{2\pi i n z}$, and that $a_0 = \lim_{\operatorname{Im} z \to \infty} f(z)$.

### Reference

<?reference?>
