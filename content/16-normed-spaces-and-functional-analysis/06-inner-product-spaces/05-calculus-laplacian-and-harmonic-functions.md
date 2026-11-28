---
title: Calculus, the Laplacian and harmonic functions
kind: api
modules:
  - Mathlib.Analysis.InnerProductSpace.Calculus
  - Mathlib.Analysis.InnerProductSpace.NormPow
  - Mathlib.Analysis.InnerProductSpace.EuclideanDist
  - Mathlib.Analysis.InnerProductSpace.Laplacian
  - Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
  - Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
  - Mathlib.Analysis.InnerProductSpace.Harmonic.HarmonicContOnCl
  - Mathlib.Analysis.FunctionalSpaces.BesselPotentialSpace
  - Mathlib.Analysis.FunctionalSpaces.SobolevInequality
explains:
  E2: [fderivInnerCLM_apply, fderiv_norm_sq_apply, fderiv_norm_rpow, InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis, InnerProductSpace.HarmonicAt, AnalyticAt.harmonicAt_re, BesselPotentialSpace.toLpₗᵢ, MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq]
  E1: auto
families: []
requires: [V07, V13, V16.C01, V16.C02, V16.C03]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Calculus, the Laplacian and harmonic functions

### Overview

An inner product gives a norm that is smooth away from the origin. This fact is the base of all calculus in Hilbert space: the square of the norm is a quadratic form, so it has a derivative at every point, and the norm itself has derivatives of all orders on the complement of $0$. The first three modules of this section collect these facts. They compute the derivative of $\langle f(t), g(t) \rangle$, of $\lVert x \rVert^2$ and of $\lVert x \rVert^p$, and they give a Euclidean distance on any finite dimensional real space.

The next modules use the inner product to define the Laplacian $\Delta f = \sum_i \partial_i^2 f$ and the harmonic functions, the functions with $\Delta f = 0$. The last two modules go to function spaces: the Bessel potential spaces $H^{s,p}$, which are Sobolev spaces defined with the Fourier transform, and the inequality of Gagliardo, Nirenberg and Sobolev. The derivative `fderiv` and the class `ContDiff` come from the volume on differential calculus. This section uses only their definitions.

### The library around it

#### Derivatives of inner products and norms

The module `Mathlib.Analysis.InnerProductSpace.Calculus` treats the inner product as a bounded real bilinear map $E \times E \to \mathbb{K}$. Its derivative at the point $p = (p_1, p_2)$ is the bounded real linear map `fderivInnerCLM 𝕜 p`, and `fderivInnerCLM_apply` gives the formula
$$D\langle \cdot, \cdot \rangle(p)(x_1, x_2) = \langle p_1, x_2 \rangle + \langle x_1, p_2 \rangle.$$
The proof is the product rule for a bilinear map: $\langle p_1 + x_1, p_2 + x_2 \rangle - \langle p_1, p_2 \rangle$ is the linear part in the formula plus $\langle x_1, x_2 \rangle$, and $|\langle x_1, x_2 \rangle| \le \lVert x_1 \rVert \lVert x_2 \rVert$ is small of second order.

The field $\mathbb{K}$ is an explicit argument of most lemmas, because the inner product is written `inner 𝕜 x y`. The lemmas follow the names of the calculus library, with the word inner in the name.

| Lean name | Statement |
|---|---|
| `contDiff_inner` | $(x, y) \mapsto \langle x, y \rangle$ is $C^n$ for every $n$ |
| `ContDiff.inner` | $x \mapsto \langle f(x), g(x) \rangle$ is $C^n$ when $f$ and $g$ are |
| `HasFDerivAt.inner` | the derivative of $\langle f, g \rangle$ is `fderivInnerCLM 𝕜 (f x, g x)` composed with $(f', g')$ |
| `HasStrictFDerivAt.inner` | the same for the strict derivative |
| `HasDerivAt.inner` | for a curve, $\frac{d}{dt}\langle f(t), g(t) \rangle = \langle f(t), g'(t) \rangle + \langle f'(t), g(t) \rangle$ |
| `deriv_inner_apply` | the same formula with `deriv` |
| `contDiff_norm_sq` | $x \mapsto \lVert x \rVert^2$ is $C^n$ for every $n$ |
| `fderiv_norm_sq_apply` | $D(\lVert \cdot \rVert^2)(x) = 2 \langle x, \cdot \rangle$ |
| `hasStrictFDerivAt_norm_sq` | the same as a strict derivative |
| `HasDerivAt.norm_sq` | $\frac{d}{dt} \lVert f(t) \rVert^2 = 2 \langle f(t), f'(t) \rangle$ |
| `contDiffAt_norm` | the norm is $C^n$ at each $x \ne 0$ |
| `ContDiff.norm` | $x \mapsto \lVert f(x) \rVert$ is $C^n$ when $f$ is $C^n$ and has no zero |
| `ContDiff.dist` | $x \mapsto d(f(x), g(x))$ is $C^n$ when $f(x) \ne g(x)$ for all $x$ |

The formula `fderiv_norm_sq_apply` is a special case of the product rule: put $f = g = \mathrm{id}$ in `fderivInnerCLM_apply` to get $\langle x, h \rangle + \langle h, x \rangle = 2 \langle x, h \rangle$ over $\mathbb{R}$. The real map `innerSL ℝ x` is the linear form $h \mapsto \langle x, h \rangle$. The norm is $\sqrt{\lVert x \rVert^2}$, and the square root is smooth on $(0, \infty)$, so `contDiffAt_norm` follows by the chain rule. At $0$ the norm is not differentiable, so the hypothesis $x \ne 0$ is necessary.

The same module has two facts about Euclidean space. The lemmas `contDiff_euclidean` and `differentiable_euclidean` say that a map into `EuclideanSpace 𝕜 ι` is $C^n$ or differentiable if and only if each coordinate `(f x).ofLp i` is. The lemma `Homeomorph.contDiff_unitBall` says that the homeomorphism `Homeomorph.unitBall` from $E$ to the open unit ball, $x \mapsto x / \sqrt{1 + \lVert x \rVert^2}$, is smooth, and `OpenPartialHomeomorph.contDiff_univUnitBall` says the same for the open partial homeomorphism form.

#### Powers of the norm

The module `Mathlib.Analysis.InnerProductSpace.NormPow` differentiates $x \mapsto \lVert x \rVert^p$ for a real exponent $p > 1$. The result `fderiv_norm_rpow` says
$$D(\lVert \cdot \rVert^p)(x) = p\, \lVert x \rVert^{p - 2} \langle x, \cdot \rangle.$$
For $x \ne 0$ this is the chain rule: $\lVert x \rVert^p = (\lVert x \rVert^2)^{p/2}$, and the derivative is $\frac{p}{2} (\lVert x \rVert^2)^{p/2 - 1} \cdot 2 \langle x, \cdot \rangle$. At $x = 0$ the right side is $0$, and the bound $\lVert x \rVert^p = o(\lVert x \rVert)$ for $p > 1$ gives the derivative $0$ directly. The case $p = 1$ fails because the norm has no derivative at $0$.

The other results of the module are `hasFDerivAt_norm_rpow`, `differentiable_norm_rpow` and `contDiff_norm_rpow` (the power is $C^1$, but not $C^2$ in general), the composed forms `Differentiable.norm_rpow` and `ContDiff.norm_rpow`, the formula `Differentiable.fderiv_norm_rpow` for $\lVert f(x) \rVert^p$, and the bound `norm_fderiv_norm_rpow_le`:
$$\lVert D(\lVert f \rVert^p)(x) \rVert \le p\, \lVert f(x) \rVert^{p-1} \lVert Df(x) \rVert.$$
On the real line, `hasDerivAt_abs_rpow` gives $\frac{d}{dx} |x|^p = p |x|^{p-2} x$. These bounds are the first step of the inequality of Sobolev below.

#### A Euclidean distance on a finite dimensional space

Let $E$ be a finite dimensional real topological vector space with a Hausdorff topology. It has no norm in general, but it is linearly homeomorphic to $\mathbb{R}^n$ with $n = \dim E$. The module `Mathlib.Analysis.InnerProductSpace.EuclideanDist` picks such an equivalence, `toEuclidean : E ≃L[ℝ] EuclideanSpace ℝ (Fin n)`, and pulls back the Euclidean distance. The results are `Euclidean.dist`, `Euclidean.ball` and `Euclidean.closedBall`. The lemmas `Euclidean.ball_eq_preimage` and `Euclidean.closedBall_eq_image` compare them with the balls of $\mathbb{R}^n$. The balls behave as metric balls: `Euclidean.isOpen_ball`, `Euclidean.isCompact_closedBall`, `Euclidean.closure_ball`, and `Euclidean.nhds_basis_ball` says that they form a basis of neighbourhoods. The lemma `Euclidean.exists_pos_lt_subset_ball` shrinks a ball around a closed set, and `ContDiff.euclidean_dist` says that $x \mapsto d_{\mathrm{E}}(f(x), g(x))$ is smooth where $f \ne g$. These balls are useful for bump functions on a space that carries no chosen norm.

#### The Laplacian

Let $E$ be a finite dimensional real inner product space and $f : E \to F$. The module `Mathlib.Analysis.InnerProductSpace.Laplacian` defines the Laplacian through the instance `InnerProductSpace.instLaplacian` of the notation class `Laplacian`. The value `Laplacian.laplacian f x`, written `Δ f x`, is the second derivative of $f$ at $x$, seen as a linear map on $E \otimes E$ by `tensorIteratedFDerivTwo`, applied to the canonical tensor $\sum_i e_i \otimes e_i$ of Section 4. The helper `bilinearIteratedFDerivTwo` gives the second derivative as a bilinear map, and `tensorIteratedFDerivTwo_eq_iteratedFDeriv` connects the two forms with `iteratedFDeriv ℝ 2 f x`.

The definition is free of coordinates. The theorem `InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis` gives the usual formula: for every orthonormal basis $(v_i)$ of $E$,
$$\Delta f(x) = \sum_i D^2 f(x)(v_i, v_i).$$
The proof is short: the canonical tensor is $\sum_i v_i \otimes v_i$ for every orthonormal basis (`InnerProductSpace.canonicalCovariantTensor_eq_sum`), and the map `tensorIteratedFDerivTwo` sends $v_i \otimes v_i$ to $D^2 f(x)(v_i, v_i)$. The special cases are `InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis`, `InnerProductSpace.laplacian_eq_iteratedDeriv_real` ($\Delta f = f''$ on $\mathbb{R}$) and `InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane` ($\Delta f = D^2 f(1, 1) + D^2 f(i, i)$ on $\mathbb{C}$).

The Laplacian is linear on $C^2$ functions: `ContDiffAt.laplacian_add`, `ContDiffAt.laplacian_sub` and `InnerProductSpace.laplacian_smul` need $f$ to be $C^2$ at $x$, while `InnerProductSpace.laplacian_neg` and `InnerProductSpace.laplacian_const` need no hypothesis. It commutes with a bounded linear map on the left: `ContDiffAt.laplacian_CLM_comp_left`, and `InnerProductSpace.laplacian_CLE_comp_left` for an equivalence, which needs no smoothness. A version whose name ends in nhds gives the identity on a neighbourhood. The relative Laplacian `InnerProductSpace.laplacianWithin f s x` uses the derivatives within a set $s$, and its lemmas need the hypothesis `UniqueDiffOn ℝ s`. The lemma `InnerProductSpace.laplacianWithin_univ` says that it is the Laplacian for $s = E$.

#### Harmonic functions

The module `Mathlib.Analysis.InnerProductSpace.Harmonic.Basic` defines `InnerProductSpace.HarmonicAt f x`: the function $f$ is $C^2$ at $x$ and $\Delta f = 0$ on a neighbourhood of $x$. The definition asks for $\Delta f = 0$ near $x$, not only at $x$, so the set of points where $f$ is harmonic is open, the lemma `InnerProductSpace.isOpen_setOfPred_harmonicAt`. The predicate `InnerProductSpace.HarmonicOnNhd f s` says that $f$ is harmonic at each point of $s$. It implies `ContDiffOn ℝ 2 f s` by `InnerProductSpace.HarmonicOnNhd.contDiffOn`. The harmonic functions form a vector space: `InnerProductSpace.HarmonicAt.add`, `InnerProductSpace.HarmonicAt.neg`, `InnerProductSpace.HarmonicAt.sub`, `InnerProductSpace.HarmonicAt.const_smul` and `InnerProductSpace.harmonicAt_const`. A bounded linear map preserves them (`InnerProductSpace.HarmonicAt.comp_CLM`), and `InnerProductSpace.harmonicAt_comp_CLE_iff` gives the equivalence for a continuous linear equivalence.

The module `Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions` gives the examples from complex analysis. A complex differentiable function $f : \mathbb{C} \to F$ is harmonic: `ContDiffAt.harmonicAt` for a $C^2$ function in the complex sense and `AnalyticAt.harmonicAt` for an analytic function. The proof uses the formula on $\mathbb{C}$: the second derivative is complex bilinear, so $D^2 f(i, i) = i^2 D^2 f(1, 1) = -D^2 f(1, 1)$, and the two terms of the Laplacian cancel. The real part is harmonic, `AnalyticAt.harmonicAt_re`, because $\mathrm{Re}$ is a real linear map and commutes with the Laplacian. The imaginary part and the conjugate are harmonic too (`AnalyticAt.harmonicAt_im`, `AnalyticAt.harmonicAt_conj`), and `AnalyticAt.harmonicAt_log_norm` says that $\log \lvert f \rvert$ is harmonic at a point where $f \ne 0$.

The module `Mathlib.Analysis.InnerProductSpace.Harmonic.HarmonicContOnCl` defines `InnerProductSpace.HarmonicContOnCl f s`: $f$ is harmonic on $s$ and continuous on the closure of $s$. This is the hypothesis of the maximum principle and of the Dirichlet problem on a ball. The constructor `InnerProductSpace.HarmonicContOnCl.mk_ball` builds it on a ball, and `InnerProductSpace.IsClosed.harmonicContOnCl_iff` says that it is the same as `InnerProductSpace.HarmonicOnNhd` on a closed set. The module repeats the algebra of the predicate, with lemmas such as `InnerProductSpace.HarmonicContOnCl.add` and `InnerProductSpace.HarmonicContOnCl.const_smul`.

#### Sobolev spaces

The module `Mathlib.Analysis.FunctionalSpaces.BesselPotentialSpace` defines the Bessel potential space `BesselPotentialSpace E F s p`. Its elements are the tempered distributions $u$ on $E$ such that
$$\mathcal{F}^{-1}\big( (1 + \lVert \xi \rVert^2)^{s/2} \mathcal{F} u \big) \in L^p.$$
The operator in the formula is `TemperedDistribution.besselPotential`, and `TemperedDistribution.MemSobolev s p u` is the unbundled condition. An element of the space stores $u$ and the $L^p$ function $v$ together, and `TemperedDistribution.MemSobolev.toBesselPotentialSpace` builds an element from the condition. The norm of $u$ is the $L^p$ norm of $v$. So the map $u \mapsto v$ is a linear isometric equivalence onto $L^p$, `BesselPotentialSpace.toLpₗᵢ`, with inverse `BesselPotentialSpace.ofLp`. The space is complete (`BesselPotentialSpace.instCompleteSpace`) because $L^p$ is complete. For $p = 2$ it is a Hilbert space, `BesselPotentialSpace.instInnerProductSpaceComplexOfNatENNReal`, and by Plancherel `BesselPotentialSpace.norm_fourier_toLp_eq` gives the norm through the Fourier transform. For an integer $s \ge 0$ and $1 < p < \infty$ the space agrees with the classical Sobolev space $W^{s,p}$, but the library defines it only by the Fourier formula.

The module `Mathlib.Analysis.FunctionalSpaces.SobolevInequality` proves the inequality of Gagliardo, Nirenberg and Sobolev. Let $E$ have dimension $n$, let $u : E \to F$ be $C^1$ with compact support, and let $1 \le p < n$ with $\frac{1}{p'} = \frac{1}{p} - \frac{1}{n}$. Then
$$\lVert u \rVert_{L^{p'}} \le C\, \lVert Du \rVert_{L^p},$$
the theorem `MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq`, with a constant $C$ that depends on $E$, $F$, the measure and $p$, not on $u$. The norms are the extended norms `MeasureTheory.eLpNorm` of Volume 18. The variants are `MeasureTheory.eLpNorm_le_eLpNorm_fderiv_one` for $p = 1$ and any Banach codomain, `MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq_inner` for a Hilbert codomain of any dimension, and `MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_le` and `MeasureTheory.eLpNorm_le_eLpNorm_fderiv` for a support in a bounded set, with a constant that depends on that set.

The proof starts with $p = 1$. In coordinates, $|u(x)| \le \int |\partial_i u|$ along the line through $x$ in direction $i$, for each $i$. Multiply the $n$ bounds, take the power $\frac{1}{n - 1}$ and integrate. The grid lines lemma `MeasureTheory.lintegral_prod_lintegral_pow_le` bounds the result by $\big(\int |Du|\big)^{n/(n-1)}$. It is proved by induction over the coordinates with the inequality of Hölder, and `MeasureTheory.GridLines.T` is the integrand of the induction. The case $p > 1$ follows from the case $p = 1$ applied to $\lvert u \rvert^\gamma$ for a suitable $\gamma > 1$, with the derivative bound of the module on powers of the norm.

#### Common errors

1. `InnerProductSpace.HarmonicAt f x` asks for $\Delta f = 0$ on a neighbourhood of $x$. A function with $\Delta f(x) = 0$ at one point is not harmonic at $x$ in general.
2. The Laplacian lemmas for sums and scalars need `ContDiffAt ℝ 2 f x`. Without it, `Δ (f + g) x` and `Δ f x + Δ g x` can differ, because `fderiv` is $0$ at a point where a function is not differentiable.
3. The lemmas of `Mathlib.Analysis.InnerProductSpace.Calculus` take the field `𝕜` as an explicit argument. Write `ContDiff.inner 𝕜 hf hg`, not `hf.inner hg`.

### Exercises

1. (A) Use `HasDerivAt.norm_sq` to prove that a differentiable curve with constant norm satisfies $\langle f(t), f'(t) \rangle = 0$.
2. (A) Use `InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis` to compute $\Delta \lVert x \rVert^2 = 2n$ on a space of dimension $n$.
3. (B) Prove that $x \mapsto \lVert x \rVert^{2 - n}$ is harmonic on $\mathbb{R}^n \setminus \{0\}$ for $n \ge 3$.
4. (B) Show that $\log \lvert z \rvert$ is harmonic on $\mathbb{C} \setminus \{0\}$ with `AnalyticAt.harmonicAt_log_norm`, and show that it is not the real part of an analytic function on all of $\mathbb{C} \setminus \{0\}$.
5. (B) Prove that the exponent $p' = np/(n - p)$ in the inequality of Sobolev is the only exponent for which the inequality can hold, with a scaling $u_\lambda(x) = u(\lambda x)$.
6. (C) Prove that `BesselPotentialSpace E F 0 2` is isometric to $L^2$ and that the Fourier transform is an isometry on it.

### Reference

<?reference?>
