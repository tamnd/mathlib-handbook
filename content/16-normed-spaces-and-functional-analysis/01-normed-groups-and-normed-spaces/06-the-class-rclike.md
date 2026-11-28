---
title: The class RCLike of the real and complex fields
kind: api
modules:
  - Mathlib.Analysis.RCLike.Basic
  - Mathlib.Analysis.RCLike.Lemmas
  - Mathlib.Analysis.RCLike.Inner
  - Mathlib.Analysis.RCLike.Sqrt
  - Mathlib.Analysis.RCLike.ContinuousMap
  - Mathlib.Analysis.RCLike.BoundedContinuous
  - Mathlib.Analysis.RCLike.TangentCone
  - Mathlib.Analysis.Normed.Module.RCLike.Basic
  - Mathlib.Analysis.Normed.Module.RCLike.Extend
explains:
  E2: [RCLike.mul_conj, RCLike.inv_eq_conj, RCLike.is_real_tfae, RCLike.nonneg_iff, RCLike.finrank_le_two, RCLike.sqrt_eq_real_add_ite, LinearMap.bound_of_sphere_bound, StrongDual.norm_extendRCLike, RCLike.wInner_one_eq_sum]
  E1: auto
families: []
requires: [V02, V07, V13, V15]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The class RCLike of the real and complex fields

### Overview

Section 2 introduces the class `RCLike K` of fields that are $\mathbb{R}$ or $\mathbb{C}$. An instance gives a real part, an imaginary part, a conjugation and an element $I$, with the axioms that hold in both fields. A theorem stated for `RCLike K` holds for real and for complex spaces with one proof. The inner product spaces of Chapter 6 and the theorem of Hahn-Banach for complex spaces in Chapter 5 use this class.

This section describes the API of the class. It covers the arithmetic of real and imaginary parts, the order on $K$, the bundled maps $\operatorname{Re}$, $\iota : \mathbb{R} \to K$ and the conjugation, the square root, the weighted inner products on $K^n$, the passage between real and complex valued continuous functions, and two facts on normed spaces over $K$.

### The library around it

#### The axioms and the arithmetic

The class `RCLike K` extends `DenselyNormedField K`, `StarRing K`, `NormedAlgebra ℝ K` and `CompleteSpace K`. Its data are the additive maps `RCLike.re` and `RCLike.im` to $\mathbb{R}$ and the element `RCLike.I`. The axioms are the ones of $\mathbb{C}$ with one twist: $I$ is either a square root of $-1$ or $0$. The lemma `RCLike.I_mul_I` states $I = 0 \lor I^2 = -1$. The case $I = 0$ is the field $\mathbb{R}$, and `RCLike.realRingEquiv` gives the ring isomorphism $K \cong \mathbb{R}$ in that case. The instances are `Real.instRCLike` and `Complex.instRCLike`.

The basic identities are the decomposition `RCLike.re_add_im`, $z = \operatorname{Re} z + \operatorname{Im} z \cdot I$, and the norm formula `RCLike.norm_sq_eq_def`, $\|z\|^2 = (\operatorname{Re} z)^2 + (\operatorname{Im} z)^2$. The conjugation is `starRingEnd K`, written $\bar z$. The library uses the names `RCLike.conj_re` and `RCLike.conj_im` for $\operatorname{Re} \bar z = \operatorname{Re} z$ and $\operatorname{Im} \bar z = -\operatorname{Im} z$. The arithmetic of real and imaginary parts follows the pattern `RCLike.<op>_re` and `RCLike.<op>_im`.

| Lean name | Statement |
|---|---|
| `RCLike.mul_re` | $\operatorname{Re}(zw) = \operatorname{Re} z \operatorname{Re} w - \operatorname{Im} z \operatorname{Im} w$ |
| `RCLike.mul_im` | $\operatorname{Im}(zw) = \operatorname{Re} z \operatorname{Im} w + \operatorname{Im} z \operatorname{Re} w$ |
| `RCLike.mul_conj` | $z \bar z = \|z\|^2$ |
| `RCLike.inv_eq_conj` | $\|z\| = 1 \Rightarrow z^{-1} = \bar z$ |
| `RCLike.add_conj` | $z + \bar z = 2 \operatorname{Re} z$ |
| `RCLike.re_le_norm` | $\operatorname{Re} z \le \|z\|$ |
| `RCLike.abs_re_le_norm` | $\lvert \operatorname{Re} z \rvert \le \|z\|$ |
| `RCLike.norm_ofReal` | $\|\iota(r)\| = \lvert r \rvert$ |

*Proof of `RCLike.mul_conj`.* Write $z = a + bI$. Then $z \bar z = (a + bI)(a - bI) = a^2 - b^2 I^2$. If $I^2 = -1$ this is $a^2 + b^2 = \|z\|^2$. If $I = 0$ then $b$ plays no role, $z = a$ and $z \bar z = a^2 = \|z\|^2$. $\square$ The second line follows: for $\|z\| = 1$, $z \bar z = 1$, so $\bar z = z^{-1}$.

The real numbers sit in $K$ through the coercion `RCLike.ofReal`, written `↑r`. The simp normal form pushes the coercion outward: `RCLike.ofReal_add`, `RCLike.ofReal_mul` and `RCLike.ofReal_pow` move sums and products through it, and `RCLike.ofReal_re` and `RCLike.ofReal_im` give $\operatorname{Re} \iota(r) = r$ and $\operatorname{Im} \iota(r) = 0$. The lemma `RCLike.is_real_tfae` collects five equivalent forms of "$z$ is real":
$$\bar z = z, \quad z \in \iota(\mathbb{R}), \quad \iota(\operatorname{Re} z) = z, \quad \operatorname{Im} z = 0, \quad z \text{ is self adjoint}.$$
*Proof.* Each statement is $b = 0$ in $z = a + bI$, when $I^2 = -1$. When $I = 0$, each statement is true. $\square$

#### The order and the dimension

An `RCLike` field has a partial order, the *star order*: $z \le w$ if and only if $\operatorname{Re} z \le \operatorname{Re} w$ and $\operatorname{Im} z = \operatorname{Im} w$. This is `RCLike.le_iff_re_im`, and `RCLike.nonneg_iff` states that $0 \le z$ if and only if $z$ is a nonnegative real. For $K = \mathbb{R}$ it is the usual order. For $K = \mathbb{C}$ it is not total, since $1$ and $I$ are not comparable. The instance `RCLike.toStarOrderedRing` makes $K$ a star ordered ring: the nonnegative elements are the elements $\bar z z$.

As a real vector space, $K$ has dimension at most $2$. The lemma `RCLike.span_one_I` states that $1$ and $I$ span $K$ over $\mathbb{R}$, and `RCLike.finrank_le_two` gives $\dim_{\mathbb{R}} K \le 2$. *Proof.* By `RCLike.re_add_im`, each $z$ is a real combination of $1$ and $I$. $\square$ So the instance `FiniteDimensional.rclike_to_real` holds, and each finite dimensional space over $K$ is a finite dimensional real space. The instance `FiniteDimensional.proper_rclike` follows from Chapter 3: a finite dimensional normed space over $K$ is proper.

#### Bundled maps

The library bundles the basic maps in several forms. The suffix gives the form: `Lm` a linear map, `CLM` a continuous linear map, `LI` a linear isometry, `CLE` a continuous linear equivalence, `Ae` an algebra equivalence.

| Lean name | Map |
|---|---|
| `RCLike.reCLM` | $\operatorname{Re}$ as a real continuous linear functional on $K$, of norm $1$ (`RCLike.reCLM_norm`) |
| `RCLike.imCLM` | $\operatorname{Im}$ as a real continuous linear functional |
| `RCLike.ofRealCLM` | $\iota : \mathbb{R} \to K$, of norm $1$ (`RCLike.ofRealCLM_norm`) |
| `RCLike.ofRealLI` | $\iota$ as a linear isometry |
| `RCLike.conjCLE` | the conjugation as a real continuous linear equivalence, of norm $1$ |
| `RCLike.conjLIE` | the conjugation as a real linear isometric equivalence |
| `RCLike.conjAe` | the conjugation as a real algebra equivalence |

The continuity lemmas follow the pattern of Volume 13: `Continuous.re`, `ContinuousAt.re` and `Filter.Tendsto.re` for the real part, and the same with `im` and `ofReal`. The maps are Lipschitz with constant $1$: `RCLike.lipschitzWith_one_re` and `RCLike.lipschitzWith_one_conj`.

#### The square root

The module `Mathlib.Analysis.RCLike.Sqrt` defines `RCLike.sqrt`, the principal square root on $K$. On $\mathbb{R}$ it is the real square root of a nonnegative number, by `RCLike.sqrt_real`, and on $\mathbb{C}$ it is `Complex.sqrt`, by `RCLike.sqrt_complex`. The lemma `RCLike.sqrt_eq_real_add_ite` gives the closed form
$$\sqrt{a} = \sqrt{\frac{\|a\| + \operatorname{Re} a}{2}} \pm \sqrt{\frac{\|a\| - \operatorname{Re} a}{2}} \, I,$$
with the sign $+$ when $\operatorname{Im} a \ge 0$. *Check.* Let $u$ and $v$ be the two real roots. Then $u^2 - v^2 = \operatorname{Re} a$, and $2uv = \sqrt{\|a\|^2 - (\operatorname{Re} a)^2} = \lvert \operatorname{Im} a \rvert$. With the sign of $\operatorname{Im} a$, $(u \pm v I)^2 = a$. $\square$ The values `RCLike.sqrt_neg_one` and `Complex.sqrt_I` are the examples $\sqrt{-1} = I$ and $\sqrt{I} = (1 + I)/\sqrt 2$. The lemma `sqrt_eq_exp` states $\sqrt z = \exp(\tfrac12 \log z)$ for $z \ne 0$.

#### Weighted inner products on finite products

The module `Mathlib.Analysis.RCLike.Inner` defines the weighted inner product `RCLike.wInner` of two functions on a finite type $\iota$:
$$\langle f, g \rangle_w = \sum_{i} w_i \langle f_i, g_i \rangle.$$
The notation is `⟪f, g⟫_[𝕜, w]`, and `⟪f, g⟫_[𝕜]` is the case $w = 1$. With the constant weight $w_i = 1/|\iota|$, written `⟪f, g⟫ₙ_[𝕜]`, the sum becomes an average (`RCLike.wInner_cWeight_eq_expect`). The lemma `RCLike.wInner_one_eq_sum` gives the unweighted form, and `RCLike.wInner_one_eq_inner` identifies it with the inner product of `PiLp 2` of Section 2. The averaged form suits sums over a finite group. The usual rules hold: `RCLike.wInner_add_left`, `RCLike.wInner_smul_left`, `RCLike.conj_wInner_symm`, and the bound `RCLike.norm_wInner_le`.

#### Real and complex valued functions

The module `Mathlib.Analysis.RCLike.ContinuousMap` compares $C(X, \mathbb{R})$ and $C(X, K)$. The map `ContinuousMap.realToRCLike` composes with $\iota$, and `ContinuousMap.rclikeToReal` takes the real part. The first map is an isometry (`ContinuousMap.isometry_realToRCLike`), an order embedding (`ContinuousMap.realToRCLikeOrderEmbedding`) and a star algebra homomorphism (`ContinuousMap.realToRCLikeStarAlgHom`), and its range is the set of self adjoint functions (`ContinuousMap.range_realToRCLike_eq_isSelfAdjoint`). The second map is a left inverse: `ContinuousMap.rclikeToReal_realToRCLike`. The module `Mathlib.Analysis.RCLike.BoundedContinuous` has one technical lemma, `RCLike.restrict_toContinuousMap_eq_toContinuousMapStar_restrict`: on a star subalgebra of bounded continuous functions with values in $K$, the passage to real valued functions commutes with the map that forgets the bound.

The module `Mathlib.Analysis.RCLike.Lemmas` adds small facts: `Polynomial.aeval_conj` states $p(\bar z) = \overline{p(z)}$ for a real polynomial $p$, and `RCLike.norm_coe_norm` states $\|\iota(\|z\|)\| = \|z\|$. The module `Mathlib.Analysis.RCLike.TangentCone` compares tangent cones over $\mathbb{R}$ and over $K$: `tangentConeAt_real_subset_isRCLikeNormedField` and `uniqueDiffOn_convex_of_isRCLikeNormedField`, which Volume 17 uses for derivatives on convex sets. The class `IsRCLikeNormedField` there is a property of a normed field: it says that the field carries an `RCLike` structure with the same norm.

#### Normed spaces over an RCLike field

The module `Mathlib.Analysis.Normed.Module.RCLike.Basic` has the lemmas that use the scalar $\|x\|^{-1}$. The lemma `norm_smul_inv_norm` states $\|\,\|x\|^{-1} x\| = 1$ for $x \ne 0$. The lemma `LinearMap.bound_of_sphere_bound` states: if a linear functional $f$ has $\|f z\| \le c$ on the sphere of radius $r > 0$, then $\|f z\| \le (c/r) \|z\|$ for all $z$. *Proof.* For $z \ne 0$, the vector $r \|z\|^{-1} z$ lies on the sphere, so $\|f z\| = \tfrac{\|z\|}{r} \|f(r \|z\|^{-1} z)\| \le \tfrac{c}{r} \|z\|$. $\square$ The bound on a ball, `ContinuousLinearMap.opNorm_bound_of_ball_bound`, follows. Over a general normed field this argument fails, because $\|x\|^{-1}$ need not be a scalar.

The module `Mathlib.Analysis.Normed.Module.RCLike.Extend` continues the extension of a real functional to a complex one of Chapter 5, Section 1, where `StrongDual.extendRCLike` is defined. It proves `StrongDual.norm_extendRCLike`: the extension $\tilde f$ of a real continuous functional $f$ has $\|\tilde f\| = \|f\|$. *Proof sketch.* For $x$, choose $c$ with $|c| = 1$ and $c \tilde f(x) = |\tilde f(x)|$. Then $|\tilde f(x)| = \tilde f(cx)$ is real, so it equals $f(cx) \le \|f\| \|x\|$. The other inequality holds because $f = \operatorname{Re} \tilde f$. $\square$ The bundled forms are `StrongDual.extendRCLikeL`, a continuous real linear equivalence between the real and the complex dual, and `StrongDual.extendRCLikeₗᵢ`, a linear isometric equivalence.

#### Common errors

1. A lemma that holds only for $\mathbb{C}$ needs `RCLike.I_mul_I` in its case form. A proof that uses $I^2 = -1$ for a general `RCLike` field must first exclude the case $I = 0$.
2. The order on `RCLike K` is the star order, not a total order. The statement $z \le w$ for complex numbers says that $w - z$ is a nonnegative real.
3. The simp normal form writes real numbers as `↑r` in $K$, not as `algebraMap ℝ K r`. The lemma `RCLike.algebraMap_eq_ofReal` converts between them.

### Exercises

1. (A) Prove `RCLike.add_conj` from `RCLike.re_add_im` and the rules for the conjugation.
2. (A) Show that $\|z\|^2 = \operatorname{Re}(z \bar z)$ in an `RCLike` field.
3. (A) Compute `RCLike.sqrt (-4 : ℂ)` with `RCLike.sqrt_neg_of_nonneg`.
4. (B) Prove that the star order on $\mathbb{C}$ is not total, and that $z \le w$ implies $\|z\| \le \|w\|$ when $0 \le z$.
5. (B) Prove `RCLike.finrank_le_two` and show that equality holds if and only if $I \ne 0$.
6. (C) Prove that a continuous function $f : X \to \mathbb{C}$ is self adjoint in $C(X, \mathbb{C})$ if and only if it is in the range of `ContinuousMap.realToRCLike`.

### Reference

<?reference?>
