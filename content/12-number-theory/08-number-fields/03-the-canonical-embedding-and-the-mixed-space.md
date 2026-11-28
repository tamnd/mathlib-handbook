---
title: The canonical embedding and the mixed space
kind: api
modules:
  - Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
  - Mathlib.NumberTheory.NumberField.EquivReindex
  - Mathlib.NumberTheory.NumberField.CanonicalEmbedding.ConvexBody
  - Mathlib.NumberTheory.NumberField.CanonicalEmbedding.PolarCoord
  - Mathlib.NumberTheory.NumberField.CanonicalEmbedding.FundamentalCone
  - Mathlib.NumberTheory.NumberField.CanonicalEmbedding.NormLeOne
explains:
  E2: [NumberField.canonicalEmbedding.integerLattice.inter_ball_finite, NumberField.mixedEmbedding.norm_eq_norm, NumberField.mixedEmbedding.convexBodySum_volume, NumberField.mixedEmbedding.exists_ne_zero_mem_ideal_of_norm_le, NumberField.mixedEmbedding.fundamentalCone.exists_unit_smul_mem, NumberField.mixedEmbedding.fundamentalCone.card_isPrincipal_norm_eq_mul_torsion, NumberField.mixedEmbedding.fundamentalCone.volume_normLeOne]
  E1: auto
families: []
requires: [V07.C02, V18.C03, V18.C06]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The canonical embedding and the mixed space

### Overview

A number field $K$ of degree $n$ has $n$ embeddings $\sigma : K \to \mathbb{C}$. Together they send $K$ into a real vector space of dimension $n$, and the ring of integers $\mathcal{O}_K$ becomes a lattice there. This is the start of the geometry of numbers. With Minkowski's theorem on convex bodies, the lattice gives the finiteness of the class group, the bound on the discriminant and the unit theorem of Section 2.

These modules hold the geometric side of that story. `Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic` defines the two embeddings of $K$, the lattices of $\mathcal{O}_K$ and of the fractional ideals, and the norm on the target space. `ConvexBody` defines the convex bodies and applies Minkowski's theorem. `PolarCoord` gives polar coordinates to compute volumes. `FundamentalCone` and `NormLeOne` build a fundamental domain for the action of the units and compute its volume with the regulator. `Mathlib.NumberTheory.NumberField.EquivReindex` relates the canonical embedding to the matrix $(\sigma_i(b_j))$ of an integral basis. Section 2 cited the results that use these modules; this section explains the objects behind them.

### The library around it

#### Two embeddings

The canonical embedding is the ring homomorphism `NumberField.canonicalEmbedding K : K →+* ((K →+* ℂ) → ℂ)`. It sends $x$ to the vector $(\sigma(x))_\sigma$ indexed by the embeddings, with no order on them: `NumberField.canonicalEmbedding.apply_at` says that the $\sigma$ coordinate is $\sigma(x)$. The map is injective (`NumberField.canonicalEmbedding_injective`). Its sup norm is the largest absolute value of a conjugate, by `NumberField.canonicalEmbedding.norm_le_iff`. The image of $\mathcal{O}_K$ is the subring `NumberField.canonicalEmbedding.integerLattice K`.

**Proposition.** For each $r$, the image of $\mathcal{O}_K$ meets the closed ball of radius $r$ in a finite set (`NumberField.canonicalEmbedding.integerLattice.inter_ball_finite`).

*Proof.* If $x \in \mathcal{O}_K$ has $|\sigma(x)| \le r$ for all $\sigma$, then the characteristic polynomial $\prod_\sigma (X - \sigma(x))$ has integer coefficients bounded in terms of $r$ and $n$. There are finitely many such polynomials, and each has at most $n$ roots. This is `NumberField.Embeddings.finite_of_norm_le` of the next section. $\square$

The coordinates of the canonical embedding are not independent: for $x$ in the real span of the image, the coordinate at the conjugate embedding $\bar\sigma$ is the complex conjugate of the coordinate at $\sigma$ (`NumberField.canonicalEmbedding.conj_apply`). So the image lies in a real subspace of dimension $n$. The mixed space removes this redundancy. It is the type `NumberField.mixedEmbedding.mixedSpace K`, defined as
$$\mathbb{R}^{r_1} \times \mathbb{C}^{r_2} = (\{w \mid w \text{ real}\} \to \mathbb{R}) \times (\{w \mid w \text{ complex}\} \to \mathbb{C}),$$
indexed by the infinite places. The mixed embedding `NumberField.mixedEmbedding K : K →+* mixedSpace K` takes the real embedding at a real place and the chosen embedding `NumberField.InfinitePlace.embedding` at a complex place (`NumberField.mixedEmbedding.mixedEmbedding_apply_isReal`, `NumberField.mixedEmbedding.mixedEmbedding_apply_isComplex`). The real dimension of the mixed space is $r_1 + 2r_2 = n$ (`NumberField.mixedEmbedding.finrank`). The linear map `NumberField.mixedEmbedding.commMap` goes from the target of the canonical embedding to the mixed space, and `NumberField.mixedEmbedding.commMap_canonical_eq_mixed` says that the two embeddings agree through it.

#### Norms at the places

For a place $w$, `NumberField.mixedEmbedding.normAtPlace w` is the absolute value of the $w$ coordinate, as a map `mixedSpace K →*₀ ℝ`. On the image of $K$ it is the place itself: `NumberField.mixedEmbedding.normAtPlace_apply` gives $\|\iota(x)\|_w = w(x)$. The norm of the mixed space is the multiplicative map
$$N(x) = \prod_w \|x\|_w^{m_w}, \qquad m_w = 1 \text{ for real } w, \quad m_w = 2 \text{ for complex } w,$$
which is `NumberField.mixedEmbedding.norm` with the formula `NumberField.mixedEmbedding.norm_apply`.

**Proposition.** For $x \in K$, the norm of $\iota(x)$ is $|N_{K/\mathbb{Q}}(x)|$ (`NumberField.mixedEmbedding.norm_eq_norm`).

*Proof.* The field norm is $\prod_\sigma \sigma(x)$ over all $n$ embeddings. A real place gives one embedding, and a complex place gives a pair $\sigma, \bar\sigma$ with $|\sigma(x)\bar\sigma(x)| = |\sigma(x)|^2$. So $|N(x)| = \prod_w w(x)^{m_w}$. $\square$

The norm is homogeneous of degree $n$ (`NumberField.mixedEmbedding.norm_smul`: $N(cx) = |c|^n N(x)$), it is $1$ on units (`NumberField.mixedEmbedding.norm_unit`), and it vanishes exactly when some coordinate vanishes (`NumberField.mixedEmbedding.norm_eq_zero_iff`). Do not mix it with the norm `‖x‖` of the normed space: `NumberField.mixedEmbedding.norm_eq_sup'_normAtPlace` says that `‖x‖` is the largest $\|x\|_w$.

Two more maps compare the mixed space with `NumberField.mixedEmbedding.realSpace K`, the functions from the places to $\mathbb{R}$. `NumberField.mixedEmbedding.normAtAllPlaces` takes the absolute value at each place, and `NumberField.mixedEmbedding.mixedSpaceOfRealSpace` goes back with real coordinates. For a set of real places $s$, `NumberField.mixedEmbedding.negAt s` changes the sign of the coordinates in $s$. A set $A$ that is stable under these sign changes has $\mathrm{vol}(A) = 2^{r_1}\mathrm{vol}(A^+)$, where $A^+$ is the part with positive real coordinates (`NumberField.mixedEmbedding.volume_eq_two_pow_mul_volume_plusPart`).

#### Lattices and bases

The image of $\mathcal{O}_K$ in the mixed space is `NumberField.mixedEmbedding.integerLattice K`, a $\mathbb{Z}$-submodule. The images of an integral basis form a real basis `NumberField.mixedEmbedding.latticeBasis K`, and `NumberField.mixedEmbedding.span_latticeBasis` says that their integer span is the lattice. The instance `NumberField.mixedEmbedding.instIsZLatticeRealMixedSpaceIntegerLattice` records that it is a full lattice: discrete and of full rank. For an invertible fractional ideal $I$, `NumberField.mixedEmbedding.idealLattice K I` and `NumberField.mixedEmbedding.fractionalIdealLatticeBasis K I` play the same roles, and `NumberField.mixedEmbedding.det_basisOfFractionalIdeal_eq_norm` says that the change of basis from $\mathcal{O}_K$ to $I$ has determinant of absolute value $N(I)$.

The standard basis `NumberField.mixedEmbedding.stdBasis K` takes the real coordinates and the real and imaginary parts of the complex coordinates; its fundamental domain is a unit cube (`NumberField.mixedEmbedding.volume_fundamentalDomain_stdBasis`). The index type `NumberField.mixedEmbedding.index K` of this basis is in bijection with the embeddings by `NumberField.mixedEmbedding.indexEquiv`, and `NumberField.mixedEmbedding.det_matrixToStdBasis` gives $\det = (i/2)^{r_2}$ for the change of coordinates from embeddings to the standard basis. For a Euclidean structure, `NumberField.mixedEmbedding.euclidean.mixedSpace K` is the same space with the $L^2$ norm, and `NumberField.mixedEmbedding.euclidean.toMixed` is a measure preserving equivalence with the mixed space.

`Mathlib.NumberTheory.NumberField.EquivReindex` treats the matrix of an integral basis $(b_j)$ under the embeddings. `NumberField.equivReindex K` is a bijection from the embeddings to the index type of the integral basis, and `NumberField.basisMatrix K` is the square matrix $(\sigma(b_j))$ indexed by embeddings. It is invertible (`NumberField.det_of_basisMatrix_non_zero`), and `NumberField.canonicalEmbedding_eq_basisMatrix_mulVec` writes the canonical embedding of $\alpha$ as this matrix times the coordinate vector of $\alpha$. Its square determinant is the discriminant, which is the link with Section 1.

#### Convex bodies and Minkowski's theorem

Minkowski's theorem says: a convex set $C$ in $\mathbb{R}^n$ that is symmetric about $0$, with $\mathrm{vol}(C) > 2^n \mathrm{covol}(L)$, contains a nonzero point of the lattice $L$. In Mathlib it is `MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure`. For the lattice of $I$, the right side is `NumberField.mixedEmbedding.minkowskiBound K I`, defined as $2^n$ times the volume of a fundamental domain. By `NumberField.mixedEmbedding.volume_fundamentalDomain_fractionalIdealLatticeBasis` and the discriminant of Section 1, this is $2^{n - r_2}\sqrt{|d_K|}\,N(I)$.

The module defines two families of convex bodies.

| Lean name | Set | Volume |
|---|---|---|
| `NumberField.mixedEmbedding.convexBodyLT` | $\|x\|_w < f(w)$ for all $w$ | $2^{r_1}\pi^{r_2}\prod_w f(w)^{m_w}$ |
| `NumberField.mixedEmbedding.convexBodyLT'` | the same, with a box at one complex place $w_0$ | `convexBodyLT'Factor` times the same product |
| `NumberField.mixedEmbedding.convexBodySum` | $\sum_w m_w\|x\|_w \le B$ | $2^{r_1}(\pi/2)^{r_2}B^n/n!$ |

The volume formulas are `NumberField.mixedEmbedding.convexBodyLT_volume` and `NumberField.mixedEmbedding.convexBodySum_volume`, with the constants `convexBodyLTFactor` and `convexBodySumFactor`. Each body is convex and symmetric (`NumberField.mixedEmbedding.convexBodyLT_convex`, `NumberField.mixedEmbedding.convexBodySum_neg_mem`). The existence results come in pairs, for an ideal and for $\mathcal{O}_K$: `NumberField.mixedEmbedding.exists_ne_zero_mem_ideal_lt` gives a nonzero $a \in I$ with $w(a) < f(w)$ for all $w$, and `NumberField.mixedEmbedding.exists_ne_zero_mem_ringOfIntegers_lt` is the case $I = \mathcal{O}_K$. The bodies with a box are used for the unit theorem and for primitive elements: `NumberField.mixedEmbedding.exists_primitive_element_lt_of_isReal` gives a generator $a$ of $K$ with all $w(a)$ small.

**Theorem (Minkowski bound).** Let $I$ be a fractional ideal. If `minkowskiBound K I ≤ volume (convexBodySum K B)`, then $I$ has a nonzero element $a$ with $|N(a)| \le (B/n)^n$ (`NumberField.mixedEmbedding.exists_ne_zero_mem_ideal_of_norm_le`).

*Proof.* Minkowski's theorem in the closed form gives $a \ne 0$ in $I$ with $\sum_w m_w w(a) \le B$. The sum has $n$ terms when each complex place counts twice. By the inequality of the arithmetic and geometric means,
$$|N(a)| = \prod_w w(a)^{m_w} \le \Big(\frac1n\sum_w m_w w(a)\Big)^n \le \Big(\frac Bn\Big)^n. \qquad \square$$

With the volume of the table, the hypothesis reads $2^{r_1}(\pi/2)^{r_2}B^n/n! \ge 2^{n-r_2}\sqrt{|d_K|}N(I)$. Since $n - r_1 - r_2 = r_2$, the smallest $B$ has $B^n = n!\,(4/\pi)^{r_2}\sqrt{|d_K|}\,N(I)$, and then
$$|N(a)| \le \frac{n!}{n^n}\Big(\frac4\pi\Big)^{r_2}\sqrt{|d_K|}\,N(I).$$
This is the bound $M_K$ of Section 2, and the lower bound `NumberField.abs_discr_ge` on the discriminant comes from it with $I = \mathcal{O}_K$ and $|N(a)| \ge 1$.

#### Polar coordinates

Volumes of sets in the mixed space are often easier in polar coordinates at the complex places. `NumberField.mixedEmbedding.realMixedSpace K` is $\mathbb{R}^{r_1} \times (\mathbb{R}\times\mathbb{R})^{r_2}$, and `NumberField.mixedEmbedding.mixedSpaceToRealMixedSpace` identifies it with the mixed space. `NumberField.mixedEmbedding.polarCoord K` applies the polar coordinates of $\mathbb{C}$ at each complex place. The second chart `NumberField.mixedEmbedding.polarSpaceCoord K` takes values in `NumberField.mixedEmbedding.polarSpace K`, which is $\mathbb{R}^{r_1 + r_2} \times \mathbb{R}^{r_2}$: the absolute values at all places, then the angles. The Jacobian is $\prod_{w \text{ complex}} \rho_w$ (`NumberField.mixedEmbedding.det_fderivPolarCoordRealSymm`), and the change of variables formulas are `NumberField.mixedEmbedding.lintegral_comp_polarCoord_symm` and `NumberField.mixedEmbedding.integral_comp_polarSpaceCoord_symm`.

For a measurable set $A$ that depends only on the absolute values at all places, `NumberField.mixedEmbedding.volume_eq_two_pow_mul_two_pi_pow_mul_integral` gives
$$\mathrm{vol}(A) = 2^{r_1}(2\pi)^{r_2}\int_{|A|}\ \prod_{w \text{ complex}} x_w \, dx,$$
where $|A|$ is the image of $A$ under `normAtAllPlaces`. The factor $2^{r_1}$ counts the signs at the real places and $2\pi$ is the integral over each angle. `NumberField.mixedEmbedding.volume_eq_two_pi_pow_mul_integral` is the form with signs kept at the real places.

#### The fundamental cone

The units act on the mixed space by coordinatewise multiplication: `NumberField.mixedEmbedding.unitSMul_smul` gives $u \cdot x = \iota(u)\,x$, and the action keeps the norm (`NumberField.mixedEmbedding.norm_unit_smul`). The map `NumberField.mixedEmbedding.logMap` sends $x$ with $N(x) \ne 0$ to the vector
$$\Big(m_w\big(\log\|x\|_w - \tfrac1n\log N(x)\big)\Big)_{w \ne w_0}$$
in the space of the logarithmic embedding of Section 2. It extends that embedding (`NumberField.mixedEmbedding.logMap_eq_logEmbedding`), it turns the action of a unit into a translation (`NumberField.mixedEmbedding.logMap_unit_smul`), and it is constant on real multiples (`NumberField.mixedEmbedding.logMap_real_smul`).

The fundamental cone `NumberField.mixedEmbedding.fundamentalCone K` is the set of $x$ with $N(x) \ne 0$ whose image under `logMap` lies in the fundamental parallelepiped of the unit lattice. It is a cone (`NumberField.mixedEmbedding.fundamentalCone.smul_mem_of_mem`), and it is a fundamental domain for the units modulo torsion.

**Proposition.** If $N(x) \ne 0$, some unit $u$ has $u \cdot x$ in the cone (`NumberField.mixedEmbedding.fundamentalCone.exists_unit_smul_mem`). If $x$ is in the cone, then $u \cdot x$ is in the cone exactly when $u$ is a root of unity (`NumberField.mixedEmbedding.fundamentalCone.unit_smul_mem_iff_mem_torsion`).

*Proof.* The image $L(\mathcal{O}_K^\times)$ is a full lattice in the log space, and every point of the space is a lattice point plus a unique point of the fundamental parallelepiped. Choose $u$ with $\mathrm{logMap}(x) - L(u^{-1})$ in the parallelepiped; then $u \cdot x$ is in the cone, since $\mathrm{logMap}(u \cdot x) = L(u) + \mathrm{logMap}(x)$. For the second claim, both $\mathrm{logMap}(x)$ and $L(u) + \mathrm{logMap}(x)$ are in the parallelepiped only if $L(u) = 0$, and the kernel of $L$ is the torsion (Section 2). $\square$

The set `NumberField.mixedEmbedding.fundamentalCone.integerSet K` is the cone intersected with the lattice of $\mathcal{O}_K$. Each nonzero principal ideal $(a)$ has exactly $w_K = |\mu_K|$ generators in it, one for each root of unity. The equivalence `NumberField.mixedEmbedding.fundamentalCone.integerSetEquiv` states this as `integerSet K ≃ {I // IsPrincipal I} × torsion K`, and the counting form is `NumberField.mixedEmbedding.fundamentalCone.card_isPrincipal_norm_eq_mul_torsion`:
$$\#\{I \text{ principal} \mid N(I) = n\} \cdot w_K = \#\{a \in \text{integerSet} \mid N(a) = n\}.$$
`NumberField.mixedEmbedding.fundamentalCone.card_isPrincipal_dvd_norm_le` is the form for ideals divisible by a fixed $J$ and with $N(I) \le s$. These counts reduce the number of ideals of norm at most $s$ to a count of lattice points in $s^{1/n}$ times a fixed set.

#### The part of norm at most one

That fixed set is `NumberField.mixedEmbedding.fundamentalCone.normLeOne K`, the points of the cone with $N(x) \le 1$ (`NumberField.mixedEmbedding.fundamentalCone.mem_normLeOne`). To count lattice points in its dilates, the module proves three facts: it is bounded (`NumberField.mixedEmbedding.fundamentalCone.isBounded_normLeOne`), its frontier has measure zero (`NumberField.mixedEmbedding.fundamentalCone.volume_frontier_normLeOne`), and its volume is
$$\mathrm{vol}(\{x \in \text{cone} \mid N(x) \le 1\}) = 2^{r_1}\pi^{r_2}R_K,$$
where $R_K$ is the regulator (`NumberField.mixedEmbedding.fundamentalCone.volume_normLeOne`).

*About the proof.* The set depends only on the absolute values, so polar coordinates reduce its volume to $2^{r_1}(2\pi)^{r_2}$ times an integral over a set in $\mathbb{R}_{>0}^{r_1+r_2}$. The map `NumberField.mixedEmbedding.fundamentalCone.expMap` takes $x$ to $(e^{x_w/m_w})_w$, and `NumberField.mixedEmbedding.fundamentalCone.expMapBasis` composes it with the basis `completeBasis K`: the logarithms of the fundamental units and one more vector $(m_w)_w$. In these coordinates the set becomes the box `NumberField.mixedEmbedding.fundamentalCone.paramSet K`, a product of $(-\infty, 0]$ and unit intervals. The Jacobian has absolute determinant $n R_K$ times an exponential (`NumberField.mixedEmbedding.fundamentalCone.abs_det_completeBasis_equivFunL_symm`). What remains is the integral of an exponential over $(-\infty, 0]$, and the constants combine to $2^{r_1}\pi^{r_2}R_K$.

With the lattice point count, these facts give the number of ideals of bounded norm in a class, and so the residue of the Dedekind zeta function. The asymptotic statements are in other modules of the chapter.

#### Common errors

1. The canonical embedding is indexed by embeddings `K →+* ℂ`, and the mixed space is indexed by places, real or complex. A complex place corresponds to two embeddings, and `NumberField.InfinitePlace.embedding` chooses one of them. Use `commMap` and `indexEquiv` to pass between the two indexings.
2. `NumberField.mixedEmbedding.norm x` is the product $\prod_w \|x\|_w^{m_w}$, while `‖x‖` is the sup norm of the normed space. The first is the norm of number theory, the second is the norm of analysis.
3. `minkowskiBound K I` and all volumes are in `ENNReal`. The hypotheses of the existence theorems compare elements of `ENNReal`, so a bound proved in `ℝ` must be moved with `ENNReal.ofReal`.

### Exercises

1. (A) For $K = \mathbb{Q}(\sqrt2)$, write the mixed space, the mixed embedding of $a + b\sqrt2$, and check that $N(\iota(a + b\sqrt2)) = |a^2 - 2b^2|$.
2. (A) Compute `minkowskiBound K 1` for $K = \mathbb{Q}(i)$ and the volume of `convexBodySum K B`, and find the smallest $B$ for which the Minkowski bound theorem applies.
3. (A) Show that $N(cx) = |c|^n N(x)$ for $c \in \mathbb{R}$ from the definition of the norm of the mixed space.
4. (B) Use the Minkowski bound with $I = \mathcal{O}_K$ to prove $\sqrt{|d_K|} \ge \frac{n^n}{n!}(\pi/4)^{r_2}$, and deduce $|d_K| > 1$ for $n \ge 2$.
5. (B) Describe the fundamental cone of a real quadratic field with fundamental unit $\varepsilon$, as a subset of $\mathbb{R}^2$, and check that it is a fundamental domain for $\{\pm\varepsilon^k\}$ modulo $\pm1$.
6. (C) For an imaginary quadratic field, compute the volume of `normLeOne K` directly and compare it with $2^{r_1}\pi^{r_2}R_K$, with the convention $R_K = 1$ for unit rank $0$.

### Reference

<?reference?>
