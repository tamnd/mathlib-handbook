---
title: Lebesgue measure in Rⁿ and Haar measure
kind: theory
modules:
  - Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
  - Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
  - Mathlib.MeasureTheory.Measure.Haar.Basic
  - Mathlib.MeasureTheory.Measure.Haar.Unique
  - Mathlib.MeasureTheory.Measure.Haar.OfBasis
  - Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
  - Mathlib.MeasureTheory.Group.Measure
  - Mathlib.MeasureTheory.Group.Defs
  - Mathlib.MeasureTheory.Constructions.HaarToSphere
  - Mathlib.MeasureTheory.Constructions.SubmoduleQuotient
explains:
  E3: [MeasureTheory.Measure.IsAddHaarMeasure, MeasureTheory.Measure.addHaarMeasure, MeasureTheory.Measure.addHaarMeasure_unique, MeasureTheory.Measure.isAddLeftInvariant_eq_smul, MeasureTheory.Measure.addHaar_image_linearMap, MeasureTheory.Measure.addHaar_smul, Real.volume_Icc_pi, Real.map_matrix_volume_pi_eq_smul_volume_pi, InnerProductSpace.volume_ball]
  E2: [Real.volume_pi_Ioo, Real.volume_pi_Ioc, Real.volume_preserving_transvectionStruct, Real.smul_map_diagonal_volume_pi, Real.map_linearMap_volume_pi_eq_smul_volume_pi, MeasureTheory.Measure.addHaar_preimage_linearMap, MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar, MeasureTheory.Measure.addHaar_ball, MeasureTheory.Measure.addHaar_closedBall, MeasureTheory.Measure.addHaar_submodule, MeasureTheory.Measure.addHaar_affineSubspace, MeasureTheory.Measure.addHaar_sphere, MeasureTheory.Measure.addHaar_parallelepiped, MeasureTheory.Measure.haarMeasure, MeasureTheory.Measure.haarMeasure_unique, MeasureTheory.Measure.addHaarMeasure_self, MeasureTheory.Measure.addHaarScalarFactor, MeasureTheory.Measure.haar.haarContent, MeasureTheory.Measure.haar.index, MeasureTheory.Measure.IsAddLeftInvariant, MeasureTheory.measure_preimage_add, Module.Basis.addHaar, Module.Basis.parallelepiped, measureSpaceOfInnerProductSpace, Real.measureSpace, OrthonormalBasis.volume_parallelepiped, EuclideanSpace.volume_ball]
  E1: auto
families: []
requires: [V07, V13, V18.C01, V18.C02]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Lebesgue measure in Rⁿ and Haar measure

### Overview

Lebesgue measure $\lambda_n$ on $\mathbb{R}^n$ gives a box the product of its side lengths. This section proves its two characteristic properties. First, it is the only translation invariant Borel measure that is finite on compact sets, up to a constant factor. Second, a linear map $T$ multiplies it by $|\det T|$. The second fact follows from the first with almost no computation, and it is the linear case of the change of variables formula of Chapter 8. The first fact is a special case of the theorem of Haar on locally compact groups, and Mathlib takes that route: it defines the volume of $\mathbb{R}^n$ as a Haar measure. The section ends with Vitali's proof that not every subset of $\mathbb{R}$ is Lebesgue measurable.

### Definitions

**Definition (Lebesgue measure on $\mathbb{R}^n$).** *Lebesgue measure* $\lambda_n$ is the unique Borel measure on $\mathbb{R}^n$ with
$$\lambda_n\Big(\prod_{i=1}^n (a_i, b_i]\Big) = \prod_{i=1}^n (b_i - a_i) \quad \text{for all } a_i \le b_i.$$

Uniqueness holds because the half-open boxes form a π-system that generates the Borel sets, and the boxes $(-m, m]^n$ of finite measure exhaust $\mathbb{R}^n$ (Chapter 2, Section 3). For existence, the construction of Section 1 works with boxes in place of intervals. Mathlib instead takes the product of $n$ copies of $\lambda$, which Chapter 6 constructs. As in dimension one, closed boxes, open boxes and half-open boxes with the same corners have the same measure.

::: mathlib
`Real.volume_Icc_pi` · `Mathlib.MeasureTheory.Measure.Lebesgue.Basic`

Mathlib models $\mathbb{R}^n$ as the function type `ι → ℝ` for a finite type `ι`, for example `Fin n → ℝ`. Its `volume` is the product measure `Measure.pi (fun _ => volume)` of Chapter 6. The theorem says `volume (Icc a b) = ∏ i, ofReal (b i - a i)` for `a b : ι → ℝ`, where `Icc a b` is a box for the pointwise order. The forms with open and half-open boxes are `Real.volume_pi_Ioo` and `Real.volume_pi_Ioc`. The Euclidean space `EuclideanSpace ℝ ι` carries the same measure, transported along a measure preserving equivalence.

<?decl Real.volume_Icc_pi?>
:::

**Definition (Haar measure).** Let $G$ be a locally compact Hausdorff topological group, written additively. A *left invariant* measure on $G$ satisfies $\mu(x + A) = \mu(A)$ for all $x \in G$ and Borel $A$. An *additive Haar measure* is a left invariant Borel measure that is finite on compact sets, positive on nonempty open sets, and regular.

On $\mathbb{R}^n$, Lebesgue measure is a Haar measure: invariance is Theorem 1 of Section 1 in each coordinate, or Theorem 1 below, and regularity holds as in Section 1.

::: mathlib
`MeasureTheory.Measure.IsAddHaarMeasure` · `Mathlib.MeasureTheory.Group.Measure`

A class on a measure with three parts: `IsAddLeftInvariant μ` (the class of `Mathlib.MeasureTheory.Group.Defs`, which says `map (x + ·) μ = μ`), `IsFiniteMeasureOnCompacts μ` and `IsOpenPosMeasure μ`. Regularity is not part of the class; it comes from instances when the space is second countable. The multiplicative form is `IsHaarMeasure`. With the class, `MeasureTheory.measure_preimage_add` gives `μ ((g + ·) ⁻¹' A) = μ A`.

<?decl MeasureTheory.Measure.IsAddHaarMeasure?>
:::

### Theorems and proofs

**Theorem 1 (Translation invariant measures on $\mathbb{R}^n$).** Let $\mu$ be a translation invariant Borel measure on $\mathbb{R}^n$ that is finite on compact sets, and let $c = \mu((0, 1]^n)$. Then $\mu = c\,\lambda_n$. In particular $\lambda_n$ is translation invariant, and it is the only such measure with $\lambda_n((0,1]^n) = 1$.

*Proof.* First, $c \le \mu([0, 1]^n) < \infty$. Let $k \ge 1$ and $Q_k = (0, 1/k]^n$. The cube $(0, 1]^n$ is the disjoint union of the $k^n$ translates $Q_k + j/k$ with $j \in \{0, \dots, k - 1\}^n$. By invariance all of them have measure $\mu(Q_k)$, so $\mu(Q_k) = c\,k^{-n}$. Now let $B = \prod_i (a_i, b_i]$ with all $a_i, b_i \in \frac{1}{k}\mathbb{Z}$ and $a_i \le b_i$. It is the disjoint union of $\prod_i k(b_i - a_i)$ translates of $Q_k$, so
$$\mu(B) = c\,k^{-n} \prod_i k(b_i - a_i) = c\,\lambda_n(B).$$
Every box with rational corners has this form for a common denominator $k$. The boxes with rational corners form a π-system, since the intersection of two of them is again one or is empty. They generate the Borel σ-algebra, since every open set is a countable union of them. The sets $(-m, m]^n$ belong to the π-system, have finite measure for both $\mu$ and $c\lambda_n$, and exhaust $\mathbb{R}^n$. The uniqueness theorem of Chapter 2, Section 3 gives $\mu = c\lambda_n$.

For the invariance of $\lambda_n$, let $x \in \mathbb{R}^n$ and $\nu(A) = \lambda_n(A + x)$. Then $\nu$ is a Borel measure, and on a half-open box $\nu(B) = \lambda_n(B + x) = \lambda_n(B)$ because $B + x$ is a box with the same side lengths. Uniqueness on the π-system of boxes gives $\nu = \lambda_n$. $\square$

::: mathlib
`MeasureTheory.Measure.isAddLeftInvariant_eq_smul` · `Mathlib.MeasureTheory.Measure.Haar.Unique`

The general form on a locally compact, second countable group: if `μ` is a Haar measure and `μ'` is left invariant and finite on compact sets, then `μ' = μ'.addHaarScalarFactor μ • μ`. The scalar `addHaarScalarFactor` plays the part of $c$.

<?decl MeasureTheory.Measure.isAddLeftInvariant_eq_smul?>
:::

**Theorem 2 (Linear maps).** Let $T : \mathbb{R}^n \to \mathbb{R}^n$ be linear. For every Borel set $A$, $\lambda_n(T(A)) = |\det T|\,\lambda_n(A)$. When $\det T = 0$, $T(A)$ lies in a null set.

*Proof.* The plan: reduce to a constant $c(T)$ by Theorem 1, show that $c$ is multiplicative, compute it on elementary matrices, and treat singular maps apart.

Step 1. Let $T$ be invertible. Then $T(A) = (T^{-1})^{-1}(A)$ is Borel, and $\nu(A) = \lambda_n(T(A))$ is the image measure of $\lambda_n$ under $T^{-1}$. It is translation invariant, since $\nu(A + x) = \lambda_n(T(A) + Tx) = \nu(A)$, and finite on compact sets, since $T$ maps compact sets to compact sets. By Theorem 1, $\nu = c(T)\lambda_n$ with $c(T) = \lambda_n(T((0, 1]^n))$.

Step 2. For invertible $S$ and $T$, $c(TS)\lambda_n(A) = \lambda_n(T(S(A))) = c(T)\lambda_n(S(A)) = c(T)c(S)\lambda_n(A)$. With $A = (0, 1]^n$ this gives $c(TS) = c(T)c(S)$.

Step 3. Let $D$ be diagonal with nonzero entries $d_i$. Then $D((0, 1]^n)$ is a box with sides $|d_i|$, so $c(D) = \prod_i |d_i| = |\det D|$. Let $E$ be the shear $E(x) = x + x_j e_i$ with $i \ne j$, so $\det E = 1$. Its image $P = E((0, 1]^n)$ is the set of $y$ with $y_k \in (0, 1]$ for $k \ne i$ and $0 < y_i - y_j \le 1$. Cut it into $P_1 = P \cap \{y_i \le 1\}$, where $y_j < y_i \le 1$, and $P_2 = P \cap \{y_i > 1\}$, where $1 < y_i \le 1 + y_j$. Then $P_2 - e_i$ is the set where $0 < y_i \le y_j$. So $P_1$ and $P_2 - e_i$ are disjoint with union $(0, 1]^n$, and by invariance $c(E) = \lambda_n(P_1) + \lambda_n(P_2 - e_i) = 1$.

Step 4. Gaussian elimination (Volume 7) writes every invertible matrix as a product of shears and one diagonal matrix. Both $c$ and $|\det|$ are multiplicative and agree on these factors, so $c(T) = |\det T|$.

Step 5. Let $\det T = 0$. Then $T(\mathbb{R}^n)$ lies in a hyperplane $V$, and an invertible $S$ maps $V$ onto $H = \{x : x_n = 0\}$. For every $m$ and $\varepsilon > 0$, $H \cap (-m, m]^n \subseteq (-m, m]^{n-1} \times (-\varepsilon, \varepsilon]$, of measure $(2m)^{n-1} 2\varepsilon$. So $H$ is a countable union of null sets, and $\lambda_n(V) = c(S^{-1})\lambda_n(H) = 0$. $\square$

::: mathlib
`Real.map_matrix_volume_pi_eq_smul_volume_pi` · `Mathlib.MeasureTheory.Measure.Lebesgue.Basic`

Step 1 to Step 4 for a matrix with `M.det ≠ 0`: `map (toLin' M) volume = ofReal |M.det⁻¹| • volume`. The proof follows the text. It applies the theorem of `Matrix.Pivot` that a matrix is a product of transvections and a diagonal matrix, with `Real.volume_preserving_transvectionStruct` for the shears and `Real.smul_map_diagonal_volume_pi` for the diagonal. The image measure under $T$ is $|\det T|^{-1}\lambda_n$, which is the theorem for preimages.

<?decl Real.map_matrix_volume_pi_eq_smul_volume_pi?>
:::

::: mathlib
`MeasureTheory.Measure.addHaar_image_linearMap` · `Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar`

The theorem for any additive Haar measure `μ` on a finite dimensional real normed space and any set `s`, not only Borel sets: `μ (f '' s) = ofReal |LinearMap.det f| * μ s`. A singular `f` is allowed; then both sides are $0$, because a proper subspace is null (`MeasureTheory.Measure.addHaar_submodule`). The version with preimages is `addHaar_preimage_linearMap`.

<?decl MeasureTheory.Measure.addHaar_image_linearMap?>
:::

**Corollary 3 (Dilations and balls).** For $r \in \mathbb{R}$ and Borel $A$, $\lambda_n(rA) = |r|^n \lambda_n(A)$. For every norm on $\mathbb{R}^n$, the balls satisfy $\lambda_n(B(x, r)) = r^n \lambda_n(B(0, 1))$ for $r \ge 0$. Every proper affine subspace is null.

*Proof.* The map $x \mapsto rx$ has determinant $r^n$. Next, $B(x, r) = x + rB(0, 1)$, so translation invariance and the first claim give the formula. An affine subspace $x + V$ with $V$ a proper linear subspace is a translate of $V$, which is null by Step 5. $\square$

::: mathlib
`MeasureTheory.Measure.addHaar_smul` · `Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar`

`μ (r • s) = ofReal |r ^ finrank ℝ E| * μ s` for an additive Haar measure. The ball forms are `addHaar_ball` and `addHaar_closedBall`, and `addHaar_sphere` says that spheres are null.

<?decl MeasureTheory.Measure.addHaar_smul?>
:::

**Theorem 4 (Haar).** Let $G$ be a locally compact Hausdorff group. There is a Haar measure on $G$, and any two Haar measures differ by a positive constant factor.

The proof is long, and this volume does not give it. Haar's idea is to count coverings. For a compact $K$ and an open $U \ni 0$, let $(K : U)$ be the least number of translates of $U$ that cover $K$. Fix a compact $K_0$ with nonempty interior. A limit of the ratios $(K : U)/(K_0 : U)$ along smaller and smaller $U$ is an invariant content, and Chapter 2, Section 2 turns it into a measure.

::: mathlib
`MeasureTheory.Measure.addHaarMeasure` · `Mathlib.MeasureTheory.Measure.Haar.Basic`

`addHaarMeasure K₀` is the Haar measure normalized by `addHaarMeasure_self : addHaarMeasure K₀ K₀ = 1`, for `K₀ : PositiveCompacts G`, a compact set with nonempty interior. The construction follows Haar's idea: `MeasureTheory.Measure.haar.index` is the covering number, and `haar.haarContent` the limit content. The multiplicative form is `haarMeasure`.

<?decl MeasureTheory.Measure.addHaarMeasure?>
:::

::: mathlib
`MeasureTheory.Measure.addHaarMeasure_unique` · `Mathlib.MeasureTheory.Measure.Haar.Basic`

Uniqueness on a second countable group: a σ-finite left invariant `μ` equals `μ K₀ • addHaarMeasure K₀`. The volume of a finite dimensional inner product space is defined this way (`measureSpaceOfInnerProductSpace`): it is `Module.Basis.addHaar` of an orthonormal basis, the Haar measure that gives the parallelepiped of the basis the value $1$ (`OrthonormalBasis.volume_parallelepiped`). `Real.measureSpace` is the case of $\mathbb{R}$.

<?decl MeasureTheory.Measure.addHaarMeasure_unique?>
:::

**Theorem 5 (Vitali).** There is a subset of $[0, 1]$ that is not Lebesgue measurable.

*Proof.* Call $x, y \in [0, 1]$ equivalent if $x - y \in \mathbb{Q}$. By the axiom of choice, choose a set $V \subseteq [0, 1]$ that contains exactly one point of each equivalence class. Let $R = \mathbb{Q} \cap [-1, 1]$, a countable set. The translates $V + q$ for $q \in R$ are pairwise disjoint: if $v + q = v' + q'$, then $v - v' \in \mathbb{Q}$, so $v = v'$ and $q = q'$. Each $x \in [0, 1]$ is equivalent to some $v \in V$, and $x - v \in R$, so
$$[0, 1] \subseteq \bigcup_{q \in R} (V + q) \subseteq [-1, 2].$$
Suppose $V$ is measurable with $\lambda(V) = m$. By translation invariance every $V + q$ has measure $m$, and countable additivity gives $1 \le \sum_{q \in R} m \le 3$. A countable sum of copies of $m$ is $0$ if $m = 0$ and $\infty$ if $m > 0$. Both contradict the inequalities. $\square$

The proof uses only countable additivity, translation invariance and $\lambda([0, 1]) = 1$. So no measure with these properties is defined on all subsets of $\mathbb{R}$, and a σ-algebra smaller than the power set is necessary. The index of this edition has no declaration for the Vitali set.

### Examples

**Example (A parallelogram).** The parallelogram spanned by $v = (2, 1)$ and $w = (1, 3)$ is $T([0, 1]^2)$ for the matrix $T$ with columns $v$ and $w$. Since $\det T = 2 \cdot 3 - 1 \cdot 1 = 5$, its area is $5$, and the triangle with vertices $0$, $v$, $w$ has area $5/2$. Mathlib has this as `MeasureTheory.Measure.addHaar_parallelepiped`: `b.addHaar (parallelepiped v) = ofReal |b.det v|`.

**Example (The volume of a Euclidean ball).** Corollary 3 reduces the ball to the constant $\omega_n = \lambda_n(B(0, 1))$. Mathlib computes it with the Gamma function: $\omega_n = \pi^{n/2} / \Gamma(n/2 + 1)$. For $n = 2$, $\Gamma(2) = 1$ and $\omega_2 = \pi$. For $n = 3$, $\Gamma(5/2) = \frac{3}{2} \cdot \frac{1}{2}\sqrt{\pi} = \frac{3\sqrt{\pi}}{4}$, so $\omega_3 = \pi^{3/2} \cdot \frac{4}{3\sqrt{\pi}} = \frac{4\pi}{3}$.

::: mathlib
`InnerProductSpace.volume_ball` · `Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls`

For a nontrivial finite dimensional inner product space `E`, `volume (ball x r) = ofReal r ^ finrank ℝ E * ofReal (√π ^ finrank ℝ E / Gamma (finrank ℝ E / 2 + 1))`. The form `EuclideanSpace.volume_ball` uses `Fintype.card ι` for the dimension. The proof uses the Gaussian integral of Chapter 6.

<?decl InnerProductSpace.volume_ball?>
:::

**Counterexample (A null set need not be small).** A line $L$ in $\mathbb{R}^2$ is uncountable and unbounded, and $\lambda_2(L) = 0$ by Corollary 3. In Mathlib this is `MeasureTheory.Measure.addHaar_affineSubspace`.

### The library around it

`Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar` states almost everything for an arbitrary additive Haar measure `μ` on a finite dimensional real normed space `E`, with the names `addHaar_*`: images and preimages under linear maps, homotheties (`addHaar_image_homothety`), balls, spheres and affine subspaces. A theorem proved there holds for `volume` on `ℝ`, on `ι → ℝ`, on `EuclideanSpace ℝ ι` and on `ℂ` at once, because each of them has an instance `IsAddHaarMeasure volume`. `Mathlib.MeasureTheory.Measure.Haar.Unique` has the uniqueness theorems for general locally compact groups.

Polar coordinates come from `Mathlib.MeasureTheory.Constructions.HaarToSphere`. For an additive Haar measure $\mu$ on a space $E$ of dimension $n$, the measure `MeasureTheory.Measure.toSphere μ` on the unit sphere gives a set $A$ the value $n \, \mu(\{t x : x \in A, \ 0 < t < 1\})$, so the whole sphere has measure $n \, \mu(B(0, 1))$, by `MeasureTheory.Measure.toSphere_apply_univ`. The lemma `MeasureTheory.Measure.measurePreserving_homeomorphUnitSphereProd` says that the map $x \mapsto (x / \|x\|, \|x\|)$ sends $\mu$ on $E \setminus \{0\}$ to the product of this measure with the measure $r^{n-1} \, dr$ on $(0, \infty)$, which is `MeasureTheory.Measure.volumeIoiPow`. For radial functions, `MeasureTheory.integral_fun_norm_addHaar` gives
$$\int_E f(\|x\|) \, d\mu(x) = n \, \mu(B(0, 1)) \int_0^\infty r^{n-1} f(r) \, dr.$$
The file `Mathlib.MeasureTheory.Constructions.SubmoduleQuotient` gives the quotient `M ⧸ p` of a module by a submodule the quotient σ-algebra, with the instance `Submodule.Quotient.instMeasurableSpaceQuotient`.

Common errors of a learner:

- Expecting `volume` on `Fin 2 → ℝ` to know the Euclidean norm. The norm of `ι → ℝ` is the sup norm, so its unit ball is a cube of volume $2^n$; use `EuclideanSpace ℝ ι` for round balls.
- Applying a theorem about `volume` to a Haar measure that is normalized differently, such as one with `μ (ball 0 1) = 1`.

### Exercises

1. (A) Compute the area of the triangle with vertices $(0, 0)$, $(3, 1)$ and $(1, 2)$.
2. (A) Show that the ellipse $\{(x, y) : x^2/a^2 + y^2/b^2 < 1\}$ has area $\pi a b$.
3. (A) Show that the unit sphere of a norm on $\mathbb{R}^n$ is null. Hint: it lies in $\overline{B}(0, 1) \setminus B(0, r)$ for every $r < 1$.
4. (B) Show that an orthogonal map preserves $\lambda_n$, and deduce that $\lambda_n$ of a Euclidean ball does not depend on the orthonormal basis used to define it.
5. (C) Find a Borel measure on $\mathbb{R}$, finite on compact sets, invariant under $x \mapsto x + 1$ and not a multiple of $\lambda$. Which step of Theorem 1 needs invariance under all translations?
6. (B) Let $A \subseteq \mathbb{R}$ be measurable with $\lambda(A) > 0$. Show that $A$ contains a set that is not Lebesgue measurable. Hint: apply the proof of Theorem 5 to $A \cap (V + q)$.

### Notes and history

Haar proved the existence of an invariant measure for compact metric groups and for locally compact separable groups in 1933, and von Neumann proved uniqueness for compact groups soon after. Weil gave the general form for locally compact groups in his book of 1940. Vitali published the non-measurable set in 1905. The formula $\pi^{n/2}/\Gamma(n/2 + 1)$ for the volume of the unit ball is classical. In Mathlib, `Mathlib.MeasureTheory.Measure.Haar.Basic` has the author Floris van Doorn, `Mathlib.MeasureTheory.Measure.Haar.Unique` the author Sébastien Gouëzel, and `Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar` the authors Floris van Doorn and Sébastien Gouëzel.

### Reference

<?reference?>
