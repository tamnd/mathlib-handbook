---
title: The unit circle, circle maps and additive characters
kind: api
modules:
  - Mathlib.Analysis.SpecialFunctions.Complex.Circle
  - Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
  - Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
  - Mathlib.Analysis.Complex.CoveringMap
explains:
  E2: [Circle.exp_eq_exp, Circle.exp_arg, Circle.argPartialEquiv, Circle.angleDiff_add_angleDiff, AddCircle.homeomorphCircle, ZMod.toCircle_apply, bijective_rootsOfUnityAddChar, circleMap_zero_mul, Complex.isCoveringMapOn_exp]
  E1: auto
families: []
requires: [V15.C06, V13, V14]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The unit circle, circle maps and additive characters

### Overview

Section 2 defines the unit circle `Circle` as a compact group and the map `Circle.exp : ℝ → Circle`, $t \mapsto e^{it}$. This section collects the rest of the library around the circle. It has four parts. The first part studies `Circle.exp` and its inverse on $(-\pi, \pi]$, the argument. The second part identifies the additive circle $\mathbb{R}/T\mathbb{Z}$ of Chapter 6 with `Circle`, and builds the additive characters of $\mathbb{Z}/N\mathbb{Z}$ with values in the circle. The third part treats `circleMap`, the parametrization $\theta \mapsto c + Re^{i\theta}$ of a circle with any center and radius, which every circle integral of Chapter 2 uses. The last part shows that $\exp$, the power maps and polynomials are covering maps.

The section uses the argument of Section 3 and the topology of Volume 13. The covering maps come from the algebraic topology of Volume 27, but the statements here need only the definition.

### The library around it

#### The exponential of the circle and the argument

The map `Circle.exp` is a continuous homomorphism from the additive group $\mathbb{R}$ onto the circle. It is periodic with period $2\pi$ (`Circle.periodic_exp`, `Circle.exp_two_pi`, `Circle.exp_int_mul_two_pi`) and onto (`Circle.exp_surjective`).

**Theorem.** For real $x, y$, $e^{ix} = e^{iy}$ if and only if $x - y \in 2\pi\mathbb{Z}$.

*Proof.* Since `Circle.exp` is a homomorphism, $e^{ix} = e^{iy}$ is $e^{i(x-y)} = 1$. By the kernel of the complex exponential (`Complex.exp_eq_one_iff`), $i(x - y) \in 2\pi i \mathbb{Z}$, and $x - y$ is real. $\square$

This is `Circle.exp_eq_exp`, and `Circle.exp_eq_one` is the case $y = 0$. The congruence form `Circle.exp_inj` uses the relation `≡ [PMOD 2 * π]`. Injectivity on an interval of length at most $2\pi$ follows: `Circle.exp_injOn_Ico`, `Circle.exp_injOn_Ioc` for half-open intervals of length at most $2\pi$, and `Circle.exp_injOn_Icc` for closed intervals of length less than $2\pi$.

The inverse on $(-\pi, \pi]$ is the argument. For $z$ on the circle, `Circle.exp_arg` states $e^{i \arg z} = z$, and `Circle.arg_exp` states $\arg e^{ix} = x$ for $x \in (-\pi, \pi]$. Mathlib packages the two maps in two ways.

1. `Circle.argPartialEquiv` is a `PartialEquiv Circle ℝ` with source all of the circle and target $(-\pi, \pi]$ (`Circle.argPartialEquiv_source`, `Circle.argPartialEquiv_target`). Its forward map is $z \mapsto \arg z$ and its inverse is `Circle.exp`.
2. `Circle.argEquiv` is an equivalence from the circle onto the subtype of $(-\pi, \pi]$.

Neither map is a homeomorphism: the argument jumps at $-1$. So the argument is injective (`Circle.injective_arg`) but not continuous on the circle.

The set `Circle.centeredArc r` is the open arc of the points $z$ with $|\arg z| < r$ (`Circle.mem_centeredArc` for $r \le \pi$). These arcs are open (`Circle.isOpen_centeredArc`), and the arcs of half-angle $\pi/2^{n+1}$ form a basis of neighbourhoods of $1$ (`Circle.hasBasis_centeredArc_div_two_pow`). The exponential maps $(-r, r)$ bijectively onto the arc of half-angle $r$ for $r \le \pi$ (`Circle.bijOn_exp_Ioo_centeredArc`). This gives the local inverses, and `isLocalHomeomorph_circleExp` states that `Circle.exp` is a local homeomorphism. With the deck group $2\pi\mathbb{Z}$ it is a covering map, `Circle.isCoveringMap_exp` and `Circle.isAddQuotientCoveringMap_exp`.

#### The angle from one point to another, and paths

The function `Circle.angleDiff x y` is the angle in $[0, 2\pi)$ that turns $x$ counterclockwise into $y$: `Circle.exp_angleDiff_mul` states $e^{i\,\mathrm{angleDiff}(x, y)} x = y$, and `Circle.angleDiff_nonneg` and `Circle.angleDiff_lt_two_pi` give the range.

**Theorem.** For $x \ne y$ on the circle, $\mathrm{angleDiff}(x, y) + \mathrm{angleDiff}(y, x) = 2\pi$.

*Proof.* Put $a = \mathrm{angleDiff}(x, y)$ and $b = \mathrm{angleDiff}(y, x)$. Then $e^{i(a+b)} x = e^{ib} y = x$, so $a + b \in 2\pi\mathbb{Z}$. Both numbers are in $[0, 2\pi)$, and both are positive because $x \ne y$ (`Circle.angleDiff_pos`). So $0 < a + b < 4\pi$, and $a + b = 2\pi$. $\square$

This is `Circle.angleDiff_add_angleDiff`. The function gives a counterclockwise path `Circle.path x y` from $x$ to $y$, the image of a segment under `Circle.exp` (`Circle.path_apply`). For $x \ne y$, the two paths from $x$ to $y$ and from $y$ to $x$ cover the circle (`Circle.range_path_union_range_path`) and meet only in $\{x, y\}$ (`Circle.range_path_inter_range_path`). These facts give the topology of the circle in a form that needs no covering theory: the circle is path connected (`Circle.instPathConnectedSpace`), the circle minus a point is path connected (`Circle.isPathConnected_compl_singleton`), and the circle minus two points is not connected (`Circle.not_isPreconnected_compl_pair`). The last fact separates the circle from an interval.

#### The additive circle and the angles

The additive circle `AddCircle T` is $\mathbb{R}/T\mathbb{Z}$, the domain of the Fourier series of Chapter 6. The map `AddCircle.toCircle` sends the class of $x$ to $e^{2\pi i x/T}$ (`AddCircle.toCircle_apply_mk`). It is well defined because $x \mapsto e^{2\pi i x/T}$ has period $T$ (`AddCircle.scaled_exp_map_periodic`). It turns addition into multiplication (`AddCircle.toCircle_add`, `AddCircle.toCircle_neg`, `AddCircle.toCircle_zsmul`), and it is continuous and injective for $T \ne 0$ (`AddCircle.continuous_toCircle`, `AddCircle.injective_toCircle`).

**Theorem.** For $T \ne 0$, `AddCircle.toCircle` is a homeomorphism from $\mathbb{R}/T\mathbb{Z}$ onto the circle.

*Proof.* The map is continuous and injective. It is onto, because `Circle.exp` is onto and $e^{it}$ is the image of the class of $tT/(2\pi)$. The additive circle is compact and the circle is Hausdorff, so a continuous bijection between them is a homeomorphism. $\square$

This is `AddCircle.homeomorphCircle`, with `AddCircle.homeomorphCircle_apply`. The variant `AddCircle.homeomorphCircle'` treats $T = 2\pi$, and its inverse is the argument (`AddCircle.homeomorphCircle'_symm_apply`). The type of angles `Real.Angle` is `AddCircle (2 * π)`, and `Real.Angle.toCircle` is the same map on it, with $\theta \mapsto \cos\theta + i \sin\theta$ (`Real.Angle.coe_toCircle`) and the inverse `Real.Angle.arg_toCircle`.

#### Additive characters

The module `Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar` packages these maps as additive characters, the homomorphisms of Chapter 6, Section 3. The type `AddChar A M` is the type of maps $\psi : A \to M$ with $\psi(0) = 1$ and $\psi(a + b) = \psi(a)\psi(b)$.

1. `AddCircle.toCircle_addChar` is the character $\mathbb{R}/T\mathbb{Z} \to$ `Circle` of the last part.
2. `ZMod.toCircle` is the character $\mathbb{Z}/N\mathbb{Z} \to$ `Circle`, $j \mapsto e^{2\pi i j/N}$, for $N \ne 0$. The formula `ZMod.toCircle_apply` uses the representative $\mathrm{val}(j)$ in $\{0, \ldots, N-1\}$, and `ZMod.toCircle_intCast` shows that any integer representative gives the same value.
3. `ZMod.stdAddChar` is the same character with values in $\mathbb{C}$ (`ZMod.stdAddChar_apply`). It is injective and primitive (`ZMod.injective_stdAddChar`, `ZMod.isPrimitive_stdAddChar`), so every character of $\mathbb{Z}/N\mathbb{Z}$ has the form $j \mapsto \psi(aj)$ for one $a$. The discrete Fourier transform of Chapter 6 uses this character.

The image of $\mathbb{Z}/N\mathbb{Z}$ is the group of $N$-th roots of unity in the circle. `ZMod.rootsOfUnityAddChar N` is the character with values in `rootsOfUnity N Circle`.

**Theorem.** For $N \ne 0$, the map $j \mapsto e^{2\pi i j/N}$ is a bijection from $\mathbb{Z}/N\mathbb{Z}$ onto the $N$-th roots of unity of the circle.

*Proof.* The map is injective, because $e^{2\pi i j/N} = 1$ with $0 \le j < N$ forces $j/N \in \mathbb{Z}$, so $j = 0$. Both groups have $N$ elements: a polynomial of degree $N$ has at most $N$ roots, and the map is an injection of a set with $N$ elements. So the map is onto. $\square$

This is `bijective_rootsOfUnityAddChar`. The equivalence `rootsOfUnityCircleEquiv` identifies the roots of unity in the circle with those in $\mathbb{C}$, and the instance `instHasEnoughRootsOfUnityCircle` records that the circle has a primitive $N$-th root of unity for every $N$.

#### The circle map

The module `Mathlib.Analysis.SpecialFunctions.Complex.CircleMap` defines
$$\mathrm{circleMap}(c, R, \theta) = c + R e^{i\theta},$$
the function `circleMap c R : ℝ → ℂ`. The radius $R$ is any real number. A negative $R$ gives the same circle, run from the opposite point, so `circleMap_mem_sphere'` places the value on the sphere of radius $|R|$. The circle integral `∮ z in C(c, R), f z` of Chapter 2 is the integral of $f(\mathrm{circleMap}(c, R, \theta))$ times the derivative over $[0, 2\pi]$.

The lemmas of the module come in three families. The first family places the points: `circleMap_mem_sphere`, `circleMap_notMem_ball`, `circleMap_ne_center` for $R \ne 0$, and the special points `circleMap_pi_div_two` and `circleMap_neg_pi_div_two`. The second family computes with the circle map at center $0$: `circleMap_zero` writes it as $Re^{i\theta}$, and the real and imaginary parts are `circleMap_zero_re` and `circleMap_zero_im`.

**Theorem.** $\mathrm{circleMap}(0, R_1, \theta_1) \cdot \mathrm{circleMap}(0, R_2, \theta_2) = \mathrm{circleMap}(0, R_1R_2, \theta_1 + \theta_2)$.

*Proof.* The left side is $R_1 e^{i\theta_1} R_2 e^{i\theta_2} = R_1 R_2 e^{i(\theta_1 + \theta_2)}$ by the addition formula. $\square$

This is `circleMap_zero_mul`. The same computation gives `circleMap_zero_div`, `circleMap_zero_inv`, `circleMap_zero_pow` and `circleMap_zero_zpow`. The third family gives distances. `norm_circleMap_zero` states $|\mathrm{circleMap}(0, R, \theta)| = |R|$, and `norm_circleMap_sub_circleMap_sq` is the law of cosines for two points on concentric circles. A point $w$ off the circle has a positive distance to it, uniformly near $w$ (`exists_ball_forall_le_norm_circleMap_sub`). This lemma is what makes the Cauchy integral a continuous function of $w$ off the circle. The map has period $2\pi$ (`periodic_circleMap`), it is injective on a half-open interval of length at most $2\pi$ for $R \ne 0$ (`injOn_circleMap_of_abs_sub_le'`), and it commutes with conjugation up to a change of sign of $\theta$ (`conj_circleMap`).

#### Covering maps

The module `Mathlib.Analysis.Complex.CoveringMap` proves that the standard maps of the punctured plane are covering maps. A map $p : E \to X$ is a covering map on a set $S \subseteq X$ (`IsCoveringMapOn p S`) when each point of $S$ has an open neighbourhood whose preimage is a disjoint union of open sets, each mapped homeomorphically onto it.

1. `Complex.isCoveringMapOn_exp`: $\exp$ is a covering map on $\mathbb{C} \setminus \{0\}$. The local inverses are the branches $\log + 2\pi i k$ of Section 3. `Complex.isAddQuotientCoveringMap_exp` adds that the fibres are the orbits of the translations by $2\pi i\mathbb{Z}$.
2. `isCoveringMapOn_npow`: in a proper nontrivially normed field where $n \ne 0$, the power map $z \mapsto z^n$ is a covering map on the complement of $0$. The form `isCoveringMapOn_zpow` treats integer powers.
3. `Polynomial.isCoveringMapOn_eval`: a polynomial map $p$ is a covering map on the complement of its critical values, the set $p(\{z : p'(z) = 0\})$.

**Theorem.** The map $\exp : \mathbb{C} \to \mathbb{C} \setminus \{0\}$ is a covering map.

*Proof sketch.* Let $w \ne 0$, and choose a ray $L$ from $0$ that misses $w$. On the complement $V$ of $L$, a continuous branch $\ell$ of the logarithm exists: rotate the principal logarithm of Section 3. The preimage $\exp^{-1}(V)$ is the disjoint union of the open sets $\ell(V) + 2\pi i k$, $k \in \mathbb{Z}$. On each of them, $\exp$ is a homeomorphism onto $V$ with inverse $\ell + 2\pi i k$. $\square$

The continuous logarithm on a simply connected set, `Complex.exists_continuousOn_eqOn_exp_comp` of Section 3, is the lifting property of this covering map.

#### Common errors

1. A learner uses `Circle.argPartialEquiv` as a homeomorphism. It is only a partial equivalence, and the argument is not continuous at $-1$. For a homeomorphism, use `AddCircle.homeomorphCircle'` from the angles.
2. A learner writes `ZMod.toCircle j = exp (2 * π * I * j / N)` with the cast of `j : ZMod N` to $\mathbb{C}$. The cast of `ZMod N` to $\mathbb{C}$ is not the representative. State the formula with $\mathrm{val}(j)$ as in `ZMod.toCircle_apply`, or start from an integer with `ZMod.toCircle_intCast`.
3. A learner assumes $R \ge 0$ in `circleMap c R`. The definition allows any real $R$. Many lemmas need `0 ≤ R`, such as `circleMap_mem_sphere`, and the general form `circleMap_mem_sphere'` uses $|R|$.

### Exercises

1. (A) Compute `Circle.angleDiff 1 (-1)` and `Circle.angleDiff (-1) 1`, and check `Circle.angleDiff_add_angleDiff`.
2. (A) Show that $\mathrm{circleMap}(c, R, \theta + \pi) = \mathrm{circleMap}(c, -R, \theta)$.
3. (B) Prove that $(\mathrm{circleMap}(0, R, \theta))^{-1} = \mathrm{circleMap}(0, R^{-1}, -\theta)$ for $R \ne 0$, and explain why `circleMap_zero_inv` has no hypothesis $R \ne 0$.
4. (B) Prove that `ZMod.toCircle` is injective from the formula with $\mathrm{val}(j)$ and `Circle.exp_eq_one`.
5. (B) Prove that the circle is not homeomorphic to $[0, 1]$, from `Circle.not_isPreconnected_compl_pair`.
6. (C) Prove that $z \mapsto z^2$ is a covering map of $\mathbb{C} \setminus \{0\}$ onto itself, but that it has no continuous inverse on $\mathbb{C} \setminus \{0\}$.

### Reference

<?reference?>
