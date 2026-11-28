---
title: Rays in modules and the orientation of the complex plane
kind: api
modules:
  - Mathlib.LinearAlgebra.Ray
  - Mathlib.LinearAlgebra.Complex.Orientation
  - Mathlib.LinearAlgebra.Complex.Determinant
explains:
  E2: [SameRay, SameRay.trans, SameRay.exists_pos_left, sameRay_or_sameRay_neg_iff_not_linearIndependent, RayVector, Module.Ray, rayOfNeZero, ray_eq_iff, Module.Ray.units_smul_of_neg, Complex.orientation]
  E1: auto
families: []
requires: [V03, V06]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Rays in modules and the orientation of the complex plane

### Overview

Over an ordered field such as $\mathbb{R}$, two nonzero vectors point in the same direction when one is a positive multiple of the other. The classes of nonzero vectors for this relation are the rays. Rays are the base of orientations: an orientation of a real vector space of dimension $n$ is a ray in the line of alternating $n$-linear forms, and two bases have the same orientation exactly when the determinant of the change of basis is positive. The determinant of Section 1 is the link between the two descriptions.

This section describes the module `Mathlib.LinearAlgebra.Ray`, which defines the relation, the type of rays and the action of units on rays, over any strictly ordered commutative semiring. It ends with the standard orientation of $\mathbb{C}$ as a real plane. The general theory of orientations, with alternating maps, is in Volume 8 with the exterior algebra.

### The library around it

#### The relation of being in the same ray

**Definition (`SameRay`).** For an ordered commutative semiring $R$ and an $R$-module $M$, two vectors $v_1, v_2 \in M$ satisfy `SameRay R v₁ v₂` when $v_1 = 0$, or $v_2 = 0$, or $r_1 v_1 = r_2 v_2$ for some $r_1 > 0$ and $r_2 > 0$.

The zero vector is in the same ray as each vector (`SameRay.zero_left`, `SameRay.zero_right`). This choice makes the relation reflexive and symmetric (`SameRay.refl`, `SameRay.symm`) without conditions, and it makes many closure lemmas true without a hypothesis. The cost is that the relation is not transitive: $v$ and $-v$ are both in the same ray as $0$.

**Theorem (`SameRay.trans`).** If `SameRay R x y` and `SameRay R y z`, and $y = 0$ implies $x = 0$ or $z = 0$, then `SameRay R x z`.

*Proof sketch.* If $x$, $y$ or $z$ is zero, the hypothesis on $y$ gives the result at once. Otherwise there are positive $r_1, r_2, s_1, s_2$ with $r_1 x = r_2 y$ and $s_1 y = s_2 z$. Then $s_1 r_1 x = r_2 s_1 y = r_2 s_2 z$, and $s_1 r_1$ and $r_2 s_2$ are positive. $\square$

The relation is compatible with the module operations. Positive and nonnegative multiples stay in the ray (`SameRay.pos_smul_left`, `SameRay.nonneg_smul_right`), so do sums of vectors in the same ray (`SameRay.add_left`, `SameRay.sum_right`), negation of both vectors (`sameRay_neg_iff`) and linear maps (`SameRay.map`). An injective linear map reflects the relation (`Function.Injective.sameRay_map_iff`). For a single vector, `sameRay_smul_right_iff` says that $v$ and $r v$ are in the same ray if and only if $0 \le r$ or $v = 0$, over a linearly ordered ring.

Over a linearly ordered field, the definition with two scalars becomes the familiar one.

**Theorem (`SameRay.exists_pos_left`).** Over a linearly ordered field, if `SameRay R x y` with $x \ne 0$ and $y \ne 0$, then $y = r x$ for some $r > 0$.

*Proof.* From $r_1 x = r_2 y$ with $r_1, r_2 > 0$, take $r = r_1 / r_2$. $\square$

The variants are `SameRay.exists_pos_right`, `SameRay.exists_nonneg_left` for a nonzero $x$ only, and the equivalences `exists_pos_left_iff_sameRay` and `exists_nonneg_left_iff_sameRay`. The form `SameRay.exists_eq_smul` writes two vectors in the same ray as $a u$ and $b u$ for one vector $u$ and nonnegative $a, b$ with $a + b = 1$; this is the form used for the equality case of the triangle inequality in normed spaces.

**Theorem (`sameRay_or_sameRay_neg_iff_not_linearIndependent`).** Over a linearly ordered field, $x$ and $y$ are in the same ray or $x$ and $-y$ are in the same ray if and only if the family $(x, y)$ is linearly dependent.

*Proof sketch.* If $(x, y)$ is dependent, then $a x + b y = 0$ with $(a, b) \ne (0, 0)$. If $a = 0$ or $b = 0$, one of the vectors is zero. Otherwise $y = -(a/b) x$, and the sign of $-a/b$ decides between $y$ and $-y$. Conversely, a relation $r_1 x = r_2 y$ or $r_1 x = -r_2 y$ with positive scalars is a nontrivial linear relation. $\square$

#### The type of rays

**Definition (`RayVector`).** `RayVector R M` is the type of the nonzero vectors of $M$. The scalar ring $R$ is an argument only so that the relation `SameRay R` on it can be an instance.

The instance `RayVector.Setoid` is the relation `SameRay R` on nonzero vectors. On nonzero vectors it is transitive, by `SameRay.trans`, so it is an equivalence relation; `equiv_iff_sameRay` states it.

**Definition (`Module.Ray`).** `Module.Ray R M` is the quotient of `RayVector R M` by this relation.

**Definition (`rayOfNeZero`).** For $v \ne 0$, `rayOfNeZero R v h` is the ray of $v$.

**Theorem (`ray_eq_iff`).** For nonzero $v_1$ and $v_2$, the rays of $v_1$ and $v_2$ are equal if and only if `SameRay R v₁ v₂`.

This is the property of each quotient, with the relation of the setoid. The principle of induction `Module.Ray.ind` reduces a statement on all rays to the rays of nonzero vectors, and `Module.Ray.someVector` chooses a nonzero vector in a ray (`Module.Ray.someVector_ray`). A positive multiple does not change the ray (`ray_pos_smul`). A linear equivalence $e : M \simeq N$ gives the equivalence `Module.Ray.map e` of the types of rays, with the rules `Module.Ray.map_apply`, `Module.Ray.map_refl` and `Module.Ray.map_symm`.

#### Negation and units

Over an ordered ring, the negation of a vector gives the negation of rays (`instNegRay`), with `neg_rayOfNeZero` for the formula and the instance `Module.Ray.instInvolutiveNeg` for $-(-x) = x$. Over a domain, for a torsion free module, a ray is never equal to its negation (`Module.Ray.ne_neg_self`). A group $G$ that acts linearly on $M$ acts on the rays (`instMulActionRay`), and the units of $R$ are the main example.

**Theorem (`Module.Ray.units_smul_of_neg`).** Over a linearly ordered commutative ring, if a unit $u$ is negative, then $u \cdot x = -x$ for each ray $x$.

The positive case is `Module.Ray.units_smul_of_pos`: a positive unit fixes each ray. The equivalences `units_smul_eq_self_iff` and `units_smul_eq_neg_iff` say that the sign of the unit is the only thing that matters. So the units act on the rays through the group $\{\pm 1\}$ of signs, and the orbit of a vector under the positive units, the subgroup `Units.posSubgroup`, is contained in its ray (`sameRay_of_mem_orbit`).

#### Orientations and the complex plane

An orientation of an $R$-module $M$ with an index type $\iota$ is the type `Orientation R M ι` of rays in the module of alternating maps $M^\iota \to R$. When $M$ is free of rank $n$ and $\iota$ has $n$ elements, this module is free of rank $1$, so an orientation is one of two rays. A basis $b$ gives an orientation, the ray of its determinant, and two bases give the same orientation exactly when the determinant of the change of basis is positive. These results are in Volume 8 with the exterior algebra; this section needs only the case of the plane.

**Definition (`Complex.orientation`).** `Complex.orientation` is the orientation of $\mathbb{C}$ as a real vector space of dimension $2$ given by the basis $(1, i)$ of Chapter 2 Section 6.

This is the standard counterclockwise orientation. It is the orientation of the plane in the theory of oriented angles of Volume 22, where `Complex.orientation` gives the area form $(w, z) \mapsto \operatorname{Im}(\bar w z)$ and the rotation by a right angle $z \mapsto i z$. The definition is in its own module, so that the theory of orientations does not import the complex numbers.

The complex conjugation reverses this orientation. As a real linear map of $\mathbb{C}$, it fixes $1$ and sends $i$ to $-i$, so its matrix in the basis $(1, i)$ is $\operatorname{diag}(1, -1)$ and its determinant is $-1$. This is `Complex.det_conjAe` for the linear map and `Complex.linearEquiv_det_conjAe` for the linear equivalence, in the module `Mathlib.LinearAlgebra.Complex.Determinant`.

#### Common errors

1. `SameRay R x y` is true when $x = 0$ or $y = 0$. So it is not transitive, and `SameRay.trans` needs a hypothesis on the middle vector.
2. `Module.Ray R M` has no zero ray, and `rayOfNeZero` needs a proof that the vector is not zero. To state a property of all rays, use `Module.Ray.ind`.
3. The relation needs an ordered scalar ring. The complex numbers have no such order by default, so `Complex.orientation` is an orientation over $\mathbb{R}$, of type `Orientation ℝ ℂ (Fin 2)`.

### Exercises

1. (A) Show that $(1, 2)$ and $(3, 6)$ are in the same ray in $\mathbb{R}^2$, and that $(1, 2)$ and $(-1, -2)$ are not.
2. (A) Give three vectors $x$, $y$, $z$ in $\mathbb{R}^2$ with `SameRay ℝ x y`, `SameRay ℝ y z` and not `SameRay ℝ x z`.
3. (B) Prove that the sum of two nonzero vectors in the same ray is not zero, over a linearly ordered field.
4. (B) Show that the map $v \mapsto -v$ on the rays of $\mathbb{R}^n$, for $n \ge 1$, has no fixed point.
5. (B) Prove that $\mathbb{R}$ as a module over itself has exactly two rays.
6. (C) Prove that the bases $(1, i)$ and $(i, 1)$ of $\mathbb{C}$ over $\mathbb{R}$ give opposite orientations, with the determinant of the change of basis.

### Reference

<?reference?>
