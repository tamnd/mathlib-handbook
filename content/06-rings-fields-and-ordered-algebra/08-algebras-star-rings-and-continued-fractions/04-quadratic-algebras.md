---
title: Quadratic algebras and the quadratic formula
kind: api
modules:
  - Mathlib.Algebra.QuadraticAlgebra.Defs
  - Mathlib.Algebra.QuadraticAlgebra.Basic
  - Mathlib.Algebra.QuadraticAlgebra.AlgHom
  - Mathlib.Algebra.QuadraticAlgebra.BaseChange
  - Mathlib.Algebra.QuadraticAlgebra.Discr
  - Mathlib.Algebra.QuadraticAlgebra.Discriminant
  - Mathlib.Algebra.QuadraticAlgebra.Int
  - Mathlib.Algebra.QuadraticAlgebra.Integral
  - Mathlib.Algebra.QuadraticAlgebra.IsQuadraticExtension
  - Mathlib.Algebra.QuadraticAlgebra.NormDeterminant
  - Mathlib.Algebra.QuadraticAlgebra.Rat
  - Mathlib.Algebra.QuadraticDiscriminant
explains:
  E2: [QuadraticAlgebra.omega_mul_omega_eq_add, QuadraticAlgebra.algebraMap_norm_eq_mul_star, QuadraticAlgebra.sq_sub_trace_smul_add_norm_eq_zero, QuadraticAlgebra.isUnit_iff_norm_isUnit, QuadraticAlgebra.lift, QuadraticAlgebra.discr_changeGenerator, QuadraticAlgebra.four_mul_norm_eq, quadratic_eq_zero_iff, discrim_le_zero]
  E1: auto
families: []
requires: [V06.C01, V06.C03, V06.C07]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Quadratic algebras and the quadratic formula

### Overview

Let $R$ be a commutative ring and let $a, b \in R$. The quadratic algebra `QuadraticAlgebra R a b` is the free $R$-module with basis $1, \omega$, with the multiplication that makes $\omega^2 = a + b\omega$. In other words, it is the quotient $R[X]/(X^2 - bX - a)$, but the library builds it directly as pairs $(x, y)$ that stand for $x + y\omega$. The Gaussian integers are `QuadraticAlgebra ℤ (-1) 0`, the ring $\mathbb{Z}[\sqrt{d}]$ is `QuadraticAlgebra ℤ d 0`, and the ring $\mathbb{Z}[(1 + \sqrt{5})/2]$ is `QuadraticAlgebra ℤ 1 1`, because $\omega = (1 + \sqrt{5})/2$ satisfies $\omega^2 = 1 + \omega$.

Each quadratic algebra carries a conjugation, a norm and a trace, and its isomorphism class is controlled by the discriminant $b^2 + 4a$. This section describes the construction and these invariants, the universal property, the classification by the discriminant, and the integral closure results over $\mathbb{Z}$ and $\mathbb{Q}$. It ends with the module `Mathlib.Algebra.QuadraticDiscriminant`, which proves the quadratic formula for a polynomial $a x^2 + b x + c$ in a field. The section uses algebras from Section 1 and star rings from Section 2.

### The library around it

#### The construction

The module `Mathlib.Algebra.QuadraticAlgebra.Defs` defines `QuadraticAlgebra R a b` as a structure with two fields `QuadraticAlgebra.re` and `QuadraticAlgebra.im`. The element with fields $x$ and $y$ stands for $x + y\omega$. Two elements are equal when their two fields agree (`QuadraticAlgebra.ext`). The product is given by `QuadraticAlgebra.mk_mul_mk`:

$$(x_1 + y_1\omega)(x_2 + y_2\omega) = (x_1 x_2 + a y_1 y_2) + (x_1 y_2 + y_1 x_2 + b y_1 y_2)\omega.$$

The generator is `QuadraticAlgebra.omega`, with `QuadraticAlgebra.re_omega` and `QuadraticAlgebra.im_omega` for its fields $0$ and $1$. The basic relation is `QuadraticAlgebra.omega_mul_omega_eq_add`: $\omega \cdot \omega = a \cdot 1 + b \cdot \omega$. The proof is one line from the product formula with $x_1 = x_2 = 0$ and $y_1 = y_2 = 1$.

The embedding of $R$ is `QuadraticAlgebra.C`, the element $r + 0\omega$. It agrees with the algebra map of the instance `QuadraticAlgebra.instAlgebra`, and the simp normal form uses `algebraMap`. The linear structure has its own names.

| Lean name | Statement |
|---|---|
| `QuadraticAlgebra.basis` | the basis $1, \omega$ indexed by `Fin 2` |
| `QuadraticAlgebra.equivProd` | the plain bijection with $R \times R$ |
| `QuadraticAlgebra.finrank_eq_two` | the rank over $R$ is $2$, when $R$ has the strong rank condition |
| `QuadraticAlgebra.algebraMap_dvd_iff` | $r$ divides $z$ if and only if $r$ divides both fields of $z$ |

The instance `QuadraticAlgebra.instCommRing` makes the type a commutative ring when $R$ is one. The proofs of the ring laws are a computation in each field.

#### Conjugation, norm and trace

The conjugate of $x + y\omega$ is $(x + by) - y\omega$ (`QuadraticAlgebra.star_mk`). It sends $\omega$ to the other root $b - \omega$ of $X^2 - bX - a$. The instance `QuadraticAlgebra.instStarRing` makes the algebra a star ring in the sense of Section 2, and `QuadraticAlgebra.starAlgEquiv` is the conjugation as an algebra automorphism. The ring is commutative, so the star is a ring homomorphism and not only an anti-homomorphism.

The norm and the trace are

$$N(x + y\omega) = x^2 + bxy - ay^2, \qquad T(x + y\omega) = 2x + by,$$

by `QuadraticAlgebra.norm_def` and `QuadraticAlgebra.trace_def`. The library bundles `QuadraticAlgebra.norm` as a monoid homomorphism to $R$ and `QuadraticAlgebra.trace` as an $R$-linear map. The two facts that link them to the conjugation are $z \bar z = N(z)$ (`QuadraticAlgebra.algebraMap_norm_eq_mul_star`) and $z + \bar z = T(z)$ (`QuadraticAlgebra.algebraMap_trace_eq_add_star`). Each is a direct computation with the product formula. Then each element is a root of its characteristic polynomial:

$$z^2 - T(z)\, z + N(z) = 0,$$

which is `QuadraticAlgebra.sq_sub_trace_smul_add_norm_eq_zero`. The proof: $z^2 - (z + \bar z) z + z \bar z = 0$.

**Units.** An element $z$ is a unit if and only if $N(z)$ is a unit of $R$ (`QuadraticAlgebra.isUnit_iff_norm_isUnit`). If $z$ is a unit, then $N(z)$ is a unit because $N$ is multiplicative. If $N(z)$ is a unit, then $N(z)^{-1} \bar z$ is an inverse of $z$, by $z \bar z = N(z)$. So the units of the Gaussian integers are the elements of norm $\pm 1$, and each solution of $x^2 - dy^2 = 1$ gives a unit $x + y\sqrt{d}$ of $\mathbb{Z}[\sqrt{d}]$. The lemma `QuadraticAlgebra.norm_eq_one_iff_mem_unitary` says that the elements of norm $1$ form the unitary submonoid `unitary`.

**Fields.** Over a field $K$, the algebra is a field if $X^2 - bX - a$ has no root in $K$. The library states this hypothesis as a `Fact` instance, and then `QuadraticAlgebra.instField` gives the field with $z^{-1} = N(z)^{-1} \bar z$ (`QuadraticAlgebra.inv_def`). Under the same hypothesis, `QuadraticAlgebra.norm_eq_zero_iff_eq_zero` says that only $0$ has norm $0$.

The module `Mathlib.Algebra.QuadraticAlgebra.NormDeterminant` gives one more description of the norm. Multiplication by $z$ is an $R$-linear map of a free module of rank $2$, and its determinant is $N(z)$ (`QuadraticAlgebra.det_toLinearMap_eq_norm`). Its matrix in the basis $1, \omega$ is $\begin{pmatrix} x & ay \\ y & x + by \end{pmatrix}$, and the determinant of this matrix is $x^2 + bxy - ay^2$.

#### The universal property

An algebra map from `QuadraticAlgebra R a b` to an $R$-algebra $A$ is fixed by the image $u$ of $\omega$, and $u$ must satisfy $u^2 = a + bu$. Conversely, each such $u$ gives a map $x + y\omega \mapsto x + yu$. Write $R[\omega]$ for `QuadraticAlgebra R a b`. The equivalence `QuadraticAlgebra.lift` states this:

$$\{u \in A \mid u u = a \cdot 1 + b \cdot u\} \simeq \mathrm{Hom}_{R\text{-alg}}(R[\omega], A).$$

The proof checks that $x + y\omega \mapsto x + yu$ respects products, which uses only the relation for $u$. The uniqueness is `QuadraticAlgebra.algHom_ext`: two algebra maps that agree at $\omega$ are equal, because $\omega$ generates the algebra (`QuadraticAlgebra.adjoin_omega_eq_top`).

A change of generator is the main use. Let $\omega' = u\omega + k$. Then $\omega'^2 = a' + b'\omega'$ with

$$a' = u^2 a - ubk - k^2, \qquad b' = ub + 2k.$$

The map `QuadraticAlgebra.changeGenerator a b u k` sends the generator of `QuadraticAlgebra R a' b'` to $u\omega + k$ (`QuadraticAlgebra.changeGenerator_omega`). It is injective when $u$ is regular, and `QuadraticAlgebra.changeGeneratorEquiv` is an isomorphism when $u$ is a unit. The map `QuadraticAlgebra.mapRingHom f a b` applies a ring homomorphism $f : R \to S$ to both fields. It respects the norm, the trace and the conjugation.

The module `Mathlib.Algebra.QuadraticAlgebra.AlgHom` studies algebra maps $f$ between two quadratic algebras over $R$. Such a map is fixed by $f(\omega)$, and its matrix in the two bases is $\begin{pmatrix} 1 & * \\ 0 & m \end{pmatrix}$, with $m$ the field `im` of $f(\omega)$ (`QuadraticAlgebra.toMatrix_algHom`). So $f$ is injective if and only if $m$ is regular (`QuadraticAlgebra.isRegular_im_omega_iff_injective`), and bijective if and only if $m$ is a unit (`QuadraticAlgebra.isUnit_im_omega_iff_bijective`). An injective $f$ respects the norm (`QuadraticAlgebra.norm_algHom`) and the conjugation (`QuadraticAlgebra.algHom_star`).

The module `Mathlib.Algebra.QuadraticAlgebra.BaseChange` treats extension of scalars. For an $R$-algebra $S$, the map `QuadraticAlgebra.baseChangeEquiv` is an isomorphism from $S \otimes_R$ `QuadraticAlgebra R a b` to `QuadraticAlgebra S a b`, with $a$ and $b$ mapped to $S$. The lemma `QuadraticAlgebra.isPushout` states the same fact as a pushout square of rings.

The module `Mathlib.Algebra.QuadraticAlgebra.IsQuadraticExtension` connects the construction with the class `Algebra.IsQuadraticExtension`, the algebras that are free of rank $2$. Each quadratic algebra is one (`QuadraticAlgebra.instIsQuadraticExtension`). Conversely, `Algebra.IsQuadraticExtension.exists_algEquiv_quadraticAlgebra` says that each commutative quadratic extension of $R$ is isomorphic to some `QuadraticAlgebra R a b`.

#### The discriminant

The module `Mathlib.Algebra.QuadraticAlgebra.Discriminant` defines `QuadraticAlgebra.discr a b` as $D = b^2 + 4a$ (`QuadraticAlgebra.discr_def`). It is the discriminant of $X^2 - bX - a$, and $D = (\omega - \bar\omega)^2$ in the algebra (`QuadraticAlgebra.algebraMap_discr`). The norm and the trace determine each other up to $D$:

$$4 N(z) = T(z)^2 - D \cdot \mathrm{im}(z)^2,$$

which is `QuadraticAlgebra.four_mul_norm_eq`. The proof: $T^2 = 4x^2 + 4bxy + b^2y^2$, and subtracting $(b^2 + 4a)y^2$ leaves $4(x^2 + bxy - ay^2)$.

A change of generator multiplies the discriminant by a square. With $a'$ and $b'$ as above,

$$b'^2 + 4a' = u^2 b^2 + 4ubk + 4k^2 + 4u^2 a - 4ubk - 4k^2 = u^2 (b^2 + 4a),$$

which is `QuadraticAlgebra.discr_changeGenerator`. The converse needs a condition on $2$. When $2$ is invertible, the element $2\omega - b$ squares to $D$, so `QuadraticAlgebra.algEquivDiscrZero` gives `QuadraticAlgebra R a b ≃ₐ[R] QuadraticAlgebra R (discr a b) 0`. Then two quadratic algebras are isomorphic if and only if their discriminants differ by the square of a unit (`QuadraticAlgebra.nonempty_algEquiv_iff_of_invertible_two`).

Over $\mathbb{Z}$, the number $2$ is not invertible, but the discriminant is $0$ or $1$ modulo $4$ (`QuadraticAlgebra.discr_emod_four_eq_zero_or_one`), and the algebra is isomorphic to one with $a = D / 4$ and $b = D \bmod 4$ (`QuadraticAlgebra.algEquivEdivEmod`). So the discriminant is a complete invariant: `QuadraticAlgebra.nonempty_algEquiv_int_iff_discr_eq` says that `QuadraticAlgebra ℤ a b` is isomorphic to the normal form for $D$ if and only if $D = b^2 + 4a$.

Over a field $K$ in which $2 \neq 0$, the algebra is a field if and only if $D$ is not a square (`QuadraticAlgebra.isField_iff_not_isSquare_discr`). If $D = s^2$, then $X^2 - bX - a$ has the root $(b + s)/2$, and the algebra is not a domain. The module `Mathlib.Algebra.QuadraticAlgebra.Rat` gives the classification over $\mathbb{Q}$: each algebra with $D \neq 0$ is isomorphic to `QuadraticAlgebra ℚ d 0` for a squarefree integer $d$ (`QuadraticAlgebra.Rat.exists_squarefree_algEquiv`), and two squarefree integers give isomorphic algebras only when they are equal (`QuadraticAlgebra.Rat.nonempty_algEquiv_iff`). The module `Mathlib.Algebra.QuadraticAlgebra.Discr` holds only deprecated names.

#### Integrality and quadratic orders

The module `Mathlib.Algebra.QuadraticAlgebra.Integral` works over a ring $R$ inside a ring $K$, with $R$ integrally closed in $K$. An element $z$ of `QuadraticAlgebra K a b` is integral over $R$ if and only if $T(z)$ and $N(z)$ lie in $R$ (`QuadraticAlgebra.isIntegral_iff`). One direction is the characteristic polynomial $X^2 - T(z) X + N(z)$. For the other direction, the conjugate $\bar z$ is integral too, so $T(z) = z + \bar z$ and $N(z) = z \bar z$ are integral elements of $K$, and so they lie in $R$. The parts are `QuadraticAlgebra.trace_mem_range_of_isIntegral` and `QuadraticAlgebra.isIntegral_omega`.

The module `Mathlib.Algebra.QuadraticAlgebra.Int` applies this to $\mathbb{Z} \subseteq \mathbb{Q}$. The ring `QuadraticAlgebra ℚ a b` is the fraction field of `QuadraticAlgebra ℤ a b` (the instance `QuadraticAlgebra.Int.instIsFractionRingIntRatCast`). The integer algebra is a domain if and only if its discriminant is not a square (`QuadraticAlgebra.Int.isDomain_iff`). It is the full ring of integers of the rational algebra if and only if $D$ is a fundamental discriminant (`QuadraticAlgebra.Int.isIntegralClosure_iff`, with `Int.IsFundamentalDiscr`). For example $\mathbb{Z}[\sqrt{5}]$ has $D = 20$, which is not fundamental, and its integral closure is $\mathbb{Z}[(1 + \sqrt 5)/2]$ with $D = 5$.

#### The quadratic formula

The module `Mathlib.Algebra.QuadraticDiscriminant` works with a polynomial $a x^2 + b x + c$ written out as `a * (x * x) + b * x + c`, not with `Polynomial`. Its discriminant `discrim a b c` is $b^2 - 4ac$. Note the sign convention: the polynomial $X^2 - bX - a$ of a quadratic algebra has `discrim 1 (-b) (-a)` equal to $b^2 + 4a$.

The basic identity is $4a(a x^2 + b x + c) = (2ax + b)^2 - (b^2 - 4ac)$. So in a domain in which $2 \neq 0$, and for $a \neq 0$, the value at $x$ is $0$ if and only if $b^2 - 4ac = (2ax + b)^2$ (`quadratic_eq_zero_iff_discrim_eq_sq`). In a field, this gives the quadratic formula `quadratic_eq_zero_iff`: if $b^2 - 4ac = s^2$, then

$$a x^2 + b x + c = 0 \iff x = \frac{-b + s}{2a} \ \text{or}\ x = \frac{-b - s}{2a}.$$

The proof: $(2ax + b)^2 = s^2$ means $(2ax + b - s)(2ax + b + s) = 0$, and $2a$ is invertible. The companions are listed here.

| Lean name | Statement |
|---|---|
| `exists_quadratic_eq_zero` | a root exists when the discriminant is a square |
| `discrim_eq_zero_iff` | the discriminant is $0$ if and only if the root is unique |
| `discrim_le_zero` | a polynomial with $a x^2 + bx + c \geq 0$ for all $x$ has $b^2 - 4ac \leq 0$ |
| `discrim_lt_zero` | a polynomial with values $> 0$ and $a \neq 0$ has $b^2 - 4ac < 0$ |

The order results need an ordered field from Chapter 7. For `discrim_le_zero`, the proof for $a \neq 0$ evaluates at $x = -b/(2a)$, where the value is $-(b^2 - 4ac)/(4a)$. A nonnegative polynomial with $a = 0$ is constant, so $b = 0$ and the discriminant is $0$. This lemma is the usual step in the proof of the Cauchy-Schwarz inequality.

#### Common errors

1. The relation is $\omega^2 = a + b\omega$, so the discriminant of `QuadraticAlgebra R a b` is $b^2 + 4a$, with a plus sign. The function `discrim a b c` of the quadratic formula is $b^2 - 4ac$, and its arguments are the coefficients of a different polynomial.
2. The conjugate of $x + y\omega$ is $(x + by) - y\omega$, not $x - y\omega$. The two agree only when $b = 0$.
3. The field instance on `QuadraticAlgebra K a b` needs a `Fact` that $X^2 - bX - a$ has no root. Lean does not find it from a hypothesis on $D$, so a proof must usually supply the instance itself.

### Exercises

1. (A) Compute $(1 + 2\omega)(3 - \omega)$ in `QuadraticAlgebra ℤ 2 1` with `QuadraticAlgebra.mk_mul_mk`, and check the result with the norm.
2. (A) Use `QuadraticAlgebra.isUnit_iff_norm_isUnit` to show that the units of `QuadraticAlgebra ℤ (-1) 0` are $\pm 1$ and $\pm\omega$.
3. (B) Find $u$ and $k$ such that `QuadraticAlgebra.changeGenerator` gives an injective algebra map from `QuadraticAlgebra ℤ 5 0` to `QuadraticAlgebra ℤ 1 1`, and show that this map is not surjective.
4. (B) Prove with `QuadraticAlgebra.lift` that `QuadraticAlgebra ℝ (-1) 0` has exactly two algebra maps to `ℂ`.
5. (B) Prove that $x^2 + x + 1 > 0$ for all real $x$, and deduce from `discrim_lt_zero` that its discriminant is negative.
6. (C) Prove that `QuadraticAlgebra ℤ a b` is a domain if and only if $b^2 + 4a$ is not a square, and compare the proof with `QuadraticAlgebra.Int.isDomain_iff`.

### Reference

<?reference?>
