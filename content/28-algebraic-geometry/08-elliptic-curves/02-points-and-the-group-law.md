---
title: Points and the group law
kind: theory
modules:
  - Mathlib.AlgebraicGeometry.EllipticCurve.Affine.AddSubMap
  - Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
  - Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula
  - Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
  - Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Basic
  - Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Formula
  - Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Point
  - Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Basic
  - Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Formula
  - Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point
explains:
  E3: [WeierstrassCurve.Affine.Nonsingular, WeierstrassCurve.Affine.Point, WeierstrassCurve.Affine.slope, WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.CoordinateRing.XYIdeal, WeierstrassCurve.Affine.Point.toClass, WeierstrassCurve.Affine.Point.instAddCommGroup, WeierstrassCurve.Jacobian.Point, WeierstrassCurve.Projective.Point]
  E2: [WeierstrassCurve.Affine.Equation, WeierstrassCurve.Affine.equation_iff_nonsingular, WeierstrassCurve.Affine.negY, WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.addPolynomial_slope, WeierstrassCurve.Affine.nonsingular_add, WeierstrassCurve.Affine.nonsingular_neg, WeierstrassCurve.Affine.CoordinateRing, WeierstrassCurve.Affine.CoordinateRing.XYIdeal_neg_mul, WeierstrassCurve.Affine.CoordinateRing.XYIdeal_mul_XYIdeal, WeierstrassCurve.Affine.CoordinateRing.degree_norm_smul_basis, WeierstrassCurve.Affine.Point.toClass_injective, WeierstrassCurve.Affine.Point.add_of_X_ne, WeierstrassCurve.Jacobian.Equation, WeierstrassCurve.Jacobian.Point.toAffineAddEquiv, WeierstrassCurve.Projective.Equation, WeierstrassCurve.Projective.Point.toAffineAddEquiv, WeierstrassCurve.addSubMap]
  E1: auto
families: []
requires: [V06.C05, V09.C05, V10.C04, V10.C05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Points and the group law

### Overview

The points of an elliptic curve form an abelian group. The sum of two points is found by a line through them: it meets the curve in a third point, and the sum is the reflection of that point. The formulas for the sum are explicit, but the associative law is hard to check from them: a direct proof is a long computation with many cases.

Mathlib proves the group law by an algebraic route. Each affine point $P$ gives a maximal ideal of the coordinate ring, and hence a class in the ideal class group. The map $P \mapsto [I_P]$ turns the chord and tangent addition into multiplication of ideal classes, and it is injective. So the points form a group, because the class group is one. This section gives the definitions, the addition formulas, this proof, and the Jacobian and projective coordinates.

### Definitions

Let $F$ be a field and $W$ a Weierstrass curve over $F$. Write $W(X, Y) = Y^2 + a_1 XY + a_3 Y - X^3 - a_2 X^2 - a_4 X - a_6$.

**Definition (Affine points).** A pair $(x, y) \in F^2$ satisfies the *equation* of $W$ when $W(x, y) = 0$. It is *nonsingular* when it satisfies the equation and the partial derivatives $W_X(x, y) = a_1 y - 3x^2 - 2a_2 x - a_4$ and $W_Y(x, y) = 2y + a_1 x + a_3$ are not both $0$. The *points* of $W$ are the nonsingular pairs together with one more point $O$, the point at infinity.

If $W$ is elliptic, each solution of the equation is nonsingular, so the points are all solutions and $O$. Over a field, a singular solution forces $\Delta = 0$.

**Definition (Negation).** For $(x, y)$ put $\bar y = -y - a_1 x - a_3$. The *negation* is $-O = O$ and $-(x, y) = (x, \bar y)$.

The two roots of $W(x, Y)$, as a quadratic in $Y$, have sum $-a_1 x - a_3$. So they are $y$ and $\bar y$, and the vertical line $X = x$ meets the curve in $(x, y)$, $(x, \bar y)$ and $O$.

**Definition (Slope and addition).** Let $P_1 = (x_1, y_1)$ and $P_2 = (x_2, y_2)$ be affine points. If $x_1 \neq x_2$, the *slope* is $\ell = (y_1 - y_2)/(x_1 - x_2)$. If $x_1 = x_2$ and $y_1 \neq \bar y_2$, then $P_1 = P_2$ and
$$\ell = \frac{3x_1^2 + 2a_2 x_1 + a_4 - a_1 y_1}{y_1 - \bar y_1} = -\frac{W_X(P_1)}{W_Y(P_1)}.$$
Put
$$x_3 = \ell^2 + a_1 \ell - a_2 - x_1 - x_2, \qquad y_3' = \ell (x_3 - x_1) + y_1.$$
The *sum* is $P_1 + P_2 = (x_3, -y_3' - a_1 x_3 - a_3)$. If $x_1 = x_2$ and $y_1 = \bar y_2$, then $P_1 + P_2 = O$. Last, $O + P = P + O = P$.

The line $Y = \ell(X - x_1) + y_1$ passes through $P_1$ and $P_2$, and the point $P_3^* = (x_3, y_3')$ is the third point on it; the sum is $-P_3^*$.

**Definition (Coordinate ring and the ideal of a point).** The *coordinate ring* of $W$ is $R = F[X, Y]/(W)$. Since $W$ is monic of degree $2$ in $Y$, $R$ is a free $F[X]$-module with basis $1, Y$. For an affine point $P = (x, y)$, its ideal is $I_P = (X - x, Y - y) \subseteq R$.

**Definition (Jacobian and projective coordinates).** In *Jacobian coordinates* a point is a class $[x : y : z]$ with $(x, y, z) \sim (u^2 x, u^3 y, u z)$ for $u \in F^\times$, on the curve
$$Y^2 + a_1 XYZ + a_3 YZ^3 = X^3 + a_2 X^2 Z^2 + a_4 X Z^4 + a_6 Z^6.$$
An affine point $(x, y)$ is $[x : y : 1]$, and $O = [1 : 1 : 0]$. In *projective coordinates* the weights are $1, 1, 1$, the curve is $Y^2 Z + a_1 XYZ + a_3 YZ^2 = X^3 + a_2 X^2 Z + a_4 XZ^2 + a_6 Z^3$, and $O = [0 : 1 : 0]$.

### Theorems and proofs

**Lemma (Negation).** For all $x, y$, $W(x, \bar y) = W(x, y)$. So $-P$ is a point when $P$ is a point, and $-(-P) = P$.

*Proof.* $Y^2 + a_1 XY + a_3 Y = Y(Y + a_1 X + a_3)$, and the substitution $Y \mapsto -Y - a_1 X - a_3$ exchanges the two factors up to the sign $(-1)^2 = 1$. So $W(X, \bar Y) = W(X, Y)$. The map $(x, y) \mapsto (x, \bar y)$ is an involutive affine map that keeps $W$, so it keeps singular points. $\square$

**Theorem (The third point).** Let $P_1, P_2$ be affine points with $P_1 + P_2 \neq O$, let $\ell$ be the slope and $g(X) = W(X, \ell(X - x_1) + y_1)$. Then
$$g(X) = -(X - x_1)(X - x_2)(X - x_3).$$
So $P_3^*$ lies on the curve.

*Proof.* The cubic $g$ has leading term $-X^3$, and its $X^2$-coefficient is $\ell^2 + a_1 \ell - a_2$, from the terms $Y^2$, $a_1 XY$ and $-a_2 X^2$. Also $g(x_1) = W(x_1, y_1) = 0$. If $x_1 \neq x_2$, then $\ell(x_2 - x_1) + y_1 = y_2$, so $g(x_2) = 0$, and $g = -(X - x_1)(X - x_2)(X - c)$ for some $c$. If $x_1 = x_2$, then $g'(x_1) = W_X(P_1) + \ell W_Y(P_1) = 0$ by the choice of $\ell$, so $x_1$ is a double root. In both cases the sum of the roots is the $X^2$-coefficient of $-g$, so $c = \ell^2 + a_1 \ell - a_2 - x_1 - x_2 = x_3$. Then $g(x_3) = 0$ says $W(P_3^*) = 0$. $\square$

**Proposition (The sum is a point).** If $P_1$ and $P_2$ are nonsingular, then so is $P_1 + P_2$.

*Proof.* Assume $P_1 + P_2 \neq O$. By the lemma it is enough that $P_3^*$ is nonsingular. Suppose it is singular. Then $g'(x_3) = W_X(P_3^*) + \ell W_Y(P_3^*) = 0$, so $x_3$ is a multiple root of $g$, and $x_3 = x_1$ or $x_3 = x_2$. If $x_3 = x_1$, then $y_3' = y_1$ and $P_3^* = P_1$, which is nonsingular. If $x_3 = x_2 \neq x_1$, then $y_3' = \ell(x_2 - x_1) + y_1 = y_2$ and $P_3^* = P_2$. Both cases contradict the assumption. $\square$

**Lemma (A point and its negative).** Let $P = (x, y)$ be a nonsingular point. Then $I_P \, I_{-P} = (X - x)$. In particular $I_P$ is invertible.

*Proof.* The product is generated by $(X - x)^2$, $(X - x)(Y - y)$, $(X - x)(Y - \bar y)$ and $(Y - y)(Y - \bar y)$. Since $y + \bar y = -a_1 x - a_3$, in $R$
$$(Y - y)(Y - \bar y) = Y^2 + (a_1 x + a_3) Y + y \bar y = -a_1 (X - x) Y + h(X) + y \bar y,$$
with $h(X) = X^3 + a_2 X^2 + a_4 X + a_6$. Now $h(x) + y \bar y = h(x) - y(y + a_1 x + a_3) = -W(x, y) = 0$, so $h(X) + y\bar y = (X - x) k(X)$ with $k(x) = h'(x)$. So $(Y - y)(Y - \bar y) = (X - x) q$ with $q = -a_1 Y + k(X)$, and $I_P I_{-P} = (X - x) J$ with $J = (X - x, Y - y, Y - \bar y, q)$. If $y \neq \bar y$, then $J$ contains the unit $y - \bar y$. If $y = \bar y$, then $W_Y(P) = y - \bar y = 0$, so $W_X(P) \neq 0$. Modulo $(X - x, Y - y)$, $q \equiv -a_1 y + h'(x) = -W_X(P) \neq 0$, so again $J = R$. $\square$

**Lemma (The line through two points).** Let $P_1, P_2$ be affine points with $P_1 + P_2 \neq O$, and $f = Y - \ell(X - x_1) - y_1$. Then $(X - x_3) \, I_{P_1} I_{P_2} = (f) \, I_{P_1 + P_2}$.

*Proof (distinct case).* Assume $x_1, x_2, x_3$ distinct. Modulo $f$, $Y$ becomes $\ell(X - x_1) + y_1$, so $R/(f) \cong F[X]/(g)$, and by the Chinese remainder theorem this is $F^3$. Each point $Q$ on the line has $Y - y_Q \equiv \ell(X - x_Q)$, so $I_Q/(f) = (X - x_Q)$. The ideals $(X - x_i)$ of $F[X]/(g)$ are its three maximal ideals, with intersection $0$. So $I_{P_1} \cap I_{P_2} \cap I_{P_3^*} = (f)$. Distinct maximal ideals are comaximal, so the intersection equals the product $I_{P_1} I_{P_2} I_{P_3^*}$. Multiply by $I_{-P_3^*} = I_{P_1 + P_2}$ and use the last lemma. $\square$

When two of $x_1, x_2, x_3$ agree, $g$ has a repeated factor, and Mathlib checks the identity by explicit products of generators.

**Lemma (No point ideal is principal).** For an affine point $P$, the ideal $I_P$ is not principal.

*Proof.* The conjugation $Y \mapsto \bar Y = -Y - a_1 X - a_3$ gives the norm $N(p + qY) = (p + qY)(p + q\bar Y) = p^2 - pq(a_1 X + a_3) - q^2 h(X)$ in $F[X]$, for $p, q \in F[X]$. This is the determinant of multiplication by $p + qY$ on the basis $1, Y$. In $N$, the term $p^2$ has even degree $2\deg p$ and $q^2 h$ has odd degree $2 \deg q + 3$. They never cancel, and the middle term has smaller degree than the larger of them. So $\deg N(p + qY) = \max(2 \deg p, 2 \deg q + 3)$, which is never $1$.

Suppose $I_P = (f)$. By the Smith normal form over $F[X]$, $\dim_F R/(f) = \deg N(f)$. But $R/I_P \cong F$, of dimension $1$. This is a contradiction. $\square$

**Theorem (Group law).** The points of $W$ form an abelian group under $+$, with neutral element $O$ and inverse $P \mapsto -P$. The map $P \mapsto [I_P]$, $O \mapsto 1$, into the class group of $R$ is an injective homomorphism.

*Proof.* Write $\kappa(P)$ for the class. First, $\kappa(P_1 + P_2) = \kappa(P_1)\kappa(P_2)$ for all $P_1, P_2$. This is clear when one point is $O$. If $P_1 + P_2 = O$ with both affine, then $P_2 = -P_1$, and the lemma on negatives gives a principal product. Otherwise the lemma on the line gives it, since $(X - x_3)$ and $(f)$ are principal.

Next, $\kappa$ is injective. If $\kappa(P) = 1$, then $P = O$ by the last lemma. If $\kappa(P) = \kappa(Q)$, then $\kappa(P + (-Q)) = 1$, so $P + (-Q) = O$. By the definition of the sum, this forces $P = -(-Q) = Q$.

The identities $O + P = P$, $P + (-P) = O$ and $P_1 + P_2 = P_2 + P_1$ follow from the definitions. For associativity, $\kappa((P + Q) + S) = \kappa(P)\kappa(Q)\kappa(S) = \kappa(P + (Q + S))$, and $\kappa$ is injective. $\square$

The proof needs neither $\Delta \neq 0$ nor the characteristic. It works for the nonsingular points of each Weierstrass curve over a field.

**Proposition (Other coordinates).** The maps $(x, y) \mapsto [x : y : 1]$ and $O \mapsto [1 : 1 : 0]$, or $O \mapsto [0 : 1 : 0]$ in projective coordinates, are bijections onto the nonsingular points of the Jacobian and projective curves. They carry the group law to addition formulas without division.

*Proof.* A point $[x : y : z]$ with $z \neq 0$ equals $[x/z^2 : y/z^3 : 1]$, which lies on the Jacobian curve exactly when $(x/z^2, y/z^3)$ lies on $W$. If $z = 0$, the equation gives $y^2 = x^3$, so $x, y \neq 0$, and $u = y/x$ gives $[x : y : 0] = [u^{-2}x : u^{-3}y : 0] = [1 : 1 : 0]$. The projective case is the same with $[x/z : y/z : 1]$ and $x^3 = 0$ at $z = 0$. At $z = 1$ the partial derivatives in $X$ and $Y$ are the affine ones, and the Euler relation makes the one in $Z$ vanish when they do. At $[1 : 1 : 0]$ the partial derivatives in $X$ and $Y$ are $-3$ and $2$, not both $0$ in any characteristic, and at $[0 : 1 : 0]$ the partial derivative in $Z$ is $1$. $\square$

### Examples

**Example (Points of order 2 on y² = x³ − x).** Here $\bar y = -y$. The points $(0, 0)$, $(1, 0)$ and $(-1, 0)$ have $\bar y = y$, so each equals its negative and has order $2$. They are nonsingular: $W_X = -3x^2 + 1$ is $1$, $-2$, $-2$ at them. Together with $O$ they form a group $(\mathbb{Z}/2)^2$, and their $x$-coordinates are the roots of the $2$-torsion polynomial $4x^3 - 4x$.

**Example (A sum on y² = x³ − x).** Take $P_1 = (0, 0)$ and $P_2 = (1, 0)$. Then $\ell = 0$, $x_3 = 0 - 0 - 1 = -1$, $y_3' = 0$, and $P_1 + P_2 = (-1, 0)$. So the sum of two points of order $2$ is the third.

**Example (A point of order 4).** Over $\mathbb{Q}(i)$, the point $P = (i, 1 - i)$ lies on the curve: $(1 - i)^2 = -2i = i^3 - i$. The tangent slope is $\ell = (3i^2 - 1)/(2(1 - i)) = -2/(1 - i) = -(1 + i)$. Then $x_3 = (1 + i)^2 - 2i = 0$ and $y_3' = -(1 + i)(-i) + 1 - i = 0$, so $2P = (0, 0)$ and $P$ has order $4$.

**Example (The group over F₅).** Over $\mathbb{F}_5$ the curve has $8$ points. For $P = (2, 1)$, $\ell = (3 \cdot 4 - 1)/2 = 11/2 = 3$, $x_3 = 9 - 4 = 0$ and $y_3' = 3(0 - 2) + 1 = 0$. So $2P = (0, 0)$, $P$ has order $4$, and the group is $\mathbb{Z}/2 \times \mathbb{Z}/4$, since it contains $(\mathbb{Z}/2)^2$.

### The library around it

::: mathlib
`WeierstrassCurve.Affine.Point` · `Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point`

`WeierstrassCurve.Affine R` is an abbreviation for `WeierstrassCurve R`, reached by `W.toAffine`. The inductive type has the constructors `zero` and `some x y h` with `h : W.Nonsingular x y`. `Affine.Equation` and `Affine.Nonsingular` are the conditions, and `equation_iff_nonsingular` holds under `[W.IsElliptic]`. The points of a curve `W` over a field are written `W.toAffine.Point`.

<?decl WeierstrassCurve.Affine.Point?>
:::

::: mathlib
`WeierstrassCurve.Affine.addX` · `Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula`

`negY`, `slope`, `addX` and `addY` are the formulas above, and `addPolynomial_slope` is the theorem on the third point. The slope has the junk value $0$ for a vertical line. `nonsingular_add` and `nonsingular_neg` state that sums and negatives are points, and `Point.add_of_X_ne` unfolds the sum.

<?decl WeierstrassCurve.Affine.addX?>
:::

::: mathlib
`WeierstrassCurve.Affine.CoordinateRing.XYIdeal` · `Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point`

`CoordinateRing` is `AdjoinRoot W.polynomial`. `XYIdeal_neg_mul` and `XYIdeal_mul_XYIdeal` are the two ideal lemmas, and `degree_norm_smul_basis` is the degree of the norm.

<?decl WeierstrassCurve.Affine.CoordinateRing.XYIdeal?>
:::

::: mathlib
`WeierstrassCurve.Affine.Point.toClass` · `Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point`

The map is an `AddMonoidHom` into `Additive (ClassGroup W.CoordinateRing)`, built before the group structure exists. `toClass_injective` gives injectivity, and `instAddCommGroup` transports the laws, for each Weierstrass curve over a field.

<?decl WeierstrassCurve.Affine.Point.instAddCommGroup?>
:::

::: mathlib
`WeierstrassCurve.Jacobian.Point` · `Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Point`

`Jacobian.Equation` is stated on `Fin 3 → R` up to scaling, and the formulas `Jacobian.dblXYZ` and `Jacobian.addXYZ` avoid division. `Point.toAffineAddEquiv` is the group isomorphism with the affine points, under `[DecidableEq F]`.

<?decl WeierstrassCurve.Jacobian.Point.toAffineAddEquiv?>
:::

::: mathlib
`WeierstrassCurve.Projective.Point` · `Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point`

The projective version has `Projective.Equation`, the formulas `Projective.addXYZ` and `Projective.dblXYZ`, and `Projective.Point.toAffineAddEquiv`.

<?decl WeierstrassCurve.Projective.Point.toAffineAddEquiv?>
:::

::: mathlib
`WeierstrassCurve.addSubMap` · `Mathlib.AlgebraicGeometry.EllipticCurve.Affine.AddSubMap`

This is the quadratic map $(s : t : u) \mapsto (s^2 - b_4 su - b_6 tu - b_8 u^2 : 2ts + b_2 su + b_4 tu + b_6 u^2 : t^2 - 4su)$ on $\mathbb{P}^2$. `Point.sym2x_add_sub_eq_addSubMap_sym2x` shows that it sends $(x_P x_Q : x_P + x_Q : 1)$ to a multiple of the same vector for $P + Q$ and $P - Q$. The file names a later use: the parallelogram law for heights.

<?decl WeierstrassCurve.addSubMap?>
:::

Common errors of a learner: the group law in Mathlib needs no `IsElliptic`, so the nonsingular points of $y^2 = x^3$ also form a group. A point of `W.toAffine.Point` carries the proof of nonsingularity, so two points with equal coordinates are equal. The point at infinity is $[1 : 1 : 0]$ in Jacobian coordinates and $[0 : 1 : 0]$ in projective coordinates.

### Exercises

1. (A) Find all points of $y^2 = x^3 - x$ over $\mathbb{F}_3$ and the group they form. *Hint:* There are four points.
2. (A) On $y^2 = x^3 - x$ over $\mathbb{Q}(i)$, compute $(0, 0) + (i, 1 - i)$ and check that it is $-P = (i, i - 1)$. *Hint:* The line is tangent at $P$.
3. (B) Show that the nonsingular points of $y^2 = x^3$ over $F$ are the $(t^{-2}, t^{-3})$, $t \in F^\times$, and that $t \mapsto (t^{-2}, t^{-3})$, $0 \mapsto O$ is an isomorphism from $(F, +)$. *Hint:* The line through two points of the parametrization has slope $(t_1^2 + t_1 t_2 + t_2^2)/(t_1 t_2 (t_1 + t_2))$.
4. (B) Show that $R/I_P \cong F$ for an affine point $P$. *Hint:* $F[X, Y]/(X - x, Y - y) \cong F$.
5. (B) Prove that $\deg N(p + qY)$ is $\max(2\deg p, 2\deg q + 3)$ in detail. *Hint:* Compare $\deg p + \deg q + 1$ with both.
6. (C) Prove the lemma on the line in the case $x_3 = x_1 \neq x_2$. *Hint:* Then $R/(f) \cong F[X]/((X - x_1)^2 (X - x_2))$, and $I_{P_1}^2/(f)$ is $((X - x_1)^2)$.
7. (C) Show that a point $(x, y)$ with $y \neq \bar y$ has order $3$ if and only if $\ell^2 + a_1 \ell - a_2 = 3x$. *Hint:* $3P = O$ means $2P = -P$.

### Notes and history

The chord and tangent construction goes back to the study of rational points on cubics, and Mordell (1922) used it to prove that the rational points form a finitely generated group. Silverman, The Arithmetic of Elliptic Curves (1986), proves associativity by the Riemann-Roch theorem through the Picard group of the curve. The class group proof in Mathlib is a form of that argument for the affine coordinate ring; the source cites a paper on it at the conference Interactive Theorem Proving 2023.

The Mathlib Author of `AlgebraicGeometry.EllipticCurve.Affine.Basic`, `Affine.Formula`, `Affine.Point`, the `Jacobian` files and the `Projective` files is David Kurniadi Angdinata. The Mathlib Author of `Affine.AddSubMap` is Michael Stoll.

### Reference

<?reference?>
