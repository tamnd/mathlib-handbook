---
title: Weierstrass equations and changes of variables
kind: theory
modules:
  - Mathlib.AlgebraicGeometry.EllipticCurve.IsomOfJ
  - Mathlib.AlgebraicGeometry.EllipticCurve.LFunction
  - Mathlib.AlgebraicGeometry.EllipticCurve.ModelsWithJ
  - Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
  - Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
  - Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
  - Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
explains:
  E3: [WeierstrassCurve, WeierstrassCurve.Δ, WeierstrassCurve.IsElliptic, WeierstrassCurve.j, WeierstrassCurve.VariableChange, WeierstrassCurve.variableChange_j, WeierstrassCurve.exists_variableChange_isShortNF, WeierstrassCurve.ofJ, WeierstrassCurve.exists_variableChange_of_j_eq, WeierstrassCurve.HasGoodReduction]
  E2: [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈, WeierstrassCurve.c₄, WeierstrassCurve.c₆, WeierstrassCurve.b_relation, WeierstrassCurve.c_relation, WeierstrassCurve.twoTorsionPolynomial_discr, WeierstrassCurve.baseChange, WeierstrassCurve.variableChange_def, WeierstrassCurve.variableChange_b₂, WeierstrassCurve.variableChange_c₄, WeierstrassCurve.variableChange_Δ, WeierstrassCurve.IsShortNF, WeierstrassCurve.j_of_isShortNF, WeierstrassCurve.Δ_of_isShortNF, WeierstrassCurve.IsCharTwoNF, WeierstrassCurve.IsCharThreeNF, WeierstrassCurve.ofJNe0Or1728, WeierstrassCurve.ofJ_j, WeierstrassCurve.IsMinimal, WeierstrassCurve.reduction, WeierstrassCurve.hasGoodReduction_iff_isElliptic_reduction, WeierstrassCurve.hasGoodReduction_or_hasMultiplicativeReduction_or_hasAdditiveReduction, WeierstrassCurve.localPolynomial, WeierstrassCurve.LFunction]
  E1: auto
families: []
requires: [V06.C04, V10.C03, V11.C03, V11.C04, V12.C08]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Weierstrass equations and changes of variables

### Overview

An elliptic curve over a field is a smooth projective curve of genus one with a marked point, and the Riemann-Roch theorem gives it a plane model by a Weierstrass equation. Mathlib starts from the equation. A Weierstrass curve is a list of five coefficients, and an elliptic curve is a Weierstrass curve with an invertible discriminant. This choice works over each commutative ring and turns the statements of this section into polynomial identities.

The section defines $\Delta$ and $j$, shows that changes of variables keep $j$, and treats normal forms, models with a given $j$, the classification by $j$ over a separably closed field, reduction modulo a prime and the $L$-function.

### Definitions

**Definition (Weierstrass curve).** Let $R$ be a commutative ring. A *Weierstrass curve* $W$ over $R$ is a tuple $(a_1, a_2, a_3, a_4, a_6)$ of elements of $R$. It stands for the equation
$$Y^2 + a_1 XY + a_3 Y = X^3 + a_2 X^2 + a_4 X + a_6.$$

**Definition (The quantities b and c).** Put $b_2 = a_1^2 + 4a_2$, $b_4 = 2a_4 + a_1 a_3$, $b_6 = a_3^2 + 4a_6$,
$$b_8 = a_1^2 a_6 + 4 a_2 a_6 - a_1 a_3 a_4 + a_2 a_3^2 - a_4^2,$$
$$c_4 = b_2^2 - 24 b_4, \qquad c_6 = -b_2^3 + 36 b_2 b_4 - 216 b_6.$$

The quantities $b_2, b_4, b_6$ come from completing the square. Multiply the equation by $4$ and put $\eta = 2Y + a_1 X + a_3$. The equation becomes
$$\eta^2 = 4X^3 + b_2 X^2 + 2 b_4 X + b_6. \tag{1}$$
The right side is the *$2$-torsion polynomial* of $W$.

**Definition (Discriminant and j-invariant).** The *discriminant* of $W$ is $\Delta = -b_2^2 b_8 - 8 b_4^3 - 27 b_6^2 + 9 b_2 b_4 b_6$. The curve $W$ is *elliptic* when $\Delta$ is a unit of $R$, and then its *$j$-invariant* is $j = c_4^3 \Delta^{-1}$.

Over a field, $W$ is elliptic if and only if $\Delta \neq 0$, and then the projective curve of $W$ is smooth. The docstring of the class warns that over a general ring the definition is right only when the Picard group of $R$ has no nontrivial $12$-torsion, for instance for fields and principal ideal domains.

**Definition (Change of variables).** A *change of variables* is a tuple $C = (u, r, s, t)$ with $u \in R^\times$ and $r, s, t \in R$. It substitutes
$$X = u^2 X' + r, \qquad Y = u^3 Y' + u^2 s X' + t,$$
and $C \cdot W$ is the curve in the coordinates $(X', Y')$: the substitution sends the equation of $W$ to $u^6$ times the equation of $C \cdot W$. In particular
$$a_1' = u^{-1}(a_1 + 2s), \quad a_2' = u^{-2}(a_2 - s a_1 + 3r - s^2), \quad a_3' = u^{-3}(a_3 + r a_1 + 2t),$$
and $a_4'$, $a_6'$ have similar formulas of weight $4$ and $6$.

Composition makes these substitutions a group with identity $(1, 0, 0, 0)$, and $C \cdot W$ is an action of it. Two curves in one orbit are *isomorphic*.

**Definition (Normal forms).** A curve is in *short normal form* when $a_1 = a_2 = a_3 = 0$, that is $Y^2 = X^3 + a_4 X + a_6$. In characteristic $3$ the normal forms are $Y^2 = X^3 + a_2 X^2 + a_6$ and $Y^2 = X^3 + a_4 X + a_6$. In characteristic $2$ they are $Y^2 + XY = X^3 + a_2 X^2 + a_6$ and $Y^2 + a_3 Y = X^3 + a_4 X + a_6$.

**Definition (Reduction types).** Let $R$ be a discrete valuation ring with fraction field $K$, additive valuation $v$ and residue field $k$. A curve over $K$ is *integral* when it comes from a curve over $R$. An integral model is *minimal* when $v(\Delta)$ is least among the integral models in its orbit. The *reduction* is the curve over $k$ obtained from a minimal model by reducing the coefficients. For a minimal model, the reduction is *good* when $v(\Delta) = 0$, *multiplicative* when $v(\Delta) > 0$ and $v(c_4) = 0$, and *additive* when $v(\Delta) > 0$ and $v(c_4) > 0$.

### Theorems and proofs

**Lemma (Relations).** For each Weierstrass curve, $4 b_8 = b_2 b_6 - b_4^2$ and $1728\,\Delta = c_4^3 - c_6^2$.

*Proof.* Expand $b_2 b_6 = a_1^2 a_3^2 + 4 a_1^2 a_6 + 4 a_2 a_3^2 + 16 a_2 a_6$ and $b_4^2 = 4 a_4^2 + 4 a_1 a_3 a_4 + a_1^2 a_3^2$. The difference is $4 b_8$. Next expand
$$c_4^3 - c_6^2 = 432 b_2^2 b_4^2 - 432 b_2^3 b_6 - 13824 b_4^3 + 15552 b_2 b_4 b_6 - 46656 b_6^2,$$
where the terms $b_2^6$ and $72 b_2^4 b_4$ cancel. By the first relation, $-1728 b_2^2 b_8 = -432 b_2^2 (b_2 b_6 - b_4^2)$ is the sum of the first two terms. The other three terms are $1728(-8 b_4^3 + 9 b_2 b_4 b_6 - 27 b_6^2)$. So the sum is $1728 \Delta$. $\square$

The discriminant of the cubic on the right of (1) is $16 \Delta$, so over a field of characteristic not $2$, $W$ is elliptic if and only if this cubic has distinct roots.

**Theorem (Change of the quantities).** Let $C = (u, r, s, t)$. Then $b_2' = u^{-2}(b_2 + 12 r)$, $b_4' = u^{-4}(b_4 + r b_2 + 6 r^2)$, $b_6' = u^{-6}(b_6 + 2 r b_4 + r^2 b_2 + 4 r^3)$, and
$$c_4' = u^{-4} c_4, \qquad c_6' = u^{-6} c_6, \qquad \Delta' = u^{-12} \Delta.$$
If $W$ is elliptic, then $C \cdot W$ is elliptic with the same $j$-invariant.

*Proof.* Each claim is a polynomial identity with integer coefficients in $a_i, r, s, t, u, u^{-1}$. So it is enough to prove it in the universal ring $A = \mathbb{Z}[a_1, a_2, a_3, a_4, a_6, r, s, t, u, u^{-1}]$, a domain of characteristic $0$, and to map $A$ to $R$.

The substitution gives $\eta = 2u^3 Y' + (a_1 + 2s) u^2 X' + a_1 r + a_3 + 2t = u^3 \eta'$, with $\eta' = 2Y' + a_1' X' + a_3'$. Let $f$ and $f'$ be the right sides of (1) for $W$ and $C \cdot W$. Four times the equation of $W$ is $\eta^2 - f(X)$, and it becomes $u^6(\eta'^2 - f'(X'))$. So $f'(X') = u^{-6} f(u^2 X' + r)$. The coefficients of $X'^2$, $X'$ and $1$ in $f(u^2X' + r)$ are $u^4(b_2 + 12 r)$, $2u^2(b_4 + r b_2 + 6r^2)$ and $b_6 + 2 r b_4 + r^2 b_2 + 4r^3$. This gives $b_2', b_4', b_6'$.

The powers of $u$ in $c_4'$ and $c_6'$ are $u^{-4}$ and $u^{-6}$ by weight, so take $u = 1$. Then $c_4' = (b_2 + 12r)^2 - 24(b_4 + r b_2 + 6 r^2) = c_4$, since the terms $24 r b_2$ and $144 r^2$ cancel. In $-b_2'^3 + 36 b_2' b_4' - 216 b_6'$ the coefficients of $r b_2^2$, $r^2 b_2$, $r b_4$ and $r^3$ are $-36 + 36$, $-432 + 648 - 216$, $432 - 432$ and $-1728 + 2592 - 864$, all $0$. So $c_6' = c_6$. The lemma now gives $1728 \Delta' = u^{-12}(c_4^3 - c_6^2) = 1728 u^{-12} \Delta$, and $A$ has no $\mathbb{Z}$-torsion, so $\Delta' = u^{-12} \Delta$. This is a unit when $\Delta$ is, and $j' = u^{-12} c_4^3 \cdot u^{12} \Delta^{-1} = j$. $\square$

**Theorem (Short normal form).** Let $2$ and $3$ be invertible in $R$. Each Weierstrass curve over $R$ is isomorphic to a curve $Y^2 = X^3 + a_4 X + a_6$. For this curve $c_4 = -48 a_4$, $c_6 = -864 a_6$, $\Delta = -16(4 a_4^3 + 27 a_6^2)$, and over a field $j = 6912\, a_4^3 / (4 a_4^3 + 27 a_6^2)$.

*Proof.* The change $(1, 0, -a_1/2, -a_3/2)$ gives $a_1' = 0$ and $a_3' = a_3 - a_3 = 0$. Then $(1, -a_2'/3, 0, 0)$ keeps $a_1' = a_3' = 0$ and gives $a_2'' = a_2' - a_2' = 0$. For the short form, $b_2 = 0$, $b_4 = 2a_4$, $b_6 = 4a_6$ and $b_8 = -a_4^2$. So $c_4 = -48 a_4$, $c_6 = -864 a_6$ and $\Delta = -64 a_4^3 - 432 a_6^2$. Last, $(-48)^3 / (-16) = 6912$. $\square$

In characteristic $3$ the first step still works, and then $a_2 = b_2$ is fixed by each change of $r$, since $3r = 0$. If $a_2 \neq 0$, the change $r = -a_4/(2a_2)$ removes $a_4$; if $a_2 = 0$, then $j = 0$. In characteristic $2$ with $a_1 \neq 0$, the change $(a_1, a_3/a_1, 0, (a_1^2 a_4 + a_3^2)/a_1^3)$ gives $Y^2 + XY = X^3 + a_2 X^2 + a_6$, with $\Delta = a_6$ and $j = 1/a_6$.

**Proposition (Models with a given j-invariant).** Let $F$ be a field, $j_0 \in F$ and $m = j_0 - 1728$. The curve $W_{j_0}: Y^2 + m XY = X^3 - 36 m^3 X - m^5$ has $c_4 = j_0 m^3$ and $\Delta = j_0^2 m^9$. The curve $Y^2 + Y = X^3$ has $c_4 = 0$ and $\Delta = -27$, and the curve $Y^2 = X^3 + X$ has $c_4 = -48$ and $\Delta = -64$. Each $j_0 \in F$ is the $j$-invariant of an elliptic curve over $F$.

*Proof.* For $W_{j_0}$, $b_2 = m^2$, $b_4 = -72 m^3$, $b_6 = -4m^5$ and $b_8 = -m^7 - 1296 m^6$. So $c_4 = m^4 + 1728 m^3 = j_0 m^3$, and
$$\Delta = m^{11} + 1296 m^{10} + 8 \cdot 72^3 m^9 - 432 m^{10} + 2592 m^{10} = m^9 (m^2 + 3456 m + 1728^2) = j_0^2 m^9,$$
since $8 \cdot 72^3 = 2985984 = 1728^2$. For $Y^2 + Y = X^3$ only $b_6 = 1$ is nonzero, and for $Y^2 = X^3 + X$, $b_4 = 2$ and $b_8 = -1$; the values follow. If $j_0 \neq 0, 1728$, then $W_{j_0}$ is elliptic and $j = j_0^3 m^9 / (j_0^2 m^9) = j_0$. If $j_0 = 1728 \neq 0$, then $2 \neq 0$, and $Y^2 = X^3 + X$ has $j = 110592/64 = 1728$. If $j_0 = 0$ and $3 \neq 0$, take $Y^2 + Y = X^3$. If $j_0 = 0$ and $3 = 0$, then $-64 = -1 \neq 0$, and $Y^2 = X^3 + X$ has $j = 1728 = 0$. $\square$

**Theorem (The j-invariant classifies).** Let $F$ be a separably closed field and $E$, $E'$ elliptic curves over $F$ with $j(E) = j(E')$. Then some change of variables sends $E$ to $E'$.

*Proof (characteristic not 2 or 3).* Assume $E: Y^2 = X^3 + A X + B$ and $E': Y^2 = X^3 + A' X + B'$. The change $(u, 0, 0, 0)$ sends $(A, B)$ to $(u^{-4} A, u^{-6} B)$. By the formula for $j$ and $\Delta \neq 0$, $j = 0$ if and only if $A = 0$, and $j = 1728$ if and only if $B = 0$. If $A = A' = 0$, take a root $u$ of $Z^6 - B/B'$; it is separable, since its derivative $6Z^5$ has only the root $0$. If $B = B' = 0$, take a root of $Z^4 - A/A'$. Otherwise $j = j'$ gives $B^2/A^3 = B'^2/A'^3$. Take $u$ with $u^2 = BA'/(B'A)$. Then $u^4 = (B^2/B'^2)(A'^2/A^2) = A/A'$ and $u^6 = u^4 u^2 = B/B'$. $\square$

In characteristics $2$ and $3$ Mathlib uses the normal forms of those characteristics and solves $u^2 = c$ or $u^3 = c$ with $c \neq 0$, and equations $Z^q + bZ + c = 0$ with $q$ a power of the characteristic and $b \neq 0$. All are separable, so a separably closed field is enough.

**Proposition (The three reduction types).** A minimal model $W$ over a discrete valuation ring has exactly one of good, multiplicative and additive reduction. It has good reduction if and only if its reduction is elliptic.

*Proof.* The coefficients lie in $R$, so $v(\Delta) \ge 0$ and $v(c_4) \ge 0$, and the three cases $v(\Delta) = 0$; $v(\Delta) > 0, v(c_4) = 0$; $v(\Delta) > 0, v(c_4) > 0$ cover all models and exclude each other. The discriminant of the reduction is the image $\bar\Delta$ of $\Delta$ in $k$, and an element of $R$ is a unit if and only if its image in $k$ is nonzero. $\square$

### Examples

**Example (The curve y² = x³ − x).** Here $a_4 = -1$, so $b_2 = 0$, $b_4 = -2$, $b_6 = 0$ and $b_8 = -1$. Then $4b_8 = -4 = -b_4^2$, $c_4 = 48$, $c_6 = 0$ and $\Delta = -8(-8) = 64$. Check: $48^3 = 110592 = 1728 \cdot 64$. The curve is elliptic over each ring in which $2$ is a unit, and $j = 48^3/64 = 1728$.

**Example (Reduction and local factors).** Over $\mathbb{Z}_{(p)}$ the curve $y^2 = x^3 - x$ has $\Delta = 2^6$, so it has good reduction at odd $p$. At $p = 2$ it is minimal, since another integral model has $v(\Delta') = 6 - 12 v(u) \ge 0$, so $v(u) \le 0$ and $v(\Delta') \ge 6$. As $v_2(48) = 4 > 0$, the reduction at $2$ is additive. Over $\mathbb{F}_5$ the points are $(0,0)$, $(1,0)$, $(4,0)$, $(2, \pm 1)$, $(3, \pm 2)$ and the point at infinity, since $2^3 - 2 = 1$ and $3^3 - 3 = 4$ in $\mathbb{F}_5$. So $a_5 = 5 + 1 - 8 = -2$ and the local polynomial is $1 + 2T + 5T^2$.

### The library around it

::: mathlib
`WeierstrassCurve` · `Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass`

The structure has the fields `a₁ a₂ a₃ a₄ a₆` and needs no ring structure on `R`. The quantities are `b₂`, `b₄`, `b₆`, `b₈`, `c₄`, `c₆` and `Δ`, with `b_relation` and `c_relation`; the sign of `Δ` follows the LMFDB. `twoTorsionPolynomial_discr` gives the discriminant `16 * Δ` of the cubic in (1). Base change is `baseChange`, written `W⁄A`.

<?decl WeierstrassCurve?>
:::

::: mathlib
`WeierstrassCurve.IsElliptic` · `Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass`

The class has the field `isUnit : IsUnit W.Δ`, and `j` is `Δ'⁻¹ * c₄ ^ 3` with `Δ'` the unit. There is no separate type of elliptic curves: a theorem takes `W : WeierstrassCurve R` and `[W.IsElliptic]`.

<?decl WeierstrassCurve.IsElliptic?>
:::

::: mathlib
`WeierstrassCurve.VariableChange` · `Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange`

The fields are `u : Rˣ` and `r s t : R`. A `Group` instance and a `MulAction` on curves give `C • W`, and `variableChange_def` lists the five coefficients. The lemmas `variableChange_b₂`, `variableChange_c₄` and `variableChange_Δ` state the theorem, and `variableChange_j` is the simp lemma `(C • W).j = W.j`.

<?decl WeierstrassCurve.variableChange_j?>
:::

::: mathlib
`WeierstrassCurve.exists_variableChange_isShortNF` · `Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms`

`IsShortNF` asks `a₁ = a₂ = a₃ = 0`, and the theorem needs `[Invertible (2 : R)]` and `[Invertible (3 : R)]`. The lemmas `Δ_of_isShortNF` and `j_of_isShortNF` give the formulas. The classes `IsCharThreeNF` and `IsCharTwoNF` collect the other normal forms.

<?decl WeierstrassCurve.exists_variableChange_isShortNF?>
:::

::: mathlib
`WeierstrassCurve.ofJ` · `Mathlib.AlgebraicGeometry.EllipticCurve.ModelsWithJ`

`ofJ j` chooses among `ofJ0`, `ofJ1728` and `ofJNe0Or1728 j` as in the proof, and `ofJ_j` states `(ofJ j).j = j`.

<?decl WeierstrassCurve.ofJ?>
:::

::: mathlib
`WeierstrassCurve.exists_variableChange_of_j_eq` · `Mathlib.AlgebraicGeometry.EllipticCurve.IsomOfJ`

The hypotheses are `[IsSepClosed F]`, `[E.IsElliptic]`, `[E'.IsElliptic]` and `E.j = E'.j`, and the conclusion is `∃ C, C • E = E'`.

<?decl WeierstrassCurve.exists_variableChange_of_j_eq?>
:::

::: mathlib
`WeierstrassCurve.HasGoodReduction` · `Mathlib.AlgebraicGeometry.EllipticCurve.Reduction`

`IsMinimal` asks that the multiplicative valuation of `Δ` is greatest among integral models, which is the least additive valuation. `reduction` maps the minimal model to the residue field. The proposition is `hasGoodReduction_iff_isElliptic_reduction` with `hasGoodReduction_or_hasMultiplicativeReduction_or_hasAdditiveReduction`.

<?decl WeierstrassCurve.HasGoodReduction?>
:::

::: mathlib
`WeierstrassCurve.LFunction` · `Mathlib.AlgebraicGeometry.EllipticCurve.LFunction`

`localPolynomial` is $1 - aT + qT^2$ with $a = q + 1 - \# W(k)$ for good reduction, $1 - T$ and $1 + T$ for split and nonsplit multiplicative reduction, and $1$ for additive reduction. Here $q$ is `Nat.card` of the residue field, with value $0$ for an infinite field. `LFunction` is the Euler product over the finite places of a number field, as an `ArithmeticFunction ℤ`. The index of this edition has no declaration for the analytic continuation of this $L$-series.

<?decl WeierstrassCurve.LFunction?>
:::

Common errors of a learner: `IsElliptic` asks for a unit discriminant, which over $\mathbb{Z}$ means $\Delta = \pm 1$; no elliptic curve over $\mathbb{Z}$ has that, so base change $y^2 = x^3 - x$ to $\mathbb{Q}$ first. The factor in `variableChange_Δ` is $u^{-12}$, because the action expresses old coordinates by new ones. The theorem on $j$ needs a separably closed field: over $\mathbb{Q}$ the curves $y^2 = x^3 - x$ and $y^2 = x^3 - 4x$ both have $j = 1728$ but are not isomorphic.

### Exercises

1. (A) Compute $b_2, b_4, b_6, b_8, c_4, \Delta$ and $j$ for $y^2 + y = x^3 - x$. *Hint:* $a_3 = 1$, $a_4 = -1$; the result is $\Delta = 37$.
2. (A) Check the formula for $a_2'$ by substitution of $X = X' + r$, $Y = Y' + sX' + t$. *Hint:* Collect the coefficient of $X'^2$.
3. (B) Show that $(u, 0, 0, 0)$ sends $a_i$ to $u^{-i} a_i$, and use it to send $y^2 = x^3 - 4x$ to $y^2 = x^3 - x$ over $\mathbb{Q}(\sqrt{2})$. *Hint:* Find $u$ with $u^4 = 4$.
4. (B) Show that $y^2 = x^3 - x$ and $y^2 = x^3 - 4x$ are not isomorphic over $\mathbb{Q}$. *Hint:* A change between short forms over $\mathbb{Q}$ has $r = s = t = 0$.
5. (B) Find a short normal form of $y^2 + xy = x^3 + 1$ over $\mathbb{Q}$ and compute $j$. *Hint:* Apply $s = -1/2$, then remove $a_2$.
6. (C) Show that an integral model over a discrete valuation ring with $v(\Delta) < 12$ is minimal, and give an integral model of $y^2 = x^3 - p^4 x$ over $\mathbb{Z}_{(p)}$ that is not minimal. *Hint:* Use $\Delta' = u^{-12} \Delta$ and $u = p$.
7. (C) In characteristic $2$, show that $j = a_1^{12}/\Delta$, so that $j = 0$ if and only if $a_1 = 0$. *Hint:* There $b_2 = a_1^2$ and $c_4 = b_2^2$.

### Notes and history

The equations take their name from Weierstrass. The quantities $b_i$, $c_i$ and $\Delta$ follow Tate, and the standard text with these conventions is Silverman, The Arithmetic of Elliptic Curves (1986), Chapter III and Appendix A; the normal forms in Mathlib follow Silverman, Proposition A.1.1. Mordell proved in 1922 that the rational points of an elliptic curve over $\mathbb{Q}$ form a finitely generated group. Buzzard started the elliptic curve library of Mathlib.

The Mathlib Authors of `AlgebraicGeometry.EllipticCurve.Weierstrass` and `ModelsWithJ` are Kevin Buzzard and David Kurniadi Angdinata, and those of `VariableChange` are Kevin Buzzard, David Kurniadi Angdinata and Jz Pan. The Mathlib Author of `NormalForms` and `IsomOfJ` is Jz Pan, of `Reduction` Bryan Wang, and of `LFunction` Thomas Browning.

### Reference

<?reference?>
