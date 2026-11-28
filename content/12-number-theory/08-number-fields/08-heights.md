---
title: Heights
kind: api
modules:
  - Mathlib.NumberTheory.Height.Basic
  - Mathlib.NumberTheory.Height.MvPolynomial
  - Mathlib.NumberTheory.Height.Northcott
  - Mathlib.NumberTheory.Height.NumberField
  - Mathlib.NumberTheory.Height.Projectivization
  - Mathlib.NumberTheory.Height.EllipticCurve
  - Mathlib.NumberTheory.MahlerMeasure
explains:
  E2: [Height.AdmissibleAbsValues, Height.mulHeight₁, Height.mulHeight, Height.mulHeight_smul_eq_mulHeight, Height.mulHeight_eval_le, Rat.mulHeight₁_eq_max, NumberField.finite_setOfPred_mulHeight₁_le, WeierstrassCurve.Affine.approx_parallelogram_law, WeierstrassCurve.Affine.finite_torsion, Polynomial.finite_mahlerMeasure_le]
  E1: auto
families: []
requires: [V11, V28]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Heights

### Overview

A height measures the arithmetic size of an algebraic object. The height of a rational number $a/b$ in lowest terms is $\max(\lvert a \rvert, \lvert b \rvert)$. There are only finitely many rational numbers of height at most $B$, and the height of a product or a sum is bounded by the heights of the factors. Weil extended this to number fields with the product formula: the height of $x$ is the product of $\max(\lvert x \rvert_v, 1)$ over all places $v$. Heights are the main tool of Diophantine geometry. The proof of the Mordell-Weil theorem for elliptic curves uses a height $h$ on the points and the approximate parallelogram law $h(P + Q) + h(P - Q) = 2h(P) + 2h(Q) + O(1)$.

The library defines heights for any field with a family of absolute values that satisfies a product formula. This setting covers the number fields of this chapter and, later, function fields. The modules `Mathlib.NumberTheory.Height.Basic`, `Mathlib.NumberTheory.Height.MvPolynomial` and `Mathlib.NumberTheory.Height.Projectivization` give the general theory. The module `Mathlib.NumberTheory.Height.NumberField` gives the instance for number fields and the Northcott property, and `Mathlib.NumberTheory.Height.Northcott` moves it to the logarithmic height. The module `Mathlib.NumberTheory.Height.EllipticCurve` applies heights to Weierstrass curves of Volume 28, and `Mathlib.NumberTheory.MahlerMeasure` proves the Northcott theorem for the Mahler measure of integer polynomials. The places and the product formula of a number field are in Section 6.

### The library around it

#### Admissible families of absolute values

**Definition.** For a field $K$, the class `Height.AdmissibleAbsValues K` gives

1. a multiset `Height.AdmissibleAbsValues.archAbsVal` of real absolute values on $K$, the archimedean ones, counted with multiplicity;
2. a set `Height.AdmissibleAbsValues.nonarchAbsVal` of absolute values that are nonarchimedean, by `Height.AdmissibleAbsValues.isNonarchimedean`;
3. for each $x \neq 0$, only finitely many nonarchimedean $v$ with $\lvert x \rvert_v \neq 1$, which is `Height.AdmissibleAbsValues.hasFiniteMulSupport`;
4. the product formula $\prod_{v\ \text{arch}}\lvert x \rvert_v \cdot \prod_{v\ \text{nonarch}}\lvert x \rvert_v = 1$ for $x \neq 0$, which is `Height.AdmissibleAbsValues.product_formula`.

The number of archimedean absolute values, with multiplicity, is `Height.totalWeight K`. For a number field $K$ the instance is `NumberField.instAdmissibleAbsValues`. The archimedean part is the multiset of infinite places, where a complex place counts twice, and the nonarchimedean part is the set of finite places of Section 6. So `NumberField.totalWeight_eq_finrank` says that the total weight is $[K : \mathbb{Q}]$.

#### Heights of elements and of tuples

For $x \in K$, the multiplicative height is
$$H(x) = \prod_{v\ \text{arch}}\max(\lvert x \rvert_v, 1) \cdot \prod_{v\ \text{nonarch}}\max(\lvert x \rvert_v, 1),$$
`Height.mulHeight₁ x`, and the logarithmic height `Height.logHeight₁ x` is $h(x) = \log H(x)$. The subscript $1$ marks the affine case of one element. For a tuple $x : \iota \to K$ with $\iota$ finite, the height `Height.mulHeight x` uses $\max_i \lvert x_i \rvert_v$ in place of $\max(\lvert x \rvert_v, 1)$, and it is $1$ for $x = 0$ by convention. The logarithmic version is `Height.logHeight x`. The version for a function with finite support, `Finsupp.logHeight`, restricts to the support.

| Lean name | Statement |
|---|---|
| `Height.one_le_mulHeight₁`, `Height.one_le_mulHeight` | $H \geq 1$, so $h \geq 0$ |
| `Height.mulHeight₁_eq_mulHeight` | $H(x) = H(x, 1)$ |
| `Height.mulHeight₁_div_eq_mulHeight` | $H(x/y) = H(x, y)$ |
| `Height.mulHeight_smul_eq_mulHeight` | $H(cx) = H(x)$ for $c \neq 0$ |
| `Height.mulHeight₁_inv` | $H(x^{-1}) = H(x)$ |
| `Height.mulHeight₁_pow`, `Height.mulHeight₁_zpow` | $H(x^n) = H(x)^{\lvert n \rvert}$ |
| `Height.mulHeight₁_mul_le` | $H(xy) \leq H(x)H(y)$ |
| `Height.mulHeight₁_add_le` | $H(x + y) \leq 2^{w}H(x)H(y)$, $w$ the total weight |
| `Height.mulHeight_comp_le` | forgetting or repeating coordinates does not increase $H$ |

*Proof of the scaling invariance.* For each $v$, $\max_i\lvert cx_i \rvert_v = \lvert c \rvert_v\max_i\lvert x_i \rvert_v$. The product over all $v$ of the factors $\lvert c \rvert_v$ is $1$ by the product formula. $\square$

So `Height.mulHeight` is a function on projective space. The module `Mathlib.NumberTheory.Height.Projectivization` makes this explicit: `Projectivization.mulHeight` is the height on `Projectivization K (ι → K)`, with `Projectivization.mulHeight_mk` for the value at the class of $x$, and `Projectivization.logHeight` is the logarithmic form. The logarithmic forms of the table have the same names with the word logHeight in place of mulHeight, for example `Height.logHeight₁_mul_le` and `Height.logHeight₁_add_le`.

#### Heights and polynomial maps

The module `Mathlib.NumberTheory.Height.MvPolynomial` bounds the height of the image of a point under polynomial maps. Let $p = (p_j)$ be a family of homogeneous polynomials of degree $N$ in the variables $x_i$. Then
$$H(p(x)) \leq C_p\,H(x)^N,$$
with an explicit constant `Height.mulHeightBound p` built from the coefficients. This is `Height.mulHeight_eval_le`, with the logarithmic form `Height.logHeight_eval_le`. A lower bound $H(p(x)) \geq c\,H(x)^N$ holds when the $p_j$ have no common zero other than $0$, in the form of a Nullstellensatz certificate: if $x_i^{M+N}$ is a combination of the $p_j$ with homogeneous coefficients of degree $M$, then `Height.mulHeight_eval_ge` applies. The linear case is `Height.mulHeight_linearMap_apply_le`. For products of binary forms, `Height.mulHeight_mul_mulHeight` gives $H(a, b)H(c, d) = H(ac, ad, bc, bd)$, and `Height.mulHeight_sym2_le` and `Height.mulHeight_sym2_ge` compare $H(ac, ad + bc, bd)$ with $H(a, b)H(c, d)$ up to constants.

#### Number fields and the Northcott property

For $K = \mathbb{Q}$ the height is the classical one: `Rat.mulHeight₁_eq_max` says $H(a/b) = \max(\lvert a \rvert, b)$ for $a/b$ in lowest terms, and `Rat.mulHeight_eq_max_abs_of_gcd_eq_one` says $H(x) = \max_i\lvert x_i \rvert$ for a tuple of coprime integers. For a number field $K$, `NumberField.mulHeight₁_eq` writes $H(x)$ with the infinite places and their multiplicities and the finite places, and `NumberField.natDenominator_le_mulHeight₁` bounds the denominator of $x$ by $H(x)$.

**Theorem (Northcott).** Let $K$ be a number field and $B \in \mathbb{R}$. Then $\{x \in K \mid H(x) \leq B\}$ is finite.

*Proof.* Let $H(x) \leq B$. The denominator $n$ of $x$ is at most $B$, and $nx$ is an algebraic integer. Each conjugate of $nx$ has absolute value at most $nB$. So the characteristic polynomial of $nx$ has integer coefficients bounded in terms of $B$ and $[K : \mathbb{Q}]$, and there are only finitely many such polynomials and roots. $\square$

This is `NumberField.finite_setOfPred_mulHeight₁_le`, with `NumberField.finite_setOfPred_logHeight₁_le` for $h$. The class `Northcott` of the order library says, for a function $f$, that each set $\{x \mid f(x) \leq B\}$ is finite. The instance for $H$ on a number field is `NumberField.instNorthcottRealMulHeight₁`, and the module `Mathlib.NumberTheory.Height.Northcott` gives the instance for $h$ from it.

#### Elliptic curves

Let $W$ be a Weierstrass curve over a field $F$ with admissible absolute values. The naive height `WeierstrassCurve.Affine.Point.naiveHeight P` of a point is $h(x(P))$, the logarithmic height of the $x$-coordinate, and $0$ at the point at infinity, by `WeierstrassCurve.Affine.Point.naiveHeight_eq_logHeight₁`.

**Theorem.** Let $W$ be elliptic. There is a constant $C$ such that for all points $P$ and $Q$,
$$\lvert h(P + Q) + h(P - Q) - 2h(P) - 2h(Q) \rvert \leq C.$$

This is `WeierstrassCurve.Affine.approx_parallelogram_law`. The proof expresses the pair $\{x(P + Q), x(P - Q)\}$ through the symmetric functions $x(P + Q) + x(P - Q)$ and $x(P + Q)x(P - Q)$, which are quotients of binary forms in $x(P)$ and $x(Q)$. The bounds of `Mathlib.NumberTheory.Height.MvPolynomial` then apply. If $F$ has the Northcott property for $h$, the sets of points of bounded naive height are finite, `WeierstrassCurve.Affine.finite_naiveHeight_le`, and the torsion subgroup is finite, `WeierstrassCurve.Affine.finite_torsion`. The second fact uses $h(2P) = 4h(P) + O(1)$: a torsion point has only finitely many multiples, so their heights are bounded.

#### Mahler measure

The Mahler measure $M(p)$ of a complex polynomial, `Polynomial.mahlerMeasure`, is $\lvert a \rvert\prod_i\max(1, \lvert \alpha_i \rvert)$ for $p = a\prod_i(X - \alpha_i)$. For a polynomial $p$ with integer coefficients, the module `Mathlib.NumberTheory.MahlerMeasure` proves:

1. `Polynomial.one_le_mahlerMeasure_of_ne_zero`: $M(p) \geq 1$ for $p \neq 0$.
2. `Polynomial.finite_mahlerMeasure_le`: for each $n$ and $B$ there are only finitely many $p$ of degree at most $n$ with $M(p) \leq B$, and `Polynomial.card_mahlerMeasure_le_prod` bounds their number.
3. `Polynomial.cyclotomic_mahlerMeasure_eq_one`: cyclotomic polynomials have $M = 1$.
4. `Polynomial.pow_eq_one_of_mahlerMeasure_eq_one`: if $M(p) = 1$, each nonzero complex root of $p$ is a root of unity. This is Kronecker's theorem.
5. `Polynomial.cyclotomic_dvd_of_mahlerMeasure_eq_one`: if $M(p) = 1$, $X \nmid p$ and $p$ is not constant, a cyclotomic polynomial divides $p$.

The finiteness in item 2 comes from the bound $\lvert a_k \rvert \leq \binom{n}{k}M(p)$ on the coefficients, so the coefficients lie in a box, `Polynomial.boxPoly`. Item 4 follows: the powers $\alpha^m$ of a root are roots of polynomials of the same degree with $M = 1$, so they take only finitely many values.

#### Common errors

1. `Height.mulHeight₁ x` is the height of $x$ as an element, and `Height.mulHeight x` is the height of a tuple as a point of projective space. The two agree through `Height.mulHeight₁_eq_mulHeight` with the tuple $(x, 1)$, not with the tuple $(x)$, whose height is $1$.
2. The heights are absolute only after a normalization. With the instance on a number field $K$, $H(x)$ is the relative height, of size $H_{\mathbb{Q}}(x)^{[K : \mathbb{Q}]}$ for $x \in \mathbb{Q}$. The absolute versions are `NumberField.absMulHeight₁` and `NumberField.absLogHeight₁`.
3. `Height.mulHeight₁_add_le` has the factor $2^{w}$ with the total weight $w$. A bound $H(x + y) \leq H(x)H(y)$ without the factor is false: $H(1 + 1) = 2$ in $\mathbb{Q}$.

### Exercises

1. (A) Compute $H(3/4)$, $H(-6/4)$ and $H(3/4, 5/6)$ in $\mathbb{Q}$, and check `Height.mulHeight₁_div_eq_mulHeight` on $3/4 = 3/4$.
2. (A) Show that the number of rational numbers of height at most $B$ is at most $(2B + 1)^2$.
3. (B) Prove `Height.mulHeight₁_inv` from the product formula.
4. (B) Show that $H(x) = 1$ for a root of unity $x$ in a number field, and use `NumberField.finite_setOfPred_mulHeight₁_le` to show that the roots of unity of $K$ form a finite set.
5. (C) Let $x \in K^\times$ with $H(x) = 1$ in a number field $K$. Show that $x$ is a root of unity, with the Northcott property applied to the powers of $x$.

### Reference

<?reference?>
