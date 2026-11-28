---
title: Weierstrass preparation and restricted power series
kind: api
modules:
  - Mathlib.RingTheory.PowerSeries.WeierstrassPreparation
  - Mathlib.RingTheory.Polynomial.Eisenstein.Distinguished
  - Mathlib.RingTheory.MvPowerSeries.Restricted
  - Mathlib.RingTheory.PowerSeries.Restricted
explains:
  E2: [PowerSeries.IsWeierstrassDivisionAt, PowerSeries.exists_isWeierstrassDivision, PowerSeries.weierstrassMod, PowerSeries.IsWeierstrassFactorizationAt, PowerSeries.exists_isWeierstrassFactorization, PowerSeries.weierstrassDistinguished, Polynomial.IsDistinguishedAt, MvPowerSeries.IsRestricted, MvPowerSeries.Restricted, PowerSeries.isRestricted_iff]
  E1: auto
families: []
requires: [V06.C05, V09.C02, V09.C05, V09.C06]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Weierstrass preparation and restricted power series

### Overview

Let $A$ be a complete local ring with maximal ideal $\mathfrak m$, for example $\mathbb{Z}_p$ or $k[[T]]$. A power series $g \in A[[X]]$ whose reduction modulo $\mathfrak m$ is not zero has a first coefficient that is a unit, at some index $n$. The Weierstrass division theorem says that every $f \in A[[X]]$ can be divided by such a $g$ with a polynomial remainder of degree less than $n$:
$$f = g q + r, \qquad r \in A[X],\ \deg r < n,$$
and that $q$ and $r$ are unique. The Weierstrass preparation theorem follows: $g = f_0 h$, where $h$ is a unit of $A[[X]]$ and $f_0$ is a distinguished polynomial of degree $n$, a monic polynomial whose lower coefficients lie in $\mathfrak m$. So, up to a unit, a power series is a polynomial. For $A = \mathbb{Z}_p$ these theorems are the base of the Iwasawa theory of $\mathbb{Z}_p[[T]]$, and for $A = k[[T]]$ they are the algebraic form of the Weierstrass theorems on analytic functions in two variables.

The second part of this section treats restricted power series over a normed ring $R$. A series $\sum a_n X^n$ is restricted for a radius $c$ when $\|a_n\| c^n \to 0$. Over a complete non-archimedean field these series converge on the closed disc of radius $c$, and for $c = 1$ they form the Tate algebra of rigid analytic geometry. The library defines the predicate in one and in several variables and, over an ultrametric ring, the ring of restricted series. This section is a guide to these four modules.

### The library around it

**Distinguished polynomials.** The module `Mathlib.RingTheory.Polynomial.Eisenstein.Distinguished` defines `Polynomial.IsDistinguishedAt f I`: the polynomial $f$ is monic, `Polynomial.IsDistinguishedAt.monic`, and its coefficients below the leading one lie in $I$. It extends `Polynomial.IsWeaklyEisensteinAt` of Chapter 5, `Polynomial.IsDistinguishedAt.toIsWeaklyEisensteinAt`. Modulo $I$ a distinguished polynomial of degree $n$ is $X^n$, `Polynomial.IsDistinguishedAt.map_eq_X_pow`, and a product of distinguished polynomials is distinguished, `Polynomial.IsDistinguishedAt.mul`. If $f = g h$ with $g$ distinguished and $h(0) \notin I$, then the degree of $g$ is the order of $f$ modulo $I$, `Polynomial.IsDistinguishedAt.coe_natDegree_eq_order_map`.

**Weierstrass division.** The module `Mathlib.RingTheory.PowerSeries.WeierstrassPreparation` works with an ideal $I$ of $A$ first, and then with the maximal ideal of a local ring. Let $n$ be the order of $g$ modulo $I$. The predicate `PowerSeries.IsWeierstrassDivisorAt g I` says that the coefficient of $X^n$ in $g$ is a unit. The predicate `PowerSeries.IsWeierstrassDivisionAt f g q r I` says that $f = g q + r$ with $\deg r < n$. For a divisor $g$ and an $I$-adically complete ring $A$, the quotient and the remainder are `PowerSeries.IsWeierstrassDivisorAt.div` and `PowerSeries.IsWeierstrassDivisorAt.mod`, and they satisfy the predicate, `PowerSeries.IsWeierstrassDivisorAt.isWeierstrassDivisionAt_div_mod`. The construction is a limit: the module builds a sequence of approximations, `PowerSeries.IsWeierstrassDivisorAt.seq`, whose differences have coefficients in higher and higher powers of $I$. A distinguished polynomial is a divisor, `Polynomial.IsDistinguishedAt.isWeierstrassDivisorAt`.

For a local ring the versions without the suffix At use the maximal ideal. If the reduction of $g$ to the residue field is nonzero, then $g$ is a divisor, `PowerSeries.IsWeierstrassDivisor.of_map_ne_zero`. In a complete local ring every $f$ has a division by $g$, `PowerSeries.exists_isWeierstrassDivision`, and it is unique, `PowerSeries.IsWeierstrassDivision.unique`. The library gives the quotient and the remainder names, `PowerSeries.weierstrassDiv` and `PowerSeries.weierstrassMod`, with the notations $f /ʷ g$ and $f \%ʷ g$. The degree bound is `PowerSeries.degree_weierstrassMod_lt`, and both operations are additive in $f$, `PowerSeries.add_weierstrassDiv` and `PowerSeries.add_weierstrassMod`.

**Weierstrass preparation.** The predicate `PowerSeries.IsWeierstrassFactorizationAt g f h I` says that $g = f h$, where $f$ is a distinguished polynomial at $I$ and $h$ is a unit. In a complete local ring every $g$ with nonzero reduction has such a factorization, `PowerSeries.exists_isWeierstrassFactorization`, and the factorization is unique, `PowerSeries.IsWeierstrassFactorization.unique`. The two factors have names, `PowerSeries.weierstrassDistinguished` and `PowerSeries.weierstrassUnit`, with `PowerSeries.isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit`, `PowerSeries.isDistinguishedAt_weierstrassDistinguished` and `PowerSeries.isUnit_weierstrassUnit`. The degree of the distinguished factor is the order of $g$ in the residue field, `PowerSeries.IsWeierstrassFactorization.natDegree_eq_toNat_order_map`. The factors behave well under products, `PowerSeries.weierstrassDistinguished_mul` and `PowerSeries.weierstrassUnit_mul`. A consequence is the comparison of quotients: for a distinguished polynomial $g$ over an $I$-adically complete ring,
$$A[X] / (g) \cong A[[X]] / (g),$$
which is `Polynomial.IsDistinguishedAt.algEquivQuotient`. The version for the distinguished factor of a series is `PowerSeries.algEquivQuotientWeierstrassDistinguished`. So $A[[X]]/(g)$ is a free $A$-module of rank $n$. The factorization also respects scalars: multiplication of $g$ by a unit $a$ of $A$ multiplies the unit factor by $a$ and keeps the distinguished factor, `PowerSeries.IsWeierstrassFactorizationAt.smul` and `PowerSeries.weierstrassDistinguished_smul`. In the proofs of later volumes, these lemmas reduce a question about an ideal of $A[[X]]$ to a question about a monic polynomial, where the theory of Chapter 5 applies.

**Restricted power series.** The module `Mathlib.RingTheory.PowerSeries.Restricted` works over a normed ring $R$ and a real number $c$. The predicate `PowerSeries.IsRestricted c f` asks that $\|a_n\| c^n \to 0$ along the cofinite filter, `PowerSeries.isRestricted_iff`. Polynomials are restricted, and sums and negatives of restricted series are restricted, so the restricted series form an additive subgroup, `PowerSeries.IsRestricted.addSubgroup`. Over an ultrametric ring, `IsUltrametricDist R`, products are restricted too, and the restricted series form a subring, `PowerSeries.IsRestricted.subring`. The predicate depends on $c$ only through $|c|$, `PowerSeries.isRestricted_abs_iff`. The rules for sums, negatives and products in one variable are the cases of the rules in several variables below, such as `MvPowerSeries.IsRestricted.add`, `MvPowerSeries.IsRestricted.neg` and `MvPowerSeries.IsRestricted.mul`, because a power series in one variable is a power series in the variables indexed by the type with one element.

The module `Mathlib.RingTheory.MvPowerSeries.Restricted` has the same theory in several variables, with a radius $c_s$ for each variable $s$. The predicate `MvPowerSeries.IsRestricted c f` asks that $\|a_t\| \prod_s c_s^{t_s} \to 0$ along the cofinite filter on the exponents $t$. Over an ultrametric ring the product rule `MvPowerSeries.IsRestricted.mul` uses `MvPowerSeries.tendsto_antidiagonal`, a statement on Cauchy products of sequences that tend to $0$. The type `MvPowerSeries.Restricted R c` is the subring of restricted series. It is a ring and an $R$-module, and a commutative $R$-algebra when $R$ is commutative, with the elements `MvPowerSeries.Restricted.X`, `MvPowerSeries.Restricted.C` and `MvPowerSeries.Restricted.monomial`. Polynomials are restricted, `MvPolynomial.isRestricted`, and `MvPolynomial.toRestricted c` is the injective ring map from polynomials, `MvPolynomial.toRestricted_injective`. A bounded ring map on coefficients gives `MvPowerSeries.Restricted.map`.

#### Common errors

1. `PowerSeries.exists_isWeierstrassDivision` needs `[IsAdicComplete (IsLocalRing.maximalIdeal A) A]` and the hypothesis that the reduction of $g$ to the residue field is nonzero. The series $g = p$ over $\mathbb{Z}_p$ has zero reduction, and $f = 1$ has no division by $p$ with a polynomial remainder of small degree.
2. The degree of the remainder is bounded by the order of $g$ modulo the maximal ideal, not by the order of $g$. For $g = p + X$ over $\mathbb{Z}_p$ the order of $g$ is $0$, but the order modulo $p$ is $1$, so the remainder is a constant.
3. The product rule `MvPowerSeries.IsRestricted.mul` and the ring structure on `MvPowerSeries.Restricted R c` need `[IsUltrametricDist R]`. Over $\mathbb{R}$ or $\mathbb{C}$ with the usual absolute value the library gives only the additive subgroup.

### Exercises

1. (A) Prove that $X^2 + pX + p$ is distinguished at the ideal $(p)$ of $\mathbb{Z}_p$, and compute its image under `Polynomial.IsDistinguishedAt.map_eq_X_pow`.
2. (A) Let $g = p + X$ over $\mathbb{Z}_p$. Write $f = X^2$ as $g q + r$ with $r \in \mathbb{Z}_p$, and check that $r = p^2$.
3. (B) Let $g = p + X - X^3$ over $\mathbb{Z}_p$. Use `PowerSeries.IsWeierstrassFactorization.natDegree_eq_toNat_order_map` to find the degree of the distinguished factor of $g$.
4. (B) Prove from `PowerSeries.isRestricted_iff` that $\sum_n p^n X^n$ is restricted for $c = 1$ over $\mathbb{Q}_p$, and that $\sum_n X^n$ is not.
5. (B) Prove that a polynomial in $R[X]$ is restricted for every $c$, using the cofinite filter in `PowerSeries.isRestricted_iff`.
6. (C) Use `Polynomial.IsDistinguishedAt.algEquivQuotient` to prove that $\mathbb{Z}_p[[X]] / (X^2 - p)$ is a free $\mathbb{Z}_p$-module of rank $2$.

### Reference

<?reference?>
