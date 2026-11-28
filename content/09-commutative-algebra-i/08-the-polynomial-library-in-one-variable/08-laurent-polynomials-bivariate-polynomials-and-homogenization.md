---
title: Laurent polynomials, bivariate polynomials and homogenization
kind: api
modules:
  - Mathlib.Algebra.Polynomial.Laurent
  - Mathlib.Algebra.Polynomial.Laurent.Roots
  - Mathlib.Algebra.Polynomial.Bivariate
  - Mathlib.Algebra.Polynomial.Homogenize
explains:
  E2: [LaurentPolynomial.exists_T_pow, LaurentPolynomial.isLocalization, LaurentPolynomial.toLaurent_reverse, LaurentPolynomial.eval₂_toLaurent, Polynomial.evalEval_C, Polynomial.aevalAevalEquiv, Polynomial.Bivariate.equivMvPolynomial, Polynomial.coeff_homogenize, Polynomial.eval_homogenize, Polynomial.homogenize_eq_of_isHomogeneous]
  E1: auto
families: []
requires: [V06.C05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Laurent polynomials, bivariate polynomials and homogenization

### Overview

Three constructions sit next to $R[X]$ and are used with it. The ring $R[T, T^{-1}]$ of Laurent polynomials allows negative exponents. The ring $R[X][Y]$ of polynomials in two variables is built as polynomials with polynomial coefficients, and it is the setting of plane curves. Homogenization turns a polynomial $f(X)$ of degree at most $n$ into a homogeneous polynomial $Z^n f(X/Z)$ in two variables, the step from the affine line to the projective line.

The four files of this section are `Mathlib.Algebra.Polynomial.Laurent`, `Mathlib.Algebra.Polynomial.Laurent.Roots`, `Mathlib.Algebra.Polynomial.Bivariate` and `Mathlib.Algebra.Polynomial.Homogenize`. Each one gives a type or a map, the link with $R[X]$, and the rules for evaluation.

### The library around it

#### Laurent polynomials

The type `LaurentPolynomial R` is an abbreviation for `AddMonoidAlgebra R ℤ`, the monoid algebra of Chapter 6, Section 8 for the group $\mathbb{Z}$. The scoped notation `R[T;T⁻¹]` is available after `open LaurentPolynomial`. The variable is written $T$ to keep it apart from the $X$ of $R[X]$. The element `LaurentPolynomial.T` $n$ is $T^n$ for $n \in \mathbb{Z}$, and `LaurentPolynomial.C` is the ring map of constants. The basic rules are `LaurentPolynomial.T_zero`, `LaurentPolynomial.T_add` and `LaurentPolynomial.T_pow`, and each $T^n$ is a unit (`LaurentPolynomial.isUnit_T`). A single term is a constant times a power: `LaurentPolynomial.single_eq_C_mul_T`.

The ring map `Polynomial.toLaurent` sends $X$ to $T^1$ (`Polynomial.toLaurent_X`) and $a X^n$ to $a T^n$ (`Polynomial.toLaurent_C_mul_T`). It is injective (`Polynomial.toLaurent_injective`), and its algebra form is `Polynomial.toLaurentAlg`. The additive map `LaurentPolynomial.trunc` keeps the terms with nonnegative exponent, and `Polynomial.trunc_toLaurent` says that it undoes `Polynomial.toLaurent`.

Each Laurent polynomial becomes a polynomial after multiplication by a power of $T$. This is `LaurentPolynomial.exists_T_pow`: for each $f$ there are $n \in \mathbb{N}$ and $g \in R[X]$ with $g = f \, T^n$ in $R[T, T^{-1}]$. Proof: the support of $f$ is finite, so it has a least element $-n$ with $n \ge 0$, or $f = 0$. Then $f \, T^n$ has all its exponents in $\mathbb{N}$, and it is the image of the polynomial with the same coefficients. This gives the induction principles `LaurentPolynomial.induction_on_mul_T` and `LaurentPolynomial.reduce_to_polynomial_of_mul_T`: to prove a property of all Laurent polynomials, prove it for $g \, T^{-n}$ with $g \in R[X]$. The induction on terms is `LaurentPolynomial.induction_on`.

The same fact makes $R[T, T^{-1}]$ the localization of $R[X]$ at the powers of $X$. The instance `LaurentPolynomial.algebraPolynomial` gives the algebra structure over $R[X]$, and `LaurentPolynomial.isLocalization` is the statement `IsLocalization.Away X`. Proof: the image of $X$ is the unit $T$, each element is $g / X^n$ by `LaurentPolynomial.exists_T_pow`, and an element of $R[X]$ whose image is zero is zero, since `Polynomial.toLaurent` is injective. So the results of Chapter 2 on localizations apply to Laurent polynomials.

The degree `LaurentPolynomial.degree` takes values in `WithBot ℤ`, with `LaurentPolynomial.degree_T` and `LaurentPolynomial.degree_C_mul_T` for single terms and `LaurentPolynomial.degree_eq_bot_iff` for the zero polynomial. The algebra automorphism `LaurentPolynomial.invert` sends $T^n$ to $T^{-n}$ (`LaurentPolynomial.invert_T`) and fixes the constants (`LaurentPolynomial.invert_C`); it is its own inverse (`LaurentPolynomial.involutive_invert`). With it, the reverse of a polynomial of Section 3 has a short description: `LaurentPolynomial.toLaurent_reverse` says that the reverse of $p$ is $T^{\deg p} \cdot p(T^{-1})$. Proof: both sides are linear in $p$ once the degree is fixed, and on $a X^k$ with $k \le \deg p$ both sides are $a T^{\deg p - k}$.

#### Evaluation of Laurent polynomials

A Laurent polynomial can be evaluated only at a unit. The ring map `LaurentPolynomial.eval₂` $f$ $x$ takes a ring map $f \colon R \to S$ and a unit $x \in S^\times$. It sends $T^n$ to $x^n$ (`LaurentPolynomial.eval₂_T`) and $C\,r$ to $f(r)$ (`LaurentPolynomial.eval₂_C`). On polynomials it agrees with the evaluation of Section 4: `LaurentPolynomial.eval₂_toLaurent` says that the evaluation of the image of $p$ is `Polynomial.eval₂` $f$ $x$ $p$. Proof: both sides are ring maps from $R[X]$, and they agree on the constants and on $X$. The evaluation in a module with a scalar action is `LaurentPolynomial.smeval`, with the sum formula `LaurentPolynomial.smeval_eq_sum`, and its linear form is `LaurentPolynomial.leval`.

The file `Mathlib.Algebra.Polynomial.Laurent.Roots` gives the analogue for $R[T, T^{-1}]$ of the fact that a polynomial with infinitely many roots is zero. Let $S$ be a domain and a faithful $R$-algebra. A Laurent polynomial whose evaluation vanishes at infinitely many units of $S$ is zero, and two Laurent polynomials that agree at infinitely many units are equal. Proof: write $f \, T^n = g$ with $g \in R[X]$ by `LaurentPolynomial.exists_T_pow`. At each unit $x$ with $f(x) = 0$, also $g(x) = f(x) \, x^n = 0$. So $g$ has infinitely many roots in $S$, so $g = 0$, and $f = g \, T^{-n} = 0$.

#### Polynomials in two variables

The file `Mathlib.Algebra.Polynomial.Bivariate` treats `Polynomial (Polynomial R)`, written `R[X][Y]` with a scoped notation of the file. The inner variable is $X$, which is `C X` in this type, and the outer variable is $Y$, which is `X`. The constants of $R$ enter by `Polynomial.CC`, the double constant map. This choice of names is the first source of confusion, and the lemmas state the roles of `C X` and `X` explicitly.

Evaluation at a point $(x, y) \in R^2$ is `Polynomial.evalEval` $x$ $y$. It evaluates the outer variable at $y$ and then the inner variable at $x$. The basic rules are `Polynomial.evalEval_C`, which says that a constant $C\,p$ with $p \in R[X]$ has the value $p(x)$, `Polynomial.evalEval_X`, which gives the value $y$, and `Polynomial.evalEval_CC`. Evaluation is multiplicative over a commutative semiring (`Polynomial.evalEval_mul`), so it preserves divisibility (`Polynomial.evalEval_dvd`), and its ring map form is `Polynomial.evalEvalRingHom`. A point $(x, y)$ with $p(x, y) = 0$ gives a ring map from the quotient by $p$: `AdjoinRoot.evalEval` sends the class of $g$ to $g(x, y)$, by `AdjoinRoot.evalEval_mk`. This is how a point of a plane curve gives a point of its coordinate ring.

For an $R$-algebra $A$ and two elements $x, y \in A$, `Polynomial.aevalAeval` $x$ $y$ is the algebra map with `C X` $\mapsto x$ and `X` $\mapsto y$ (`Polynomial.aevalAeval_X` and `Polynomial.aevalAeval_Y`). The universal property is `Polynomial.aevalAevalEquiv`: algebra maps from $R[X][Y]$ to $A$ correspond to pairs $(x, y) \in A \times A$. Proof: an algebra map from $R[X][Y]$ is fixed by its values on the two variables, by the universal property of Section 4 applied twice, and each pair of values gives such a map.

The swap `Polynomial.Bivariate.swap` is the algebra automorphism that exchanges the two variables (`Polynomial.Bivariate.swap_X` and `Polynomial.Bivariate.swap_Y`); on monomials it is `Polynomial.Bivariate.swap_monomial_monomial`, and it is compatible with evaluation by `Polynomial.Bivariate.aevalAeval_swap`. The link with Chapter 6 is `Polynomial.Bivariate.equivMvPolynomial`, an algebra isomorphism from $R[X][Y]$ to `MvPolynomial (Fin 2) R`. It sends `C X` to the variable $0$ and `X` to the variable $1$ (`Polynomial.Bivariate.equivMvPolynomial_C_X` and `Polynomial.Bivariate.equivMvPolynomial_X`). Under it the derivative in $Y$ becomes the partial derivative in the variable $1$, by `Polynomial.Bivariate.pderiv_one_equivMvPolynomial`.

#### Homogenization

The file `Mathlib.Algebra.Polynomial.Homogenize` defines `Polynomial.homogenize` $p$ $n$ in `MvPolynomial (Fin 2) R`. For $p$ of degree at most $n$ it is $\sum_k a_k X_0^k X_1^{n-k}$, so $X_0$ plays the role of $X$ and $X_1$ is the new variable. The coefficient formula is `Polynomial.coeff_homogenize`: the coefficient at an exponent $(m_0, m_1)$ is $a_{m_0}$ when $m_0 + m_1 = n$, and zero otherwise. So the result is homogeneous of degree $n$, by `Polynomial.isHomogeneous_homogenize` with `MvPolynomial.IsHomogeneous`. On the basic polynomials the formulas are `Polynomial.homogenize_C`, `Polynomial.homogenize_X_pow` and `Polynomial.homogenize_monomial`. The linear form is `Polynomial.homogenizeLM`.

Dehomogenization is the substitution $X_0 \mapsto X$, $X_1 \mapsto 1$. The lemma `Polynomial.aeval_homogenize_X_one` says that it undoes homogenization when $\deg p \le n$. The converse is the uniqueness statement `Polynomial.homogenize_eq_of_isHomogeneous`: a homogeneous $q$ of degree $n$ whose dehomogenization is $p$ is the homogenization of $p$ of degree $n$. Proof: compare the coefficients of $q$ at $(k, n - k)$. Homogeneity says that $q$ has no other terms, and the substitution $X_1 \mapsto 1$ sends the term at $(k, n - k)$ to a term of degree $k$ in $X$, with no collisions. So the coefficient of $q$ at $(k, n - k)$ is $a_k$, which is `Polynomial.coeff_homogenize`.

Over a field, evaluation of the homogenization is `Polynomial.eval_homogenize`: for $x = (x_0, x_1)$ with $x_1 \ne 0$, the value is $p(x_0 / x_1) \, x_1^n$. Proof: each term $a_k x_0^k x_1^{n-k}$ equals $a_k (x_0 / x_1)^k x_1^n$. Homogenization is multiplicative when the degrees add, by `Polynomial.homogenize_mul`: for $\deg p \le m$ and $\deg q \le n$, the homogenization of $pq$ of degree $m + n$ is the product of the homogenizations. Over a ring without zero divisors it keeps divisibility, `Polynomial.homogenize_dvd`, and `Polynomial.homogenize_eq_zero_iff` says that it is zero only for $p = 0$ when $\deg p \le n$. The function `Polynomial.toTupleMvPolynomial` packs the pair of the homogenization of $p$ in degree $\deg p$ and the power $X_1^{\deg p}$. It writes the map $x \mapsto p(x)$ as a map of the projective line, with `Polynomial.eval_eq_div_eval_toTupleMvPolynomial` for the value as a quotient.

#### Common errors

1. Reading `C X` in `R[X][Y]` as a constant. It is the inner variable $X$, and `X` is the outer variable $Y$. Check `Polynomial.evalEval_C` and `Polynomial.evalEval_X` before a computation.
2. Using `LaurentPolynomial.eval₂` at an element that is not a unit. The point is an element of $S^\times$, so a computation at $x \in S$ first needs a proof that $x$ is a unit.
3. Homogenizing to a degree below the degree of $p$. Then the terms of degree above $n$ are lost, and `Polynomial.aeval_homogenize_X_one` and `Polynomial.homogenize_mul` do not apply.

### Exercises

1. (A) Use `LaurentPolynomial.exists_T_pow` to write $T^{-2} + 3 + T$ as $g \, T^{-n}$ with $g \in \mathbb{Z}[X]$.
2. (A) Compute the homogenization of degree $3$ of $X^2 - 1$ with `Polynomial.coeff_homogenize`.
3. (B) Show that `LaurentPolynomial.invert` sends the image of $X^2 + X$ to $T^{-2} + T^{-1}$, and relate the result to `LaurentPolynomial.toLaurent_reverse`.
4. (B) Prove with `Polynomial.aevalAevalEquiv` that two algebra maps from $R[X][Y]$ that agree on `C X` and on `X` are equal.
5. (B) For $p = Y^2 - X^3 - 1$ in $\mathbb{Z}[X][Y]$ and the point $(0, 1)$, build the ring map of `AdjoinRoot.evalEval` and compute the image of the class of $X + Y$.
6. (C) Prove that a Laurent polynomial over $\mathbb{Q}$ that vanishes at every positive integer is zero, with `LaurentPolynomial.exists_T_pow` and the finiteness of the roots of a nonzero polynomial.

### Reference

<?reference?>
