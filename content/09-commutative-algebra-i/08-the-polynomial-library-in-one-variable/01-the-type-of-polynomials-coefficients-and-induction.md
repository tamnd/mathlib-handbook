---
title: The type of polynomials, coefficients and induction
kind: api
modules:
  - Mathlib.Algebra.Polynomial.Basic
  - Mathlib.Algebra.Polynomial.Monomial
  - Mathlib.Algebra.Polynomial.Coeff
  - Mathlib.Algebra.Polynomial.Inductions
  - Mathlib.Algebra.Polynomial.BigOperators
  - Mathlib.Algebra.Polynomial.Cardinal
  - Mathlib.Algebra.Polynomial.Basis
  - Mathlib.Algebra.Polynomial.CoeffList
  - Mathlib.Algebra.Polynomial.CoeffMem
  - Mathlib.Algebra.Polynomial.OfFn
  - Mathlib.Algebra.Polynomial.Identities
  - Mathlib.Algebra.Polynomial.Sequence
explains:
  E2: [Polynomial.sum_C_mul_X_pow_eq, Polynomial.ringHom_ext, Polynomial.coeff_X_pow_mul, Polynomial.card_support_le_one_iff_monomial, Polynomial.X_mul_divX_add, Polynomial.degree_pos_induction_on, Polynomial.prod_X_sub_C_nextCoeff, Polynomial.ofCoeffList_coeffList, Polynomial.toFn_comp_ofFn_eq_id, Polynomial.Sequence.span_degreeLE]
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

## The type of polynomials, coefficients and induction

### Overview

This section describes the base of the library: the type `Polynomial R`, its three constructors, the coefficients and the support, finite sums over the support, and the induction principles. It also covers the smaller files that give other views of a polynomial: a basis, a list of coefficients, a vector of coefficients, and a sequence of polynomials of each degree. The degree appears here only where an induction needs it; Section 2 treats it in full.

In this Mathlib, `Polynomial R` is an abbreviation for `AddMonoidAlgebra R ℕ`, the monoid algebra of Chapter 6, Section 8, over the additive monoid $\mathbb{N}$. So a polynomial is a finitely supported function $\mathbb{N} \to R$ with the convolution product, and the general results on monoid algebras apply to it directly. Inside the namespace `Polynomial`, the notation `R[X]` stands for `Polynomial R`. The notation is scoped, so a file must open the namespace or write `open Polynomial` to use it.

### The library around it

#### Constructors and coefficients

The file `Mathlib.Algebra.Polynomial.Basic` gives three ways to build polynomials. The ring map `Polynomial.C` sends $a \in R$ to the constant polynomial $a$. The element `Polynomial.X` is the variable. The linear map `Polynomial.monomial` $n$ sends $a$ to $a X^n$. The three are related by `Polynomial.C_mul_X_pow_eq_monomial`, which says $C(a) X^n = \operatorname{monomial} n \, a$, and by `Polynomial.monomial_zero_left` and `Polynomial.X_pow_eq_monomial`. Products of monomials follow `Polynomial.monomial_mul_monomial`: $(a X^n)(b X^m) = (ab) X^{n+m}$. The variable commutes with every polynomial (`Polynomial.X_mul` and `Polynomial.commute_X`), also over a noncommutative ring.

The coefficient of $p$ at $n$ is written `p.coeff n`. Here `coeff` is the field of the monoid algebra structure, so the coefficient function of $p$ is a finitely supported function `ℕ →₀ R` and `p.coeff n` is its value. Two polynomials are equal when all their coefficients are equal; the `ext` tactic reduces `p = q` to `p.coeff n = q.coeff n` for a new variable `n`. The support `Polynomial.support` is the finite set of exponents with a nonzero coefficient, and `Polynomial.mem_support_iff` says $n \in \operatorname{supp} p \iff p_n \ne 0$.

The coefficient lemmas are named after the shape of the polynomial.

| Lean name | Statement |
| --- | --- |
| `Polynomial.coeff_C` | $C(a)_n$ is $a$ for $n = 0$ and $0$ otherwise |
| `Polynomial.coeff_X` | $X_n$ is $1$ for $n = 1$ and $0$ otherwise |
| `Polynomial.coeff_monomial_same` | $(a X^n)_n = a$ |
| `Polynomial.coeff_C_mul_X_pow` | $(a X^k)_n$ is $a$ for $n = k$ and $0$ otherwise |
| `Polynomial.coeff_C_mul` | $(C(a) p)_n = a \, p_n$ |
| `Polynomial.coeff_mul_C` | $(p \, C(a))_n = p_n \, a$ |
| `Polynomial.coeff_X_pow_mul` | $(X^n p)_{d+n} = p_d$ |
| `Polynomial.coeff_mul_X_pow` | $(p X^n)_{d+n} = p_d$ |
| `Polynomial.mul_coeff_zero` | $(pq)_0 = p_0 q_0$ |
| `Polynomial.coeff_one_add_X_pow` | $((1 + X)^n)_k = \binom{n}{k}$ |

The general product rule is `Polynomial.coeff_mul`: $(pq)_n = \sum_{i + j = n} p_i q_j$, a sum over the antidiagonal of $n$. The rule `Polynomial.coeff_X_pow_mul` follows from it. Proof: the only nonzero coefficient of $X^n$ is at $n$, so in the sum for $(X^n p)_{d+n}$ only the pair $(n, d)$ contributes, and it gives $1 \cdot p_d$.

The coefficient file `Mathlib.Algebra.Polynomial.Coeff` also has the bundled coefficient maps. `Polynomial.lcoeff` $R$ $n$ is the $R$-linear map $p \mapsto p_n$, and `Polynomial.constantCoeff` is the ring map $p \mapsto p_0$. The lemma `Polynomial.C_dvd_iff_dvd_coeff` says that $C(r)$ divides $p$ exactly when $r$ divides each coefficient. The variable is a regular element (`Polynomial.isRegular_X`), and the support of a product has at most $|\operatorname{supp} p| \cdot |\operatorname{supp} q|$ elements (`Polynomial.card_support_mul_le`). The file `Mathlib.Algebra.Polynomial.Monomial` characterizes monomials: `Polynomial.card_support_le_one_iff_monomial` says that $p$ has at most one nonzero coefficient exactly when $p = a X^n$. Proof: if the support is empty, $p = 0 \, X^0$; if it is $\{n\}$, then $p$ and $p_n X^n$ have the same coefficients. The converse is `Polynomial.support_monomial`. The same file proves that a nontrivial ring has infinitely many polynomials (`Polynomial.infinite`).

#### Sums over the support

The function `Polynomial.sum` $p$ $f$ is $\sum_{n \in \operatorname{supp} p} f(n, p_n)$, by `Polynomial.sum_def`. It is the standard way to define a map out of polynomials. Each polynomial is the sum of its terms: `Polynomial.sum_C_mul_X_pow_eq` says $\sum_n C(p_n) X^n = p$. Proof: compare the coefficients at $m$. By `Polynomial.coeff_C_mul_X_pow`, the term for $n$ contributes $p_n$ when $n = m$ and $0$ otherwise. So the sum gives $p_m$ when $m$ is in the support, and $0 = p_m$ when it is not. The variant `Polynomial.sum_monomial_eq` uses `monomial`.

A sum is additive in $p$ when $f$ is additive in its second argument; this is `Polynomial.sum_add_index`, with the two hypotheses $f(n, 0) = 0$ and $f(n, a + b) = f(n, a) + f(n, b)$. On a single term `Polynomial.sum_monomial_index` gives $f(n, a)$. The bundled form `Polynomial.lsum` takes a family of linear maps and gives a linear map. To prove that two maps out of `R[X]` agree, use the extension lemmas. `Polynomial.addHom_ext` checks additive maps on each $a X^n$, `Polynomial.lhom_ext'` checks linear maps on each `monomial n`, and `Polynomial.ringHom_ext` checks ring maps on the constants and on $X$. Proof of the last: two ring maps that agree on $C(a)$ and on $X$ agree on $C(a) X^n$, and by additivity on each sum of such terms, so on all of `R[X]` by `Polynomial.sum_C_mul_X_pow_eq`.

#### Induction

The basic induction principle is `Polynomial.induction_on`. To prove a property for all polynomials, prove it for constants, show that it passes to sums, and show that it passes from $C(a) X^n$ to $C(a) X^{n+1}$. The variant `Polynomial.induction_on'` asks only for sums and monomials. These follow from `Polynomial.sum_C_mul_X_pow_eq`: a polynomial is a finite sum of terms.

The file `Mathlib.Algebra.Polynomial.Inductions` adds the Horner scheme. The map `Polynomial.divX` divides by $X$ and drops the constant term: its coefficients are $(\operatorname{divX} p)_n = p_{n+1}$ (`Polynomial.coeff_divX`). The identity `Polynomial.X_mul_divX_add` says $X \cdot \operatorname{divX} p + C(p_0) = p$. Proof: compare coefficients. At $0$ the left side gives $0 + p_0$. At $n + 1$ it gives $(\operatorname{divX} p)_n + 0 = p_{n+1}$. The induction `Polynomial.recOnHorner` builds a polynomial from $0$ by the two steps $p \mapsto p + C(a)$ and $p \mapsto p X$, and it works by recursion on the degree, since `divX` lowers the degree. Its form for positive degree is `Polynomial.degree_pos_induction_on`: a property of $C(a) X$ for $a \ne 0$ that passes to $pX$ and to $p + C(a)$ holds for every polynomial of positive degree. Proof: apply `Polynomial.recOnHorner`. A polynomial $p + C(a)$ or $pX$ of positive degree comes either from a $p$ of positive degree, where the hypotheses apply, or from a constant $p$, where $pX = C(b) X$ or $p + C(a)$ is constant, which has degree $0$. The lemma `Polynomial.natDegree_ne_zero_induction_on` is a version without products.

#### Products and sums of families

The file `Mathlib.Algebra.Polynomial.BigOperators` computes the degree, the leading coefficient and some coefficients of finite products. Over a ring without zero divisors, `Polynomial.natDegree_prod` adds the natural degrees of nonzero factors and `Polynomial.leadingCoeff_prod` multiplies the leading coefficients. For sums, `Polynomial.natDegree_sum_le` bounds the degree by the maximum of the degrees. The constant term of a product is the product of the constant terms (`Polynomial.coeff_zero_prod`).

The products of linear factors $X - c_i$ have special lemmas. `Polynomial.natDegree_multiset_prod_X_sub_C_eq_card` says that $\prod_{c \in s} (X - c)$ has degree $|s|$ over a nontrivial ring. `Polynomial.prod_X_sub_C_nextCoeff` says that the coefficient below the leading one is $-\sum_i c_i$. Proof: by induction on the finite set. A product of monic polynomials has as next coefficient the sum of the next coefficients of the factors (`Polynomial.Monic.nextCoeff_prod`), and the next coefficient of $X - c$ is $-c$. The multiset form `Polynomial.multiset_prod_X_sub_C_coeff_card_pred` gives the same coefficient. These are the first of the relations between roots and coefficients that Section 6 completes.

#### Other views of a polynomial

Several small files give other descriptions of the same data.

| File | Main declarations | Content |
| --- | --- | --- |
| `Mathlib.Algebra.Polynomial.Basis` | `Polynomial.basisMonomials` | the basis $(X^n)_{n \in \mathbb{N}}$ of `R[X]` over $R$ (`Polynomial.coe_basisMonomials`) |
| `Mathlib.Algebra.Polynomial.Cardinal` | `Polynomial.cardinalMk_le_max` | $\#R[X] \le \max(\#R, \aleph_0)$, with equality over a nontrivial ring |
| `Mathlib.Algebra.Polynomial.CoeffList` | `Polynomial.coeffList`, `Polynomial.ofCoeffList` | the list of coefficients from the leading one down to the constant term |
| `Mathlib.Algebra.Polynomial.OfFn` | `Polynomial.ofFn`, `Polynomial.toFn` | a vector $v \in R^n$ as the polynomial $\sum_{i < n} v_i X^i$ |
| `Mathlib.Algebra.Polynomial.Sequence` | `Polynomial.Sequence` | a family $(p_i)$ with $\deg p_i = i$ |
| `Mathlib.Algebra.Polynomial.Identities` | `Polynomial.binomExpansion`, `Polynomial.evalSubFactor` | the expansion of $f(x + y)$ to order $2$ and the factor $x - y$ of $f(x) - f(y)$ |
| `Mathlib.Algebra.Polynomial.CoeffMem` | `Polynomial.coeff_divByMonic_mem_pow_natDegree_mul` | the coefficients of a quotient by a monic polynomial lie in a bounded submodule |

The list `Polynomial.coeffList` $p$ has length $\deg p + 1$ for $p \ne 0$ and length $0$ for $p = 0$ (`Polynomial.length_coeffList_eq_ite`), and it starts with the leading coefficient (`Polynomial.coeffList_eq_cons_leadingCoeff`). The map `Polynomial.ofCoeffList` reads a list from the constant term upward. So the two do not undo each other: `Polynomial.ofCoeffList_coeffList` says that the composite gives the reverse of $p$, which Section 3 defines. The vector maps are linear. `Polynomial.ofFn_coeff_eq_val_of_lt` says that the coefficient of `ofFn n v` at $i < n$ is $v_i$, so `Polynomial.toFn_comp_ofFn_eq_id` holds: reading the first $n$ coefficients gives $v$ back.

A `Polynomial.Sequence` is a family of polynomials $S_0, S_1, \dots$ with $\deg S_i = i$ (`Polynomial.Sequence.degree_eq`). Over a domain it is linearly independent (`Polynomial.Sequence.linearIndependent`). When all leading coefficients are units, `Polynomial.Sequence.span_degreeLE` says that $S_0, \dots, S_m$ span the polynomials of degree at most $m$, and `Polynomial.Sequence.basis` is the resulting basis of `R[X]`. Proof of the span: by induction on $m$. A polynomial $p$ of degree at most $m$ differs from $(p_m / \operatorname{lc} S_m) S_m$ by a polynomial of degree less than $m$, which lies in the span of $S_0, \dots, S_{m-1}$. The binomial polynomials and the Chebyshev polynomials are examples.

#### Common errors

1. Using the extension lemma of the namespace `Polynomial`. It is deprecated in this Mathlib, because `Polynomial R` is `AddMonoidAlgebra R ℕ`. Use the `ext` tactic, which produces the goal `p.coeff n = q.coeff n`, or `AddMonoidAlgebra.ext` for equality of the coefficient functions.
2. Writing `R[X]` without `open Polynomial`. The notation is scoped, and without the namespace Lean reads `R[X]` as indexing into $R$.
3. Expecting `Polynomial.ofCoeffList` to undo `Polynomial.coeffList`. The two lists run in opposite directions, so the composite gives the reverse of the polynomial.

### Exercises

1. (A) Use `Polynomial.coeff_C_mul_X_pow` and `Polynomial.coeff_mul_C` to compute the coefficient of $X^3$ in $(2X^3 + X)(X^2 + 5)$.
2. (A) Prove with `Polynomial.ringHom_ext` that a ring map $\mathbb{Z}[X] \to S$ is fixed by the image of $X$.
3. (B) Prove with `Polynomial.induction_on` that $X$ commutes with every polynomial, without `Polynomial.X_mul`.
4. (B) Show with `Polynomial.coeff_one_add_X_pow` that $\sum_k \binom{n}{k} = 2^n$, by evaluation at $1$.
5. (B) Use `Polynomial.prod_X_sub_C_nextCoeff` to find the coefficient of $X^2$ in $(X - 1)(X - 2)(X - 3)$.
6. (C) Show that the polynomials $\binom{X}{i} = X(X-1)\cdots(X-i+1)/i!$ over $\mathbb{Q}$ form a `Polynomial.Sequence`, and use `Polynomial.Sequence.span_degreeLE` to show that they span the polynomials of degree at most $m$.

### Reference

<?reference?>
