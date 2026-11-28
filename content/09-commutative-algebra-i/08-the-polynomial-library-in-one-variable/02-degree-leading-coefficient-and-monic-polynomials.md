---
title: Degree, leading coefficient and monic polynomials
kind: api
modules:
  - Mathlib.Algebra.Polynomial.Degree.Defs
  - Mathlib.Algebra.Polynomial.Degree.Operations
  - Mathlib.Algebra.Polynomial.Degree.Lemmas
  - Mathlib.Algebra.Polynomial.Degree.Domain
  - Mathlib.Algebra.Polynomial.Degree.Monomial
  - Mathlib.Algebra.Polynomial.Degree.Support
  - Mathlib.Algebra.Polynomial.Degree.SmallDegree
  - Mathlib.Algebra.Polynomial.Degree.Units
  - Mathlib.Algebra.Polynomial.Degree.CardPowDegree
  - Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
  - Mathlib.Algebra.Polynomial.SpecificDegree
  - Mathlib.Algebra.Polynomial.Monic
explains:
  E2: [Polynomial.degree_eq_natDegree, Polynomial.coeff_mul_degree_add_degree, "Polynomial.leadingCoeff_mul'", Polynomial.degree_add_eq_left_of_degree_lt, Polynomial.degree_sub_lt_left, Polynomial.Monic.as_sum, Polynomial.natDegree_le_of_dvd, Polynomial.Monic.isUnit_iff, Polynomial.cardPowDegree_isEuclidean, Polynomial.IsMonicOfDegree.mul]
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

## Degree, leading coefficient and monic polynomials

### Overview

The degree is the most used invariant of a polynomial, and the files under `Mathlib/Algebra/Polynomial/Degree` hold several hundred lemmas about it. This section explains the two degree functions, the leading coefficient and the next coefficient, the rules for sums and products, the special behaviour over a ring without zero divisors, and monic polynomials. It ends with the small files on units, polynomials of small degree, the absolute value $q^{\deg p}$ over a finite field and the predicate "monic of degree $n$".

The lemmas follow a naming scheme that makes most of them easy to guess. A lemma about `degree` has a twin about `natDegree`, a lemma that needs no hypothesis on the ring has a primed twin that asks for a nonzero product of leading coefficients, and a lemma for a domain drops the prime and the hypothesis.

### The library around it

#### Two degrees

The file `Mathlib.Algebra.Polynomial.Degree.Defs` defines `Polynomial.degree` $p$ as the maximum of the support, a value in `WithBot ℕ`. So the zero polynomial has degree $\bot$ (`Polynomial.degree_zero`, `Polynomial.degree_eq_bot`). The natural degree `Polynomial.natDegree` $p$ is the same number in $\mathbb{N}$, with the value $0$ for $p = 0$ (`Polynomial.natDegree_zero`). The two agree away from zero: `Polynomial.degree_eq_natDegree` says $\deg p = \operatorname{natDeg} p$ in `WithBot ℕ` for $p \ne 0$. Proof: the support of a nonzero $p$ is nonempty, so its maximum is a natural number $n$, and `natDegree` reads this $n$ out of `WithBot ℕ`.

The degree is the correct function for statements that must hold also for $0$, such as $\deg(pq) = \deg p + \deg q$ over a domain. The natural degree is easier for arithmetic with indices, such as the coefficient $p_{\operatorname{natDeg} p}$. Lemmas such as `Polynomial.natDegree_lt_iff_degree_lt` and `Polynomial.natDegree_eq_of_degree_eq_some` move between the two. The degree is a case of the degree of a monoid algebra of Chapter 6, Section 9: `Polynomial.supDegree_eq_degree` and `Polynomial.supDegree_eq_natDegree` identify the two with `AddMonoidAlgebra.supDegree`.

The leading coefficient `Polynomial.leadingCoeff` $p$ is the coefficient $p_{\operatorname{natDeg} p}$ (`Polynomial.coeff_natDegree`), and it is zero only for $p = 0$ (`Polynomial.leadingCoeff_eq_zero`). The next coefficient `Polynomial.nextCoeff` $p$ is the coefficient one step below, and $0$ for constant $p$. A polynomial is monic, `Polynomial.Monic` $p$, when its leading coefficient is $1$ (`Polynomial.Monic.def`).

The coefficients above the degree are zero, and the degree is characterized by this. `Polynomial.degree_le_iff_coeff_zero` says $\deg p \le n$ exactly when $p_m = 0$ for all $m > n$, and `Polynomial.coeff_eq_zero_of_natDegree_lt` gives one direction for the natural degree. Proof of the first: $\deg p \le n$ means that every element of the support is at most $n$, which is the same as $p_m = 0$ for $m > n$ by `Polynomial.mem_support_iff`.

#### The basic values

| Polynomial | `degree` | `natDegree` | `leadingCoeff` |
| --- | --- | --- | --- |
| $0$ | $\bot$ | $0$ | $0$ |
| $C(a)$, $a \ne 0$ | $0$ (`Polynomial.degree_C`) | $0$ (`Polynomial.natDegree_C`) | $a$ (`Polynomial.leadingCoeff_C`) |
| $X$ | $1$ (`Polynomial.degree_X`) | $1$ | $1$ |
| $X^n$ | $n$ | $n$ (`Polynomial.natDegree_X_pow`) | $1$ (`Polynomial.leadingCoeff_X_pow`) |
| $a X^n$, $a \ne 0$ | $n$ (`Polynomial.degree_C_mul_X_pow`) | $n$ | $a$ |
| $X - C(a)$ | $1$ (`Polynomial.degree_X_sub_C`) | $1$ (`Polynomial.natDegree_X_sub_C`) | $1$ (`Polynomial.leadingCoeff_X_sub_C`) |

The degree of $X$ and of $X^n$ needs a nontrivial ring, since over the zero ring $X = 0$.

#### Sums and products

The general rules are inequalities. `Polynomial.degree_add_le` says $\deg(p + q) \le \max(\deg p, \deg q)$, `Polynomial.degree_sub_le` is the same for a difference, and `Polynomial.degree_mul_le` says $\deg(pq) \le \deg p + \deg q$. The natural degree versions are `Polynomial.natDegree_add_le` and `Polynomial.natDegree_mul_le`.

Equality holds in a sum when one degree is strictly larger. `Polynomial.degree_add_eq_left_of_degree_lt` says $\deg(p + q) = \deg p$ when $\deg q < \deg p$. Proof: at the index $d = \deg p$ the coefficient of $p + q$ is $p_d + q_d = p_d + 0 \ne 0$, so $\deg(p + q) \ge d$, and the inequality `Polynomial.degree_add_le` gives the other direction. The companion `Polynomial.leadingCoeff_add_of_degree_lt` gives the leading coefficient of the sum.

In a product the top coefficient is always the product of the leading coefficients: `Polynomial.coeff_mul_degree_add_degree` says $(pq)_{m+n} = \operatorname{lc}(p) \operatorname{lc}(q)$ for $m = \operatorname{natDeg} p$ and $n = \operatorname{natDeg} q$. Proof: by `Polynomial.coeff_mul`, the coefficient is $\sum_{i + j = m + n} p_i q_j$. If $i > m$ then $p_i = 0$, and if $i < m$ then $j > n$ and $q_j = 0$. So only the pair $(m, n)$ contributes. If this product is not zero, the degree and the leading coefficient of $pq$ follow: these are `Polynomial.natDegree_mul'`, `Polynomial.degree_mul'` and `Polynomial.leadingCoeff_mul'`, which ask for $\operatorname{lc}(p) \operatorname{lc}(q) \ne 0$.

Over a ring without zero divisors the hypothesis is automatic for nonzero $p$ and $q$, and the unprimed lemmas hold: `Polynomial.degree_mul`, `Polynomial.natDegree_mul`, `Polynomial.leadingCoeff_mul`, `Polynomial.degree_pow` and `Polynomial.leadingCoeff_pow`. The leading coefficient is then a monoid map, `Polynomial.leadingCoeffHom`, and so is the degree, `Polynomial.degreeMonoidHom`, with values in `Multiplicative (WithBot ℕ)`. The file `Mathlib.Algebra.Polynomial.Degree.Domain` adds the consequences for divisibility: `Polynomial.natDegree_le_of_dvd` says that a divisor of a nonzero $q$ has natural degree at most $\operatorname{natDeg} q$. Proof: write $q = pr$. Then $r \ne 0$, so $\operatorname{natDeg} q = \operatorname{natDeg} p + \operatorname{natDeg} r \ge \operatorname{natDeg} p$. The contrapositive is `Polynomial.not_dvd_of_degree_lt`.

The difference of two polynomials of the same degree and leading coefficient has a smaller degree. This is `Polynomial.degree_sub_lt_left`, the step of each division algorithm. Proof: at the index $d$ of the common degree the coefficient of $p - q$ is $\operatorname{lc}(p) - \operatorname{lc}(q) = 0$, and above $d$ all coefficients are zero. So the support of $p - q$ lies below $d$. Since the degree takes values in a well-founded order, induction on the degree is available as `Polynomial.degree_lt_wf`.

The file `Mathlib.Algebra.Polynomial.Degree.Lemmas` treats composition and maps of coefficients. Over a ring without zero divisors `Polynomial.natDegree_comp` says $\operatorname{natDeg}(p \circ q) = \operatorname{natDeg} p \cdot \operatorname{natDeg} q$, and `Polynomial.leadingCoeff_comp` computes the leading coefficient when $q$ is not constant. `Polynomial.degree_map_eq_of_injective` says that an injective map of coefficients keeps the degree.

#### Supports, monomials and small degrees

The file `Mathlib.Algebra.Polynomial.Degree.Support` writes a polynomial as a sum up to its degree: `Polynomial.as_sum_range_C_mul_X_pow` says $p = \sum_{i=0}^{\operatorname{natDeg} p} C(p_i) X^i$. Each element of the support is at most the natural degree (`Polynomial.le_natDegree_of_mem_supp`), so the support has at most $\operatorname{natDeg} p + 1$ elements (`Polynomial.card_supp_le_succ_natDegree`). The file `Mathlib.Algebra.Polynomial.Degree.Monomial` says that a polynomial with at most one term is its leading term (`Polynomial.monomial_natDegree_leadingCoeff_eq_self`). The file `Mathlib.Algebra.Polynomial.Degree.SmallDegree` computes the degree and the leading coefficient of $aX + b$, $aX^2 + bX + c$ and $aX^3 + bX^2 + cX + d$ for $a \ne 0$, as in `Polynomial.degree_quadratic`, `Polynomial.leadingCoeff_quadratic` and `Polynomial.natDegree_cubic`. A polynomial of natural degree at most $1$ is $C(a) X + C(b)$ (`Polynomial.exists_eq_X_add_C_of_natDegree_le_one`).

#### Monic polynomials

The file `Mathlib.Algebra.Polynomial.Monic` holds the theory of monic polynomials. Products and powers of monic polynomials are monic (`Polynomial.Monic.mul`, `Polynomial.Monic.pow`). The leading coefficient of a monic factor is $1$, so the product of the leading coefficients is never zero over a nontrivial ring, and the degree adds without a hypothesis on the ring: `Polynomial.Monic.natDegree_mul`, `Polynomial.Monic.degree_mul` and `Polynomial.Monic.natDegree_pow`. For the same reason a monic polynomial is a regular element (`Polynomial.Monic.isRegular`). The usual examples are `Polynomial.monic_X`, `Polynomial.monic_X_pow`, `Polynomial.monic_X_sub_C`, and `Polynomial.monic_X_pow_add` for $X^n + p$ with $\deg p < n$.

The lemma `Polynomial.Monic.as_sum` writes a monic $p$ of natural degree $n$ as $X^n + \sum_{i < n} C(p_i) X^i$. Proof: split the sum of `Polynomial.as_sum_range_C_mul_X_pow` into the terms $i < n$ and the top term $C(p_n) X^n = C(1) X^n = X^n$. The only monic unit is $1$: `Polynomial.Monic.isUnit_iff` says $p$ is a unit exactly when $p = 1$. Proof: let $pq = 1$. Over a nontrivial ring $q \ne 0$, and $\operatorname{lc}(p) \operatorname{lc}(q) = \operatorname{lc}(q) \ne 0$. So `Polynomial.natDegree_mul'` gives $\operatorname{natDeg} p + \operatorname{natDeg} q = \operatorname{natDeg} 1 = 0$. Then $p$ is a monic constant, which is $1$. Over the zero ring every polynomial is $1$. Over a domain, `Polynomial.Monic.irreducible_iff_natDegree` tests irreducibility of a monic polynomial on monic factorizations of smaller degree. Maps of coefficients keep monic polynomials monic (`Polynomial.Monic.map`). The subtype `Polynomial.MonicDegreeEq` $R$ $n$ holds the monic polynomials of degree $n$, in a form that still makes sense over the zero ring.

#### Units, finite fields and fixed degrees

The file `Mathlib.Algebra.Polynomial.Degree.Units` describes the units over a ring without zero divisors: `Polynomial.isUnit_iff` says that they are the constants $C(r)$ with $r$ a unit, and `Polynomial.natDegree_eq_zero_of_isUnit` gives the degree. The file `Mathlib.Algebra.Polynomial.Degree.CardPowDegree` defines over a finite field $\mathbb{F}_q$ the absolute value `Polynomial.cardPowDegree`, with $|p| = q^{\operatorname{natDeg} p}$ and $|0| = 0$ (`Polynomial.cardPowDegree_apply`). The lemma `Polynomial.cardPowDegree_isEuclidean` says that it is compatible with the Euclidean division of Section 5: a smaller absolute value means a smaller degree. It is used for the finiteness of class groups of function fields.

The file `Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree` defines the predicate `Polynomial.IsMonicOfDegree` $p$ $n$: $p$ is monic and $\operatorname{natDeg} p = n$. It is closed under products, `Polynomial.IsMonicOfDegree.mul`, with degree $m + n$. Proof: the product is monic by `Polynomial.Monic.mul`, and its degree is $m + n$ by `Polynomial.Monic.natDegree_mul`. Over a nontrivial ring, `Polynomial.isMonicOfDegree_iff` reduces the predicate to a bound on the degree and the coefficient at $n$. The file `Mathlib.Algebra.Polynomial.SpecificDegree` treats degrees $2$ and $3$ over a field: such a polynomial is irreducible exactly when it has no root (`Polynomial.irreducible_iff_roots_eq_zero_of_degree_le_three`), because a nontrivial factorization has a factor of degree $1$.

#### Common errors

1. Using `natDegree` in a statement that must hold for $p = 0$. The equation $\operatorname{natDeg}(pq) = \operatorname{natDeg} p + \operatorname{natDeg} q$ needs $p \ne 0$ and $q \ne 0$, while `Polynomial.degree_mul` holds for all $p$ and $q$ over a domain.
2. Applying `Polynomial.degree_mul` over a ring with zero divisors. Over $\mathbb{Z}/4$ the product $(2X + 1)(2X + 1) = 1$ has degree $0$. Use the primed lemmas with the hypothesis on the leading coefficients, or a monic factor.
3. Forgetting `Nontrivial R` in the basic values. Over the zero ring every polynomial is $0$, so `Polynomial.natDegree_X_pow` and `Polynomial.degree_X` need a nontrivial ring.

### Exercises

1. (A) Compute with `Polynomial.degree_add_eq_left_of_degree_lt` the degree of $X^5 + 3X^2 + 1$ over $\mathbb{Z}$.
2. (A) Show with `Polynomial.Monic.isUnit_iff` that $X + 1$ is not a unit in $R[X]$ for a nontrivial ring $R$.
3. (B) Prove with `Polynomial.coeff_mul_degree_add_degree` that $\operatorname{lc}(p^n) = \operatorname{lc}(p)^n$ when $\operatorname{lc}(p)$ is not a zero divisor.
4. (B) Use `Polynomial.natDegree_le_of_dvd` to show that $X^2 + 1$ does not divide $X + 2$ in $\mathbb{Q}[X]$.
5. (B) Show that $2X + 1$ is a unit in $(\mathbb{Z}/4)[X]$, and explain why this does not contradict `Polynomial.isUnit_iff`.
6. (C) Prove with `Polynomial.degree_sub_lt_left` and `Polynomial.degree_lt_wf` that for a monic $g$ every $f$ has the form $qg + r$ with $\deg r < \deg g$.

### Reference

<?reference?>
