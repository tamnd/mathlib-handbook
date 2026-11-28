---
title: Degrees, variables, derivatives and division in several variables
kind: api
modules:
  - Mathlib.Algebra.MvPolynomial.Degrees
  - Mathlib.Algebra.MvPolynomial.Variables
  - Mathlib.Algebra.MvPolynomial.Supported
  - Mathlib.Algebra.MvPolynomial.Equiv
  - Mathlib.Algebra.MvPolynomial.Derivation
  - Mathlib.Algebra.MvPolynomial.PDeriv
  - Mathlib.Algebra.MvPolynomial.Division
  - Mathlib.Algebra.MvPolynomial.Expand
  - Mathlib.Algebra.MvPolynomial.Nilpotent
  - Mathlib.Algebra.MvPolynomial.NoZeroDivisors
  - Mathlib.Algebra.MvPolynomial.SchwartzZippel
explains:
  E2: [MvPolynomial.mem_vars_iff_degreeOf_ne_zero, MvPolynomial.supported_eq_range_rename, MvPolynomial.degreeOf_eq_natDegree, MvPolynomial.mkDerivationEquiv, MvPolynomial.pderiv_comm, MvPolynomial.divMonomial_add_modMonomial, MvPolynomial.prime_X, MvPolynomial.isUnit_iff, MvPolynomial.schwartz_zippel_totalDegree]
  E1: auto
families: []
requires: [V06.C05, V09.C05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Degrees, variables, derivatives and division in several variables

### Overview

Section 4 described the ring `MvPolynomial σ R`, its coefficients, its evaluation maps and its renamings. This section covers the files that measure a polynomial and the files that act on it. A polynomial has a multiset of degrees, a degree in each variable, a total degree and a finite set of variables. It lives in the subalgebra of the polynomials in a set of variables. It can be read as a polynomial in one variable over a ring of polynomials in the other variables. It has partial derivatives, it can be divided by a monomial, and its variables can be raised to a power.

The last three files give ring theory. They decide when a polynomial is a unit or nilpotent, how degrees behave over a domain, and how often a nonzero polynomial vanishes on a grid. The last result is the Schwartz-Zippel lemma, which is a basic tool of computer algebra and of combinatorics.

The proofs in this section use one idea again and again: a statement about all coefficients is a statement about the finite support of a finitely supported function `σ →₀ ℕ →₀ R`. The reader who keeps this picture in mind can guess most proofs.

### The library around it

#### Degrees

The file `Mathlib.Algebra.MvPolynomial.Degrees` has three measures of size. The multiset `MvPolynomial.degrees` of $p$ is the supremum, in the lattice of multisets on $\sigma$, of the exponent vectors of the monomials of $p$. So the multiplicity of $i$ in `MvPolynomial.degrees` is the highest power of $x_i$ that occurs in $p$. The number `MvPolynomial.degreeOf` $i$ $p$ is this multiplicity, and `MvPolynomial.degreeOf_eq_sup` writes it as the supremum of $m(i)$ over the support. The number `MvPolynomial.totalDegree` is the supremum of $\sum_i m(i)$ over the support.

The basic estimates are the ones of one variable. The lemma `MvPolynomial.degrees_add_le` says $\deg(p + q) \le \deg p \sqcup \deg q$ and `MvPolynomial.degrees_mul_le` says $\deg(pq) \le \deg p + \deg q$, both in the order of multisets. The lemma `MvPolynomial.degreeOf_mul_le` is the same bound for one variable, and `MvPolynomial.totalDegree_pow` bounds the total degree of $p^n$ by $n$ times the total degree of $p$. A polynomial of total degree zero is a constant: `MvPolynomial.totalDegree_eq_zero_iff_eq_C` says that this happens exactly when $p = C(a_0)$ with $a_0$ the constant coefficient. The comparison lemmas `MvPolynomial.degreeOf_le_totalDegree` and `MvPolynomial.totalDegree_le_degrees_card` link the three measures. The lemma `MvPolynomial.coeff_eq_zero_of_totalDegree_lt` says that a coefficient beyond the total degree is zero.

The file also has `MvPolynomial.degreesLE`, the submodule of the polynomials whose degrees lie below a given multiset. Renaming with an injective map moves the degrees by the map (`MvPolynomial.degrees_rename_of_injective`), and a change of coefficients can only lower them (`MvPolynomial.degrees_map_le`).

#### Variables and supported polynomials

The finite set `MvPolynomial.vars` of $p$ is the set of variables that occur in $p$. Its definition is the underlying finset of `MvPolynomial.degrees`, and `MvPolynomial.vars_eq_support_biUnion_support` gives the other description: the union of the supports of the exponent vectors. The lemma `MvPolynomial.mem_vars_iff_degreeOf_ne_zero` says that $i$ occurs in $p$ exactly when the degree of $p$ in $x_i$ is not zero. Proof: $i$ is in the finset of the multiset `MvPolynomial.degrees` exactly when its multiplicity is not zero, and this multiplicity is the degree in $x_i$.

The set of variables behaves as a support: `MvPolynomial.vars_add_subset` and `MvPolynomial.vars_mul` say that the variables of $p + q$ and of $pq$ are among the variables of $p$ and $q$. A polynomial with no variable is a constant (`MvPolynomial.vars_eq_empty_iff_eq_C`). A renaming moves the variables by the map (`MvPolynomial.vars_rename`). In the other direction, `MvPolynomial.exists_rename_eq_of_vars_subset_range` says that a polynomial whose variables lie in the range of an injective map $f$ is a renaming by $f$. Two ring homomorphisms that agree on the constants and on the variables of $p$ agree on $p$ (`MvPolynomial.hom_congr_vars`).

The file `Mathlib.Algebra.MvPolynomial.Supported` puts these facts into a subalgebra. For a set $s \subseteq \sigma$, `MvPolynomial.supported` $R$ $s$ is the subalgebra of the polynomials whose variables lie in $s$, and `MvPolynomial.mem_supported` is this description. The lemma `MvPolynomial.supported_eq_range_rename` says that it is the range of the renaming along the inclusion $s \to \sigma$. Proof: a polynomial in the range has its variables in $s$ by `MvPolynomial.vars_rename`, and a polynomial with variables in $s$ is a renaming by `MvPolynomial.exists_rename_eq_of_vars_subset_range`. The lemma `MvPolynomial.supported_eq_adjoin_X` says that the subalgebra is also the algebra generated by the $x_i$ with $i \in s$. Since the renaming along an inclusion is injective, the subalgebra is isomorphic to `MvPolynomial s R`: this is `MvPolynomial.supportedEquivMvPolynomial`. Over a nontrivial ring the map $s \mapsto$ `MvPolynomial.supported` $R$ $s$ is strictly monotone (`MvPolynomial.supported_strictMono`).

#### Equivalences between polynomial rings

The file `Mathlib.Algebra.MvPolynomial.Equiv` collects the isomorphisms that change the set of variables. The table gives the main ones.

| Lean name | Statement |
| --- | --- |
| `MvPolynomial.isEmptyAlgEquiv` | $R[\emptyset] \cong R$ |
| `MvPolynomial.uniqueAlgEquiv` | $R[\sigma] \cong R[X]$ for a one point type $\sigma$ |
| `MvPolynomial.sumAlgEquiv` | $R[S_1 \sqcup S_2] \cong R[S_2][S_1]$ |
| `MvPolynomial.commAlgEquiv` | $R[S_2][S_1] \cong R[S_1][S_2]$ |
| `MvPolynomial.optionEquivLeft` | $R[\text{Option } S] \cong R[S][X]$ |
| `MvPolynomial.optionEquivRight` | $R[\text{Option } S] \cong R[X][S]$ |
| `MvPolynomial.finSuccEquiv` | $R[x_0, \dots, x_n] \cong R[x_1, \dots, x_n][X]$ |
| `MvPolynomial.mapAlgEquiv` | an isomorphism $A_1 \cong A_2$ gives $A_1[\sigma] \cong A_2[\sigma]$ |

The ring isomorphism `MvPolynomial.sumRingEquiv` is `MvPolynomial.sumAlgEquiv` without the algebra structure. The ring version of the first line is `MvPolynomial.isEmptyRingEquiv`, and the ring version of the last line is `MvPolynomial.mapEquiv`. The helper `MvPolynomial.mvPolynomialEquivMvPolynomial` builds an isomorphism between two rings of polynomials from two homomorphisms that are inverse on the constants and on the variables.

The isomorphism `MvPolynomial.finSuccEquiv` is the tool for induction on the number of variables. It sends $x_0$ to $X$ (`MvPolynomial.finSuccEquiv_X_zero`) and $x_{j+1}$ to the constant $C(x_j)$ (`MvPolynomial.finSuccEquiv_X_succ`). The degree of the image in $X$ is the degree of $f$ in $x_0$: this is `MvPolynomial.natDegree_finSuccEquiv` and, for $f \ne 0$, `MvPolynomial.degree_finSuccEquiv`. The general form `MvPolynomial.degreeOf_eq_natDegree` says that the degree of $p$ in $x_a$ is the degree in $X$ of the image of $p$ under `MvPolynomial.optionEquivLeft`, after the renaming that sends $a$ to the extra point. Proof: both sides are the supremum of the exponent of $x_a$ over the monomials of $p$, because the isomorphism sends the monomial $c \, x^m$ to $(c \, x^{m'}) X^{m(a)}$ with $m'$ the restriction of $m$.

In the other direction, `Polynomial.toMvPolynomial` $i$ sends a polynomial in one variable to the polynomial in the variable $x_i$. It is injective (`Polynomial.toMvPolynomial_injective`).

#### Derivations and partial derivatives

The file `Mathlib.Algebra.MvPolynomial.Derivation` proves the universal property of $R[\sigma]$ for derivations. Let $A$ be a module over $R[\sigma]$. A derivation $D \colon R[\sigma] \to A$ over $R$ is fixed by its values on the variables (`MvPolynomial.derivation_ext`), and any values are possible. The map `MvPolynomial.mkDerivation` builds the derivation from a function $f \colon \sigma \to A$, and `MvPolynomial.mkDerivation_X` says that it sends $x_i$ to $f(i)$. Together they give the linear isomorphism `MvPolynomial.mkDerivationEquiv` between functions $\sigma \to A$ and derivations. Proof sketch: on a monomial, the Leibniz rule forces $D(x^m) = \sum_i m(i) \, x^{m - e_i} f(i)$, so this formula defines the only candidate. The lemma `MvPolynomial.leibniz_iff_X` reduces the Leibniz rule for a linear map to the case of one factor a variable, and this case holds by the formula. Two derivations that agree on the variables in $s$ agree on `MvPolynomial.supported` $R$ $s$ (`MvPolynomial.derivation_eqOn_supported`).

The file `Mathlib.Algebra.MvPolynomial.PDeriv` defines the partial derivative `MvPolynomial.pderiv` $i$ as the derivation with values $\partial_i x_j = \delta_{ij}$ (`MvPolynomial.pderiv_X`, `MvPolynomial.pderiv_X_self`). It is a term of type `Derivation`, so additivity, `MvPolynomial.pderiv_mul` and `MvPolynomial.pderiv_C` are general facts on derivations. The coefficient formula `MvPolynomial.coeff_pderiv` says that the coefficient of $x^m$ in $\partial_i p$ is $(m(i) + 1)$ times the coefficient of $x^{m + e_i}$ in $p$. The lemma `MvPolynomial.pderiv_comm` says $\partial_i \partial_j p = \partial_j \partial_i p$. Proof: both sides are linear in $p$, so it is enough to check a monomial $x^m$. For $i = j$ there is nothing to prove. For $i \ne j$ both sides are $m(i) \, m(j) \, x^{m - e_i - e_j}$, or zero when $m(i) = 0$ or $m(j) = 0$. If $x_i$ does not occur in $p$, then $\partial_i p = 0$ (`MvPolynomial.pderiv_eq_zero_of_notMem_vars`). The file also records how partial derivatives pass through renaming, change of coefficients and `MvPolynomial.sumAlgEquiv`.

#### Division by a monomial

The file `Mathlib.Algebra.MvPolynomial.Division` divides by a monomial $x^s$. The quotient `MvPolynomial.divMonomial` keeps the monomials $x^m$ of $p$ with $s \le m$ and divides them by $x^s$. The remainder `MvPolynomial.modMonomial` keeps the other monomials. The lemma `MvPolynomial.coeff_divMonomial` says that the coefficient of $x^{s'}$ in the quotient is the coefficient of $x^{s + s'}$ in $p$. The identity `MvPolynomial.divMonomial_add_modMonomial` says $x^s \cdot (p \operatorname{div} x^s) + (p \operatorname{mod} x^s) = p$. Proof: compare the coefficient of $x^m$. If $s \le m$, the first term gives the coefficient of $x^m$ in $p$ and the second gives zero. If not, the first term gives zero and the second gives the coefficient of $x^m$ in $p$.

These operations come from the general division by an element of the exponent monoid in `AddMonoidAlgebra`, which Section 9 describes. They give the divisibility results for monomials. The lemma `MvPolynomial.X_dvd_iff_modMonomial_eq_zero` says that $x_i$ divides $p$ exactly when the remainder by $x_i$ is zero. The lemma `MvPolynomial.monomial_dvd_monomial` says that $c \, x^m$ divides $d \, x^n$ exactly when $c$ divides $d$ and either $m \le n$ or $d = 0$. Over a ring with cancellation, `MvPolynomial.X_dvd_mul_iff` says that $x_i$ divides $pq$ exactly when it divides $p$ or $q$, so $x_i$ is prime: this is `MvPolynomial.prime_X`. Proof: $x_i$ divides $p$ exactly when every monomial of $p$ contains $x_i$. Write $p = x_i p_1 + p_0$ and $q = x_i q_1 + q_0$ with $p_0, q_0$ free of $x_i$. Then $x_i$ divides $pq$ exactly when it divides $p_0 q_0$. Under the isomorphism with a polynomial ring in $x_i$, $p_0 q_0$ has degree zero in $x_i$, so it is divisible by $x_i$ only when it is zero, and a ring with cancellation has no zero divisors.

#### Expansion

The file `Mathlib.Algebra.MvPolynomial.Expand` defines `MvPolynomial.expand` $p$, the algebra map that sends each $x_i$ to $x_i^p$ (`MvPolynomial.expand_X`). On monomials it multiplies the exponent vector by $p$ (`MvPolynomial.expand_monomial`), so it multiplies the total degree by $p$ (`MvPolynomial.totalDegree_expand`). For $p > 0$ it is injective (`MvPolynomial.expand_inj`). The lemma `MvPolynomial.of_irreducible_expand` says that if the expansion of $f$ is irreducible, then $f$ is irreducible, because a factorization of $f$ expands to a factorization of its expansion. The file also proves that expansion commutes with substitution (`MvPolynomial.expand_aeval`), with renaming and with evaluation. This file is the multivariate version of the expansion of Chapter 8, and it serves the theory of the Frobenius map in characteristic $p$.

#### Units, nilpotents and domains

The file `Mathlib.Algebra.MvPolynomial.Nilpotent` describes units and nilpotents over a commutative ring. The lemma `MvPolynomial.isNilpotent_iff` says that $P$ is nilpotent exactly when all its coefficients are nilpotent. The lemma `MvPolynomial.isUnit_iff` says that $P$ is a unit exactly when its constant coefficient is a unit and all its other coefficients are nilpotent. Proof sketch: both results hold in one variable. A polynomial uses only finitely many variables, so `MvPolynomial.exists_rename_eq_of_vars_subset_range` puts it in $R[x_1, \dots, x_n]$, and `MvPolynomial.finSuccEquiv` gives an induction on $n$ from the one variable case. Over a reduced ring a unit is a constant unit (`MvPolynomial.isUnit_iff_eq_C_of_isReduced`), and the ring of polynomials is again reduced (`MvPolynomial.instIsReduced`). The file also gives the instances that make `MvPolynomial.C` and `algebraMap` local homomorphisms.

The file `Mathlib.Algebra.MvPolynomial.NoZeroDivisors` gives the exact formulas over a ring with no zero divisors. The degrees add (`MvPolynomial.degrees_mul_eq`) and the degree in each variable adds (`MvPolynomial.degreeOf_mul_eq`) when both factors are nonzero. It then classifies the divisors of a monomial over a domain: `MvPolynomial.dvd_monomial_iff_exists` says that a divisor of $a \, x^n$ with $a \ne 0$ is a monomial $b \, x^m$ with $m \le n$ and $b \mid a$. The special case `MvPolynomial.dvd_X_iff_exists` says that a divisor of $x_i$ is a unit constant or a unit times $x_i$.

#### The Schwartz-Zippel lemma

The file `Mathlib.Algebra.MvPolynomial.SchwartzZippel` bounds the number of zeros of a nonzero polynomial $p$ in $n$ variables over a domain $R$ on a grid $S^n$, for a finite set $S \subseteq R$. The lemma `MvPolynomial.schwartz_zippel_totalDegree` says
$$\frac{\#\{x \in S^n : p(x) = 0\}}{\#S^n} \le \frac{\deg p}{\#S},$$
with $\deg p$ the total degree. Proof sketch: induct on $n$ with `MvPolynomial.finSuccEquiv`. Write $p = \sum_{k \le d} p_k(x_1, \dots, x_n) \, x_0^k$ with $p_d \ne 0$. A point is a zero of $p$ only if it is a zero of $p_d$, which has total degree at most $\deg p - d$, or if $x_0$ is a root of a nonzero polynomial of degree $d$ in one variable, which has at most $d$ roots. Add the two bounds. The lemma `MvPolynomial.schwartz_zippel_sum_degreeOf` is the sharper form with one set $S_i$ for each variable, where the bound is $\sum_i \deg_{x_i} p / \#S_i$. The lemma `MvPolynomial.schwartz_zippel_sup_sum` is a form with a supremum over the support.

#### Common errors

1. Using `MvPolynomial.totalDegree` for an estimate in one variable. The total degree adds the exponents of all the variables. For the exponent of one variable use `MvPolynomial.degreeOf`, and for the whole exponent profile use `MvPolynomial.degrees`.
2. Writing a partial derivative as a plain function. `MvPolynomial.pderiv` $i$ is a `Derivation`, so `MvPolynomial.pderiv i p` is a coercion. The rules for sums, products and constants come from the general API of derivations, and `simp` finds them through this coercion.
3. Expecting `MvPolynomial.supported` to be a type of polynomials in fewer variables. It is a subalgebra of `MvPolynomial σ R`. To work in `MvPolynomial s R`, transport along `MvPolynomial.supportedEquivMvPolynomial`.

### Exercises

1. (A) Show that `MvPolynomial.degreeOf` $i$ $(x_i^3 x_j + x_j^5)$ is $3$ for $i \ne j$, and compute the total degree.
2. (A) Use `MvPolynomial.pderiv_X` and `MvPolynomial.pderiv_mul` to compute $\partial_i (x_i^2 x_j)$ for $i \ne j$.
3. (B) Show that $x_i$ divides $p$ exactly when every exponent vector $m$ in the support of $p$ has $m(i) \ge 1$. Use `MvPolynomial.X_dvd_iff_modMonomial_eq_zero`.
4. (B) Prove that $1 + 2x$ is a unit of $(\mathbb{Z}/4\mathbb{Z})[x, y]$ with `MvPolynomial.isUnit_iff`, and give its inverse.
5. (B) Show that `MvPolynomial.supported` $R$ $s$ $\cap$ `MvPolynomial.supported` $R$ $t$ is `MvPolynomial.supported` $R$ $(s \cap t)$.
6. (C) Use `MvPolynomial.schwartz_zippel_totalDegree` to show that a nonzero polynomial over an infinite domain does not vanish on all of $R^n$.

### Reference

<?reference?>
