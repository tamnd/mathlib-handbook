---
title: Characteristic polynomials of linear families and linear recurrences
kind: api
modules:
  - Mathlib.Algebra.Module.LinearMap.Polynomial
  - Mathlib.Algebra.LinearRecurrence
explains:
  E2: [Matrix.toMvPolynomial_eval_eq_apply, LinearMap.polyCharpoly_map_eq_charpoly, LinearMap.polyCharpoly_coeff_isHomogeneous, LinearMap.nilRank, LinearMap.exists_isNilRegular, LinearRecurrence.toInit, LinearRecurrence.solSpace_rank, LinearRecurrence.geom_sol_iff_root_charPoly]
  E1: auto
families: []
requires: [V04, V05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Characteristic polynomials of linear families and linear recurrences

### Overview

This section has two applications of the characteristic polynomial. The first is about a family of endomorphisms $\varphi(x)$ that depends linearly on a parameter $x$ in a free module $L$. The characteristic polynomial of $\varphi(x)$ is then a polynomial in the coordinates of $x$, and its coefficients are homogeneous. This gives the nil rank of the family and the nil regular parameters, which Lie theory uses to define the rank of a Lie algebra and to find Cartan subalgebras. The second application is the classical theory of linear recurrences: the sequences with $u_{n+d} = \sum_{i<d} a_i u_{n+i}$ form a module of rank $d$, and a geometric sequence $q^n$ is a solution exactly when $q$ is a root of the characteristic polynomial of the recurrence.

### The library around it

#### Matrices as linear polynomials

Let $M$ be an $m \times n$ matrix over a commutative ring $R$. Each row of $M$ gives a linear polynomial in the variables $X_j$, $j \in n$: the row $i$ gives $\sum_j M_{ij} X_j$. This family is `Matrix.toMvPolynomial M`, with values in `MvPolynomial n R`.

**Theorem.** The evaluation of the polynomial of row $i$ at a vector $c$ is the entry $i$ of $M c$.

*Proof.* The evaluation of $\sum_j M_{ij} X_j$ at $c$ is $\sum_j M_{ij} c_j$, which is $(M c)_i$ by the definition of the product with a vector. $\square$

This is `Matrix.toMvPolynomial_eval_eq_apply`. The polynomials are homogeneous of degree $1$ (`Matrix.toMvPolynomial_isHomogeneous`) and have no constant term (`Matrix.toMvPolynomial_constantCoeff`). The identity matrix gives the variables (`Matrix.toMvPolynomial_one`). The product of matrices is a substitution: `Matrix.toMvPolynomial_mul` says that the polynomials of $M N$ are the polynomials of $M$ with $N$ substituted for the variables.

For a linear map $f : M_1 \to M_2$ with bases $b_1$ and $b_2$, the same construction applied to the matrix of $f$ is `LinearMap.toMvPolynomial b₁ b₂ f`. The evaluation lemma is `LinearMap.toMvPolynomial_eval_eq_apply`, and the rules `LinearMap.toMvPolynomial_id`, `LinearMap.toMvPolynomial_comp` and `LinearMap.toMvPolynomial_baseChange` are as for matrices.

#### The characteristic polynomial of a linear family

Let $L$ and $M$ be finite free modules over a commutative ring $R$, and let $\varphi : L \to \operatorname{End}_R(M)$ be a linear map. Fix a basis $b$ of $L$ indexed by $\iota$. The polynomial `LinearMap.polyCharpoly φ b` lies in $(\operatorname{MvPolynomial}\ \iota\ R)[X]$: it is a polynomial in $X$ whose coefficients are polynomials in the coordinates of $x$.

**Theorem.** For each $x \in L$, the evaluation of `LinearMap.polyCharpoly φ b` at the coordinates of $x$ is the characteristic polynomial of $\varphi(x)$.

*Proof sketch.* Choose a basis of $M$. The matrix of $\varphi(x)$ is $\sum_i x_i A_i$, where $A_i$ is the matrix of $\varphi(b_i)$, so its entries are linear polynomials in the coordinates $x_i$. The characteristic polynomial of a matrix is a universal polynomial in its entries, `Matrix.charpoly.univ`. Substitution of the linear polynomials into this universal polynomial gives `polyCharpoly`, and evaluation at $x$ gives the characteristic polynomial of the matrix of $\varphi(x)$. This does not depend on the basis of $M$, since the characteristic polynomial does not. $\square$

This is `LinearMap.polyCharpoly_map_eq_charpoly`, and `LinearMap.polyCharpoly_coeff_eval` is the form for one coefficient. The polynomial is monic of degree $\dim M$ (`LinearMap.polyCharpoly_monic`, `LinearMap.polyCharpoly_natDegree`).

**Theorem.** Let $\dim M = d$. The coefficient of $X^i$ in `LinearMap.polyCharpoly φ b` is a homogeneous polynomial of degree $d - i$ in the coordinates.

*Proof sketch.* For $t \in R$, the matrix of $\varphi(t x)$ is $t$ times the matrix of $\varphi(x)$. The characteristic polynomial of $t A$ is $\det(X - t A)$, and its coefficient of $X^i$ is $t^{d - i}$ times the coefficient of $\det(X - A)$. The proof in Mathlib works with the universal polynomial, where this scaling is an identity of polynomials. $\square$

This is `LinearMap.polyCharpoly_coeff_isHomogeneous`. The behavior under base change is `LinearMap.polyCharpoly_baseChange`.

#### Nil rank and nil regular elements

The nil rank `LinearMap.nilRank φ` is the smallest $n$ such that the coefficient of $X^n$ in `LinearMap.polyCharpoly φ b` is a nonzero polynomial. It does not depend on $b$ (`LinearMap.nilRank_eq_polyCharpoly_natTrailingDegree`). For each $x$, the characteristic polynomial of $\varphi(x)$ has no nonzero coefficient below $X^n$: `LinearMap.nilRank_le_natTrailingDegree_charpoly`. So $X^{\text{nilRank}}$ divides each of these polynomials. The nil rank is at most $\dim M$ (`LinearMap.nilRank_le_finrank`).

An element $x \in L$ is nil regular, `LinearMap.IsNilRegular φ x`, when the coefficient of $X^{\text{nilRank}}$ in the characteristic polynomial of $\varphi(x)$ is not zero (`LinearMap.isNilRegular_def`). Equivalently, the trailing degree of this polynomial is the nil rank (`LinearMap.isNilRegular_iff_natTrailingDegree_charpoly_eq_nilRank`).

**Theorem.** If $R$ is an infinite domain, then nil regular elements exist.

*Proof.* The coefficient of $X^{\text{nilRank}}$ is a nonzero polynomial in the coordinates. A nonzero polynomial over an infinite domain has a point where it does not vanish. At this point $x$, the coefficient of $X^{\text{nilRank}}$ in the characteristic polynomial of $\varphi(x)$ is not zero. $\square$

This is `LinearMap.exists_isNilRegular`, and `LinearMap.exists_isNilRegular_of_finrank_le_card` needs only that $R$ has at least $\dim M$ elements. For a Lie algebra $L$ and its adjoint map $\varphi = \operatorname{ad}$, the nil rank is the rank of $L$, and the nil regular elements are the regular elements whose generalized $0$-eigenspaces are Cartan subalgebras.

#### Linear recurrences

A linear recurrence of order $d$ over a commutative ring $R$ is a structure `LinearRecurrence R` with the fields `LinearRecurrence.order` and `LinearRecurrence.coeffs`, a function `Fin E.order → R`. A sequence $u : \mathbb{N} \to R$ is a solution, `LinearRecurrence.IsSolution E u`, when
$$u_{n+d} = \sum_{i<d} a_i u_{n+i}$$
for each $n$. The solutions form the submodule `LinearRecurrence.solSpace E` of $\mathbb{N} \to R$ (`LinearRecurrence.is_sol_iff_mem_solSpace`). The Fibonacci sequence is the solution of the recurrence with $d = 2$ and $a = (1, 1)$ that starts with $0, 1$.

**Theorem.** A solution is determined by its first $d$ terms, and each choice of the first $d$ terms gives a solution. So the map from solutions to their first $d$ terms is a linear equivalence $\operatorname{Sol}(E) \simeq R^d$.

*Proof.* Given the first $d$ terms, the recurrence defines each later term from the $d$ terms before it, by strong induction. This is the solution `LinearRecurrence.mkSol E init`, which is a solution (`LinearRecurrence.is_sol_mkSol`) with the given first terms (`LinearRecurrence.mkSol_eq_init`). Two solutions with the same first $d$ terms agree at each $n$, by strong induction on $n$. The map to the first $d$ terms is linear, and these two facts make it bijective. $\square$

This is `LinearRecurrence.toInit`. It gives the basis `LinearRecurrence.basis` of the solution space and `LinearRecurrence.solSpace_rank`: over a ring with the strong rank condition, the solution space has rank $d$. The linear map `LinearRecurrence.tupleSucc` shifts a window of $d$ consecutive terms by one step; its matrix is the companion matrix of the recurrence.

The characteristic polynomial of the recurrence is `LinearRecurrence.charPoly E`, the polynomial $X^d - \sum_{i<d} a_i X^i$. It is monic of degree $d$ (`LinearRecurrence.charPoly_monic`, `LinearRecurrence.charPoly_degree_eq_order`).

**Theorem.** The geometric sequence $n \mapsto q^n$ is a solution if and only if $q$ is a root of the characteristic polynomial.

*Proof.* The sequence is a solution when $q^{n+d} = \sum_i a_i q^{n+i}$ for each $n$, that is $q^n \chi(q) = 0$ for each $n$, where $\chi$ is the characteristic polynomial. The case $n = 0$ gives $\chi(q) = 0$, and conversely $\chi(q) = 0$ gives the equation for each $n$. $\square$

This is `LinearRecurrence.geom_sol_iff_root_charPoly`. If $\chi$ has $d$ distinct roots $q_1, \dots, q_d$ in a field, the $d$ geometric sequences are linearly independent, by the Vandermonde determinant of Chapter 4, so they form a basis of the solution space. This gives the closed form of the Fibonacci numbers with the roots $(1 \pm \sqrt{5}) / 2$.

#### Common errors

1. Writing the recurrence in the wrong order. In `LinearRecurrence.IsSolution`, the coefficient `coeffs i` multiplies $u_{n+i}$, the term $i$ steps after $n$, and the new term is $u_{n+d}$. For $u_{n+2} = u_{n+1} + 2 u_n$ the coefficients are `![2, 1]`.
2. Expecting the nil rank to be the nilpotency index of some $\varphi(x)$. It is the trailing degree of the generic characteristic polynomial, which is the generic dimension of the generalized $0$-eigenspace, and not a degree of nilpotency.
3. Using `LinearRecurrence.solSpace_rank` over a ring without the strong rank condition. The equivalence `LinearRecurrence.toInit` holds over any commutative semiring, but the statement on the rank needs a ring where ranks behave.

### Exercises

1. (A) Write the recurrence $u_{n+2} = u_{n+1} + u_n$ as a `LinearRecurrence ℚ` and compute its characteristic polynomial.
2. (A) For $M = \begin{pmatrix} 1 & 2 \\ 0 & 3 \end{pmatrix}$, write the two polynomials of `Matrix.toMvPolynomial M`.
3. (B) Find all solutions over $\mathbb{Q}$ of $u_{n+2} = 5 u_{n+1} - 6 u_n$.
4. (B) Let $\varphi : \mathbb{Q}^2 \to \operatorname{End}(\mathbb{Q}^2)$ send $(x, y)$ to the matrix $\begin{pmatrix} x & y \\ 0 & x \end{pmatrix}$. Compute the characteristic polynomial of $\varphi(x, y)$, check that its coefficients are homogeneous, and find the nil rank.
5. (B) Show that the shift map $u \mapsto (n \mapsto u_{n+1})$ maps the solution space of a linear recurrence into itself.
6. (C) Show that the sequences $n \mapsto n q^n$ and $n \mapsto q^n$ are solutions of $u_{n+2} = 2 q u_{n+1} - q^2 u_n$ for $q \ne 0$, and that they form a basis of its solution space over a field.

### Reference

<?reference?>
