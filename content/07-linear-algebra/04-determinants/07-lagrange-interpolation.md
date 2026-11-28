---
title: Lagrange interpolation
kind: api
modules:
  - Mathlib.LinearAlgebra.Lagrange
explains:
  E2: [Lagrange.basisDivisor, Lagrange.basis, Lagrange.eval_basis_self, Lagrange.sum_basis, Lagrange.interpolate, Lagrange.eval_interpolate_at_node, Lagrange.degree_interpolate_lt, Lagrange.funEquivDegreeLT, Lagrange.nodal, Lagrange.nodalWeight]
  E1: auto
families: []
requires: [V03, V06]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Lagrange interpolation

### Overview

Let $F$ be a field, and let $x_1, \dots, x_n$ be distinct elements of $F$ with values $r_1, \dots, r_n \in F$. There is exactly one polynomial $p$ of degree less than $n$ with $p(x_i) = r_i$ for all $i$. In the language of linear algebra, the evaluation map from the polynomials of degree less than $n$ to $F^n$ is a linear isomorphism. Its matrix in the basis $1, X, \dots, X^{n-1}$ is the Vandermonde matrix, whose determinant $\prod_{i < j} (x_j - x_i)$ is not zero; this is why the result is in the chapter on determinants. The inverse map has an explicit form, the formula of Lagrange.

The module `Mathlib.LinearAlgebra.Lagrange` states these facts with a finite set $s$ of indices and a map $v$ from indices to nodes, injective on $s$. It also has the second form of the formula, with the nodal polynomial $\prod_i (X - x_i)$ and the barycentric weights.

### The library around it

#### Uniqueness

The first part of the module, in the namespace Polynomial, proves uniqueness over an integral domain. A nonzero polynomial of degree less than $n$ has fewer than $n$ roots, so a polynomial of degree less than $n$ that vanishes at $n$ distinct points is zero. Mathlib proves it with the Vandermonde matrix of Chapter 3 instead: the values at the points are the product of the Vandermonde matrix with the vector of coefficients, and this matrix has a nonzero determinant. Two polynomials with the difference of degree less than $n$ and the same values at $n$ points are equal. The forms of these statements for an indexed family of points need the hypothesis `Set.InjOn v s`.

The existence of an interpolating polynomial for any family of points, without a bound on the degree, is `Polynomial.exists_eval_eq_iff`: a polynomial with $q(x_i) = y_i$ for all $i$ exists if and only if $x_i = x_j$ implies $y_i = y_j$.

#### The Lagrange basis

**Definition (`Lagrange.basisDivisor`).** For $x, y \in F$, `Lagrange.basisDivisor x y` is the polynomial $(x - y)^{-1} (X - y)$.

For $x \ne y$, it has degree $1$, value $1$ at $x$ (`Lagrange.eval_basisDivisor_left_of_ne`) and value $0$ at $y$ (`Lagrange.eval_basisDivisor_right`). For $x = y$ it is $0$, since $0^{-1} = 0$ in a field of Mathlib (`Lagrange.basisDivisor_self`).

**Definition (`Lagrange.basis`).** For a finite set $s$ of indices, nodes $v$ and $i \in s$, `Lagrange.basis s v i` is the product of `Lagrange.basisDivisor (v i) (v j)` over $j \in s$ with $j \ne i$, that is,
$$L_i = \prod_{j \in s,\, j \ne i} \frac{X - v_j}{v_i - v_j}.$$

The value of $L_i$ at $v_j$ is $0$ for $j \ne i$ (`Lagrange.eval_basis_of_ne`), because one factor vanishes.

**Theorem (`Lagrange.eval_basis_self`).** If $v$ is injective on $s$ and $i \in s$, then $L_i(v_i) = 1$.

*Proof.* Each factor $(v_i - v_j)^{-1}(v_i - v_j)$ is $1$, because $v_i \ne v_j$ for $j \ne i$. $\square$

The degree of $L_i$ is $|s| - 1$ (`Lagrange.degree_basis`), and its leading coefficient is $\prod_{j \ne i} (v_i - v_j)^{-1}$ (`Lagrange.leadingCoeff_basis`). For two nodes, $L_i$ is one basis divisor (`Lagrange.basis_pair_left`).

**Theorem (`Lagrange.sum_basis`).** If $v$ is injective on a nonempty set $s$, then $\sum_{j \in s} L_j = 1$.

*Proof.* Both sides have degree less than $|s|$, and both have the value $1$ at each node $v_i$, since $L_i(v_i) = 1$ and $L_j(v_i) = 0$ for $j \ne i$. By uniqueness they are equal. $\square$

#### The interpolation map

**Definition (`Lagrange.interpolate`).** `Lagrange.interpolate s v` is the $F$-linear map from the values $r : \iota \to F$ to the polynomials, with `Lagrange.interpolate s v r` equal to $\sum_{i \in s} r_i L_i$.

The formula is `Lagrange.interpolate_apply`, and the fully expanded form, with the product of the factors $X - v_j$ and the scalar $r_i / \prod_{j \ne i} (v_i - v_j)$, is `Lagrange.interpolate_eq_sum`. The values $r_i$ for $i \notin s$ do not matter (`Lagrange.interpolate_eq_of_values_eq_on`).

**Theorem (`Lagrange.eval_interpolate_at_node`).** If $v$ is injective on $s$ and $i \in s$, the value of `Lagrange.interpolate s v r` at $v_i$ is $r_i$.

*Proof.* The value is $\sum_{j \in s} r_j L_j(v_i) = r_i$, by the values of the basis polynomials at the nodes. $\square$

**Theorem (`Lagrange.degree_interpolate_lt`).** If $v$ is injective on $s$, the interpolating polynomial has degree less than $|s|$.

The two theorems give existence, and the uniqueness of the first subsection gives that each polynomial $f$ of degree less than $|s|$ is the interpolation of its own values at the nodes. The module states this with the lemmas in the namespace Lagrange whose names begin with eq_interpolate. The map is injective on the values at the nodes: `Lagrange.interpolate_eq_iff_values_eq_on`. The interpolation of the constant $1$ is $1$ (`Lagrange.interpolate_one`).

**Definition (`Lagrange.funEquivDegreeLT`).** If $v$ is injective on $s$, `Lagrange.funEquivDegreeLT` is the linear isomorphism from `Polynomial.degreeLT F s.card`, the space of polynomials of degree less than $|s|$, to the functions $s \to F$. It sends $f$ to its values at the nodes, and its inverse is the interpolation.

This is the statement of the overview in the form of a linear equivalence, and with it the polynomials of degree less than $n$ have dimension $n$. The interpolation also gives recursive formulas, used to build the polynomial one node at a time: `Lagrange.interpolate_eq_add_interpolate_erase` writes the interpolation on $s$ with the interpolations on $s$ without $i$ and on $s$ without $j$, which is the scheme of Neville. The coefficients of the interpolation have formulas: `Lagrange.leadingCoeff_eq_sum` gives the leading coefficient of a polynomial of degree $|s| - 1$ as the divided difference $\sum_i f(v_i) / \prod_{j \ne i} (v_i - v_j)$, and `Lagrange.iterate_derivative_interpolate` gives its derivatives.

#### The nodal polynomial and the barycentric form

**Definition (`Lagrange.nodal`).** For a commutative ring $R$, a finite set $s$ and nodes $v$, `Lagrange.nodal s v` is the polynomial $\ell = \prod_{i \in s} (X - v_i)$.

It is monic of degree $|s|$ (`Lagrange.nodal_monic`, `Lagrange.degree_nodal`), its roots are the nodes (`Lagrange.eval_nodal_at_node`), and `Lagrange.nodal_eq_mul_nodal_erase` removes one factor. Its derivative is $\sum_i \prod_{j \ne i} (X - v_j)$ (`Lagrange.derivative_nodal`). For a finite subgroup $G$ of the units of a field, the nodal polynomial of the elements of $G$ is $X^{|G|} - 1$ (`Lagrange.nodal_subgroup_eq_X_pow_card_sub_one`).

**Definition (`Lagrange.nodalWeight`).** For $i \in s$, `Lagrange.nodalWeight s v i` is the barycentric weight $w_i = \prod_{j \in s,\, j \ne i} (v_i - v_j)^{-1}$.

By `Lagrange.nodalWeight_eq_eval_derivative_nodal`, $w_i = \ell'(v_i)^{-1}$. With the weights, $L_i = w_i \, \ell / (X - v_i)$ (`Lagrange.basis_eq_prod_sub_inv_mul_nodal_div`), so the interpolation is
$$p = \sum_{i \in s} w_i \frac{\ell}{X - v_i} r_i,$$
which is `Lagrange.interpolate_eq_nodalWeight_mul_nodal_div_X_sub_C`. At a point $x$ that is not a node, the value is $\ell(x) \sum_i w_i r_i / (x - v_i)$ (`Lagrange.eval_interpolate_not_at_node`). Divide this by the same formula for the constant values $r_i = 1$, whose interpolation is $1$; the result is the barycentric formula
$$p(x) = \frac{\sum_i w_i r_i / (x - v_i)}{\sum_i w_i / (x - v_i)},$$
which is `Lagrange.eval_interpolate_not_at_node'`. The weights do not depend on the values $r$, so they are computed once for many interpolations.

#### Common errors

1. The basis polynomials and the interpolation need the nodes to be distinct on $s$. Most lemmas take the hypothesis `Set.InjOn v s`; without it, a factor $(v_i - v_j)^{-1}$ is $0$, and $L_i$ is zero.
2. `Lagrange.basis` is a protected name. Inside the namespace Lagrange write `Lagrange.basis` in full, since the short name alone does not refer to it.
3. `Lagrange.interpolate s v` is a linear map, so apply it to the vector of values: write `Lagrange.interpolate s v r`, not a function of two arguments.

### Exercises

1. (A) Compute `Lagrange.basis` for the nodes $0, 1, 2$ of $\mathbb{Q}$ and check `Lagrange.sum_basis` for them.
2. (A) Find the polynomial of degree less than $3$ over $\mathbb{Q}$ with the values $1, 3, 7$ at $0, 1, 2$.
3. (B) Show that `Lagrange.nodal s v` vanishes at each node, and that it is not zero at each other point of a field.
4. (B) Prove that the interpolation of the values $r_i = v_i$ is the polynomial $X$, if $s$ has at least two elements.
5. (B) Use `Lagrange.funEquivDegreeLT` to prove that `Polynomial.degreeLT F n` has dimension $n$ over a field with at least $n$ elements.
6. (C) Compute the barycentric weights for the nodes of the group of the fourth roots of unity in $\mathbb{C}$, and check that $w_i = v_i / 4$.

### Reference

<?reference?>
