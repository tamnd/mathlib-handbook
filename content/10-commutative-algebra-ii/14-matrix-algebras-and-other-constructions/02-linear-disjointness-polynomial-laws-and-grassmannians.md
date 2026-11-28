---
title: Linear disjointness, quadratic algebras, polynomial laws and Grassmannians
kind: api
modules:
  - Mathlib.RingTheory.LinearDisjoint
  - Mathlib.RingTheory.QuadraticAlgebra
  - Mathlib.RingTheory.PolynomialLaw.Basic
  - Mathlib.RingTheory.Grassmannian
explains:
  E2: [Subalgebra.LinearDisjoint, Subalgebra.linearDisjoint_iff_injective, Subalgebra.LinearDisjoint.finrank_sup_of_free, Subalgebra.LinearDisjoint.of_finrank_coprime_of_free, Subalgebra.LinearDisjoint.of_isField, Algebra.norm_quadraticAlgebra_apply, Algebra.discr_quadraticAlgebra, PolynomialLaw, PolynomialLaw.ground, Module.Grassmannian]
  E1: auto
families: []
requires: [V08, V10.C08, V10.C12]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Linear disjointness, quadratic algebras, polynomial laws and Grassmannians

### Overview

This section collects four constructions that use tensor products of algebras and modules.

1. Two subalgebras $A$ and $B$ of an $R$-algebra $S$ are linearly disjoint if the multiplication map $A \otimes_R B \to S$ is injective. For fields, this is the condition that makes the degree of a compositum the product of the degrees.
2. The quadratic algebra $R[\omega]$ with $\omega^2 = a + b\omega$ is free of rank $2$ over $R$. Its trace, norm and discriminant have explicit formulas.
3. A polynomial law from $M$ to $N$ is a family of maps $S \otimes_R M \to S \otimes_R N$, one for each $R$-algebra $S$, natural in $S$. It is the right notion of a polynomial map between modules that need not be free.
4. The Grassmannian $G(k, M; R)$ is the set of submodules of $M$ whose quotient is projective of constant rank $k$. As a functor of $R$-algebras, it is the functor that the Grassmannian scheme represents.

### The library around it

#### Linearly disjoint subalgebras

The module `Mathlib.RingTheory.LinearDisjoint` defines `Subalgebra.LinearDisjoint A B` for subalgebras $A$ and $B$ of $S$. The definition is linear disjointness of the underlying submodules, `Submodule.LinearDisjoint`, and `Subalgebra.linearDisjoint_iff_injective` gives the form with the multiplication map `Subalgebra.mulMap`. When $A$ and $B$ are linearly disjoint, `Subalgebra.LinearDisjoint.mulMap` is an isomorphism $A \otimes_R B \cong A \sqcup B$ onto the subalgebra that they generate.

The main tool is the passage between bases and linear disjointness.

1. `Subalgebra.LinearDisjoint.linearIndependent_mul_of_flat`: if $A$ and $B$ are linearly disjoint and one of them is flat, then the products $a_ib_j$ of independent families are independent.
2. `Subalgebra.LinearDisjoint.of_basis_mul`: if $\{a_i\}$ and $\{b_j\}$ are bases of $A$ and $B$ and the products $a_ib_j$ are independent, then $A$ and $B$ are linearly disjoint.

For free modules of finite rank, this gives a rank formula and a criterion.

**Theorem.** Let $S$ be commutative and let $A$, $B$ be free of finite rank over $R$. If $A$ and $B$ are linearly disjoint, then $\operatorname{rank}(A \sqcup B) = \operatorname{rank} A \cdot \operatorname{rank} B$. This is `Subalgebra.LinearDisjoint.finrank_sup_of_free`. Conversely, if the ranks are coprime and some auxiliary modules are free, then $A$ and $B$ are linearly disjoint, `Subalgebra.LinearDisjoint.of_finrank_coprime_of_free`.

*Proof sketch of the criterion over fields.* The compositum $A \sqcup B$ contains $A$ and $B$, so its degree over $R$ is divisible by $\operatorname{rank} A$ and by $\operatorname{rank} B$. It is at most the product, since $A \sqcup B$ is spanned over $A$ by a basis of $B$. Coprimality forces equality, and then the multiplication map is a surjection between spaces of the same finite dimension. $\square$

Other results:

1. Over a field $R$, linearly disjoint subalgebras meet in $R$, `Subalgebra.LinearDisjoint.inf_eq_bot`.
2. If $S$ is a domain, then $A \otimes_R B$ is a domain, `Subalgebra.LinearDisjoint.isDomain`.
3. If $A \otimes_R B$ is a field, then $A$ and $B$ are linearly disjoint in each $S$, `Subalgebra.LinearDisjoint.of_isField`.
4. If $A$ and $B$ are flat and both transcendental over $R$, then $A \otimes_R B$ is not a field, `Algebra.TensorProduct.not_isField_of_transcendental`.
5. If $A \sqcup B = S$ and $B$ is free of finite rank, the norm and the trace from $B$ to $R$ agree with those from $S$ to $A$, `Subalgebra.LinearDisjoint.norm_algebraMap` and `Subalgebra.LinearDisjoint.trace_algebraMap`.

The version for intermediate fields, `IntermediateField.LinearDisjoint`, is in Volume 11.

#### Quadratic algebras

The structure `QuadraticAlgebra R a b` has elements $x + y\omega$ with $x, y \in R$ and $\omega^2 = a + b\omega$. It is isomorphic to $R[X]/(X^2 - bX - a)$, and $\{1, \omega\}$ is the basis `QuadraticAlgebra.basis a b`. The Gaussian integers are the case $a = -1$, $b = 0$ over $\mathbb{Z}$.

The module `Mathlib.RingTheory.QuadraticAlgebra` connects the explicit formulas with the general norm, trace and discriminant of an algebra. For $z = x + y\omega$, multiplication by $z$ sends $1$ to $x + y\omega$ and $\omega$ to $ay + (x + by)\omega$. So the matrix of $z$ in the basis $\{1, \omega\}$ is
$$\begin{pmatrix} x & ay \\ y & x + by \end{pmatrix},$$
which is `Algebra.leftMulMatrix_quadraticAlgebra`. Then:

| Lean name | Statement |
|---|---|
| `Algebra.trace_quadraticAlgebra_apply` | $\operatorname{Tr}(z) = 2x + by$ |
| `Algebra.norm_quadraticAlgebra_apply` | $N(z) = x^2 + bxy - ay^2$ |
| `Algebra.discr_quadraticAlgebra` | the discriminant of $\{1, \omega\}$ is $b^2 + 4a$ |
| `QuadraticAlgebra.polynomial_discr_eq_discr` | $b^2 + 4a$ is the discriminant of $X^2 - bX - a$ |

The discriminant is $\det\begin{pmatrix} 2 & b \\ b & 2a + b^2 \end{pmatrix} = b^2 + 4a$, the determinant of the trace form.

#### Polynomial laws

The module `Mathlib.RingTheory.PolynomialLaw.Basic` defines `PolynomialLaw R M N`, with notation `M →ₚₗ[R] N`. A law $f$ gives, for each $R$-algebra $S$, a map `PolynomialLaw.toFun S f : S ⊗[R] M → S ⊗[R] N`. The maps are natural: for an algebra map $h : S \to T$, the square with $h \otimes M$ and $h \otimes N$ commutes, `PolynomialLaw.isCompat`.

The definition only asks for algebras $S$ in the universe of $R$. The extension to all universes uses two facts. Each element of $S \otimes_R M$ comes from $P \otimes_R M$ for a polynomial ring $P$ in finitely many variables, `PolynomialLaw.exists_lift`. Each finitely generated subalgebra is the image of such a ring, `PolynomialLaw.exists_range_φ_eq_of_fg`.

The ground map `PolynomialLaw.ground f : M → N` is the case $S = R$. It does not determine $f$ in general. For example, over $R = \mathbb{F}_2$ the law $x \mapsto x^2 - x$ on $M = N = R$ has zero ground map but is not zero over $\mathbb{F}_2[t]$. The values of $f$ on all algebras $S$ hold the full information.

Polynomial laws form an $R$-module, the instance `PolynomialLaw.instModule`, and they compose, `PolynomialLaw.comp` with `PolynomialLaw.toFun_comp_apply`. The identity is `PolynomialLaw.id`. Linear maps and quadratic forms give polynomial laws of degree $1$ and $2$.

#### Grassmannians

The structure `Module.Grassmannian R M k` in `Mathlib.RingTheory.Grassmannian` is a submodule $N \subseteq M$ with three properties of $M/N$:

1. $M/N$ is finitely generated, `Module.Grassmannian.finite_quotient`;
2. $M/N$ is projective, `Module.Grassmannian.projective_quotient`;
3. $M/N$ has rank $k$ at each prime, `Module.Grassmannian.rankAtStalk_eq`, with the rank function `Module.rankAtStalk` of Chapter 12.

For an algebra map $A \to B$, the base change `Module.Grassmannian.map` sends $N \subseteq A \otimes_R M$ to the kernel of $B \otimes_R M \to B \otimes_A (A \otimes_R M)/N$. This is functorial, `Module.Grassmannian.map_id` and `Module.Grassmannian.map_comp`, so `Module.Grassmannian.functor k` is a functor from `CommAlgCat R` to types.

The definition uses quotients, not subspaces, as in algebraic geometry. Over a field $F$ and a space $V$ of dimension $n$, the subspaces of dimension $k$ correspond to the quotients of dimension $n - k$. So the classical Grassmannian is $G(n - k, V; F)$.

#### Common errors

1. `Subalgebra.LinearDisjoint` is not symmetric by definition in a ring that is not commutative. Use `Subalgebra.LinearDisjoint.symm` only for commutative $S$, and the forms with the suffix of_commute in general.
2. In `QuadraticAlgebra R a b` the relation is $\omega^2 = a + b\omega$, with $a$ first. The ring $\mathbb{Z}[\sqrt{d}]$ is `QuadraticAlgebra ℤ d 0`, not `QuadraticAlgebra ℤ 0 d`.
3. `Module.Grassmannian R M k` is about quotients of rank $k$. A submodule of rank $k$ in $F^n$ is an element of `Module.Grassmannian F (Fin n → F) (n - k)`.

### Exercises

1. (A) Compute the trace and the norm of $3 + 2i$ in $\mathbb{Z}[i]$ with the formulas above.
2. (A) Show that $\mathbb{Q}(\sqrt{2})$ and $\mathbb{Q}(\sqrt[3]{2})$ are linearly disjoint over $\mathbb{Q}$ with the coprime criterion.
3. (B) Show that $\mathbb{Q}(\sqrt{2})$ and $\mathbb{Q}(\sqrt{8})$ are not linearly disjoint over $\mathbb{Q}$ in $\mathbb{R}$, and compute the kernel of the multiplication map.
4. (B) Show that the discriminant of $\mathbb{Z}[\omega]$ with $\omega^2 = \omega + 1$ is $5$.
5. (B) Show that for $M = R^n$ and $k = 0$, the Grassmannian $G(0, M; R)$ has one element.
6. (C) Show that $G(n - 1, F^n; F)$ is in bijection with the lines through the origin in $F^n$, for a field $F$.

### Reference

<?reference?>
