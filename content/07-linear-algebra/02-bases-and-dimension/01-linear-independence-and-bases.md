---
title: Linear independence and bases
kind: theory
modules:
  - Mathlib.LinearAlgebra.LinearIndependent.Defs
  - Mathlib.LinearAlgebra.Basis.Defs
  - Mathlib.LinearAlgebra.Basis.Basic
  - Mathlib.LinearAlgebra.StdBasis
explains:
  E3: [LinearIndependent, Module.Basis]
  E2: [linearIndependent_iff, Fintype.linearIndependent_iff, LinearIndependent.pair_iff, Module.Basis.repr, Module.Basis.mk, Module.Basis.constr, Module.Basis.equivFun, Pi.basisFun]
  E1: auto
families: []
requires: [V07.C01, V03]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Linear independence and bases

### Overview

A family of vectors spans a module if each vector is a linear combination of the family. It is linearly independent if no nontrivial combination is zero. A basis is a family with both properties. Then each vector is a combination of the basis in exactly one way, and the coefficients are its coordinates. A basis turns a module into a module of columns, and it turns questions about vectors into computations with numbers.

This section defines linear independence and bases for a module over a ring, proves that a basis is the same as a linear equivalence with the module $R^{(\iota)}$ of finitely supported coordinates, and proves that a linear map is fixed by its values on a basis, which can be chosen freely. Over a field each module has a basis. That theorem and the count of the basis vectors are the subject of Section 2.

### Definitions

**Definition (Linear independence).** Let $M$ be an $R$-module and $(v_i)_{i \in \iota}$ a family of vectors of $M$. The family is linearly independent if, for each finite set $F \subseteq \iota$ and each choice of scalars $(c_i)_{i \in F}$,
$$\sum_{i \in F} c_i v_i = 0 \quad \Longrightarrow \quad c_i = 0 \text{ for each } i \in F.$$
A family that is not linearly independent is linearly dependent: some nontrivial finite combination vanishes.

The definition uses families, not sets. The family $(v, v)$ with the same vector twice is dependent, since $1 \cdot v + (-1) \cdot v = 0$. The set $\{v, v\}$ is the set $\{v\}$, and it is independent if $v \neq 0$ over a field.

::: mathlib
`LinearIndependent` · `Mathlib.LinearAlgebra.LinearIndependent.Defs`

The predicate `LinearIndependent R v` for a family `v : ι → M`. The definition says that the map `Finsupp.linearCombination R v : (ι →₀ R) →ₗ[R] M` is injective. Here `ι →₀ R` is the type of the finitely supported functions, the coefficients of a finite combination. The ring is explicit, because the same family can be independent over $\mathbb{Q}$ and dependent over $\mathbb{R}$. For a set `s : Set M`, the predicate is `LinearIndepOn R id s`.

<?decl LinearIndependent?>
:::

::: mathlib
`linearIndependent_iff` · `Mathlib.LinearAlgebra.LinearIndependent.Defs`

The form over a ring: `LinearIndependent R v ↔ ∀ l : ι →₀ R, linearCombination R v l = 0 → l = 0`. The definition by injectivity and this form agree because a linear map between groups is injective when its kernel is zero.

<?decl linearIndependent_iff?>
:::

::: mathlib
`Fintype.linearIndependent_iff` · `Mathlib.LinearAlgebra.LinearIndependent.Defs`

For a finite index type: `LinearIndependent R v ↔ ∀ g : ι → R, ∑ i, g i • v i = 0 → ∀ i, g i = 0`. This is the form of the textbook for a finite list of vectors. Use it for families indexed by `Fin n`.

<?decl Fintype.linearIndependent_iff?>
:::

**Definition (Basis).** A basis of $M$ is a family $(b_i)_{i \in \iota}$ that is linearly independent and spans $M$. A module with a basis is a free module.

**Definition (Coordinates).** Let $(b_i)$ be a basis. Each $x \in M$ is a finite combination $x = \sum_i c_i b_i$, and the coefficients $c_i$ are unique by the next theorem. They are the coordinates of $x$. The coordinate vector $(c_i)_{i \in \iota}$ is a finitely supported function $\iota \to R$.

::: mathlib
`Module.Basis` · `Mathlib.LinearAlgebra.Basis.Defs`

A basis `b : Module.Basis ι R M` is a structure with one field, `repr : M ≃ₗ[R] (ι →₀ R)`, the map to the coordinates. The vectors of the basis are recovered as `b i = repr.symm (Finsupp.single i 1)`, and `b` coerces to a function `ι → M`. So Mathlib takes the coordinate isomorphism as the definition, and it derives the independence and the span as theorems. This choice makes the coordinates computable from the data and avoids a choice of the coefficients.

<?decl Module.Basis?>
:::

::: mathlib
`Module.Basis.repr` · `Mathlib.LinearAlgebra.Basis.Defs`

The coordinate map `b.repr : M ≃ₗ[R] ι →₀ R`. The coordinate of `x` at `i` is `b.repr x i`. The lemma `Module.Basis.repr_self` gives `b.repr (b i) = Finsupp.single i 1`, and `Module.Basis.sum_repr` gives `∑ i, b.repr x i • b i = x` for a finite index type.

<?decl Module.Basis.repr?>
:::

::: mathlib
`Module.Basis.equivFun` · `Mathlib.LinearAlgebra.Basis.Defs`

For a finite index type, the coordinates as a plain function: `b.equivFun : M ≃ₗ[R] (ι → R)`. With `ι = Fin n`, this is the isomorphism $M \cong R^n$ of the textbook.

<?decl Module.Basis.equivFun?>
:::

**Definition (Standard basis).** In $R^n$, let $e_i$ be the vector with $1$ in the place $i$ and $0$ elsewhere. The family $(e_1, \dots, e_n)$ is the standard basis.

::: mathlib
`Pi.basisFun` · `Mathlib.LinearAlgebra.StdBasis`

The standard basis `Pi.basisFun R η` of `η → R`, for a finite type `η`. Its vector at `i` is `Pi.single i 1`, and its coordinate map is the identity: the coordinates of a vector of $R^n$ in the standard basis are its entries.

<?decl Pi.basisFun?>
:::

### Theorems and proofs

**Theorem (Uniqueness of the coordinates).** A family $(b_i)$ is linearly independent if and only if each vector of its span is a combination of the $b_i$ in only one way.

*Proof.* Suppose that the family is independent, and that $\sum_i c_i b_i = \sum_i d_i b_i$ with finitely many nonzero coefficients. Then $\sum_i (c_i - d_i) b_i = 0$, so $c_i - d_i = 0$ for each $i$. Conversely, suppose that the combinations are unique. If $\sum_i c_i b_i = 0$, then this combination and the zero combination give the same vector $0$, so $c_i = 0$ for each $i$. $\square$

**Theorem (Basis and coordinates).** A family $(b_i)_{i \in \iota}$ is a basis of $M$ if and only if the map
$$\Phi : R^{(\iota)} \to M, \qquad \Phi(c) = \sum_i c_i b_i,$$
is a linear equivalence. Here $R^{(\iota)}$ is the module of the finitely supported functions $\iota \to R$.

*Proof.* The map $\Phi$ is linear, since the sum and the scalar action on $R^{(\iota)}$ are pointwise. Its image is the span of the family. Its kernel is the set of the coefficient families $c$ with $\sum c_i b_i = 0$. So $\Phi$ is surjective if and only if the family spans $M$, and $\Phi$ is injective if and only if the family is independent, by Chapter 1, Section 2. A linear map is an equivalence if and only if it is bijective. $\square$

This theorem is the definition in Mathlib, read from right to left: the inverse $\Phi^{-1}$ is the field `repr`.

::: mathlib
`Module.Basis.mk` · `Mathlib.LinearAlgebra.Basis.Basic`

The basis `Module.Basis.mk hli hsp` from a proof `hli : LinearIndependent R v` and a proof `hsp : ⊤ ≤ span R (Set.range v)`. This is the form of the textbook definition. The lemma `Module.Basis.mk_apply` says that its vectors are the `v i`.

<?decl Module.Basis.mk?>
:::

**Theorem (Universal property of a basis).** Let $(b_i)_{i \in \iota}$ be a basis of $M$ and $N$ an $R$-module. For each family $(w_i)_{i \in \iota}$ in $N$ there is exactly one linear map $f : M \to N$ with $f(b_i) = w_i$ for each $i$. It is $f(\sum_i c_i b_i) = \sum_i c_i w_i$.

*Proof.* Uniqueness: two linear maps that agree on the $b_i$ agree on their span, which is $M$, by the extensionality theorem of Chapter 1. Existence: each $x \in M$ has unique coordinates $c_i$, so the formula $f(x) = \sum_i c_i w_i$ defines a function. It is linear because the coordinate map $x \mapsto (c_i)$ is linear and the map $(c_i) \mapsto \sum c_i w_i$ is linear. Its value at $b_j$ is $w_j$, since the coordinates of $b_j$ are $1$ at $j$ and $0$ elsewhere. $\square$

The theorem says that a basis is a free set of generators: there are no relations to respect. It fails for a spanning family that is not independent. In $\mathbb{Z}/2$, seen as a $\mathbb{Z}$-module, the family $(1)$ spans, but there is no linear map $\mathbb{Z}/2 \to \mathbb{Z}$ that sends $1$ to $1$, since $2 \cdot 1 = 0$ must go to $2 \neq 0$.

::: mathlib
`Module.Basis.constr` · `Mathlib.LinearAlgebra.Basis.Defs`

The map `b.constr S : (ι → N) ≃ₗ[S] (M →ₗ[R] N)` that sends a family of values to the linear map with these values on the basis. It is a linear equivalence, which contains both the existence and the uniqueness. The extra ring `S` lets the equivalence be linear over a second ring; in most uses `S = R` or `S = ℕ`. The value on a basis vector is `Module.Basis.constr_basis`.

<?decl Module.Basis.constr?>
:::

**Theorem (Independence in a vector space).** Let $V$ be a vector space over a field $K$, $(v_1, \dots, v_n)$ an independent family and $w \in V$. The family $(v_1, \dots, v_n, w)$ is independent if and only if $w \notin \operatorname{span}\{v_1, \dots, v_n\}$.

*Proof.* If $w = \sum c_i v_i$, then $\sum c_i v_i - 1 \cdot w = 0$ is a nontrivial relation, since the coefficient of $w$ is $-1 \neq 0$. Conversely, suppose that $w$ is not in the span and that $\sum c_i v_i + c w = 0$. If $c \neq 0$, then $w = -c^{-1} \sum c_i v_i$ is in the span, a contradiction. So $c = 0$, and then $\sum c_i v_i = 0$ gives $c_i = 0$ by the independence of the $v_i$. $\square$

The proof divides by $c$. Over $\mathbb{Z}$ the statement fails: in $\mathbb{Z}$, the vector $2$ is independent, $3$ is not in $2\mathbb{Z}$, and yet $(2, 3)$ is dependent, since $3 \cdot 2 - 2 \cdot 3 = 0$.

::: mathlib
`LinearIndependent.pair_iff` · `Mathlib.LinearAlgebra.LinearIndependent.Lemmas`

The test for two vectors: `LinearIndependent R ![x, y] ↔ ∀ s t, s • x + t • y = 0 → s = 0 ∧ t = 0`. The notation `![x, y]` is the family indexed by `Fin 2`. The general step of the last theorem, over a division ring, is `linearIndepOn_insert`, stated for sets.

<?decl LinearIndependent.pair_iff?>
:::

### Examples

**Example (Three vectors in $\mathbb{Q}^3$).** Let $v_1 = (1, 1, 0)$, $v_2 = (0, 1, 1)$ and $v_3 = (1, 0, 1)$. Suppose $a v_1 + b v_2 + c v_3 = 0$. The coordinates give $a + c = 0$, $a + b = 0$ and $b + c = 0$. Add the three: $2(a + b + c) = 0$, so $a + b + c = 0$. Subtract each equation from this one: $b = 0$, $c = 0$ and $a = 0$. So the family is independent. It also spans: $e_1 = \frac{1}{2}(v_1 - v_2 + v_3)$, $e_2 = \frac{1}{2}(v_1 + v_2 - v_3)$ and $e_3 = \frac{1}{2}(-v_1 + v_2 + v_3)$, and the $e_i$ span. So $(v_1, v_2, v_3)$ is a basis of $\mathbb{Q}^3$. The coordinates of $x = (2, 3, 5)$ solve $a + c = 2$, $a + b = 3$, $b + c = 5$. Then $a + b + c = 5$, so $a = 0$, $b = 3$, $c = 2$, and $x = 3 v_2 + 2 v_3$.

**Example (Polynomials).** In the space $P_n$ of the real polynomials of degree at most $n$, the monomials $1, x, \dots, x^n$ form a basis. They span by the definition of $P_n$. They are independent: if $\sum_{k=0}^n c_k x^k$ is the zero polynomial, then each coefficient is $0$, by the definition of equality of polynomials. Another basis is $1, (x - 1), (x - 1)^2, \dots, (x - 1)^n$, and the coordinates of $p$ in it are the Taylor coefficients $p^{(k)}(1) / k!$.

**Example (A basis of $\mathbb{Z}^2$).** The vectors $u = (2, 1)$ and $w = (1, 1)$ form a basis of $\mathbb{Z}^2$ over $\mathbb{Z}$. They are independent: $a(2, 1) + b(1, 1) = 0$ gives $2a + b = 0$ and $a + b = 0$, so $a = 0$ and $b = 0$. They span: $e_1 = u - w$ and $e_2 = 2w - u$. The vectors $(2, 0)$ and $(0, 1)$ are independent but do not form a basis of $\mathbb{Z}^2$, since $e_1$ is not an integer combination of them. Over $\mathbb{Q}$ they do form a basis. Chapter 4 gives the test: two integer vectors form a basis of $\mathbb{Z}^2$ if and only if their determinant is $\pm 1$. Here $\det \begin{pmatrix} 2 & 1 \\ 1 & 1 \end{pmatrix} = 1$ and $\det \begin{pmatrix} 2 & 0 \\ 0 & 1 \end{pmatrix} = 2$.

**Counterexample (A module with no basis).** The $\mathbb{Z}$-module $\mathbb{Z}/2$ has no basis. A basis is not empty, since $\mathbb{Z}/2 \neq 0$. Each nonempty family contains a vector $v$, and $2 \cdot v = 0$ is a nontrivial relation. The $\mathbb{Z}$-module $\mathbb{Q}$ has no basis either: two nonzero rationals $p/q$ and $r/s$ satisfy $(qr) \cdot \frac{p}{q} - (sp) \cdot \frac{r}{s} = 0$, so a basis has at most one vector, and $\mathbb{Z} \cdot \frac{p}{q}$ does not contain $\frac{p}{2q}$.

### The library around it

Linear independence is in `Mathlib.LinearAlgebra.LinearIndependent.Defs`, with the lemmas for adding vectors in `Mathlib.LinearAlgebra.LinearIndependent.Lemmas`. Bases are in `Mathlib.LinearAlgebra.Basis.Defs` and `Mathlib.LinearAlgebra.Basis.Basic`. The standard bases of $R^n$ and of products are in `Mathlib.LinearAlgebra.StdBasis`. Other ways to build a basis are `Module.Basis.ofEquivFun`, from an equivalence with `ι → R`, and `Module.Basis.map`, the image of a basis by a linear equivalence.

The type `ι →₀ R` of finitely supported functions plays the part of the column of coordinates. For a finite `ι`, it is equivalent to `ι → R`, and `Module.Basis.equivFun` uses this. For an infinite `ι`, the finite support is the condition that a combination has finitely many terms.

### Exercises

1. (A) Decide if $(1, 2, 3)$, $(4, 5, 6)$ and $(7, 8, 9)$ are independent in $\mathbb{Q}^3$. Hint: compare $v_1 + v_3$ with $v_2$.
2. (A) Find the coordinates of $(5, 7)$ in the basis $(2, 1), (1, 1)$ of $\mathbb{Z}^2$.
3. (A) Show that each subfamily of an independent family is independent, and that a family that contains $0$ is dependent.
4. (B) Show that $1, \sqrt{2}, \sqrt{3}$ are independent over $\mathbb{Q}$ in $\mathbb{R}$. Hint: square a relation $a + b\sqrt{2} = -c\sqrt{3}$.
5. (B) Show that the functions $e^{x}, e^{2x}, e^{3x}$ are independent in the real vector space of functions $\mathbb{R} \to \mathbb{R}$. Hint: differentiate a relation, or look at the growth as $x \to \infty$.
6. (B) Let $f : M \to N$ be linear and $(v_i)$ a family in $M$. Show that if $(f(v_i))$ is independent, then $(v_i)$ is independent. Show that the converse holds when $f$ is injective.
7. (B) Show that $(a, b), (c, d)$ is a basis of $\mathbb{Z}^2$ if and only if $a d - b c = \pm 1$. Hint: write $e_1$ and $e_2$ in the family and compare the two matrices.
8. (C) Show that the $\mathbb{Z}$-module $\mathbb{Z}^{\mathbb{N}}$ of all integer sequences is not spanned by any countable family. Deduce that the family $(e_n)$ of the unit sequences is independent but does not span. Hint: a countable family has a countable span, and $\mathbb{Z}^{\mathbb{N}}$ is uncountable.

### Notes and history

The idea of linear independence is in the work of Euler and of Lagrange on systems of linear equations and on linear differential equations. Grassmann in 1844 and Peano in 1888 gave the abstract notions of span and independence. The word "basis" became standard in the 1920s.

In Mathlib, the files on bases go back to Johannes Hölzl, Mario Carneiro and Alexander Bentkamp, and linear independence has work by Anne Baanen. The change from a predicate on a family to a structure with the field `repr` was made so that the coordinates are part of the data. A theorem that needs the coordinates then does not need a choice, and the coordinates of a concrete basis compute.

### Reference

<?reference?>
