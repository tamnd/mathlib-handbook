---
title: The trace of a linear map and more on characteristic polynomials
kind: api
modules:
  - Mathlib.LinearAlgebra.Trace
  - Mathlib.LinearAlgebra.PID
  - Mathlib.LinearAlgebra.Charpoly.BaseChange
  - Mathlib.LinearAlgebra.Matrix.Charpoly.LinearMap
  - Mathlib.LinearAlgebra.Matrix.Charpoly.Univ
  - Mathlib.LinearAlgebra.Matrix.Charpoly.Disc
  - Mathlib.LinearAlgebra.Matrix.Charpoly.FiniteField
  - Mathlib.LinearAlgebra.Matrix.Hessenberg.Defs
  - Mathlib.LinearAlgebra.Matrix.Hessenberg.Similarity
explains:
  E2: [LinearMap.trace, LinearMap.trace_eq_matrix_trace, LinearMap.trace_mul_comm, LinearMap.trace_restrict_eq_of_forall_mem, LinearMap.charpoly_baseChange, Matrix.Represents, LinearMap.exists_monic_and_natDegree_eq_and_coeff_mem_pow_and_aeval_eq_zero, Matrix.charpoly.univ, FiniteField.Matrix.charpoly_pow_card, Matrix.Hessenberg.Similarity.charpoly_eq]
  E1: auto
families: []
requires: [V03, V05, V06]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The trace of a linear map and more on characteristic polynomials

### Overview

The trace of a square matrix is the sum of its diagonal entries, and Chapter 3 shows that similar matrices have the same trace. So the trace of an endomorphism of a free module of finite rank does not depend on the basis. This section describes the trace of linear maps in Mathlib, with its basic identities, and then several results on characteristic polynomials that complete Section 1: the characteristic polynomial after an extension of scalars, the theorem of Cayley and Hamilton for finitely generated modules that are not free, the universal characteristic polynomial, the discriminant of a matrix, the powers of matrices over finite fields, and the reduction to Hessenberg form.

### The library around it

#### The trace of an endomorphism

**Definition (`LinearMap.trace`).** For a commutative semiring $R$ and an $R$-module $M$, `LinearMap.trace R M` is the $R$-linear map from `M →ₗ[R] M` to $R$ that sends $f$ to the trace of the matrix of $f$ in a finite basis, when $M$ has one, and to $0$ otherwise.

The definition chooses a basis, and the result does not depend on it.

**Theorem (`LinearMap.trace_eq_matrix_trace`).** For each finite basis $b$ of $M$, the trace of $f$ is the trace of the matrix `LinearMap.toMatrix b b f`.

*Proof sketch.* For two bases $b$ and $c$, the matrices of $f$ are conjugate by the matrix of the change of basis $P$, and $\operatorname{tr}(P A P^{-1}) = \operatorname{tr}(A P^{-1} P) = \operatorname{tr}(A)$ by the rule $\operatorname{tr}(X Y) = \operatorname{tr}(Y X)$ for matrices. This is `LinearMap.traceAux_eq`. $\square$

The converse direction is `Matrix.trace_toLin_eq`: the linear map of a matrix has the trace of the matrix. The version for the standard basis of $R^n$ is `Matrix.trace_toLin'_eq`. A semiring map $f$ applied to the entries keeps the trace (`Matrix.trace_map`).

**Theorem (`LinearMap.trace_mul_comm`).** For a free module $M$ of finite rank, $\operatorname{tr}(f g) = \operatorname{tr}(g f)$ for all endomorphisms $f$ and $g$.

The form for two maps $f : M \to N$ and $g : N \to M$ between different modules is `LinearMap.trace_comp_comm'`, and the forms for three factors are `LinearMap.trace_mul_cycle` and `LinearMap.trace_comp_cycle`. Consequences are that the trace of a commutator $f g - g f$ is $0$ (`LinearMap.trace_lie`) and that conjugate maps have the same trace (`LinearMap.trace_conj`, `LinearMap.trace_conj'`). The identity has the trace $\dim M$ (`LinearMap.trace_id`, `LinearMap.trace_one`).

The trace behaves well with the constructions of the earlier chapters. On a product, $\operatorname{tr}(f \times g) = \operatorname{tr} f + \operatorname{tr} g$ (`LinearMap.trace_prodMap'`). The dual map has the same trace (`LinearMap.trace_transpose'`). For a linear form $\varphi$ and a vector $x$, the map $v \mapsto \varphi(v) x$ has the trace $\varphi(x)$ (`LinearMap.trace_smulRight`). A projection onto $p$ has the trace $\dim p$ (`LinearMap.IsProj.trace`), and over a ring of characteristic zero an idempotent with free range and kernel of finite rank has trace $0$ only when it is $0$ (`LinearMap.IsIdempotentElem.trace_eq_zero_iff`). The trace of a nilpotent map is nilpotent (`LinearMap.isNilpotent_trace_of_isNilpotent`).

The module also has the description of the trace without bases. Under the isomorphism $M^* \otimes M \cong \operatorname{End}(M)$ of a free module of finite rank, the trace is the contraction $\varphi \otimes x \mapsto \varphi(x)$ (`LinearMap.trace_eq_contract`). On a tensor product, $\operatorname{tr}(f \otimes g) = \operatorname{tr} f \cdot \operatorname{tr} g$ (`LinearMap.trace_tensorProduct'`), and after an extension of scalars the trace is the image of the trace (`LinearMap.trace_baseChange`). The tensor products are in Volume 8.

#### The trace of a restriction

Over a field, if $f$ maps $M$ into a subspace $p$, then in a basis of $M$ that extends a basis of $p$ the matrix of $f$ has zero rows outside $p$, so $f$ and its restriction to $p$ have the same trace. Over a principal ideal domain the same is true.

**Theorem (`LinearMap.trace_restrict_eq_of_forall_mem`).** Let $R$ be a principal ideal domain and $M$ a free $R$-module of finite rank. If $f(x) \in p$ for all $x \in M$, then the trace of the restriction of $f$ to $p$ equals the trace of $f$.

*Proof sketch.* The submodule $p$ is free, and Chapter 7 gives a basis $b$ of $M$ and a basis of $p$ of the form $a_i b_{\sigma(i)}$, the Smith normal form. In the basis $b$, the diagonal entry of $f$ at an index outside the range of $\sigma$ is zero, because $f(b_j)$ is in $p$. The remaining diagonal entries are the diagonal entries of the restriction in the basis of $p$. $\square$

The module `Mathlib.LinearAlgebra.PID` holds this one result, so that the files on the trace do not import the theory of principal ideal domains.

#### Characteristic polynomials after a change of rings

**Theorem (`LinearMap.charpoly_baseChange`).** For an $R$-algebra $A$ and an endomorphism $f$ of a free $R$-module $M$ of finite rank, the characteristic polynomial of the extension $A \otimes_R f$ is the image of the characteristic polynomial of $f$ under the map $R[X] \to A[X]$.

*Proof sketch.* A basis of $M$ gives a basis of $A \otimes_R M$, and in it the matrix of $A \otimes_R f$ is the image of the matrix of $f$. The characteristic polynomial of a matrix commutes with ring maps applied to the entries. $\square$

The same module gives `LinearMap.det_baseChange` and `LinearEquiv.det_baseChange`, and `LinearMap.det_eq_sign_charpoly_coeff`: $\det f = (-1)^n \chi_f(0)$, with $n = \dim M$.

The universal case contains all others.

**Definition (`Matrix.charpoly.univ`).** For a commutative ring $R$ and a finite type $n$, `Matrix.charpoly.univ R n` is the characteristic polynomial of the $n \times n$ matrix whose entries are the variables $X_{ij}$ of the ring of polynomials `MvPolynomial (n × n) R`.

Each characteristic polynomial over a commutative $R$-algebra is an image of it: `Matrix.charpoly.univ_map_eval₂Hom` says that the evaluation of the variables at the entries of a matrix $M$ sends it to $\chi_M$. It is monic of degree $|n|$ (`Matrix.charpoly.univ_monic`, `Matrix.charpoly.univ_natDegree`), and the coefficient of $X^i$ is a homogeneous polynomial of degree $|n| - i$ in the entries (`Matrix.charpoly.univ_coeff_isHomogeneous`). This polynomial is the tool to prove an identity for all matrices once: prove it for the generic matrix, over a domain where more methods are available, and then specialize.

#### Cayley and Hamilton for finitely generated modules

The theorem of Cayley and Hamilton of Section 2 is for free modules. Over a commutative ring, each finitely generated module has an endomorphism that satisfies a monic polynomial, from a matrix that represents it on a family of generators.

**Definition (`Matrix.Represents`).** For a family $b : \iota \to M$, a matrix $A$ and an endomorphism $f$, `Matrix.Represents b A f` says that $f(b_j) = \sum_i A_{ij} b_i$ for all $j$.

The form with the columns is `Matrix.represents_iff'`. The family need not be independent, so a map can have many matrices; if $b$ spans $M$, the matrix determines the map (`Matrix.Represents.eq`). The matrices that represent some map form the subalgebra `Matrix.isRepresentation R b`, and for a spanning family the map to the endomorphisms is surjective (`Matrix.isRepresentation.toEnd_surjective`).

**Theorem (`LinearMap.exists_monic_and_natDegree_eq_and_coeff_mem_pow_and_aeval_eq_zero`).** Let $M$ be a finitely generated module over a commutative ring $R$, $I$ an ideal and $f$ an endomorphism with range in $I M$. Then there is a monic polynomial $p = X^n + a_{n-1} X^{n-1} + \dots + a_0$, with $n$ the least number of generators of $M$ and $a_k \in I^{n-k}$ for each $k$, with $p(f) = 0$.

*Proof sketch.* Choose generators $b_1, \dots, b_n$. Since $f(b_j) \in I M$, there is a matrix $A$ with entries in $I$ that represents $f$ (`Matrix.isRepresentation.toEnd_exists_mem_ideal`). The map from the subalgebra of representing matrices to the endomorphisms is an algebra map, so $\chi_A(f)$ is the image of $\chi_A(A) = 0$. The coefficient of $X^k$ in $\chi_A$ is a sum of products of $n - k$ entries of $A$, so it is in $I^{n-k}$. $\square$

This is the determinant trick, the form of Matsumura, and it is the base of the lemma of Nakayama in the volumes on commutative algebra. The case $I = R$ is `LinearMap.exists_monic_and_aeval_eq_zero`: each endomorphism of a finitely generated module is integral over $R$.

#### Discriminants, finite fields and Hessenberg form

The discriminant of a square matrix, `Matrix.discr A`, is the discriminant of its characteristic polynomial. It is invariant under conjugation by an invertible matrix (`Matrix.discr_conj`), and for a $2 \times 2$ matrix it is $\operatorname{tr}(A)^2 - 4 \det A$ (`Matrix.discr_fin_two`).

**Theorem (`FiniteField.Matrix.charpoly_pow_card`).** Over a finite field $K$ with $q$ elements, $\chi_{M^q} = \chi_M$ for each square matrix $M$.

*Proof sketch.* Over an algebraic closure the eigenvalues of $M^q$ are the $q$-th powers $\lambda_i^q$ of the eigenvalues of $M$. The Frobenius map $x \mapsto x^q$ is an automorphism that permutes the roots of $\chi_M$, because $\chi_M$ has coefficients in $K$, which the Frobenius map fixes. So the two polynomials have the same roots with the same multiplicities. $\square$

The trace version is `FiniteField.trace_pow_card`, $\operatorname{tr}(M^q) = \operatorname{tr}(M)^q$, and `ZMod.charpoly_pow_card` and `ZMod.trace_pow_card` are the cases $K = \mathbb{Z}/p\mathbb{Z}$.

A square matrix indexed by a successor order is upper Hessenberg, `Matrix.IsUpperHessenberg`, when $M_{ij} = 0$ for $j + 1 < i$: all entries below the first subdiagonal are zero (`Matrix.isUpperHessenberg_fin_iff`). An upper triangular matrix is upper Hessenberg (`Matrix.IsUpperTriangular.isUpperHessenberg`). The characteristic polynomial of a Hessenberg matrix has a short recursive formula, so numerical methods first reduce a matrix to this form. The structure `Matrix.Hessenberg.Similarity A` is a certificate of such a reduction: a permutation $\sigma$, a lower triangular matrix $L$ with nonzero diagonal and an upper Hessenberg matrix $H$, with $A_\sigma L = L H$ for the matrix $A_\sigma$ with rows and columns permuted by $\sigma$.

**Theorem (`Matrix.Hessenberg.Similarity.charpoly_eq`).** Over a domain, the matrix $H$ of a certificate has the characteristic polynomial of $A$.

*Proof.* The matrix $L$ is triangular with nonzero diagonal, so $\det L \ne 0$, and $A_\sigma L = L H$ gives $\chi_{A_\sigma} = \chi_H$ by `Matrix.charpoly_eq_of_mul_eq_mul`. A simultaneous permutation of rows and columns does not change the characteristic polynomial (`Matrix.charpoly_reindex`). $\square$

#### Common errors

1. `LinearMap.trace R M` is $0$ on a module without a finite basis, so `LinearMap.trace_id` and `LinearMap.trace_mul_comm` need the instances `Module.Free R M` and `Module.Finite R M`.
2. `LinearMap.trace R M` is a linear map. Write `LinearMap.trace R M f`, with both explicit arguments $R$ and $M$ before $f$.
3. `Matrix.Represents b A f` does not need $b$ to be a basis, so the matrix is not unique. Use `Matrix.Represents.eq` only with a spanning family, and do not expect a statement like `LinearMap.toMatrix` for it.

### Exercises

1. (A) Compute the trace of the map $(x, y) \mapsto (x + 2 y, 3 x + 4 y)$ on $\mathbb{Q}^2$ with `LinearMap.trace_eq_matrix_trace`.
2. (A) Show that the trace of a projection onto a line of $\mathbb{R}^3$ is $1$.
3. (B) Prove that there are no endomorphisms $f$, $g$ of $\mathbb{Q}^n$, $n \ge 1$, with $f g - g f = \operatorname{id}$.
4. (B) Compute `Matrix.discr` of `!![a, b; c, d]`, and show that over $\mathbb{R}$ it is nonnegative for a symmetric matrix.
5. (B) Check `FiniteField.Matrix.charpoly_pow_card` for $M$ = `!![0, 1; 1, 1]` over $\mathbb{Z}/2\mathbb{Z}$.
6. (C) Let $M$ be a finitely generated module over a commutative ring $R$, and $I$ an ideal with $I M = M$. Use `LinearMap.exists_monic_and_natDegree_eq_and_coeff_mem_pow_and_aeval_eq_zero` with $f = \operatorname{id}$ to find $a \in I$ with $(1 + a) M = 0$.

### Reference

<?reference?>
