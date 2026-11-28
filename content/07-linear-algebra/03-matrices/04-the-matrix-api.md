---
title: The basic matrix API
kind: api
modules:
  - Mathlib.Data.Matrix.Basic
  - Mathlib.Data.Matrix.DMatrix
  - Mathlib.Data.Matrix.PEquiv
  - Mathlib.Data.Matrix.Reflection
  - Mathlib.Data.Matrix.Auto
  - Mathlib.Data.Matrix.Action
  - Mathlib.Data.Matrix.Bilinear
  - Mathlib.Data.Matrix.Cartan
  - Mathlib.Data.Matrix.DualNumber
  - Mathlib.Data.Matrix.Invertible
explains:
  E2: [Matrix.instAlgebra, Matrix.algebraMap_eq_diagonal, Matrix.scalar_commute, RingHom.mapMatrix, Matrix.transposeAlgEquiv, Matrix.transpose_list_prod, Matrix.entryLinearMap, PEquiv.toMatrix_trans, Matrix.mulᵣ_eq]
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

## The basic matrix API

### Overview

Section 1 defined matrices and their algebra. This section is the reference for the bundled structure around them. The square matrices over a commutative ring form an algebra, and the scalar matrices are the image of the ring. A map of the entries gives a map of matrices, and each kind of map (additive, linear, ring, algebra) has a bundled version. The transpose is an equivalence of modules and an anti-isomorphism of rings. The section also covers two smaller tools: the matrices of partial equivalences, which are the matrices with at most one entry $1$ in each row and column, and the definitions with good computation for concrete matrices of type `Matrix (Fin m) (Fin n) α`.

### The library around it

#### Matrices as an algebra

For a commutative semiring $R$ and an $R$-algebra $\alpha$, the square matrices `Matrix n n α` form an $R$-algebra. This is the instance `Matrix.instAlgebra`. The structure map sends $r$ to the diagonal matrix with the entries $r \cdot 1$.

**Theorem.** The image of $r \in R$ in `Matrix n n α` is the diagonal matrix with the entries $\operatorname{algebraMap}(r)$.

*Proof.* The structure map of the algebra is the composition of the structure map $R \to (n \to \alpha)$, the constant functions, with the ring map $(n \to \alpha) \to \operatorname{Mat}_n(\alpha)$ that sends $v$ to the diagonal matrix of $v$. $\square$

This is `Matrix.algebraMap_eq_diagonal`, with the bundled form `Matrix.algebraMap_eq_diagonalRingHom`. The diagonal maps also exist as bundled maps: `Matrix.diagonalAddMonoidHom`, `Matrix.diagonalLinearMap`, `Matrix.diagonalRingHom` and `Matrix.diagonalAlgHom`.

The scalar matrices are given by the ring map `Matrix.scalar n : α →+* Matrix n n α`, with the algebra version `Matrix.scalarAlgHom`. It is injective for a nonempty $n$ (`Matrix.scalar_inj`). A scalar matrix commutes with each matrix when the scalar is central.

**Theorem.** If $r \in \alpha$ commutes with each element of $\alpha$, then the scalar matrix $r I$ commutes with each square matrix $M$.

*Proof.* The entries of $(r I) M$ are $r M_{ij}$, and the entries of $M (r I)$ are $M_{ij} r$. These are equal since $r$ is central. $\square$

This is `Matrix.scalar_commute`, and `Matrix.scalar_comm` is the form for rectangular matrices. For a noncommutative $\alpha$, the exact condition is `Matrix.scalar_commute_iff`: $r I$ commutes with $M$ if and only if the left and right actions of $r$ on $M$ agree.

The powers of matrices have the expected rules: `Matrix.diagonal_pow`, `Matrix.transpose_pow` and `Matrix.map_pow`. The products with vectors are additive in each argument: `Matrix.mulVec_sum`, `Matrix.sum_mulVec`, `Matrix.vecMul_sum` and `Matrix.sum_vecMul`.

#### Maps of the entries

A map $f : \alpha \to \beta$ gives the map `Matrix.map M f` of matrices, which applies $f$ to each entry. When $f$ respects some structure, the map of matrices respects the matching structure:

| Lean name | Map of entries | Map of matrices |
|---|---|---|
| `Equiv.mapMatrix` | equivalence | equivalence |
| `AddMonoidHom.mapMatrix` | additive map | additive map |
| `AddEquiv.mapMatrix` | additive equivalence | additive equivalence |
| `LinearMap.mapMatrix` | linear map | linear map |
| `LinearEquiv.mapMatrix` | linear equivalence | linear equivalence |
| `RingHom.mapMatrix` | ring map | ring map of square matrices |
| `RingEquiv.mapMatrix` | ring isomorphism | ring isomorphism |
| `AlgHom.mapMatrix` | algebra map | algebra map |
| `AlgEquiv.mapMatrix` | algebra isomorphism | algebra isomorphism |

**Theorem.** A ring map $f : \alpha \to \beta$ gives a ring map $\operatorname{Mat}_n(\alpha) \to \operatorname{Mat}_n(\beta)$.

*Proof.* The map is additive since $f$ is. The entries of $f(M N)$ are $f(\sum_k M_{ik} N_{kj}) = \sum_k f(M_{ik}) f(N_{kj})$, which are the entries of $f(M) f(N)$. The identity goes to the identity since $f(0) = 0$ and $f(1) = 1$. $\square$

This is `RingHom.mapMatrix`. It is functorial: `RingHom.mapMatrix_id` and `RingHom.mapMatrix_comp`. The reduction of an integer matrix modulo $p$ and the inclusion of a rational matrix in the real matrices are examples. Each bundled version has the rules `..._refl`, `..._symm` and `..._trans` for equivalences, and `..._id` and `..._comp` for maps.

The entry in row $i$ and column $j$ is a map too: `Matrix.entryAddHom`, `Matrix.entryAddMonoidHom` and the linear form `Matrix.entryLinearMap R α i j`. The lemma `LinearMap.entryLinearMap_comp_mapMatrix` says that the entry of $f(M)$ is $f$ of the entry of $M$. The diagonal is the linear map `Matrix.diagLinearMap`, with `Matrix.diag_sum`.

A substructure of the entries gives a substructure of the matrices, with the entries in the substructure: `AddSubmonoid.matrix`, `AddSubgroup.matrix`, `Submodule.matrix`, `Subsemiring.matrix` and `Subring.matrix`. For example the integer matrices are a subring of the rational matrices.

#### Structural equivalences

The transpose is the linear equivalence `Matrix.transposeLinearEquiv` between `Matrix m n α` and `Matrix n m α`. On square matrices it reverses products.

**Theorem.** The transpose is a ring isomorphism $\operatorname{Mat}_n(\alpha) \simeq \operatorname{Mat}_n(\alpha)^{\mathrm{op}}$ for a commutative $\alpha$.

*Proof.* The transpose is bijective and additive. It sends $1$ to $1$, and $(M N)^T = N^T M^T$ by Section 1. This is the product of $M^T$ and $N^T$ in the opposite ring. $\square$

This is `Matrix.transposeRingEquiv`, and the algebra version is `Matrix.transposeAlgEquiv`. The consequence `Matrix.transpose_list_prod` says that the transpose of a product of a list is the product of the transposes in the reverse order. For a noncommutative $\alpha$, the matching statement uses the opposite entries, `RingEquiv.mopMatrix`.

Other structural equivalences are:

| Lean name | Equivalence |
|---|---|
| `Matrix.ofLinearEquiv` | functions $m \to n \to \alpha$ and matrices, as a linear equivalence |
| `Matrix.rowLinearEquiv`, `Matrix.colLinearEquiv` | a matrix and the family of its rows, or of its columns |
| `Matrix.prodLinearEquiv`, `Matrix.prodAlgEquiv` | matrices of pairs and pairs of matrices |
| `Matrix.piLinearEquiv`, `Matrix.piAlgEquiv` | matrices of families and families of matrices |

A matrix over a finite type of entries is a finite type: `Matrix.instFintypeOfDecidableEq`. This makes it possible to count matrices over a finite field.

#### Matrices of partial equivalences

A partial equivalence $f : m \simeq. n$ is a bijection between a part of $m$ and a part of $n$. Its matrix `PEquiv.toMatrix f` has the entry $1$ at $(i, j)$ when $f(i) = j$, and $0$ elsewhere. These are the permutation matrices when $f$ is an equivalence, and the matrices of coordinate projections and inclusions in general.

**Theorem.** For partial equivalences $f : l \simeq. m$ and $g : m \simeq. n$, the matrix of $f$ followed by $g$ is the product $\tilde{f} \tilde{g}$ of their matrices.

*Proof.* The entry $(i, k)$ of $\tilde{f} \tilde{g}$ is $\sum_j \tilde{f}_{ij} \tilde{g}_{jk}$. At most one term is nonzero, the term with $j = f(i)$, and it is $1$ exactly when $g(f(i)) = k$. $\square$

This is `PEquiv.toMatrix_trans`. The other rules are `PEquiv.toMatrix_refl`, `PEquiv.toMatrix_symm` (the matrix of the inverse is the transpose), `PEquiv.toMatrix_bot` and `PEquiv.toMatrix_injective`. For an equivalence $\sigma$, `PEquiv.toMatrix_toPEquiv_mulVec` says that the product with a vector permutes its entries, and `PEquiv.toMatrix_toPEquiv_mul` says that the product with a matrix permutes its rows. The single entry matrices `(PEquiv.single a b).toMatrix` multiply by `PEquiv.single_mul_single`.

#### Concrete matrices

For matrices of type `Matrix (Fin m) (Fin n) α`, the file `Mathlib.Data.Matrix.Reflection` gives versions of the operations that unfold by recursion on $m$ and $n$. The product `Matrix.mulᵣ` computes entry by entry, and `Matrix.mulᵣ_eq` states that it equals the product. So a product of two concrete matrices can be found by a rewrite:

```lean
example [AddCommMonoid α] [Mul α] (a b c d e f g h : α) :
    !![a, b; c, d] * !![e, f; g, h] =
      !![a * e + b * g, a * f + b * h; c * e + d * g, c * f + d * h] :=
  (Matrix.mulᵣ_eq _ _).symm
```

The other operations are `Matrix.transposeᵣ`, `Matrix.mulVecᵣ`, `Matrix.vecMulᵣ` and `Matrix.dotProductᵣ`, with the lemmas `Matrix.transposeᵣ_eq` and so on. The predicates `Matrix.Forall` and `Matrix.Exists` expand a quantifier over all matrices into a quantifier over the entries: `Matrix.forall_iff`. The module `Mathlib.Data.Matrix.Auto` once held lemmas of this kind for each size, and it now contains no declarations. The modules `Mathlib.Data.Matrix.Action`, `Mathlib.Data.Matrix.Bilinear`, `Mathlib.Data.Matrix.Cartan`, `Mathlib.Data.Matrix.DualNumber` and `Mathlib.Data.Matrix.Invertible` are deprecated, and their content is in the modules of the same names in the folder LinearAlgebra/Matrix, for example `Mathlib.LinearAlgebra.Matrix.Invertible`.

#### Matrices with entries of varying types

A `DMatrix m n α` is a matrix whose entry at $(i, j)$ has the type $\alpha\,i\,j$. It is the dependent form of `Matrix`. It has the additive structures of matrices (`DMatrix.instAddCommGroup`), extensionality (`DMatrix.ext`), the transpose `DMatrix.transpose`, and the map of entries `DMatrix.map` with its bundled form `AddMonoidHom.mapDMatrix`. It has no product, since the sum $\sum_k M_{ik} N_{kj}$ needs one type for all its terms.

#### Common errors

1. Writing a matrix as `fun i j ↦ _` with a matrix type. Lean then sees a function, and lemmas about `Matrix` do not fire. Use `Matrix.of` to build a matrix from a function.
2. Expecting the transpose to be a ring map. It reverses products, so it is a ring isomorphism to the opposite ring, `Matrix.transposeRingEquiv`, and not an endomorphism of the ring.
3. Applying `RingHom.mapMatrix` to rectangular matrices. Only square matrices form a ring; for rectangular matrices use `AddMonoidHom.mapMatrix` or `LinearMap.mapMatrix`.

### Exercises

1. (A) Compute $\begin{pmatrix} 1 & 2 \\ 3 & 4 \end{pmatrix} \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$ by hand, and state the rewrite that gives it in Lean.
2. (A) Show that the image of $r$ in `Matrix n n R` for a commutative ring $R$ is $r \cdot 1$.
3. (B) Find two real $2 \times 2$ matrices $A$ and $B$ with $(A B)^T \ne A^T B^T$.
4. (B) Let $f : \mathbb{Z} \to \mathbb{Z}/2$ be the reduction map. Show that the image of an invertible integer matrix under `RingHom.mapMatrix f` is invertible, and give an integer matrix with invertible image that is not invertible.
5. (B) Show that the matrix of a permutation $\sigma$ has the inverse $\sigma^{-1}$ and that this inverse is its transpose.
6. (C) Show that a matrix that commutes with each matrix in `Matrix n n K` for a field $K$ is a scalar matrix. Hint: use the matrices of `PEquiv.single i j`.

### Reference

<?reference?>
