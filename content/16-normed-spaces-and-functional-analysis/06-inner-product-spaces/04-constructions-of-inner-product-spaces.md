---
title: Constructions of inner product spaces
kind: api
modules:
  - Mathlib.Analysis.InnerProductSpace.Subspace
  - Mathlib.Analysis.InnerProductSpace.ProdL2
  - Mathlib.Analysis.InnerProductSpace.Completion
  - Mathlib.Analysis.InnerProductSpace.MulOpposite
  - Mathlib.Analysis.InnerProductSpace.TensorProduct
  - Mathlib.Analysis.InnerProductSpace.CanonicalTensor
  - Mathlib.Analysis.InnerProductSpace.Coalgebra
  - Mathlib.Analysis.InnerProductSpace.ExteriorPower
  - Mathlib.Analysis.InnerProductSpace.GramMatrix
explains:
  E2: [OrthogonalFamily, OrthogonalFamily.norm_sum, WithLp.prod_inner_apply, Submodule.orthogonalDecomposition, TensorProduct.inner_tmul, TensorProduct.norm_tmul, OrthonormalBasis.tensorProduct, Matrix.gram, Matrix.posSemidef_gram, Matrix.posDef_gram_iff_linearIndependent]
  E1: auto
families: []
requires: [V07, V13, V16.C01, V16.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Constructions of inner product spaces

### Overview

Section 1 defines an inner product space, and Sections 2 and 3 study orthonormal families and Hilbert spaces. The examples there are $\mathbb{K}^n$ and $\ell^2$. This section collects the constructions that make new inner product spaces from old ones: a subspace, a product with the $L^2$ inner product, a quotient by a subspace, the completion, the multiplicative opposite, the tensor product and the exterior powers. Each construction has an inner product that the library installs as an instance, and a formula on simple elements that a proof uses through the simplifier.

The section also treats the Gram matrix of a family of vectors. The Gram matrix records all the inner products $\langle v_i, v_j \rangle$, and its positivity is the matrix form of the inequality of Cauchy-Schwarz.

### The library around it

#### Subspaces and orthogonal families

A submodule $W$ of an inner product space $E$ is an inner product space with the restricted inner product. The instance is `Submodule.innerProductSpace`, and the lemma `Submodule.coe_inner` says that $\langle x, y \rangle_W = \langle x, y \rangle_E$ for $x, y \in W$. The instance `ClosedSubmodule.innerProductSpace` does the same for a closed submodule. The lemma `orthonormal_span` says that an orthonormal family stays orthonormal as a family in its span.

The module `Mathlib.Analysis.InnerProductSpace.Subspace` also defines orthogonal families of subspaces. Let $G_i$ be inner product spaces and let $V_i : G_i \to E$ be linear isometries. The predicate `OrthogonalFamily 𝕜 G V` says that $\langle V_i x, V_j y \rangle = 0$ for $i \ne j$. The main case is a family of submodules $V_i \subseteq E$ with their inclusions `(V i).subtypeₗᵢ`. An orthonormal family is an orthogonal family of lines: `Orthonormal.orthogonalFamily`.

| Lean name | Statement |
|---|---|
| `OrthogonalFamily.norm_sum` | $\lVert \sum_{i \in s} V_i(l_i) \rVert^2 = \sum_{i \in s} \lVert l_i \rVert^2$ |
| `OrthogonalFamily.inner_right_fintype` | $\langle V_i v, \sum_j V_j(l_j) \rangle = \langle v, l_i \rangle$ |
| `OrthogonalFamily.summable_iff_norm_sq_summable` | in a complete space, $\sum_i V_i(f_i)$ converges if and only if $\sum_i \lVert f_i \rVert^2 < \infty$ |
| `OrthogonalFamily.independent` | orthogonal submodules are independent |
| `OrthogonalFamily.comp` | an orthogonal family stays orthogonal along an injective reindexing |
| `DirectSum.IsInternal.collectedBasis_orthonormal` | orthonormal bases of the pieces of an internal direct sum give an orthonormal basis of the sum |

The identity `OrthogonalFamily.norm_sum` is the theorem of Pythagoras for subspaces. Expand the square: $\lVert \sum_i V_i l_i \rVert^2 = \sum_{i,j} \langle V_i l_i, V_j l_j \rangle$. The terms with $i \ne j$ vanish by orthogonality, and $\langle V_i l_i, V_i l_i \rangle = \lVert l_i \rVert^2$ because $V_i$ is an isometry. The criterion of summability follows from it: the partial sums of $\sum_i V_i f_i$ form a Cauchy net exactly when the partial sums of $\sum_i \lVert f_i \rVert^2$ do. Section 3 uses orthogonal families for the Hilbert sums `OrthogonalFamily.linearIsometry`.

#### Products, quotients and completions

The product $E \times F$ carries the sup norm, so it is not an inner product space. The type `WithLp 2 (E × F)` of Section 2 of Chapter 1 carries the $L^2$ norm $\sqrt{\lVert x \rVert^2 + \lVert y \rVert^2}$. The module `Mathlib.Analysis.InnerProductSpace.ProdL2` gives it the instance `WithLp.instProdInnerProductSpace`, and `WithLp.prod_inner_apply` gives the formula
$$\langle (x_1, x_2), (y_1, y_2) \rangle = \langle x_1, y_1 \rangle + \langle x_2, y_2 \rangle.$$
The definition `OrthonormalBasis.prod` joins orthonormal bases of $E$ and $F$ into an orthonormal basis of the product, indexed by the sum type `ι₁ ⊕ ι₂`.

The same module splits a space along a subspace. Let $K \subseteq E$ be a subspace with an orthogonal projection, the instance `Submodule.HasOrthogonalProjection K` of Chapter 7. Then `Submodule.orthogonalDecomposition K` is the linear isometric equivalence $E \cong K \times K^\perp$ with the $L^2$ norm on the right. The lemmas `Submodule.fst_orthogonalDecomposition_apply` and `Submodule.snd_orthogonalDecomposition_apply` say that its components are the two orthogonal projections. The quotient $E / K$ gets an inner product from the isometry `Submodule.quotientEquivOrthogonal K : E ⧸ K ≃ₗᵢ[𝕜] Kᗮ`. The instance is `Submodule.instQuotientInnerProductSpace`, and `Submodule.inner_quotient_eq` defines the inner product of two classes as the inner product of their images in $K^\perp$.

The module `Mathlib.Analysis.InnerProductSpace.Completion` extends the inner product to two quotient constructions of Chapter 4. On the separation quotient of a seminormed space, `SeparationQuotient.instInnerProductSpace` is the inner product, and `SeparationQuotient.inner_mk_mk` says that it agrees with the inner product of representatives. The lemma `Inseparable.inner_eq_inner` gives the reason: two inseparable vectors have the same inner products. On the completion, `UniformSpace.Completion.innerProductSpace` is the instance, `UniformSpace.Completion.inner_coe` says $\langle \bar a, \bar b \rangle = \langle a, b \rangle$, and `UniformSpace.Completion.continuous_inner` gives the continuity that defines the extension. So the completion of an inner product space is a Hilbert space.

The module `Mathlib.Analysis.InnerProductSpace.MulOpposite` puts the same inner product on the opposite type $H^{\mathrm{mop}}$: `MulOpposite.inner_op` says $\langle \mathrm{op}\, x, \mathrm{op}\, y \rangle = \langle x, y \rangle$, and `OrthonormalBasis.mulOpposite` moves an orthonormal basis to the opposite.

#### Tensor products

Let $E$ and $F$ be inner product spaces over $\mathbb{K}$. The module `Mathlib.Analysis.InnerProductSpace.TensorProduct` puts an inner product on the algebraic tensor product `TensorProduct 𝕜 E F`, written `E ⊗[𝕜] F`. On pure tensors it is
$$\langle x \otimes y, x' \otimes y' \rangle = \langle x, x' \rangle \langle y, y' \rangle,$$
the lemma `TensorProduct.inner_tmul`, and it extends by sesquilinearity. The instances are `TensorProduct.instNormedAddCommGroup` and `TensorProduct.instInnerProductSpace`. The tensor product is not completed: for infinite dimensional $E$ and $F$, the space `E ⊗[𝕜] F` is not a Hilbert space.

The hard part of the construction is positivity: $\langle t, t \rangle > 0$ for $t \ne 0$. A tensor $t$ is a finite sum of pure tensors, so it lies in $E' \otimes F'$ for finite dimensional subspaces $E' \subseteq E$ and $F' \subseteq F$. The lemma `TensorProduct.inner_mapIncl_mapIncl` says that the inclusion $E' \otimes F' \to E \otimes F$ keeps the inner product. In $E' \otimes F'$, take orthonormal bases $(e_i)$ and $(f_j)$. Then $t = \sum c_{ij}\, e_i \otimes f_j$ and $\langle t, t \rangle = \sum |c_{ij}|^2$, which is positive when $t \ne 0$.

| Lean name | Statement |
|---|---|
| `TensorProduct.norm_tmul` | $\lVert x \otimes y \rVert = \lVert x \rVert \lVert y \rVert$ |
| `TensorProduct.dist_tmul_le` | $d(x \otimes y, x' \otimes y') \le \lVert x \rVert \lVert y \rVert + \lVert x' \rVert \lVert y' \rVert$ |
| `TensorProduct.ext_iff_inner_left` | two tensors are equal if they have the same inner products with all pure tensors |
| `Orthonormal.tmul` | the products $b_i \otimes c_j$ of orthonormal families are orthonormal |
| `OrthonormalBasis.tensorProduct` | an orthonormal basis of $E \otimes F$ indexed by `ι₁ × ι₂` |
| `TensorProduct.mkL` | the bounded bilinear map $(x, y) \mapsto x \otimes y$ |
| `TensorProduct.mapL` | the tensor product $f \otimes g$ of two bounded operators |
| `TensorProduct.norm_mapL_le` | $\lVert f \otimes g \rVert \le \lVert f \rVert \lVert g \rVert$ |
| `TensorProduct.adjoint_mapL` | $(f \otimes g)^* = f^* \otimes g^*$ |

The algebraic equivalences of Volume 7 become isometries. The commutativity $E \otimes F \cong F \otimes E$ is `TensorProduct.commIsometry`, the associativity is `TensorProduct.assocIsometry`, and the unit laws $\mathbb{K} \otimes E \cong E$ and $E \otimes \mathbb{K} \cong E$ are `TensorProduct.lidIsometry` and `TensorProduct.ridIsometry`. A pair of isometries gives `TensorProduct.mapIsometry`, a pair of isometric equivalences gives `TensorProduct.congrIsometry`, and a pair of continuous linear equivalences gives `TensorProduct.congrL`. The one sided forms are `ContinuousLinearMap.lTensor` and `ContinuousLinearMap.rTensor`, with the isometric versions `LinearIsometry.lTensor` and `LinearIsometryEquiv.rTensor`. Each comes with a lemma, with a name that ends in apply or tmul, that computes it on pure tensors, and with lemmas such as `TensorProduct.mapL_comp` and `TensorProduct.mapL_pow` for composition and powers.

The module `Mathlib.Analysis.InnerProductSpace.CanonicalTensor` defines two tensors of a real inner product space. The linear form `InnerProductSpace.canonicalContravariantTensor E : E ⊗[ℝ] E →ₗ[ℝ] ℝ` sends $x \otimes y$ to $\langle x, y \rangle$. In finite dimension, `InnerProductSpace.canonicalCovariantTensor E` is the element $\sum_i e_i \otimes e_i$, and `InnerProductSpace.canonicalCovariantTensor_eq_sum` says that it does not depend on the orthonormal basis $(e_i)$. The Laplacian of Section 5 contracts a second derivative with this tensor.

The module `Mathlib.Analysis.InnerProductSpace.Coalgebra` uses adjoints to turn an algebra into a coalgebra. Let $E$ be finite dimensional and linearly equivalent to an algebra $A$. Then `InnerProductSpace.coalgebraOfAlgebra` gives $E$ a coalgebra structure whose comultiplication is the adjoint of the multiplication $A \otimes A \to A$. In the other direction, `InnerProductSpace.algebraOfCoalgebra` gives an algebra, and `InnerProductSpace.AlgebraOfCoalgebra.mul_def` says $x y = \mathrm{comul}^*(x \otimes y)$. These are definitions, not instances, because a space can carry many such structures. The lemmas `Pi.comul_eq_adjoint` and `Pi.counit_eq_adjoint` check the case of $\mathbb{K}^n$.

#### Exterior powers and Gram matrices

Let $v_1, \dots, v_n$ be vectors of an inner product space. The Gram matrix `Matrix.gram 𝕜 v` is the matrix with entries $\langle v_i, v_j \rangle$, as `Matrix.gram_apply` says.

| Lean name | Statement |
|---|---|
| `Matrix.isHermitian_gram` | the Gram matrix is Hermitian |
| `Matrix.posSemidef_gram` | the Gram matrix is positive semidefinite |
| `Matrix.posDef_gram_iff_linearIndependent` | it is positive definite if and only if $v$ is linearly independent |
| `Matrix.det_gram_ne_zero_iff_linearIndependent` | $\det G(v) \ne 0$ if and only if $v$ is linearly independent |
| `Matrix.gram_eq_one_iff_orthonormal` | $G(v) = I$ if and only if $v$ is orthonormal |
| `Matrix.gram_eq_conjTranspose_mul` | in an orthonormal basis, $G(v) = M^* M$ for the matrix $M$ of coordinates |
| `Matrix.posSemidef_opNorm_smul_gram_sub_gram` | $\lVert f \rVert^2 G(v) - G(f \circ v)$ is positive semidefinite |

The proof of positivity is one line. For $c \in \mathbb{K}^n$,
$$\bar c^{\,T} G(v)\, c = \sum_{i,j} \bar c_i \langle v_i, v_j \rangle c_j = \Big\langle \sum_i c_i v_i, \sum_j c_j v_j \Big\rangle = \Big\lVert \sum_i c_i v_i \Big\rVert^2 \ge 0,$$
the lemma `Matrix.star_dotProduct_gram_mulVec`. The value is $0$ only when $\sum_i c_i v_i = 0$, so the form is definite exactly when $v$ is independent. For $n = 2$, the determinant of the Gram matrix is $\lVert v_1 \rVert^2 \lVert v_2 \rVert^2 - |\langle v_1, v_2 \rangle|^2 \ge 0$, the inequality of Cauchy-Schwarz.

The module `Mathlib.Analysis.InnerProductSpace.ExteriorPower` uses the Gram determinant to define an inner product on the exterior power $\Lambda^n E$ of a finite dimensional real space. On decomposable elements,
$$\langle v_1 \wedge \dots \wedge v_n, w_1 \wedge \dots \wedge w_n \rangle = \det\big(\langle v_j, w_i \rangle\big)_{i,j},$$
the lemma `exteriorPower.inner_ιMulti_ιMulti`, and `exteriorPower.inner_ιMulti_self` says that $\lVert v_1 \wedge \dots \wedge v_n \rVert^2 = \det G(v)$. The definition `OrthonormalBasis.exteriorPower` gives the orthonormal basis $e_{i_1} \wedge \dots \wedge e_{i_n}$ for $i_1 < \dots < i_n$, indexed by the subsets of size $n$ of a linearly ordered index type.

#### Common errors

1. The product `E × F` has the sup norm and no inner product instance. Use `WithLp 2 (E × F)`, and move between the two types with `WithLp.toLp` and `WithLp.ofLp`.
2. `E ⊗[𝕜] F` is the algebraic tensor product. It is an inner product space, but in infinite dimension it is in general not complete. A theorem that needs `CompleteSpace` does not apply to it in infinite dimension.
3. `Matrix.gram 𝕜 v` takes the field as an explicit argument. The entry $(i, j)$ is $\langle v_i, v_j \rangle$, which is conjugate linear in $v_i$, so $G(v)$ is the transpose of the matrix with entries $\langle v_j, v_i \rangle$.

### Exercises

1. (A) Use `WithLp.prod_inner_apply` to prove that $(x, 0)$ and $(0, y)$ are orthogonal in `WithLp 2 (E × F)`.
2. (A) Prove from `TensorProduct.inner_tmul` that $x \otimes y$ and $x' \otimes y'$ are orthogonal when $x \perp x'$.
3. (B) Prove that the Gram matrix of $v$ and the Gram matrix of $(U v_i)$ are equal for a linear isometry $U$, and deduce that $\det G(v)$ is invariant under isometries.
4. (B) Let $K$ be a closed subspace of a Hilbert space $E$. Show that the norm of the class of $x$ in $E / K$ is the distance from $x$ to $K$.
5. (B) Compute $\lVert v_1 \wedge v_2 \rVert$ for $v_1 = (1, 0, 0)$ and $v_2 = (1, 1, 0)$ in $\mathbb{R}^3$, and interpret it as an area.
6. (C) Prove that the completion of `E ⊗[𝕜] F` for $E = F = \ell^2(\mathbb{N})$ is isometric to $\ell^2(\mathbb{N} \times \mathbb{N})$.

### Reference

<?reference?>
