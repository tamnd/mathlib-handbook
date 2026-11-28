---
title: Proper cones, duality and doubly stochastic matrices
kind: api
modules:
  - Mathlib.Analysis.Convex.Cone.Basic
  - Mathlib.Analysis.Convex.Cone.Closure
  - Mathlib.Analysis.Convex.Cone.Dual
  - Mathlib.Analysis.Convex.Cone.InnerDual
  - Mathlib.Analysis.Convex.Cone.TensorProduct
  - Mathlib.Analysis.Convex.DoublyStochasticMatrix
  - Mathlib.Analysis.Convex.Birkhoff
explains:
  E2: [ProperCone, ProperCone.dual, ProperCone.dual_dual_flip, ProperCone.hyperplane_separation_point, ProperCone.innerDual, ProperCone.relative_hyperplane_separation, PointedCone.minTensorProduct_eq_max_of_simplicial_generating_left, doublyStochastic, doublyStochastic_eq_convexHull_permMatrix, exists_eq_sum_perm_of_mem_doublyStochastic]
  E1: auto
families: []
requires: [V07, V13, V16.C01, V16.C05, V16.C06]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Proper cones, duality and doubly stochastic matrices

### Overview

A convex cone is a convex set that is closed under multiplication by positive scalars. A pointed cone also contains $0$, so it is a submodule over the nonnegative scalars. A proper cone is a pointed cone that is closed. Proper cones are the feasible sets of conic programs, which generalize linear programs: a linear program uses the cone of vectors with nonnegative coordinates, and a semidefinite program uses the cone of positive semidefinite matrices.

The dual of a set $s$ is the cone of functionals that are nonnegative on $s$. The main theorem is the bipolar theorem: in a locally convex space, a proper cone is equal to its double dual. Its proof is a separation argument. If $x_0$ is not in the closed cone $C$, the geometric Hahn Banach theorem of Chapter 5 gives a continuous functional $f$ with $f \ge 0$ on $C$ and $f(x_0) < 0$. In a Hilbert space, the dual of a cone is again a cone in the same space, by the Riesz representation of Chapter 7. The theorem of Farkas follows: a vector $b$ is in the image $A(C)$ of a proper cone under a bounded operator if and only if $\langle b, y \rangle \ge 0$ for all $y$ with $A^* y$ in the dual of $C$. In this form $A(C)$ means the closure of the image, which is again a proper cone.

The second topic is the set of doubly stochastic matrices, the square matrices with nonnegative entries whose rows and columns sum to $1$. This set is convex and contains each permutation matrix. The theorem of Birkhoff says that it is exactly the convex hull of the permutation matrices, and that these are its extreme points.

### The library around it

The file `Mathlib.Analysis.Convex.Cone.Basic` defines `ProperCone R E` as an abbreviation for `ClosedSubmodule R≥0 E`, the closed submodules of `E` over the nonnegative elements of `R`. So a proper cone has a coercion to `PointedCone R E` by `ProperCone.toPointedCone`, membership `ProperCone.mem_toPointedCone`, and the lemmas `ProperCone.isClosed`, `ProperCone.nonempty`, `ProperCone.convex` and `ProperCone.smul_mem`. The partial order on proper cones is inclusion, and `ProperCone.mem_bot` says that the smallest cone is `{0}`. In an ordered module, `ProperCone.positive R E` is the cone of nonnegative vectors, with `ProperCone.mem_positive`. A continuous linear map `f` pushes cones forward with `ProperCone.map f`, which takes the closure of the image, and pulls them back with `ProperCone.comap f`. The lemmas `ProperCone.mem_map`, `ProperCone.comap_comap` and `ProperCone.map_id` describe these operations. The lemma `ConvexCone.Pointed.of_nonempty_of_isClosed` says that a closed nonempty convex cone over a dense field contains $0$, and `ConvexCone.canLift` uses it to turn such a cone into a proper cone with the lift tactic.

The file `Mathlib.Analysis.Convex.Cone.Closure` defines `ConvexCone.closure` and `PointedCone.closure`, the topological closure of a cone, which is a cone again. The lemmas `ConvexCone.coe_closure`, `ConvexCone.mem_closure` and `ConvexCone.closure_eq` describe it, and `PointedCone.closure_eq` says that the closure of a closed cone is the cone.

The file `Mathlib.Analysis.Convex.Cone.Dual` defines the dual with respect to a bilinear pairing `p : M →ₗ[R] N →ₗ[R] R` that is a continuous perfect pairing. The cone `ProperCone.dual p s` is the set of `y : N` with `0 ≤ p x y` for all `x ∈ s`, as `ProperCone.mem_dual` says, and `PointedCone.isClosed_dual` explains why it is closed. The lemmas `ProperCone.dual_union`, `ProperCone.dual_iUnion`, `ProperCone.dual_singleton`, `ProperCone.dual_zero`, `ProperCone.dual_univ` and `ProperCone.dual_le_dual` give the algebra of duals, and `ProperCone.subset_dual_dual` is the easy half of the bipolar theorem. The separation results are `ProperCone.hyperplane_separation_point`, for a point outside a proper cone, and `ProperCone.hyperplane_separation`, for a compact convex set disjoint from it, in a real locally convex space. The bipolar theorem is `ProperCone.dual_dual_flip`: the dual for `p` of the dual for `p.flip` of `C` is `C`, and `ProperCone.dual_flip_dual` is the same with the roles exchanged.

The file `Mathlib.Analysis.Convex.Cone.InnerDual` treats a real Hilbert space, where the pairing is the inner product. The cone `ProperCone.innerDual s` is the set of `y` with $\langle x, y \rangle \ge 0$ for all $x \in s$, with `ProperCone.mem_innerDual` and the analogues of the lemmas above. The bipolar theorem is `ProperCone.innerDual_innerDual`. The Farkas lemma has two forms. `ProperCone.hyperplane_separation_of_notMem` says that if `b` is not in `ProperCone.map f K`, then there is `y` with `f† y` in the inner dual of `K` and $\langle b, y \rangle < 0$, where `f†` is the adjoint `ContinuousLinearMap.adjoint f`. `ProperCone.relative_hyperplane_separation` is the equivalence: `b` is in the image cone if and only if $\langle b, y \rangle \ge 0$ for all such `y`. Since `ProperCone.map` takes the closure of the image, this statement holds with no extra hypothesis on `f`.

The file `Mathlib.Analysis.Convex.Cone.TensorProduct` proves one result on tensor products of cones in finite dimensional real spaces. The minimal tensor product of two cones is generated by the tensors $x \otimes y$ with $x$ and $y$ in the cones, and the maximal one is the dual of the minimal tensor product of the dual cones. The theorem `PointedCone.minTensorProduct_eq_max_of_simplicial_generating_left` says that the two agree when the first cone is simplicial and spans the space and the second is proper, and `PointedCone.minTensorProduct_eq_max_of_simplicial_generating_right` is the mirror form. The proof uses `PointedCone.basis_coord_mem_dual`, which says that the coordinate functionals of a basis are in the dual of each cone inside the hull of the basis, together with the bipolar theorem.

The file `Mathlib.Analysis.Convex.DoublyStochasticMatrix` defines `doublyStochastic R n` as a submonoid of `Matrix n n R`, so a product of doubly stochastic matrices is doubly stochastic. The lemma `mem_doublyStochastic` gives the definition: nonnegative entries, `M *ᵥ 1 = 1` and `1 ᵥ* M = 1`, and `mem_doublyStochastic_iff_sum` states it with sums. The lemma `doublyStochastic_eq_rowStochastic_inf_colStochastic` writes the set as the intersection of the row stochastic and column stochastic matrices of the matrix library. The basic facts are `convex_doublyStochastic`, `permMatrix_mem_doublyStochastic`, `transpose_mem_doublyStochastic_iff`, `nonneg_of_mem_doublyStochastic` and `le_one_of_mem_doublyStochastic`. The lemma `exists_mem_doublyStochastic_eq_smul_iff` characterizes the nonnegative matrices with all row and column sums equal to $s$ as the multiples $s M'$ of doubly stochastic matrices.

The file `Mathlib.Analysis.Convex.Birkhoff` proves the Birkhoff theorem. The main step is `exists_eq_sum_perm_of_mem_doublyStochastic`, which writes each doubly stochastic matrix as a convex combination of permutation matrices. Its proof is by strong induction on the number of nonzero entries. The Hall marriage theorem gives a permutation $\sigma$ with $M_{i \sigma(i)} > 0$ for each $i$. With $c$ the smallest of these entries, $M - c P_\sigma$ is $1 - c$ times a doubly stochastic matrix with fewer nonzero entries, by `exists_mem_doublyStochastic_eq_smul_iff`. Then `doublyStochastic_eq_convexHull_permMatrix` is the set equality, and `extremePoints_doublyStochastic` identifies the extreme points with the permutation matrices, with `Set.extremePoints` from the theory of extreme points. A consequence for norms is `Matrix.l2_opNorm_le_one_of_mem_doublyStochastic`: a real doubly stochastic matrix has operator norm at most $1$ on the Euclidean space.

#### Common errors

1. `ProperCone.dual` takes a pairing, not just a space. For the dual cone in a Hilbert space, use `ProperCone.innerDual`, and for the topological dual, use the pairing of `E` with its dual.
2. `ProperCone.map f C` is the closure of `f '' C`, not the image itself. A membership statement in `ProperCone.map f C` does not give a preimage point in `C`.
3. `doublyStochastic R n` is a submonoid, so membership is `M ∈ doublyStochastic R n`. Use `mem_doublyStochastic` to unfold it, not a lemma on set builder notation.

### Exercises

1. (A) Prove that `ProperCone.innerDual` reverses inclusion, with `ProperCone.mem_innerDual`.
2. (A) Show that the identity matrix is doubly stochastic with `permMatrix_mem_doublyStochastic`.
3. (B) Compute the inner dual of the cone of vectors with nonnegative coordinates in `EuclideanSpace ℝ (Fin n)`.
4. (B) Derive the classical Farkas lemma for a real matrix $A$ from `ProperCone.relative_hyperplane_separation`, with the positive cone.
5. (B) Prove that a doubly stochastic matrix with entries in $\{0, 1\}$ is a permutation matrix.
6. (C) Prove that each $3 \times 3$ doubly stochastic matrix is a convex combination of at most $5$ permutation matrices, with the Carathéodory theorem.

### Reference

<?reference?>
