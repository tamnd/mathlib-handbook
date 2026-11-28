---
title: Bilinear maps, multiplication and the other operator norms
kind: api
modules:
  - Mathlib.Analysis.Normed.Operator.Bilinear
  - Mathlib.Analysis.Normed.Operator.Mul
  - Mathlib.Analysis.Normed.Operator.NNNorm
  - Mathlib.Analysis.Normed.Operator.Prod
  - Mathlib.Analysis.Normed.Operator.Asymptotics
  - Mathlib.Analysis.Normed.Operator.Conformal
  - Mathlib.Analysis.Normed.Operator.ContinuousAlgEquiv
  - Mathlib.Analysis.Normed.Operator.Extend
explains:
  E2: [ContinuousLinearMap.opNorm_le_bound₂, ContinuousLinearMap.le_opNorm₂, ContinuousLinearMap.opNorm_flip, LinearMap.mkContinuous₂_norm_le, ContinuousLinearMap.opNorm_mul, RegularNormedAlgebra, ContinuousLinearMap.opNNNorm_le_bound, ContinuousLinearMap.opNorm_prod, IsConformalMap, LinearMap.opNorm_extendOfNorm_le]
  E1: auto
families: []
requires: [V07, V13, V15, V16.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Bilinear maps, multiplication and the other operator norms

### Overview

A continuous bilinear map $B : E \times F \to G$ is, in Mathlib, a continuous linear map from $E$ into the continuous linear maps from $F$ to $G$. Its type is `E →L[𝕜] F →L[𝕜] G`. With this choice the operator norm of section 2 applies twice, and there is no separate type of bilinear maps. The bound $\|B(x, y)\| \le C \|x\| \|y\|$ is then the statement that $\|B\| \le C$. Composition, the flip of the two variables, multiplication in a normed algebra and scalar multiplication are all bilinear maps of this kind.

This section gives the API for these maps. It also gives the operator norm with values in $\mathbb{R}_{\ge 0}$ and in $[0, \infty]$, the norm of a map into a product, the asymptotic notation for linear maps, conformal linear maps, and the extension of a bounded map from a dense subspace. A short paragraph treats the algebra automorphisms of the algebra of operators.

### The library around it

The two basic estimates are `ContinuousLinearMap.le_opNorm₂`, which gives $\|f x y\| \le \|f\| \|x\| \|y\|$, and `ContinuousLinearMap.opNorm_le_bound₂`, which gives $\|f\| \le C$ from $0 \le C$ and the bound $\|f x y\| \le C \|x\| \|y\|$ for all $x$ and $y$. The second lemma is two applications of `ContinuousLinearMap.opNorm_le_bound`. The lemma `ContinuousLinearMap.le_of_opNorm₂_le_of_le` combines a bound on $\|f\|$ with bounds on $\|x\|$ and $\|y\|$.

To build a bilinear map, start with a bilinear map `E →ₗ[𝕜] F →ₗ[𝕜] G` of linear algebra and a constant. The constructor `LinearMap.mkContinuous₂` takes the constant $C$ and the bound $\|f x y\| \le C \|x\| \|y\|$. The lemma `LinearMap.mkContinuous₂_norm_le` gives $\|f\| \le C$ when $0 \le C$. The constructor `LinearMap.mkContinuous₂OfExists` takes only the existence of a constant. The bilinear maps of linear algebra come from constructors such as `LinearMap.mk₂`, which take the four laws of bilinearity.

The map `ContinuousLinearMap.flip` changes the order of the two variables. The lemma `ContinuousLinearMap.opNorm_flip` states that the flip keeps the norm, and `ContinuousLinearMap.flipₗᵢ` gives the flip as a linear isometric equivalence. Composition is also bilinear. The map `ContinuousLinearMap.compL` sends $g$ to the map $f \mapsto g \circ f$, and `ContinuousLinearMap.norm_compL_le` states that its norm is at most $1$. The semilinear version is `ContinuousLinearMap.compSL`. The maps `ContinuousLinearMap.precompL` and `ContinuousLinearMap.precompR` compose a bilinear map with a linear map on one side. The map `ContinuousLinearMap.bilinearComp` composes a bilinear map with a linear map in each variable. For calculus, `ContinuousLinearMap.map_add_add` expands $f(x + x', y + y')$, and `ContinuousLinearMap.deriv₂` is the derivative of a bilinear map as a linear map on $E \times F$.

Multiplication in a normed algebra $R$ over $\mathbb{K}$ is the bilinear map `ContinuousLinearMap.mul 𝕜 R`. The bound $\|xy\| \le \|x\| \|y\|$ gives `ContinuousLinearMap.opNorm_mul_le`, so the norm is at most $1$. Equality needs more. The class `RegularNormedAlgebra 𝕜 R` states that $x \mapsto (y \mapsto xy)$ is an isometry, so that $\|x\|$ is the operator norm of the left multiplication by $x$. Each normed algebra with $\|1\| = 1$ is regular, by the instance `NormedAlgebra.instRegularNormedAlgebra`, and each C⋆-algebra is regular, also without a unit. In a nontrivial regular algebra, `ContinuousLinearMap.opNorm_mul` gives $\|\mathrm{mul}\| = 1$, and `ContinuousLinearMap.mulₗᵢ` gives the left multiplication as a linear isometry. The map `ContinuousLinearMap.mulLeftRight` sends $(x, y)$ to $z \mapsto x z y$. The scalar multiplication $(c, x) \mapsto c x$ is `ContinuousLinearMap.lsmul`, with the norm $1$ by `ContinuousLinearMap.opNorm_lsmul` when $E$ is not trivial. The map `ContinuousLinearMap.toSpanSingletonLIE` sends $x$ to $c \mapsto c x$, and it is a linear isometric equivalence between $E$ and the maps from $\mathbb{K}$ to $E$.

The operator norm has two other forms. The norm `‖f‖₊` takes values in $\mathbb{R}_{\ge 0}$, and the extended norm `‖f‖ₑ` takes values in $[0, \infty]$. The lemmas copy the real lemmas with `NNNorm` or `ENorm` in the name. So `ContinuousLinearMap.le_opNNNorm` and `ContinuousLinearMap.opNNNorm_le_bound` are the forms of `ContinuousLinearMap.le_opNorm` and `ContinuousLinearMap.opNorm_le_bound` in $\mathbb{R}_{\ge 0}$, and `ContinuousLinearMap.le_opENorm` and `ContinuousLinearMap.opENorm_le_bound` are the extended forms. The bound in $\mathbb{R}_{\ge 0}$ needs no proof of $0 \le C$. The lemma `ContinuousLinearMap.lipschitzWith` states that $f$ is Lipschitz with constant `‖f‖₊`, and `ContinuousLinearMap.opNNNorm_le_of_lipschitzWith` gives the converse. The lemma `ContinuousLinearMap.exists_lt_apply_of_lt_opNorm` gives a vector of the unit ball where $f$ comes near its norm. The lemma `ContinuousLinearMap.sSup_sphere_eq_norm` gives the norm as a supremum on the unit sphere.

The norm of a map into a product is the maximum of the norms of the two components. The lemma `ContinuousLinearMap.opNorm_prod` states $\|f.\mathrm{prod}\, g\| = \|(f, g)\|$, where the right side uses the sup norm of the product. The map `ContinuousLinearMap.prodₗᵢ` gives this identification as a linear isometric equivalence. The lemmas `ContinuousLinearMap.norm_fst` and `ContinuousLinearMap.norm_snd` give the norm $1$ of the two projections, when the factor that the projection keeps is not trivial. The map `ContinuousLinearMap.prodMapL` is the bilinear map $(f, g) \mapsto f \times g$.

The module on asymptotics states that a continuous linear map is big O of the identity. The lemma `ContinuousLinearMap.isBigOWith_id` gives the constant $\|f\|$, and `ContinuousLinearMap.isBigO_comp` gives $g \circ f = O(f)$ along each filter. The lemma `ContinuousLinearEquiv.isBigO_comp_rev` gives the opposite bound for an equivalence. These lemmas are the base of the theory of the derivative.

A conformal linear map is a nonzero multiple of a linear isometry. The predicate `IsConformalMap f'` states that $f' = c \cdot \ell$ for a scalar $c \ne 0$ and a linear isometry $\ell$. The lemmas `isConformalMap_id`, `IsConformalMap.comp` and `LinearIsometry.isConformalMap` give the first examples. A conformal map of a nontrivial space is not zero, as `IsConformalMap.ne_zero` states. In calculus, a map is conformal at a point when its derivative at that point is a conformal linear map.

The module on algebra equivalences proves that each continuous algebra equivalence between the algebras of operators of two spaces is a conjugation. The statement `ContinuousLinearEquiv.conjContinuousAlgEquiv_surjective` gives this result when the two spaces have a separating dual. For Hilbert spaces, the same module proves that a continuous star algebra equivalence is a conjugation by a linear isometric equivalence.

The module on extensions extends a bounded linear map from a dense subspace to the whole space. The map `LinearMap.extendOfNorm` takes a linear map $f : E \to F$, a linear map $e : E \to E'$ with dense range, and a bound $\|f x\| \le C \|e x\|$, and gives a continuous linear map on $E'$. The lemma `LinearMap.extendOfNorm_eq` states that the extension agrees with $f$ on the range of $e$, and `LinearMap.opNorm_extendOfNorm_le` bounds its norm by $C$. The codomain must be complete. The isometric versions are `LinearMap.extendOfIsometry` and `LinearEquiv.extendOfIsometry`. The map `LinearIsometry.completion` extends a linear isometry to the completion. Section 2 gives the related construction `ContinuousLinearMap.extend` for a map that is already continuous.

#### Common errors

1. Writing a bilinear map as a map on $E \times F$. The type `E × F →L[𝕜] G` holds the linear maps on the product, and these are not bilinear. Use `E →L[𝕜] F →L[𝕜] G`, and apply it as `f x y`.
2. Expecting `ContinuousLinearMap.opNorm_mul` without a regular algebra. The norm of multiplication can be less than $1$ when $\|1\| > 1$. The equality needs `RegularNormedAlgebra 𝕜 R` and a nontrivial algebra.
3. Using `ContinuousLinearMap.extend` on a map that is not continuous. That construction needs a continuous map on the dense subspace. For a linear map with only a norm bound, use `LinearMap.extendOfNorm`.

### Exercises

1. (A) Show that $(x, y) \mapsto x y$ on $\mathbb{R}$ has norm $1$ as a bilinear map, with `ContinuousLinearMap.opNorm_mul`.
2. (A) Use `LinearMap.mkContinuous₂_norm_le` to show that a bilinear form $B$ on $\mathbb{R}^2$ with $|B(x, y)| \le 3 \|x\| \|y\|$ has norm at most $3$.
3. (B) Prove `ContinuousLinearMap.opNorm_flip` from `ContinuousLinearMap.le_opNorm₂` and `ContinuousLinearMap.opNorm_le_bound₂`.
4. (B) Give a normed algebra with $\|1\| = 2$, and compute the norm of the left multiplication by $1$. Explain why this algebra is not regular.
5. (B) Show that $x \mapsto 2x$ on $\mathbb{R}^2$ with the Euclidean norm satisfies `IsConformalMap`, and that a diagonal map with the entries $1$ and $2$ does not.
6. (C) Let $P$ be the subspace of polynomial functions in the continuous functions on $[0, 1]$, with the sup norm. Use `LinearMap.extendOfNorm` and the density of $P$ to extend $p \mapsto p(0)$ from $P$, and show that the extension is the evaluation at $0$.

### Reference

<?reference?>
