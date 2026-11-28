---
title: Continuous multilinear and alternating maps
kind: api
modules:
  - Mathlib.Topology.Algebra.Module.Multilinear.Basic
  - Mathlib.Topology.Algebra.Module.Multilinear.Bounded
  - Mathlib.Topology.Algebra.Module.Multilinear.Topology
  - Mathlib.Topology.Algebra.Module.Alternating.Basic
  - Mathlib.Topology.Algebra.Module.Alternating.Topology
explains:
  E2: [ContinuousMultilinearMap, ContinuousMultilinearMap.linearDeriv, ContinuousMultilinearMap.mkPiRing, ContinuousMultilinearMap.hasBasis_nhds_zero, ContinuousMultilinearMap.completeSpace, Bornology.IsVonNBounded.image_multilinear, ContinuousAlternatingMap, ContinuousMultilinearMap.alternatization, ContinuousAlternatingMap.isClosedEmbedding_toContinuousMultilinearMap]
  E1: auto
families: []
requires: [V07, V13.C01, V13.C04, V14.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Continuous multilinear and alternating maps

### Overview

A multilinear map $f : \prod_i E_i \to F$ is linear in each variable when the other variables are fixed. The determinant, the product of $n$ numbers and the $n$-th derivative of a smooth map are examples. In analysis these maps must be continuous, and the space of continuous multilinear maps must have a topology: the higher derivatives of a function take values in it.

This section describes the type `ContinuousMultilinearMap R M₁ M₂`, with the notation `M [×n]→L[R] N` for maps of $n$ variables in one module, and the type `ContinuousAlternatingMap R M N ι` of continuous maps that vanish when two arguments are equal, with the notation `M [⋀^ι]→L[R] N`. It then describes the topology of uniform convergence on bounded sets on these types. For normed spaces, Volume 16 gives the operator norm on the same types; the topology there is the same.

### The library around it

#### The type of continuous multilinear maps

A term of `ContinuousMultilinearMap R M₁ M₂` is a structure with two fields: a multilinear map `ContinuousMultilinearMap.toMultilinearMap` and its continuity `ContinuousMultilinearMap.cont` for the product topology on $\prod_i M_1(i)$. The coercion to functions is injective (`ContinuousMultilinearMap.toMultilinearMap_injective`), and `ContinuousMultilinearMap.ext` proves equality from equality at each point.

The algebraic rules of multilinear maps have continuous forms with the same names.

| Lean name | Statement |
|---|---|
| `ContinuousMultilinearMap.map_update_add` | $f(\dots, x + y, \dots) = f(\dots, x, \dots) + f(\dots, y, \dots)$ |
| `ContinuousMultilinearMap.map_update_smul` | $f(\dots, c x, \dots) = c \, f(\dots, x, \dots)$ |
| `ContinuousMultilinearMap.map_coord_zero` | if one argument is $0$, then $f(m) = 0$ |
| `ContinuousMultilinearMap.map_smul_univ` | $f(c_1 m_1, \dots, c_n m_n) = (\prod_i c_i) f(m)$ |
| `ContinuousMultilinearMap.map_add_univ` | $f(m + m')$ is the sum of $f$ over all mixtures of $m$ and $m'$ |
| `ContinuousMultilinearMap.map_sum_finset` | the expansion of $f$ at a family of finite sums |

The type is an additive commutative monoid, a group when $M_2$ is a topological additive group, and a module when the scalars act continuously on $M_2$. A continuous multilinear map is not continuous in a uniform way: the map $(x, y) \mapsto x y$ on $\mathbb{R}^2$ is continuous, but not uniformly continuous.

#### Constructions

The library builds new maps from old ones in the usual ways.

1. `ContinuousMultilinearMap.compContinuousLinearMap` composes with a continuous linear map in each argument, and `ContinuousLinearMap.compContinuousMultilinearMap` composes with a continuous linear map at the output.
2. `ContinuousMultilinearMap.prod` and `ContinuousMultilinearMap.pi` combine maps with the same arguments into a map to a product. The equivalences `ContinuousMultilinearMap.prodEquiv` and `ContinuousMultilinearMap.piEquiv` say that this gives all maps to a product.
3. `ContinuousMultilinearMap.domDomCongr` renames the index type along an equivalence $\iota \simeq \iota'$.
4. `ContinuousMultilinearMap.mkPiRing R ι z` is the map $(m_i) \mapsto (\prod_i m_i) z$ on $R^\iota$. By `ContinuousMultilinearMap.mkPiRing_apply_one_eq_self`, each continuous multilinear map on $R^\iota$ has this form, with $z = f(1, \dots, 1)$.
5. `ContinuousMultilinearMap.uncurry0` and `ContinuousMultilinearMap.curry0` identify maps of zero variables with constants. A map of zero variables is constant, and `ContinuousMultilinearMap.constOfIsEmpty` is the general form.
6. `ContinuousMultilinearMap.toContinuousLinearMap f m i` fixes all arguments except the $i$-th one and gives a continuous linear map.
7. `ContinuousMultilinearMap.restrictScalars` and `ContinuousMultilinearMap.codRestrict` change the scalars and the codomain.

The derivative of a multilinear map is linear in the increment. `ContinuousMultilinearMap.linearDeriv f x` is the continuous linear map $y \mapsto \sum_i f(x_1, \dots, y_i, \dots, x_n)$, and `ContinuousMultilinearMap.linearDeriv_apply` gives this formula. Calculus uses this map as the Fréchet derivative of $f$ at $x$.

#### Bounded sets

A set $s$ in a topological vector space is von Neumann bounded if each neighbourhood of $0$ absorbs it. The lemma `Bornology.IsVonNBounded.image_multilinear` says that a continuous multilinear map sends bounded sets to bounded sets. The proof works one variable at a time: scale $m_i$ by $c_i$ to put it into a small neighbourhood, and the factor $\prod_i c_i$ goes out of $f$ by `ContinuousMultilinearMap.map_smul_univ`. The form `Bornology.IsVonNBounded.image_multilinear'` needs a nonempty index type in place of continuous scalar multiplication on the codomain.

#### The topology on the space of maps

The type `ContinuousMultilinearMap 𝕜 E F` carries the topology of uniform convergence on von Neumann bounded sets. This is the multilinear form of the topology of the space `E →L[𝕜] F` of the earlier section. The map `ContinuousMultilinearMap.toUniformOnFun` sends a map to the type of functions with this uniform structure, and `ContinuousMultilinearMap.isUniformEmbedding_toUniformOnFun` says that it is a uniform embedding. So the space is a uniform additive group (`ContinuousMultilinearMap.instIsUniformAddGroup`).

| Lean name | Statement |
|---|---|
| `ContinuousMultilinearMap.hasBasis_nhds_zero` | the sets $\{f \mid f(S) \subseteq V\}$ with $S$ bounded and $V \in \mathcal{N}(0)$ form a basis at $0$ |
| `ContinuousMultilinearMap.instContinuousSMul` | scalar multiplication is continuous |
| `ContinuousMultilinearMap.instT2Space` | the space is Hausdorff when $F$ is |
| `ContinuousMultilinearMap.instContinuousEvalConstForall` | for fixed $m$, the map $f \mapsto f(m)$ is continuous |
| `ContinuousMultilinearMap.hasSum_eval` | if $\sum_a p_a = q$, then $\sum_a p_a(m) = q(m)$ |
| `ContinuousMultilinearMap.isVonNBounded_image2_apply` | a bounded set of maps on a bounded set of points gives a bounded set |
| `ContinuousMultilinearMap.completeSpace` | the space is complete when $F$ is complete and the topology is coherent with the bounded sets |
| `ContinuousMultilinearMap.instCompleteSpace` | the instance form, when $\prod_i E_i$ is a sequential space |

The coherence condition in `ContinuousMultilinearMap.completeSpace` says that a set is closed when its intersection with each bounded set is closed. Metrizable spaces satisfy it, so the space of maps between Banach spaces is complete. The continuous linear maps `ContinuousMultilinearMap.compContinuousLinearMapL` and `ContinuousLinearMap.compContinuousMultilinearMapL` are the compositions of the earlier part, with continuity in the map.

#### Continuous alternating maps

A continuous alternating map `f : M [⋀^ι]→L[R] N` is a continuous multilinear map of the variables $m_i \in M$ that vanishes when $m_i = m_j$ for some $i \ne j$. The structure extends `ContinuousMultilinearMap`, with the extra field `ContinuousAlternatingMap.map_eq_zero_of_eq'`. The projection `ContinuousAlternatingMap.toContinuousMultilinearMap` forgets the extra field, and `ContinuousAlternatingMap.toAlternatingMap` forgets the continuity.

The library repeats the multilinear API for alternating maps, with the same names: `ContinuousAlternatingMap.map_add_univ`, `ContinuousAlternatingMap.prod`, `ContinuousAlternatingMap.pi`, `ContinuousAlternatingMap.compContinuousLinearMap` and others. Two results are new. `ContinuousAlternatingMap.map_eq_zero_of_not_injective` says that $f(v) = 0$ when $v$ is not injective. `ContinuousMultilinearMap.alternatization` turns a multilinear map $g$ into the alternating map $\sum_\sigma \operatorname{sign}(\sigma) \, g \circ \sigma$; its continuous linear form is `ContinuousMultilinearMap.alternatizationL`.

The topology on the alternating maps is the topology induced from the multilinear maps. For a Hausdorff target, `ContinuousAlternatingMap.isClosedEmbedding_toContinuousMultilinearMap` says that the projection is a closed embedding: the condition $f(v) = 0$ for $v$ with two equal entries is a closed condition. So the space of alternating maps is complete when the space of multilinear maps is complete (`ContinuousAlternatingMap.completeSpace`). To build a continuous linear map to the alternating maps, `ContinuousAlternatingMap.liftCLM` takes a continuous linear map to the multilinear maps whose values are alternating.

#### Common errors

1. A lemma about `ContinuousMultilinearMap` does not apply to a continuous alternating map at once. Apply it to `ContinuousAlternatingMap.toContinuousMultilinearMap f`, or look for the lemma with the same name in the namespace `ContinuousAlternatingMap`.
2. The notation `M [×n]→L[R] N` is for $n$ copies of one module, indexed by `Fin n`. A map on a family `E : ι → Type*` needs the full form `ContinuousMultilinearMap R E N`.
3. `ContinuousMultilinearMap.completeSpace` takes the coherence condition as an explicit hypothesis. For normed spaces, use the instance from the normed space library and do not prove the condition by hand.

### Exercises

1. (A) Show that the map $(x, y) \mapsto x y$ on $\mathbb{R}^2$ is `ContinuousMultilinearMap.mkPiRing ℝ (Fin 2) 1`.
2. (A) Use `ContinuousMultilinearMap.map_coord_zero` to prove that $f(m) = 0$ when one coordinate of $m$ is $0$.
3. (B) Compute `ContinuousMultilinearMap.linearDeriv` of the product map $(x_1, x_2, x_3) \mapsto x_1 x_2 x_3$ on $\mathbb{R}^3$ at a point.
4. (B) Prove that the alternatization of the map $(x, y) \mapsto x_1 y_2$ on $\mathbb{R}^2 \times \mathbb{R}^2$ is the determinant of the matrix with columns $x$ and $y$.
5. (C) Prove that if $p_n \to q$ in the space of continuous multilinear maps, then $p_n(m) \to q(m)$ for each $m$, and explain why the converse fails.

### Reference

<?reference?>
