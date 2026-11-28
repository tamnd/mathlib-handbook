---
title: Weak topologies and local convexity
kind: api
modules:
  - Mathlib.Topology.Algebra.Module.IsWeak
  - Mathlib.Topology.Algebra.Module.Spaces.WeakBilin
  - Mathlib.Topology.Algebra.Module.Spaces.WeakDual
  - Mathlib.Topology.Algebra.Module.Spaces.CharacterSpace
  - Mathlib.Topology.Algebra.Module.TopDualPairing
  - Mathlib.Topology.Algebra.Module.PerfectPairing
  - Mathlib.Topology.Algebra.Module.LocallyConvex
explains:
  E2: [LinearMap.IsWeak, LinearMap.isWeak_iff, WeakBilin, WeakDual, WeakSpace, WeakDual.tendsto_iff_forall_eval_tendsto, WeakDual.characterSpace, LinearMap.IsContPerfPair, LocallyConvexSpace, locallyConvexSpace_iff_zero]
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

## Weak topologies and local convexity

### Overview

Let $B : E \times F \to \mathbb{k}$ be a bilinear pairing. The weak topology on $E$ for $B$ is the coarsest topology that makes each map $x \mapsto B(x, y)$ continuous. Two cases matter most. The weak topology on a topological vector space $E$ comes from the pairing of $E$ with its dual, and the weak star topology on the dual comes from the same pairing read the other way. These topologies have fewer open sets than the original ones, so more sets are compact. The theorem of Banach and Alaoglu, which Volume 16 treats, is the main example.

This section describes the predicate `LinearMap.IsWeak`, the type copies `WeakBilin`, `WeakSpace` and `WeakDual`, the character space of a topological algebra, continuous perfect pairings, and the class `LocallyConvexSpace`.

### The library around it

#### The predicate for a weak topology

Let `B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜` be a bilinear map and let $E$ carry a topology `t`. The predicate `LinearMap.IsWeak B` says that `t` is the topology induced by the map $x \mapsto (y \mapsto B\,x\,y)$ from $E$ to the product $\mathbb{k}^F$. This is `LinearMap.isWeak_iff`. The predicate is a class, so lemmas take it as an instance argument.

| Lean name | Statement |
|---|---|
| `LinearMap.IsWeak.continuous_iff` | $f : \alpha \to E$ is continuous if and only if each $a \mapsto B(f a, y)$ is continuous |
| `LinearMap.IsWeak.continuous_eval` | each $x \mapsto B(x, y)$ is continuous |
| `LinearMap.IsWeak.tendsto_iff_forall_eval_tendsto` | for injective $B$, $f \to x$ if and only if $B(f, y) \to B(x, y)$ for each $y$ |
| `LinearMap.IsWeak.isEmbedding` | for injective $B$, the map $E \to \mathbb{k}^F$ is an embedding |
| `LinearMap.IsWeak.isTopologicalAddGroup` | a weak topology makes $E$ a topological additive group |
| `LinearMap.IsWeak.continuousSMul` | scalar multiplication is continuous |
| `LinearMap.IsWeak.congr` | the predicate does not depend on the form of $B$ |

The proofs are short, because an induced topology inherits the algebraic continuity of the product $\mathbb{k}^F$. The predicate separates the topology from the type, so a space can have its weak topology as its own topology, as the weak dual does.

#### Type copies with the weak topology

A type has one topology, so a second topology needs a type copy.

1. `WeakBilin B` is a copy of $E$ with the weak topology of $B$. The pairing `WeakBilin.pairing B` is $B$ on the copy, and `WeakBilin.isWeak` says that it makes the topology weak. The copy is a module and a topological additive group (`WeakBilin.instIsTopologicalAddGroup`), and `WeakBilin.linearEquiv` is the linear equivalence with $E$.
2. `WeakSpace 𝕜 E` is a copy of the topological vector space $E$ with the weak topology of the pairing with its dual. The map `toWeakSpaceCLM 𝕜 E : E →L[𝕜] WeakSpace 𝕜 E` is continuous: the weak topology is coarser. Its inverse is not continuous in general, but `WeakSpace.isOpen_of_isOpen` says that a set whose image is weakly open is open. `WeakSpace.map` sends a continuous linear map to a continuous linear map between the weak spaces.
3. `WeakDual 𝕜 E` is a copy of the dual `StrongDual 𝕜 E` with the weak star topology. The equivalence `StrongDual.toWeakDual` and its inverse `WeakDual.toStrongDual` move between the copies. A functional in the weak dual is still a continuous linear map on $E$, by `instContinuousLinearMapClassWeakDual`.

For the weak dual, convergence is pointwise convergence: `WeakDual.tendsto_iff_forall_eval_tendsto` says that $f_i \to f$ if and only if $f_i(y) \to f(y)$ for each $y \in E$. The predicate `WeakDual.isWeak` records the weak topology, and `WeakDual.instT2Space` says that the weak dual is Hausdorff when $\mathbb{k}$ is. The previous section identifies the weak dual with the space `E →Lₚₜ[𝕜] 𝕜` of pointwise convergence.

#### The character space

Let $A$ be a topological algebra over $\mathbb{k}$. A *character* is a nonzero continuous algebra homomorphism $A \to \mathbb{k}$. The set `WeakDual.characterSpace 𝕜 A` is the set of characters inside the weak dual. It carries the weak star topology, and it is the space of the Gelfand theory of commutative Banach algebras.

| Lean name | Statement |
|---|---|
| `WeakDual.CharacterSpace.isClosed` | for a unital algebra, the character space is closed in the weak dual |
| `WeakDual.CharacterSpace.union_zero_isClosed` | the character space with $0$ added is closed |
| `WeakDual.CharacterSpace.toAlgHom` | a character as an algebra homomorphism |
| `WeakDual.CharacterSpace.apply_mem_spectrum` | $\varphi(a)$ is in the spectrum of $a$ |
| `WeakDual.ker_isMaximal` | the kernel of a character is a maximal ideal |
| `WeakDual.CharacterSpace.ext_ker` | two characters with the same kernel are equal |
| `WeakDual.gelfandTransform` | the map $A \to C(\text{characters}, \mathbb{k})$, $a \mapsto (\varphi \mapsto \varphi(a))$ |

The proof of `WeakDual.CharacterSpace.apply_mem_spectrum` is one line: $a - \varphi(a)$ lies in the kernel of $\varphi$, so it is not a unit. The closedness results hold because the conditions $\varphi(ab) = \varphi(a)\varphi(b)$ and $\varphi(1) = 1$ are closed conditions in the topology of pointwise convergence.

#### Continuous perfect pairings

The predicate `LinearMap.IsContPerfPair B` says that the pairing $B : M \times N \to R$ is continuous and that both induced maps, from $M$ to the dual of $N$ and from $N$ to the dual of $M$, are bijective. The fields give `LinearMap.IsContPerfPair.continuous_uncurry`, `LinearMap.IsContPerfPair.bijective_left` and `LinearMap.IsContPerfPair.bijective_right`. The map `LinearMap.toContPerfPair` is the induced equivalence, and the instance `LinearMap.flip.instIsContPerfPair` says that the flip of a perfect pairing is perfect.

The module `Mathlib.Topology.Algebra.Module.TopDualPairing` has one result. In a finite dimensional Hausdorff space over a complete nontrivially normed field, the pairing of $E$ with its dual is perfect: `topDualPairing_isContPerfPair`.

#### Locally convex spaces

The class `LocallyConvexSpace 𝕜 E` says that each point has a basis of convex neighbourhoods. In a topological additive group it is enough to ask this at $0$: `locallyConvexSpace_iff_zero` says that the class holds if and only if the convex neighbourhoods of $0$ form a basis. Normed spaces and weak topologies are locally convex. To prove the class, `LocallyConvexSpace.ofBasisZero` takes a basis of $\mathcal{N}(0)$ by convex sets.

The class is closed under the usual constructions.

1. An infimum of locally convex topologies is locally convex (`LocallyConvexSpace.iInf`, `LocallyConvexSpace.sInf`, `LocallyConvexSpace.inf`).
2. An induced topology from a locally convex space is locally convex (`LocallyConvexSpace.induced`, `Topology.IsInducing.locallyConvexSpace`).
3. Products and Pi types of locally convex spaces are locally convex (`Prod.locallyConvexSpace`, `Pi.locallyConvexSpace`).
4. A submodule of a locally convex space is locally convex (`instLocallyConvexSpaceSubtypeMemSubmodule`).
5. An ordered field with its order topology is locally convex over itself (`LinearOrderedSemiring.toLocallyConvexSpace`).

The first two items prove that each weak topology is locally convex: it is induced from a product of copies of $\mathbb{k}$.

The geometric results use convex neighbourhoods to separate sets. `Disjoint.exists_open_convexes` says that a compact convex set and a disjoint closed convex set lie in disjoint open convex sets. The case of a point is `exists_open_convex_of_notMem`. These results are the first step of the geometric Hahn and Banach theorem. A real locally convex space is locally path connected (`LocallyConvexSpace.toLocallyPathConnectedSpace`), because a convex set contains the segment between two of its points.

#### Common errors

1. A lemma about `StrongDual 𝕜 E` does not apply to `WeakDual 𝕜 E`. Use `StrongDual.toWeakDual` and `WeakDual.toStrongDual` to move between the types; the functionals are the same, but the topologies differ.
2. `LinearMap.IsWeak.tendsto_iff_forall_eval_tendsto` needs the injectivity of $B$. Without it, the weak topology is not Hausdorff and a sequence can converge to two limits.
3. `LocallyConvexSpace 𝕜 E` needs a partial order on $\mathbb{k}$. For complex spaces, the usual form is `LocallyConvexSpace ℝ E`, with the real scalars.

### Exercises

1. (A) Prove from `WeakDual.tendsto_iff_forall_eval_tendsto` that the coordinate functionals $e_n^*$ on $\ell^2$ tend to $0$ in the weak dual.
2. (A) Show that $\mathbb{R}$ with its usual topology is a locally convex space over itself, and find the instance.
3. (B) Prove that a character $\varphi$ of a unital algebra satisfies $\varphi(1) = 1$, and deduce `WeakDual.CharacterSpace.apply_mem_spectrum` for $a = 1$.
4. (B) Show that the weak topology of a pairing is locally convex, with `LocallyConvexSpace.induced` and `Pi.locallyConvexSpace`.
5. (C) Prove that the unit sphere of an infinite dimensional normed space is dense in the unit ball for the weak topology.

### Reference

<?reference?>
