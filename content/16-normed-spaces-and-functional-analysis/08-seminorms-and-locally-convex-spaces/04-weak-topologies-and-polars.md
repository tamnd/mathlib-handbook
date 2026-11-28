---
title: Weak topologies and polars
kind: api
modules:
  - Mathlib.Analysis.LocallyConvex.WeakDual
  - Mathlib.Analysis.LocallyConvex.WeakSpace
  - Mathlib.Analysis.LocallyConvex.Polar
  - Mathlib.Analysis.Normed.Module.Dual
  - Mathlib.Analysis.LocallyConvex.WeakOperatorTopology
  - Mathlib.Analysis.VonNeumannAlgebra.Basic
explains:
  E2: [LinearMap.weakBilin_withSeminorms, LinearMap.mem_span_iff_continuous, Convex.toWeakSpace_closure, LinearMap.polar, LinearMap.tripolar_eq_polar, NormedSpace.polar_closedBall, ContinuousLinearMapWOT, ContinuousLinearMapWOT.tendsto_iff_forall_dual_apply_tendsto, VonNeumannAlgebra, VonNeumannAlgebra.commutant_commutant]
  E1: auto
families: []
requires: [V07, V13, V14, V16.C01, V16.C05, V16.C06]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Weak topologies and polars

### Overview

A bilinear pairing $B : E \times F \to \mathbb{K}$ gives a topology on $F$: the coarsest topology for which each map $y \mapsto B(x, y)$ is continuous. This is the weak topology of the pairing. It comes from the seminorms $y \mapsto |B(x, y)|$, one for each $x \in E$, so it is locally convex and section 2 applies to it. The two main cases are the weak topology on a space $E$, from the pairing with its dual, and the weak star topology on the dual, from the pairing with $E$. The continuous linear functionals for a weak topology are exactly the functionals of the pairing.

The polar of a set $s \subseteq E$ is the set of $y \in F$ with $|B(x, y)| \le 1$ for all $x \in s$. Polars turn unions into intersections, they are closed and absolutely convex, and the polar of the polar of the polar is the polar. In a normed space, the polar of the ball of radius $r$ is the ball of radius $1 / r$ in the dual. The section ends with the weak operator topology and with von Neumann algebras, the algebras of operators on a Hilbert space that are equal to their double commutant.

### The library around it

The types `WeakBilin B`, `WeakSpace 𝕜 E` and `WeakDual 𝕜 E` are in the volume on topological algebra. `WeakBilin B` is a copy of $F$ with the weak topology of $B$, `WeakSpace 𝕜 E` is $E$ with its weak topology, and `WeakDual 𝕜 E` is the dual with the weak star topology. The module `Mathlib.Analysis.LocallyConvex.WeakDual` adds the seminorms. For a linear functional $f$, the seminorm `LinearMap.toSeminorm f` is $x \mapsto \|f x\|$. The family `LinearMap.toSeminormFamily B` has one such seminorm for each $x$. The theorem `LinearMap.weakBilin_withSeminorms` states that this family gives the weak topology, and `LinearMap.hasBasis_weakBilin` gives the basis of neighborhoods of $0$. The instance `WeakBilin.locallyConvexSpace` follows.

The functionals of a weak topology are described by `LinearMap.mem_span_iff_continuous`. A linear functional $\varphi$ is continuous for the topology of a family of functionals $f_i$ if and only if $\varphi$ is a finite linear combination of the $f_i$. The lemma `LinearMap.mem_span_iff_bound` gives the bound behind this, $\|\varphi(x)\| \le c \max_{i \in s} \|f_i(x)\|$. For the pairing of a space with its dual, `LinearMap.dualEmbedding_surjective` states that each continuous functional on the weak space comes from the pairing, and the equivalences `LinearMap.leftDualEquiv` and `LinearMap.rightDualEquiv` give the identifications.

The module `Mathlib.Analysis.LocallyConvex.WeakSpace` proves the theorem of Mazur. The map `toWeakSpace 𝕜 E` is the identity from $E$ to its weak space. For a convex set $s$ in a locally convex real space, `Convex.toWeakSpace_closure` states that the weak closure of $s$ equals its closure in the original topology. So a closed convex set is weakly closed. The lemma `toWeakSpace_closedConvexHull_eq` gives the same for the closed convex hull. The general form is `LinearMap.image_closure_of_convex`: a linear map $e$ such that $f \circ e$ is continuous for each continuous functional $f$ sends the closure of a convex set into the closure of its image. The proof applies the separation theorem of chapter 5. The instances `instT2SpaceWeakSpaceOfSeparatingDual` and `instSeparatingDualWeakSpace` state that the weak space is Hausdorff when the dual separates points.

The polar `LinearMap.polar B s` is the set of $y$ with $\|B(x, y)\| \le 1$ for all $x \in s$, by `LinearMap.polar_mem_iff`. The polar is antitone, by `LinearMap.polar_antitone`. It sends unions to intersections, by `LinearMap.polar_union` and `LinearMap.polar_iUnion`. It is closed in the weak topology, by `LinearMap.polar_isClosed`, and it is absolutely convex, by `LinearMap.polar_AbsConvex`. The lemma `LinearMap.subset_bipolar` states that $s$ is in the polar of its polar for the flipped pairing. The lemma `LinearMap.tripolar_eq_polar` states that the third polar equals the first. The polar of a subspace is its annihilator, by `LinearMap.polar_subMulAction`. The two polar maps form a Galois connection, by `LinearMap.polar_gc`.

For a topological vector space and its dual, `StrongDual.polar 𝕜 s` is the polar for the pairing `topDualPairing`, and `StrongDual.mem_polar_iff` states that $x' \in s^\circ$ if and only if $\|x'(z)\| \le 1$ for all $z \in s$. The submodule `StrongDual.polarSubmodule 𝕜 m` is the annihilator of a subspace. The module `Mathlib.Analysis.Normed.Module.Dual` computes these polars in a normed space. The lemma `NormedSpace.polar_closedBall` states that the polar of the closed ball of radius $r > 0$ is the closed ball of radius $1 / r$ in the dual, and `NormedSpace.polar_ball` states the same for the open ball. The polar of a neighborhood of $0$ is bounded, by `NormedSpace.isBounded_polar_of_mem_nhds_zero`, and the polar of a closure is the polar of the set, by `NormedSpace.polar_closure`. With the theorem of Banach-Alaoglu, `WeakDual.isCompact_closedBall` of chapter 5, these lemmas show that the polar of a neighborhood of $0$ is weak star compact.

The weak operator topology on continuous linear maps from $E$ to $F$ is the coarsest topology for which each map $A \mapsto y(A x)$ is continuous, for $x \in E$ and $y$ in the dual of $F$. The type `ContinuousLinearMapWOT` has the notation `E →WOT[𝕜] F`. It is a type synonym, and `ContinuousLinearMapWOT.toCLM` and `ContinuousLinearMapWOT.ofCLM` pass between it and `E →L[𝕜] F`. The theorem `ContinuousLinearMapWOT.tendsto_iff_forall_dual_apply_tendsto` states that $A_n \to A$ if and only if $y(A_n x) \to y(A x)$ for all $x$ and $y$. The theorem `ContinuousLinearMapWOT.withSeminorms` gives the seminorms $A \mapsto \|y(A x)\|$. Multiplication is continuous in each variable but not jointly, which is the content of `ContinuousLinearMapWOT.instIsSemitopologicalRingId`. The map `ContinuousLinearMap.WOTofCLM` is the identity from the usual topology to the weak operator topology, bundled as a continuous linear map.

The module `Mathlib.Analysis.VonNeumannAlgebra.Basic` defines `VonNeumannAlgebra H` for a complex Hilbert space $H$. It is a star subalgebra of `H →L[ℂ] H` that is equal to its double commutant. The commutant `VonNeumannAlgebra.commutant S` is again a von Neumann algebra, and `VonNeumannAlgebra.commutant_commutant` states that the commutant of the commutant is $S$. The abstract class `WStarAlgebra M` states that a $C^*$ algebra is the dual of a Banach space, by `WStarAlgebra.exists_predual`. The theorem of von Neumann that a star algebra is its own double commutant if and only if it is closed in the weak operator topology is not yet in Mathlib.

#### Common errors

1. Expecting the weak topology on a normed space to be the norm topology. In infinite dimension they differ: the unit sphere of $\ell^2$ has $0$ in its weak closure. Use `WeakSpace 𝕜 E` and the map `toWeakSpace 𝕜 E` to state results for the weak topology.
2. Confusing the two polars of a pairing. `LinearMap.polar B s` is a set in $F$ for $s \subseteq E$, and the bipolar uses the flipped pairing `LinearMap.flip`. The lemma `LinearMap.subset_bipolar` needs both.
3. Using `ContinuousLinearMapWOT` as `E →L[𝕜] F`. It is a different type with a different topology. Pass through `ContinuousLinearMapWOT.toCLM` to use the operator norm.

### Exercises

1. (A) Use `NormedSpace.polar_closedBall` to compute the polar of the closed unit ball of a normed space.
2. (A) Show that the polar of the subspace $\{(t, 0)\}$ of $\mathbb{R}^2$, for the standard pairing, is the subspace $\{(0, t)\}$.
3. (B) Prove `LinearMap.tripolar_eq_polar` from `LinearMap.subset_bipolar` and `LinearMap.polar_antitone`.
4. (B) Show that the unit vectors $e_n$ of $\ell^2$ tend to $0$ in the weak topology and not in norm.
5. (B) Use `Convex.toWeakSpace_closure` to prove that a closed subspace of a normed real space is weakly closed.
6. (C) Show that the shift operators $S^n$ on $\ell^2$, with $S e_k = e_{k+1}$, tend to $0$ in the weak operator topology, while $\|S^n x\| = \|x\|$ for all $n$.

### Reference

<?reference?>
