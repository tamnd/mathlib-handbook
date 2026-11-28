---
title: Constructions of uniform spaces and uniform equivalences
kind: api
modules:
  - Mathlib.Topology.UniformSpace.Basic
  - Mathlib.Topology.UniformSpace.Pi
  - Mathlib.Topology.UniformSpace.Matrix
  - Mathlib.Topology.UniformSpace.DiscreteUniformity
  - Mathlib.Topology.UniformSpace.Separation
  - Mathlib.Topology.UniformSpace.Equiv
  - Mathlib.Topology.UniformSpace.Compact
  - Mathlib.Topology.UniformSpace.OfCompactT2
  - Mathlib.Topology.UniformSpace.Uniformizable
  - Mathlib.Topology.UniformSpace.OfFun
  - Mathlib.Topology.UniformSpace.AbsoluteValue
  - Mathlib.Topology.UniformSpace.Real
  - Mathlib.Topology.UniformSpace.Ultra.Basic
  - Mathlib.Topology.UniformSpace.Ultra.Constructions
  - Mathlib.Topology.UniformSpace.Ultra.Completion
explains:
  E2: [uniformContinuous_iff_le_comap, uniformity_comap, uniformity_prod, Pi.uniformity, cauchy_pi_iff, t0Space_iff_uniformity, lebesgue_number_lemma, unique_uniformity_of_compact, completelyRegularSpace_iff_exists_uniformSpace, UniformSpace.isClopen_ball_of_isSymm_of_isTrans_of_mem_uniformity]
  E1: auto
families: []
requires: [V04, V13.C02, V13.C04, V13.C05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Constructions of uniform spaces and uniform equivalences

### Overview

Section 1 defines a uniform space by its filter of entourages and treats uniform continuity and completeness. This section describes how the library makes new uniform spaces from old ones: pullbacks, products, sums, subtypes, function spaces and quotients. It also covers the uniform equivalences, the special uniformities of compact spaces, the uniformities that come from a distance function with values in an ordered group, and the non-archimedean uniformities.

All constructions follow one rule. The uniform structures on a type form a complete lattice, and a construction is a pullback, a pushforward, an infimum or a supremum in this lattice. So the theory is parallel to the theory of topologies in Chapter 1, and each construction on uniformities induces the matching construction on topologies.

### The library around it

#### The lattice of uniformities and the pullback

The module `Mathlib.Topology.UniformSpace.Basic` gives `UniformSpace X` a complete lattice, `instCompleteLatticeUniformSpace`. The order is the reverse of the order on uniformity filters: $u \le v$ means that $u$ has more entourages. So the bottom is the discrete uniformity, whose uniformity filter is the principal filter of the diagonal, `bot_uniformity`, and the top is the indiscrete uniformity, `top_uniformity`. A map is uniformly continuous for the identity of $X$ exactly when the uniformities compare, `le_iff_uniformContinuous_id`.

The pullback of a uniformity on $Y$ along $f : X \to Y$ is `UniformSpace.comap f`. Its entourages are the preimages under $f \times f$, by `uniformity_comap`:

$$\mathcal{U}_X = (f \times f)^* \mathcal{U}_Y.$$

The pullback has a universal property: `uniformContinuous_iff_le_comap` says that $f$ is uniformly continuous if and only if $u_X \le$ `UniformSpace.comap f` $u_Y$. The proof is the definition. Uniform continuity says that the preimage of each entourage of $Y$ is an entourage of $X$, and the right side says that each set $(f \times f)^{-1}(V)$ is in $\mathcal{U}_X$. The lemmas `UniformSpace.comap_comap`, `UniformSpace.comap_inf` and `UniformSpace.comap_iInf` say that the pullback respects composition and infima. Each construction keeps the topology: `UniformSpace.toTopologicalSpace_comap`, `UniformSpace.toTopologicalSpace_iInf` and `UniformSpace.toTopologicalSpace_inf`.

A subtype has the pullback uniformity along the coercion, `uniformity_subtype`. A product has the infimum of the two pullbacks along the projections, `uniformity_prod`:

$$\mathcal{U}_{X \times Y} = (\pi_1 \times \pi_1)^* \mathcal{U}_X \sqcap (\pi_2 \times \pi_2)^* \mathcal{U}_Y.$$

The maps `uniformContinuous_fst`, `uniformContinuous_snd` and `UniformContinuous.prodMk` give the universal property of the product. A sum has the supremum of the pushforwards along the inclusions, `Sum.uniformity`. The order dual, the universe lift, `MulOpposite` and `Additive` carry the uniformity of the base type through the instances `OrderDual.instUniformSpace`, `ULift.uniformSpace`, `instUniformSpaceMulOpposite` and `instUniformSpaceAdditive`.

The module also holds lemmas that relate the uniformity to the topology. The neighbourhoods of a point are the balls, `nhds_le_uniformity` and `UniformSpace.isOpen_ball`. The closure of a set of pairs is the intersection of the sets $V \circ s \circ V$, `closure_eq_uniformity`. The uniformity has a basis of open symmetric entourages, `uniformity_hasBasis_open_symmetric`, and a basis of closed entourages, `uniformity_hasBasis_closed`. The class `UniformContinuous₂` treats functions of two variables, with `UniformContinuous₂.comp`.

#### Products of a family, matrices and the discrete uniformity

The module `Mathlib.Topology.UniformSpace.Pi` gives the product of a family. The uniformity is the infimum of the pullbacks along the evaluation maps, `Pi.uniformity`. A filter on $\prod_i X_i$ is Cauchy if and only if each projection is Cauchy, `cauchy_pi_iff`. The proof is the formula for the uniformity: the product filter $l \times l$ is below an infimum of pullbacks exactly when it is below each one. A product of complete spaces is complete, `Pi.complete`. The lemmas `Pi.uniformContinuous_proj`, `uniformContinuous_pi` and `Pi.uniformContinuous_precomp` treat maps into and out of a product.

The module `Mathlib.Topology.UniformSpace.Matrix` uses this for `Matrix m n R`, with `Matrix.instUniformSpace` and `Matrix.instCompleteSpace`. The module `Mathlib.Topology.UniformSpace.DiscreteUniformity` defines the class `DiscreteUniformity X`: the uniformity is the bottom, by `discreteUniformity_iff_eq_bot`. Such a space has the discrete topology, `DiscreteUniformity.instDiscreteTopology`, and each function from it is uniformly continuous, `DiscreteUniformity.uniformContinuous`.

#### Separation

The module `Mathlib.Topology.UniformSpace.Separation` translates the separation axioms. Two points are inseparable if and only if each entourage contains the pair, `inseparable_iff_ker_uniformity`. So a uniform space is $T_0$ if and only if the intersection of all entourages is the diagonal, `t0Space_iff_uniformity`. Each uniform space is regular, `UniformSpace.to_regularSpace`, so a $T_0$ uniform space is $T_3$. A set whose points are pairwise far apart, for one fixed entourage, is closed, `isClosed_of_spaced_out`.

The separation quotient of Chapter 4 has a uniformity, `SeparationQuotient.instUniformSpace`. Its uniformity is the pushforward, `SeparationQuotient.uniformity_eq`. A uniformly continuous map to a $T_0$ space factors through the quotient, `SeparationQuotient.lift'` with `SeparationQuotient.uniformContinuous_lift'`.

#### Uniform equivalences

The module `Mathlib.Topology.UniformSpace.Equiv` defines `UniformEquiv X Y`, with the notation `X ≃ᵤ Y`: an equivalence with both directions uniformly continuous. It follows the pattern of the homeomorphisms of Chapter 1. There are `UniformEquiv.refl`, `UniformEquiv.symm` and `UniformEquiv.trans`, a coercion to functions through `UniformEquiv.instEquivLike`, and the forgetful map `UniformEquiv.toHomeomorph`. A uniform equivalence is a uniform embedding, `UniformEquiv.isUniformEmbedding`, and it keeps completeness, `UniformEquiv.completeSpace_iff`. The usual equivalences of products and function types exist, with the names of the equivalences of Volume 1: `UniformEquiv.prodComm`, `UniformEquiv.prodAssoc`, `UniformEquiv.piCongrLeft`, `UniformEquiv.funUnique`, `UniformEquiv.piFinTwo`. An equivalence that is a uniform inducing map gives a uniform equivalence, `Equiv.toUniformEquivOfIsUniformInducing`.

#### Compact spaces and uniformizable spaces

The module `Mathlib.Topology.UniformSpace.Compact` holds the uniform facts about compact sets. The Lebesgue number lemma `lebesgue_number_lemma` says: if a compact set $K$ is covered by open sets $U_i$, then there is an entourage $V$ such that each ball $V[x]$ with $x \in K$ lies in one $U_i$. On a compact space the uniformity is the neighbourhood filter of the diagonal, `nhdsSet_diagonal_eq_uniformity`. So a compact space has at most one uniformity that induces its topology, `unique_uniformity_of_compact`. The proof: two such uniformities both equal $\mathcal{N}(\Delta)$, which depends only on the topology. A disjoint compact set and closed set have disjoint uniform thickenings, `Disjoint.exists_uniform_thickening`.

The existence half is in `Mathlib.Topology.UniformSpace.OfCompactT2`: a compact $R_1$ space has the uniformity `uniformSpaceOfCompactR1`. The module `Mathlib.Topology.UniformSpace.Uniformizable` gives the general answer. A topology comes from a uniformity if and only if the space is completely regular, `completelyRegularSpace_iff_exists_uniformSpace`. One direction is `UniformSpace.toCompletelyRegularSpace`. For the other, the continuous maps to $[0, 1]$ give pseudometrics, and their infimum is the uniformity.

#### Uniformities from a distance function

The module `Mathlib.Topology.UniformSpace.OfFun` builds a uniformity from a function $d : X \to X \to M$ with values in an ordered additive monoid. The definition `UniformSpace.ofFun` needs $d(x, x) = 0$, symmetry, the triangle inequality and a condition that makes the sets $\{d < \varepsilon\}$ a filter basis. Its entourages have the basis given by `UniformSpace.hasBasis_ofFun`. The module `Mathlib.Topology.UniformSpace.AbsoluteValue` uses this for an absolute value on a ring: `AbsoluteValue.uniformSpace` takes $d(x, y) = |x - y|$, with the basis `AbsoluteValue.hasBasis_uniformity`. The module `Mathlib.Topology.UniformSpace.Real` holds the instances `Real.instCompleteSpace` and `NNReal.instCompleteSpace` and the coercion `ContinuousMap.coeNNRealReal`.

#### Non-archimedean uniformities

The modules under `Mathlib.Topology.UniformSpace.Ultra` treat the class `IsUltraUniformity X`. It says that the uniformity has a basis of symmetric transitive entourages. A transitive entourage $V$ satisfies $V \circ V \subseteq V$, like the relation $d(x, y) < \varepsilon$ for an ultrametric. For such $V$ the ball $V[x]$ is clopen, `UniformSpace.isClopen_ball_of_isSymm_of_isTrans_of_mem_uniformity`. The proof: the ball is open because it is a neighbourhood of each of its points by transitivity, and its complement is open because if $y \notin V[x]$, then $V[y]$ misses $V[x]$, again by transitivity and symmetry. So each point has a basis of clopen neighbourhoods, `UniformSpace.nhds_basis_clopens`.

The class passes to the constructions: `IsUltraUniformity.comap`, `IsUltraUniformity.prod`, `IsUltraUniformity.pi`, `IsUltraUniformity.inf` and `IsUltraUniformity.iInf`. It also passes to the completion, `IsUltraUniformity.completion_iff`, and to the separation quotient, `IsUltraUniformity.separationQuotient_iff`. The $p$-adic numbers are the main example.

#### Common errors

1. The order on `UniformSpace X` is the reverse of the order on uniformity filters. The bottom element is the discrete uniformity, with the most entourages.
2. `UniformSpace.comap f` takes the uniformity of the target as an explicit argument. It is not an instance. A type synonym with a pulled back uniformity must declare its instance by hand.
3. The class `IsUltraUniformity X` asks for a basis of entourages that are both symmetric and transitive. A uniformity with only one transitive entourage does not satisfy it.

### Exercises

1. (A) Prove `uniformContinuous_iff_le_comap` from the definition of uniform continuity.
2. (A) Prove that the projections from $X \times Y$ are uniformly continuous, and that a map into $X \times Y$ is uniformly continuous if both components are.
3. (B) Prove `cauchy_pi_iff`: a filter on a product is Cauchy if and only if each projection is Cauchy.
4. (B) Prove that on a compact space each entourage is a neighbourhood of the diagonal, and deduce that a compact space has at most one compatible uniformity.
5. (B) For a symmetric transitive entourage $V$, prove that the ball $V[x]$ is clopen.
6. (C) Prove the Lebesgue number lemma for a compact subset of a uniform space.

### Reference

<?reference?>
