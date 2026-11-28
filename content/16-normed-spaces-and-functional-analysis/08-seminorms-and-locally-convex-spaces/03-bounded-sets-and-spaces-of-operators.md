---
title: Bounded sets and spaces of operators
kind: api
modules:
  - Mathlib.Analysis.LocallyConvex.Bounded
  - Mathlib.Analysis.LocallyConvex.ContinuousOfBounded
  - Mathlib.Analysis.LocallyConvex.Asymptotics
  - Mathlib.Analysis.LocallyConvex.Montel
  - Mathlib.Analysis.LocallyConvex.StrongTopology
  - Mathlib.Analysis.LocallyConvex.PointwiseConvergence
explains:
  E2: [Bornology.IsVonNBounded, Bornology.isVonNBounded_iff, Bornology.isBounded_iff_isVonNBounded, WithSeminorms.isVonNBounded_iff_seminorm_bounded, LinearMap.clmOfExistsBoundedImage, LinearMap.continuous_of_locally_bounded, MontelSpace, MontelSpace.finiteDimensional_of_normedSpace, PointwiseConvergenceCLM.withSeminorms, WithSeminorms.isBigOTVS_iff]
  E1: auto
families: []
requires: [V07, V13, V14, V16.C01, V16.C03]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Bounded sets and spaces of operators

### Overview

In a metric space a set is bounded when it lies in some ball. A topological vector space has no metric in general, but it has a notion of boundedness that uses only the neighborhoods of $0$. A set $S$ is bounded in the sense of von Neumann when each neighborhood $V$ of $0$ absorbs it: $S \subseteq c V$ for all scalars $c$ of large norm. In a normed space this agrees with the bounded sets of the metric. In a space with a family of seminorms it means that each seminorm is bounded on $S$.

The bounded sets control the continuity of linear maps and the topologies on spaces of maps. A linear map from a metrizable space is continuous if and only if it maps bounded sets to bounded sets. The space of continuous linear maps carries the topology of uniform convergence on bounded sets, the strong topology, and the topology of pointwise convergence. A space in which each closed bounded set is compact is a Montel space, and a normed Montel space has finite dimension, by the theorem of Riesz.

### The library around it

The predicate `Bornology.IsVonNBounded 𝕜 s` states that each neighborhood of $0$ absorbs $s$, by `Bornology.isVonNBounded_iff`. The bounded sets form a bornology, `Bornology.vonNBornology 𝕜 E`. Finite unions, closures, sums and images by continuous linear maps of bounded sets are bounded. The lemmas are `Bornology.isVonNBounded_union`, `Bornology.IsVonNBounded.closure`, `Bornology.isVonNBounded_add` and `Bornology.IsVonNBounded.image`. A compact set is bounded, by `IsCompact.isVonNBounded`, and so is the range of a convergent sequence, by `Filter.Tendsto.isVonNBounded_range`. A product set is bounded if and only if each projection is bounded, by `Bornology.isVonNBounded_pi_iff`.

In a normed space, `Bornology.isBounded_iff_isVonNBounded` states that the two notions of boundedness agree. The lemma `NormedSpace.isBounded_iff_subset_smul_ball` gives the form with a multiple of the unit ball. In a space with a family of seminorms $(p_i)$, `WithSeminorms.isVonNBounded_iff_seminorm_bounded` states that $s$ is bounded if and only if each $p_i$ is bounded on $s$. The lemma `WithSeminorms.isVonNBounded_iff_finset_seminorm_bounded` gives the form with finite suprema, and `WithSeminorms.image_isVonNBounded_iff_seminorm_bounded` gives the form for an image. There is also a form with sequences. The lemma `Bornology.isVonNBounded_iff_smul_tendsto_zero` states that $s$ is bounded if and only if $\varepsilon_n x_n \to 0$ for each sequence $x_n$ in $s$ and each sequence of scalars $\varepsilon_n \to 0$ with $\varepsilon_n \ne 0$.

The module `Mathlib.Analysis.LocallyConvex.ContinuousOfBounded` gives the link with continuity. The map `LinearMap.clmOfExistsBoundedImage` turns a linear map that maps some neighborhood of $0$ to a bounded set into a continuous linear map. When the source is first countable, `LinearMap.continuous_of_locally_bounded` states that a linear map that maps bounded sets to bounded sets is continuous. The proof argues by sequences. If $f$ is not continuous at $0$, there is a sequence $x_n \to 0$ with $f(x_n)$ outside a neighborhood of $0$. A sequence of scalars $c_n \to \infty$ with $c_n x_n \to 0$ gives a bounded set with an unbounded image.

The module `Mathlib.Analysis.LocallyConvex.Asymptotics` describes the relations of Landau for functions into spaces with seminorms. The relations `f =O[𝕜; l] g` and `f =o[𝕜; l] g` are `Asymptotics.IsBigOTVS` and `Asymptotics.IsLittleOTVS`. They use neighborhoods of $0$ in place of norms. The lemma `WithSeminorms.isBigOTVS_iff` states that $f = O(g)$ if and only if, for each seminorm $p_i$ of the target, there are finitely many seminorms of the source with a bound of the usual form. The lemma `WithSeminorms.isLittleOTVS_iff` is the same for small $o$. The forms `PolynormableSpace.isBigOTVS_iff` and `PolynormableSpace.isLittleOTVS_iff` use all continuous seminorms.

The proofs of these forms reduce to one seminorm at a time. The lemma `Seminorm.isBigO_comp_iff` states that $p \circ f = O(q \circ g)$ if and only if $p(f(x)) \le C \, q(g(x))$ eventually for one constant $C$, and `Seminorm.isLittleO_comp_iff` states that $p \circ f = o(q \circ g)$ if and only if the same bound holds eventually for each $\varepsilon > 0$ in place of $C$. For normed spaces the relations agree with the usual relations `Asymptotics.IsBigO` and `Asymptotics.IsLittleO`. Volume 17 uses the general relations to define derivatives of maps between spaces that have no norm.

The bounded sets also connect with the uniform boundedness principle of chapter 4. In a barrelled space, a family of continuous linear maps that is bounded at each point is equicontinuous. For a family of operators between normed spaces, this means that a set of operators is bounded for the topology of pointwise convergence if and only if it is bounded in the operator norm, when the source is a Banach space.

The class `MontelSpace 𝕜 E` states that each closed bounded set is compact, by `MontelSpace.heine_borel`. Mathlib does not ask that a Montel space be barrelled. The theorem `MontelSpace.finiteDimensional_of_normedSpace` states that a normed Montel space has finite dimension, since its closed unit ball is compact. For a Montel space $E$, `ContinuousLinearEquiv.toCompactConvergenceCLM` states that on the continuous linear maps from $E$ the strong topology and the topology of uniform convergence on compact sets are equal. The space of maps with the second topology is `CompactConvergenceCLM`.

The strong topology on `E →L[𝕜] F` is the topology of uniform convergence on bounded sets. It is the default topology of Mathlib on this type, and for normed spaces it is the topology of the operator norm. The general structure is `UniformConvergenceCLM`, which takes a family of sets, and the module `Mathlib.Analysis.LocallyConvex.StrongTopology` proves that this topology is locally convex when $F$ is locally convex. The instances are `UniformConvergenceCLM.locallyConvexSpace` and `ContinuousLinearMap.instLocallyConvexSpace`.

The topology of pointwise convergence uses the family of finite sets. The type is `PointwiseConvergenceCLM`, with the notation `E →Lₚₜ[𝕜] F`. When $F$ is a normed space, `PointwiseConvergenceCLM.seminorm` is the seminorm $A \mapsto \|A x\|$ for a fixed $x$. The theorem `PointwiseConvergenceCLM.withSeminorms` states that these seminorms give the topology, and `PointwiseConvergenceCLM.tendsto_nhds` states that $A_n \to A$ if and only if $A_n x \to A x$ for each $x$. The instance `PointwiseConvergenceCLM.instLocallyConvexSpace` states that this space is locally convex. The weak operator topology of section 4 goes one step further: it tests $A x$ against the functionals of $F$.

#### Common errors

1. Confusing `Bornology.IsBounded` and `Bornology.IsVonNBounded`. The first uses the bornology of a metric, and the second uses the neighborhoods of $0$. They agree for normed spaces, by `Bornology.isBounded_iff_isVonNBounded`, but only the second makes sense in a general topological vector space.
2. Using `LinearMap.continuous_of_locally_bounded` without `FirstCountableTopology` on the source. The proof needs sequences. For a space with seminorms, `WithSeminorms.firstCountableTopology` gives this instance from a countable family.
3. Expecting the strong topology on operators between normed spaces to be the topology of pointwise convergence. The type `E →L[𝕜] F` has the operator norm topology. Use `E →Lₚₜ[𝕜] F` for pointwise convergence.

### Exercises

1. (A) Show that the set $\{n e_n\}$ in $\ell^2$ is not bounded, with `Bornology.isBounded_iff_isVonNBounded`.
2. (A) Show that the set of functions $f_n(t) = t^n$ is bounded in the continuous functions on $[0, 1]$ with the sup norm.
3. (B) In the space of continuous functions on $\mathbb{R}$ with the seminorms $p_n(f) = \sup_{|t| \le n} |f(t)|$, show with `WithSeminorms.isVonNBounded_iff_seminorm_bounded` that a set is bounded if and only if it is uniformly bounded on each compact interval.
4. (B) Use `Bornology.isVonNBounded_iff_smul_tendsto_zero` to show that the range of a convergent sequence is bounded, and compare with `Filter.Tendsto.isVonNBounded_range`.
5. (B) Show that $\mathbb{R}^n$ is a Montel space, and use `MontelSpace.finiteDimensional_of_normedSpace` to show that $\ell^2$ is not one.
6. (C) Prove `LinearMap.continuous_of_locally_bounded` for a linear map between normed spaces, with the sequence argument of the text.

### Reference

<?reference?>
