---
title: Balanced sets and topologies from seminorms
kind: api
modules:
  - Mathlib.Analysis.LocallyConvex.Basic
  - Mathlib.Analysis.LocallyConvex.BalancedCoreHull
  - Mathlib.Analysis.LocallyConvex.AbsConvex
  - Mathlib.Analysis.LocallyConvex.AbsConvexOpen
  - Mathlib.Analysis.LocallyConvex.WithSeminorms
explains:
  E2: [Balanced, balanced_iff_smul_mem, balancedCore, balancedHull, nhds_basis_balanced, AbsConvex, absConvexHull_eq_convexHull_balancedHull, WithSeminorms, WithSeminorms.hasBasis_zero_ball, PolynormableSpace]
  E1: auto
families: []
requires: [V07, V13, V14, V16.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Balanced sets and topologies from seminorms

### Overview

The balls of a seminorm at $0$ have three properties. They are convex. They are balanced: if $x$ is in the ball and $|c| \le 1$, then $c x$ is in the ball. They are absorbent: each vector is in some multiple of the ball. A topological vector space in which $0$ has a basis of convex neighborhoods is locally convex, and in such a space the neighborhoods can also be taken balanced. The gauge of such a neighborhood is a continuous seminorm, so the topology of a locally convex space comes from a family of seminorms.

This section gives the sets and the families. A set that is convex and balanced is absolutely convex. Each set has a largest balanced subset, its balanced core, and a smallest balanced superset, its balanced hull. A family of seminorms $(p_i)_{i \in I}$ defines a topology: a set $U$ is a neighborhood of $x$ when it contains a ball $\{y \mid \max_{i \in s} p_i(y - x) < r\}$ for a finite set $s$ and some $r > 0$. The predicate `WithSeminorms` states that the topology of a space is this topology. The spaces of continuous functions with uniform convergence on compact sets, the spaces of smooth functions and the weak topologies of section 4 are all of this kind, so one set of lemmas covers all of them.

### The library around it

The predicate `Balanced 𝕜 s` states that $a \cdot s \subseteq s$ for each scalar $a$ with $\|a\| \le 1$, and `balanced_iff_smul_mem` gives the form with elements. The predicates `Absorbs 𝕜 s t` and `Absorbent 𝕜 s` are in the theory of bornologies. The first states that $t \subseteq c \cdot s$ for all scalars $c$ of large norm, and `absorbs_iff_norm` gives this form. The second states that $s$ absorbs each point. Each neighborhood of $0$ in a topological vector space is absorbent, by `absorbent_nhds_zero`. Balanced sets are closed under unions, intersections, images and preimages by linear maps, closures, and convex hulls. The lemmas are `balanced_iUnion`, `balanced_iInter`, `Balanced.image`, `Balanced.closure` and `Balanced.convexHull`. A balanced set is symmetric, by `Balanced.neg_eq`. Over $\mathbb{R}$, `balanced_iff_neg_mem` states that a convex set is balanced if and only if it is symmetric.

The module on the balanced core and hull defines `balancedCore 𝕜 s`, the union of all balanced subsets of $s$, and `balancedHull 𝕜 s`, the set of all $a \cdot x$ with $\|a\| \le 1$ and $x \in s$. The hull is a `ClosureOperator` on sets, so the general lemmas on closure operators apply to it. The lemmas `balancedCore.balanced` and `balancedHull.balanced` state that both sets are balanced, and `balancedHull_eq_iUnion` and `balancedCore_eq_iInter` give the explicit forms. The core of a neighborhood of $0$ is a neighborhood of $0$, by `balancedCore_mem_nhds_zero`. From this, `nhds_basis_balanced`, `nhds_basis_open_balanced` and `nhds_basis_closed_balanced` give three bases of balanced neighborhoods of $0$ in each topological vector space.

The predicate `AbsConvex 𝕜 s` states that $s$ is balanced and convex. The closure operator `absConvexHull 𝕜` gives the smallest absolutely convex superset, and `closedAbsConvexHull 𝕜` gives the smallest closed one. The lemma `absConvexHull_eq_convexHull_balancedHull` states that the absolutely convex hull is the convex hull of the balanced hull. Over $\mathbb{R}$, `convexHull_union_neg_eq_absConvexHull` states that it is the convex hull of $s \cup -s$. The lemma `closedAbsConvexHull_eq_closure_absConvexHull` gives the closed hull as a closure. The lemma `isCompact_closedAbsConvexHull_of_totallyBounded` states that, in a complete locally convex real space, the closed absolutely convex hull of a totally bounded set is compact.

The type `AbsConvexOpenSets 𝕜 E` is the type of absolutely convex open sets that contain $0$. Over $\mathbb{R}$ or $\mathbb{C}$, `gaugeSeminormFamily 𝕜 E` is the family of their gauges, and `gaugeSeminormFamily_ball` states that the unit ball of the gauge of $s$ is $s$. The theorem `with_gaugeSeminormFamily` states that the topology of a locally convex space is given by this family. The instance `LocallyConvexSpace.toPolynormableSpace` gives the same fact as a class.

The module `Mathlib.Analysis.LocallyConvex.WithSeminorms` has the main definitions. A `SeminormFamily 𝕜 E ι` is a function from $\iota$ to `Seminorm 𝕜 E`. The sets `SeminormFamily.basisSets p` are the balls at $0$ of the finite suprema, and `SeminormFamily.moduleFilterBasis p` turns them into a filter basis with a topology. The structure `WithSeminorms p` states that the topology of $E$ is this topology. The lemmas `WithSeminorms.hasBasis_zero_ball` and `WithSeminorms.hasBasis_ball` give the basis of neighborhoods at $0$ and at each point. The lemma `WithSeminorms.mem_nhds_iff` gives the form with elements. The lemma `WithSeminorms.tendsto_nhds` states that $u \to y$ if and only if $p_i(u - y) \to 0$ for each $i$. When the family is directed, `WithSeminorms.hasBasis_zero_ball_of_directed` gives a basis with a single seminorm in each ball. The norm gives `norm_withSeminorms`, a family with one seminorm.

The lemma `WithSeminorms.continuous_seminorm` states that each $p_i$ is continuous. The lemma `Seminorm.bound_of_continuous` states that each continuous seminorm $q$ satisfies $q \le C \max_{i \in s} p_i$ for a finite set $s$ and a constant $C$. The lemma `WithSeminorms.separating_iff_T1` states that the space is Hausdorff if and only if the family separates points. The lemma `WithSeminorms.firstCountableTopology` states that a countable family gives a first countable topology. Products, induced topologies and infima keep the property, by `withSeminorms_pi`, `LinearMap.withSeminorms_induced` and `withSeminorms_iInf`.

A linear map between spaces with seminorms is continuous when each seminorm of the target is bounded by a finite supremum of seminorms of the source. The predicate for this is `Seminorm.IsBounded`, and `WithSeminorms.continuous_of_isBounded` gives the continuity. For a normed space as source or target, `WithSeminorms.continuous_normedSpace_dom` and `WithSeminorms.continuous_normedSpace_rng` give simpler forms.

Two classes record the existence of seminorms without a choice of family. The class `PolynormableSpace 𝕜 E` states that the topology comes from some family of seminorms, and `PolynormableSpace.withSeminorms` gives the family of all continuous seminorms. Over $\mathbb{R}$ or $\mathbb{C}$ it is the same as `LocallyConvexSpace`. The class `IsNormableSpace 𝕜 E` states that the topology comes from a single seminorm, and `IsNormableSpace.toNormedSpace` turns the space into a normed space with the same topology. Products, subspaces and finite products of such spaces have the instances `instPolynormableSpaceProd`, `instPolynormableSpaceSubtypeMemSubmodule` and `instIsNormableSpaceProd`.

#### Common errors

1. Using the balls of a single seminorm $p_i$ as a basis of neighborhoods. In general the basis needs balls of finite suprema, as in `WithSeminorms.hasBasis_zero_ball`. Only a directed family gives a basis with single seminorms.
2. Expecting a balanced set to be convex. The union of the two axes in $\mathbb{R}^2$ is balanced and not convex. Use `AbsConvex` when you need both.
3. Applying `with_gaugeSeminormFamily` over a general field. It needs `RCLike 𝕜`, since the gauge uses the order of the real numbers. Over a general normed field, use `PolynormableSpace`.

### Exercises

1. (A) Show that a nonempty balanced set contains $0$, with `Balanced.zero_mem`.
2. (A) Compute the balanced hull and the balanced core of the segment from $(1, 0)$ to $(1, 1)$ in $\mathbb{R}^2$.
3. (B) For the family $p_n(f) = \sup_{|t| \le n} |f(t)|$ on the continuous functions on $\mathbb{R}$, show that the family is directed and that convergence for the topology is uniform convergence on compact sets.
4. (B) Prove that the space is Hausdorff when the family separates points, from `WithSeminorms.tendsto_nhds`.
5. (B) Show that each linear functional on $\mathbb{R}^n$ is continuous for the topology of the family of seminorms $x \mapsto |x_i|$, with `WithSeminorms.continuous_of_isBounded`.
6. (C) Prove that the topology of the family $(p_n)$ of exercise 3 is not given by a single norm. Show that a bounded neighborhood of $0$ would give a seminorm $p_n$ that bounds all the others.

### Reference

<?reference?>
