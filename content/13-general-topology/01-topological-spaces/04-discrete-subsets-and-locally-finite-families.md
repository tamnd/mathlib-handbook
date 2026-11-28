---
title: Discrete subsets, derived sets and locally finite families
kind: api
modules:
  - Mathlib.Topology.DerivedSet
  - Mathlib.Topology.DiscreteSubset
  - Mathlib.Topology.LocallyFinite
  - Mathlib.Topology.LocallyFinsupp
  - Mathlib.Topology.LocallyFinsupp.Pushforward
  - Mathlib.Topology.IndicatorConstPointwise
explains:
  E2: [closure_eq_self_union_derivedSet, isClosed_iff_derivedSet_subset, compl_mem_codiscrete_iff, IsClosed.tendsto_coe_cofinite_iff, LocallyFinite.closure_iUnion, LocallyFinite.isClosed_iUnion, LocallyFinite.continuous, Function.locallyFinsuppWithin.finiteSupport, tendsto_indicator_const_iff_forall_eventually]
  E1: auto
families: []
requires: [V01, V03, V04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Discrete subsets, derived sets and locally finite families

### Overview

A set is small near a point when only a few of its points, or a few members of a family, come near that point. This section collects the notions of the library that make this idea exact. The derived set of $A$ is the set of the accumulation points of $A$. A subset is discrete when each of its points is isolated in it. A family of sets is locally finite when each point has a neighbourhood that meets only finitely many members. A function has locally finite support when its support is a locally finite set of points.

These notions appear in many places. Locally finite families give the partitions of unity and the paracompact spaces. Discrete sets give the zeros and poles of a meromorphic function, and functions with locally finite support give divisors in complex analysis and cycles in algebraic geometry. The section uses the open sets, closures and continuous maps of Sections 1 to 3. The statements of the library use the neighbourhood filter `nhds x` and the filter `nhdsWithin x s` of neighbourhoods of $x$ relative to $s$. Chapter 2 explains these filters. A reader who does not know them yet can read each filter statement as a statement about neighbourhoods.

### The library around it

#### The derived set

Let $X$ be a topological space and $A \subseteq X$. A point $x$ is an *accumulation point* of $A$ if each neighbourhood of $x$ meets $A$ in a point other than $x$. Mathlib states this for a filter: `AccPt x F` says that the punctured neighbourhood filter of $x$ meets $F$, and for a set one takes the principal filter `Filter.principal A`. The module `Mathlib.Topology.DerivedSet` defines `derivedSet A` as the set of the accumulation points of $A$, with `mem_derivedSet` as the unfolding lemma. The relative form `relDerivedSet A` is `derivedSet A ∩ A`, the points of $A$ that are not isolated in $A$ (`relDerivedSet_apply`). It is an order homomorphism on `Set X`, so its monotonicity is part of its type.

The two main facts relate the derived set to the closure.

$$\overline{A} = A \cup A', \qquad A \text{ closed} \iff A' \subseteq A,$$

where $A'$ is the derived set. These are `closure_eq_self_union_derivedSet` and `isClosed_iff_derivedSet_subset`. Proof of the first: a point of $\overline{A}$ that is not in $A$ has each neighbourhood meet $A$, and the meeting point is not $x$, so $x \in A'$. Conversely $A' \subseteq \overline{A}$ is clear (`derivedSet_subset_closure`). The second fact follows, because $A$ is closed exactly when $\overline{A} = A$.

The derived set commutes with finite unions (`derivedSet_union`) and is monotone (`derivedSet_mono`). In a $T_1$ space the derived set is closed (`isClosed_derivedSet`) and does not change under closure (`derivedSet_closure`). A continuous injective map sends derived sets into derived sets (`Continuous.image_derivedSet`, from `AccPt.map`). The derived set also describes perfect sets: `perfect_iff_eq_derivedSet` says that $U$ is perfect if and only if $U = U'$, and `preperfect_iff_subset_derivedSet` says that $U$ has no isolated point if and only if $U \subseteq U'$.

#### Discrete subsets

A set $s$ is discrete, `IsDiscrete s`, if the subspace topology on $s$ is the discrete topology. The class form is `DiscreteTopology ↥s`, and `isDiscrete_iff_discreteTopology` passes between the two. The module `Mathlib.Topology.DiscreteSubset` gives the usual criteria.

| Lean name | Statement |
|---|---|
| `isDiscrete_iff_forall_mem_exists_isOpen` | each $y \in s$ has an open $U$ with $U \cap s = \{y\}$ |
| `isDiscrete_iff_nhdsWithin` | the neighbourhood filter of $x$ within $s$ is `pure x` for $x \in s$ |
| `isDiscrete_iff_forall_subset_exists_isOpen` | each subset of $s$ is the trace of an open set |
| `discreteTopology_of_noAccPts` | a set with no accumulation point in itself is discrete |
| `IsDiscrete.union` | a union of two closed discrete sets is discrete |
| `IsDiscrete.iUnion` | a finite union of closed discrete sets is discrete |
| `IsDiscrete.image` | an inducing map keeps discrete sets |
| `IsDiscrete.isLocallyClosed` | in a $T_1$ space a discrete set is locally closed |

The union lemmas need the closedness. The sets $\{0\}$ and $\{1/n : n \ge 1\}$ in $\mathbb{R}$ are both discrete, but their union is not, because $0$ is a limit of the second set.

The second notion of discreteness concerns compact sets. A set $s$ is *closed and discrete* if and only if each point of $X$ has a punctured neighbourhood that misses $s$ (`isClosed_and_discrete_iff`). In a locally compact space this is a finiteness statement. The theorem `IsClosed.tendsto_coe_cofinite_iff` says: in a $T_1$ space that is weakly locally compact, a closed set $s$ is discrete if and only if the inclusion $s \to X$ tends to the cocompact filter along the cofinite filter. By `tendsto_cofinite_cocompact_iff`, the second condition says that each compact set meets $s$ in a finite set. Proof sketch of one direction: if $K$ is compact and $K \cap s$ is infinite, then $K \cap s$ has an accumulation point in $K$, because $K$ is compact. That point is in $s$, because $s$ is closed, and it is not isolated in $s$. This contradicts discreteness.

#### The codiscrete filters

A property holds *outside a discrete set* when the set where it fails is closed and discrete. The library expresses this with a filter. The filter `Filter.codiscreteWithin U` is the supremum of the punctured neighbourhood filters of the points of $U$ relative to $U$, and `Filter.codiscrete X` is the case $U = X$. A set $S$ is in `Filter.codiscrete X` if and only if no point of $X$ is an accumulation point of the complement of $S$ (`mem_codiscrete_accPt`). In other words:

$$S^c \in \mathrm{codiscrete}(X) \iff S \text{ is closed and discrete},$$

which is `compl_mem_codiscrete_iff`. The proof is the criterion `isClosed_and_discrete_iff` above, read with `mem_codiscrete`.

So `∀ᶠ x in Filter.codiscrete X, p x` says that $p$ fails only on a closed discrete set. The lemmas `eventually_codiscrete_iff_forall_eventually_nhdsNE` and `eventuallyEq_codiscrete_iff_forall_eventuallyEq_nhdsNE` turn such a statement into a statement at each point: $p$ holds on a punctured neighbourhood of each point. This is the form in which complex analysis states that the zeros of a nonzero analytic function are isolated. The relative lemmas carry the suffix `Within`, for example `mem_codiscreteWithin` and `eventuallyEq_codiscreteWithin_iff_forall_eventuallyEq_nhdsWithin`.

The codiscrete filter is finer than the cofinite filter in a $T_1$ space (`codiscrete_le_cofinite`), and the two agree in a compact $T_1$ space (`codiscrete_eq_cofinite`). On a compact set $K$, a set that is codiscrete within $K$ misses only finitely many points of $K$ (`IsCompact.finite_sdiff_of_mem_codiscreteWithin`).

#### Locally finite families

A family $(f_i)_{i \in \iota}$ of subsets of $X$ is locally finite, `LocallyFinite f`, if each point $x$ has a neighbourhood $t$ such that $\{i : f_i \cap t \neq \emptyset\}$ is finite. The module `Mathlib.Topology.LocallyFinite` proves the closure properties: a finite family is locally finite (`locallyFinite_of_finite`), a family of subsets of a locally finite family is locally finite (`LocallyFinite.subset`), the closures of a locally finite family are locally finite (`LocallyFinite.closure`), and preimages under a continuous map stay locally finite (`LocallyFinite.preimage_continuous`). Reindexing by an injective map keeps the property (`LocallyFinite.comp_injective`), and each point lies in only finitely many members (`LocallyFinite.point_finite`).

The central result says that closure commutes with locally finite unions:

$$\overline{\textstyle\bigcup_i f_i} = \textstyle\bigcup_i \overline{f_i}.$$

This is `LocallyFinite.closure_iUnion`. Proof: the inclusion $\supseteq$ holds for each family. For $\subseteq$, let $x$ be in the closure of the union, and let $t$ be a neighbourhood of $x$ that meets only $f_{i_1}, \dots, f_{i_n}$. Then $x$ is in the closure of $f_{i_1} \cup \dots \cup f_{i_n}$, which is the finite union of the closures. As a consequence, a locally finite union of closed sets is closed (`LocallyFinite.isClosed_iUnion`). The same idea gives the gluing lemma for continuous maps: if a locally finite family of closed sets covers $X$, and $g$ is continuous on each member, then $g$ is continuous (`LocallyFinite.continuous`). For two closed sets this is the pasting lemma of a first course.

#### Functions with locally finite support

The module `Mathlib.Topology.LocallyFinsupp` defines the predicate `LocallyFiniteSupport f`: each point has a neighbourhood that meets the support of $f$ in a finite set. The lemma `LocallyFiniteSupport.iff_locallyFinite_support` says that this holds exactly when the family of singletons of the support is locally finite.

The bundled type is `Function.locallyFinsuppWithin U Y`, for a set $U \subseteq X$ and a type $Y$ with a zero. An element is a function $D : X \to Y$ with support in $U$ (`Function.locallyFinsuppWithin.supportWithinDomain`) and locally finite support at each point of $U$. The abbreviation `Function.locallyFinsupp X Y` is the case $U = X$. Such a function coerces to $X \to Y$ through a `FunLike` instance, and `Function.locallyFinsuppWithin.ext` proves equality pointwise. The type inherits the structure of $Y$: it is an additive commutative group when $Y$ is one (`Function.locallyFinsuppWithin.instAddCommGroup`), a lattice when $Y$ is one, and an ordered group when $Y$ is a linearly ordered group. The coercion lemmas `Function.locallyFinsuppWithin.coe_add`, `Function.locallyFinsuppWithin.coe_neg` and `Function.locallyFinsuppWithin.coe_sub` say that the operations are pointwise. The function `Function.locallyFinsuppWithin.single x y` is the function with the value $y$ at $x$ and $0$ elsewhere.

In complex analysis such a function with values in $\mathbb{Z}$ is a divisor: it gives an integer order at each point, and only finitely many points in each compact set have a nonzero order. The library has the operations that divisor theory needs. The positive and negative parts are `D⁺` and `D⁻`, from the lattice ordered group structure (`Function.locallyFinsuppWithin.posPart_apply`). The truncation `D.truncate y hy` takes the minimum of $D$ with a value $y \ge 0$ (`Function.locallyFinsuppWithin.truncate_apply`). The restriction `D.restrict h` to a smaller set $V \subseteq U$ is zero outside $V$ (`Function.locallyFinsuppWithin.restrict_apply`), and it is a group homomorphism and a lattice homomorphism (`Function.locallyFinsuppWithin.restrictMonoidHom`, `Function.locallyFinsuppWithin.restrictLatticeHom`).

The topology enters through three facts. In a $T_1$ space the support is discrete (`Function.locallyFinsuppWithin.discreteSupport`), and it is closed when $U$ is closed (`Function.locallyFinsuppWithin.closedSupport`). In a Hausdorff space, when $U$ is compact, the support is finite (`Function.locallyFinsuppWithin.finiteSupport`). Proof of the last fact: each point of $U$ has an open neighbourhood that meets the support in a finite set. Finitely many of these neighbourhoods cover $U$, and the support lies in $U$, so it is finite. In a $T_1$ space the condition of locally finite support within $U$ is equivalent to the condition that $f$ is zero along `Filter.codiscreteWithin U` (`supportDiscreteWithin_iff_locallyFiniteWithin`), which joins this module to the codiscrete filters.

The module `Mathlib.Topology.LocallyFinsupp.Pushforward` defines the pushforward `Function.locallyFinsupp.map` along a spectral map $f : X \to Y$ between prespectral spaces, with a weight function $w$. Its value at $y$ is the finite sum $\sum_{x \in f^{-1}(y)} c(x) w(x)$ (`Function.locallyFinsupp.map_apply`). The pushforward along the identity with weight $1$ is the identity (`Function.locallyFinsupp.map_id`). This construction serves the pushforward of algebraic cycles in Volume 28.

#### Pointwise convergence of indicator functions

The module `Mathlib.Topology.IndicatorConstPointwise` treats a sequence or a net of sets $A_i$ and a set $A$. Let $b \neq 0$ be in a $T_1$ space with a zero. Then the indicator functions $b \cdot \mathbf{1}_{A_i}$ tend pointwise to $b \cdot \mathbf{1}_A$ if and only if, for each $x$, eventually $x \in A_i \iff x \in A$. This is `tendsto_indicator_const_iff_forall_eventually`. The reason is that the indicator takes only the two values $0$ and $b$, and in a $T_1$ space each of them has a neighbourhood that misses the other. The forms with a prime replace the $T_1$ hypothesis by the two conditions $\{0\}^c \in \mathcal{N}(b)$ and $\{b\}^c \in \mathcal{N}(0)$. The pointwise form is `tendsto_indicator_const_apply_iff_eventually`, and `tendsto_indicator_const_iff_tendsto_pi_pure` states the same condition as a limit in a product of filters.

#### Common errors

1. Using `IsDiscrete.union` without closedness. A union of two discrete sets need not be discrete, and the lemma needs both sets closed.
2. Reading `Filter.codiscrete X` as the cofinite filter. The two agree only in a compact $T_1$ space. In $\mathbb{R}$, the set $\mathbb{R} \setminus \mathbb{Z}$ is in the codiscrete filter but not in the cofinite filter.
3. Forgetting the support condition of `Function.locallyFinsuppWithin U Y`. A function with locally finite support on $X$ is not an element for a smaller $U$ unless its support lies in $U$. Use `Function.locallyFinsuppWithin.restrict` to pass to a smaller set.

### Exercises

1. (A) Compute the derived set of $\{1/n : n \ge 1\}$ in $\mathbb{R}$, and check `closure_eq_self_union_derivedSet` on it.
2. (A) Let $X$ be an indiscrete space with at least two points and $a \in X$. Show that the derived set of $\{a\}$ is $X \setminus \{a\}$, so a derived set need not be closed when $X$ is not $T_1$.
3. (B) Show that $\mathbb{Z}$ is closed and discrete in $\mathbb{R}$, and deduce that $\mathbb{Z}^c$ is in `Filter.codiscrete ℝ`.
4. (B) Give a locally finite family of closed sets in $\mathbb{R}$ whose union is $\mathbb{R}$, and a family of closed sets that is not locally finite whose union is not closed.
5. (B) Prove `LocallyFinite.continuous` for two closed sets from the closed set criterion of continuity.
6. (C) Let $X$ be a Hausdorff space and $D$ a function on $X$ with locally finite support. Show that $D$ has finite support on each compact set, and give a function on $\mathbb{R}$ with infinite discrete support and locally finite support.

### Reference

<?reference?>
