---
title: Irreducible sets, locally closed sets and dimension
kind: api
modules:
  - Mathlib.Topology.Irreducible
  - Mathlib.Topology.LocallyClosed
  - Mathlib.Topology.JacobsonSpace
  - Mathlib.Topology.KrullDimension
  - Mathlib.Topology.InductiveDimension.Classes
  - Mathlib.Topology.InductiveDimension.Functions
explains:
  E2: [isIrreducible_iff_closure, IsPreirreducible.image, preirreducibleSpace_iff_open_dense, isClosed_of_mem_irreducibleComponents, isLocallyClosed_iff_isOpen_coborder, IsLocallyClosed.inter, instJacobsonSpaceOfT1Space, zeroDimensionalSpace_iff_isTopologicalBasis_isClopen]
  E1: auto
families: []
requires: [V04, V13.C01, V13.C02, V13.C04, V13.C05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Irreducible sets, locally closed sets and dimension

### Overview

A connected space does not split into two disjoint nonempty open sets. An *irreducible* space satisfies a much stronger condition: two nonempty open sets always meet. In a Hausdorff space this happens only for a point, so the notion is useless in analysis. In the Zariski topology of algebraic geometry it is the normal case: the affine line over an infinite field is irreducible, because two nonempty open sets are complements of finite sets. Irreducible sets are the topological form of varieties, and the irreducible components are the topological form of the decomposition of a variety into its components.

This section describes four related groups of modules. `Mathlib.Topology.Irreducible` defines irreducible sets and spaces and irreducible components. `Mathlib.Topology.LocallyClosed` studies the sets of the form $U \cap Z$ with $U$ open and $Z$ closed. `Mathlib.Topology.JacobsonSpace` defines the spaces in which the closed points are dense in each closed set. The last group defines two notions of dimension: the Krull dimension of a space, from chains of irreducible closed sets, and the small inductive dimension, from the frontiers of a basis. The section uses connectedness from Section 1, the separation axioms of Chapter 4 and compactness of Chapter 5.

### The library around it

#### Irreducible sets

A set $s$ is *preirreducible* if for all open $u$ and $v$ that meet $s$, the set $s \cap u \cap v$ is nonempty. It is *irreducible* if it is preirreducible and nonempty. The predicates are `IsPreirreducible s` and `IsIrreducible s`, and the classes for the whole space are `PreirreducibleSpace X` and `IrreducibleSpace X`. The pattern "pre" for "possibly empty" is the same as for `IsPreconnected` and `IsConnected`. An irreducible set is connected (`IsIrreducible.isConnected` in `Mathlib.Topology.Connected.Basic`): two disjoint open sets that meet $s$ would contradict the definition.

There are closed forms of the definition. The lemma `isPreirreducible_iff_isClosed_union_isClosed` says that $s$ is preirreducible if and only if $s \subseteq Z_1 \cup Z_2$ with $Z_1, Z_2$ closed implies $s \subseteq Z_1$ or $s \subseteq Z_2$. The form `isIrreducible_iff_sUnion_isClosed` extends this to finite unions. This is the form in which a variety is irreducible: it is not the union of two proper closed subvarieties.

The basic facts are these.

| Lean name | Statement |
|---|---|
| `isIrreducible_singleton` | a point is irreducible |
| `Set.Subsingleton.isPreirreducible` | a subsingleton is preirreducible |
| `isIrreducible_iff_closure` | $\overline{s}$ is irreducible iff $s$ is irreducible |
| `IsPreirreducible.image` | the image under a map continuous on $s$ is preirreducible |
| `IsPreirreducible.open_subset` | an open subset of a preirreducible set is preirreducible |
| `IsPreirreducible.interior` | the interior of a preirreducible set is preirreducible |
| `subset_closure_inter_of_isPreirreducible_of_isOpen` | an open set that meets $S$ is dense in $S$ |
| `preirreducibleSpace_iff_open_dense` | $X$ is preirreducible iff each nonempty open set is dense |
| `IsDiscrete.subsingleton_of_isPreirreducible` | a discrete preirreducible set has at most one point |

The proof of `isIrreducible_iff_closure` uses one fact: an open set $u$ meets $\overline{s}$ if and only if it meets $s$. So the condition of the definition for $\overline{s}$ and for $s$ is the same condition. The proof of `IsPreirreducible.image` pulls back: if $u$ and $v$ are open and meet $f(s)$, then $f^{-1}(u)$ and $f^{-1}(v)$ are relatively open and meet $s$, so they meet each other in $s$, and the image of a common point is in $f(s) \cap u \cap v$. The characterization `preirreducibleSpace_iff_open_dense` is the definition with $s = X$: a nonempty open $u$ is dense if and only if it meets each nonempty open $v$. The dot form is `IsOpen.dense`.

For spaces, `irreducibleSpace_def` says that $X$ is irreducible if and only if `univ` is irreducible. The instance `instIrreducibleSpaceCofiniteTopologyOfInfinite` makes an infinite type with the cofinite topology irreducible, which is the topological model of the affine line. Irreducibility goes to images under continuous surjections (`Function.Surjective.irreducibleSpace`) and to nonempty open subspaces (`Topology.IsOpenEmbedding.irreducibleSpace`). For a subtype, `isIrreducible_iff_irreducibleSpace` connects the set form and the class form.

#### Irreducible components

By the lemma of Zorn, each preirreducible set is in a maximal one (`exists_preirreducible`). The maximal irreducible sets are the *irreducible components*, and the set of them is `irreducibleComponents X`. The component that contains a point $x$ is `irreducibleComponent x`, with `mem_irreducibleComponent` and `isIrreducible_irreducibleComponent`. A component is closed (`isClosed_of_mem_irreducibleComponents` and `isClosed_irreducibleComponent`), because the closure of an irreducible set is irreducible and contains it, so maximality gives equality. The lemma `irreducibleComponents_eq_maximals_closed` says that the components are the maximal elements among the irreducible closed sets, and `sUnion_irreducibleComponents` says that they cover $X$. Unlike connected components, two irreducible components can meet: in the Zariski topology, the union of two crossing lines in the plane has two components with one common point.

The library also controls components under maps. If $f$ is continuous, open and surjective and its fibres are preirreducible, then `irreducibleComponentsEquivOfIsPreirreducibleFiber` is an order isomorphism between the components of the target and those of the source.

#### Locally closed sets and the coborder

A set is *locally closed* if it is the intersection of an open set and a closed set. The predicate `IsLocallyClosed s` and the coborder are defined in `Mathlib.Topology.Defs.Basic`. The *coborder* of $s$ is the complement of $\overline{s} \setminus s$:

$$\mathrm{coborder}(s) = (\overline{s} \setminus s)^c = s \cup (\overline{s})^c,$$

which is `coborder_eq_union_closure_compl`. The coborder contains $s$ (`subset_coborder`) and is dense (`dense_coborder`). A closed set has coborder `univ` (`IsClosed.coborder_eq`).

The main criterion is `isLocallyClosed_iff_isOpen_coborder`: $s$ is locally closed if and only if its coborder is open. In one direction, if $s = U \cap Z$, then $s = U \cap \overline{s}$ since $\overline{s} \subseteq Z$, so $\overline{s} \setminus s = \overline{s} \setminus U$ is closed. In the other direction, $s = \mathrm{coborder}(s) \cap \overline{s}$ is the intersection of an open set and a closed set. The theorem `isLocallyClosed_tfae` collects more forms: $s$ is open in its closure, $s$ is open as a subset of a subspace, and $s$ is locally closed at each of its points.

The pointwise notion `IsLocallyClosedAt s x` says that near $x$ the set agrees with a closed set. It has many forms, named `isLocallyClosedAt_iff_...`, for example `isLocallyClosedAt_iff_exists_eq_inter_closure`. The lemma `isLocallyClosed_iff_isLocallyClosedAt` makes the global notion the pointwise notion at each point of $s$. Locally closed sets are closed under finite intersection (`IsLocallyClosed.inter`): $(U \cap Z) \cap (U' \cap Z') = (U \cap U') \cap (Z \cap Z')$. They are closed under continuous preimages (`IsLocallyClosed.preimage`), and the image under an inducing map with locally closed range is locally closed (`IsLocallyClosed.image`).

#### Jacobson spaces

A point $x$ is closed when $\{x\}$ is closed. The set of closed points is `closedPoints X`, with `mem_closedPoints_iff` as the simp lemma. A space is a *Jacobson space* when the closed points are dense in each closed set: `JacobsonSpace X` has the field `closure_inter_closedPoints`, which says $\overline{Z \cap \mathrm{closedPoints}(X)} = Z$ for each closed $Z$. The name comes from commutative algebra: the spectrum of a Jacobson ring is a Jacobson space.

The lemma `jacobsonSpace_iff_locallyClosed` gives an equivalent form: each nonempty locally closed set contains a closed point. The instance `instJacobsonSpaceOfT1Space` makes each $T_1$ space Jacobson, since there each point is closed and `closedPoints_eq_univ` holds. The property passes to open and closed subspaces (`JacobsonSpace.of_isOpenEmbedding`, `JacobsonSpace.of_isClosedEmbedding`), and it is local on an open cover (`TopologicalSpace.IsOpenCover.jacobsonSpace_iff`). A Jacobson space with finitely many closed points is discrete (`JacobsonSpace.discreteTopology`).

#### Krull dimension

The *Krull dimension* of a topological space is the supremum of the lengths $n$ of chains $Z_0 \subsetneq Z_1 \subsetneq \dots \subsetneq Z_n$ of irreducible closed sets. In Lean, `topologicalKrullDim X` is `Order.krullDim` of the order of irreducible closed sets `TopologicalSpace.IrreducibleCloseds X`, with values in `WithBot ℕ∞`. The empty space has dimension $\bot$. The module proves that the dimension does not grow on subspaces (`topologicalKrullDim_subspace_le` and `Topology.IsInducing.topologicalKrullDim_le`), that a homeomorphism keeps it (`IsHomeomorph.topologicalKrullDim_eq`), and that a discrete space has dimension at most $0$ (`topologicalKrullDim_zero_of_discreteTopology`). For quasi-sober $T_0$ spaces it relates the coheight of points in the specialization order to the components: `coheightZeroSetOrderIsoIrreducibleComponents` identifies the points of coheight $0$ with the irreducible components.

#### Small inductive dimension

The small inductive dimension is defined by recursion. The empty space has dimension less than $0$, and $X$ has dimension less than $n + 1$ if it has a basis of open sets whose frontiers have dimension less than $n$. The class is `HasSmallInductiveDimensionLT X n`, with the constructors `HasSmallInductiveDimensionLT.zero` and `HasSmallInductiveDimensionLT.succ`, and the shifted form `HasSmallInductiveDimensionLE X n`. The bound is monotone (`HasSmallInductiveDimensionLT.mono`) and passes to subspaces by the instance `instHasSmallInductiveDimensionLTSubtype`.

The first two cases have a concrete meaning. The lemma `hasSmallInductiveDimensionLT_zero_iff` says that dimension less than $0$ is `IsEmpty X`. The abbreviation `ZeroDimensionalSpace X` is dimension less than $1$, and `zeroDimensionalSpace_iff_isTopologicalBasis_isClopen` says that this holds if and only if the clopen sets form a basis. The reason is that a set is clopen exactly when its frontier is empty. The consequences are the useful ones: `nhds_basis_isClopen` gives a basis of clopen neighbourhoods, and `exists_clopen_of_closed_subset_open` finds a clopen set between a closed set and an open set in a compact zero dimensional space.

The function `smallInductiveDimension X : WithBot ℕ∞` is the least $n$ with `HasSmallInductiveDimensionLE X n`. The lemmas `smallInductiveDimension_le_iff` and `smallInductiveDimension_lt_iff` connect the function to the classes, `smallInductiveDimension_eq_bot` says that the value is $\bot$ exactly for the empty space, and `Homeomorph.smallInductiveDimension_congr` and `Topology.IsInducing.smallInductiveDimension_le` give the invariance and the monotonicity.

#### Common errors

1. `IsIrreducible s` contains `s.Nonempty`, and `IsPreirreducible s` does not. A lemma that produces a component or a generic point needs the nonempty form, so use `IsIrreducible.isPreirreducible` and `IsIrreducible.nonempty` to split the hypothesis.
2. In a Hausdorff space each irreducible set is a point. A proof that uses irreducibility in a metric space is usually a proof about subsingletons.
3. The two dimensions take values in `WithBot ℕ∞`, so the empty space has dimension $\bot$, not $-1$, and a statement such as "dimension $\le 0$" needs the cast `((0 : ℕ) : WithBot ℕ∞)`.

### Exercises

1. (A) Show that an infinite set with the cofinite topology is irreducible, and that each infinite subset is dense.
2. (A) Show that each irreducible set is connected, and give a connected space that is not irreducible.
3. (B) Prove that $s$ is locally closed if and only if $s$ is open in $\overline{s}$, and compare your proof with `isLocallyClosed_tfae`.
4. (B) Let $X = Z_1 \cup Z_2$ with $Z_1$ and $Z_2$ irreducible and closed, and neither contained in the other. Show that `irreducibleComponents X` is $\{Z_1, Z_2\}$.
5. (B) Prove that a finite $T_1$ space is discrete, and deduce it from `JacobsonSpace.discreteTopology`.
6. (C) Prove that the Cantor set has small inductive dimension $0$: find a basis of clopen sets.

### Reference

<?reference?>
