---
title: Partial homeomorphisms
kind: api
modules:
  - Mathlib.Topology.PartialHomeomorph.Defs
  - Mathlib.Topology.PartialHomeomorph.Basic
  - Mathlib.Topology.OpenPartialHomeomorph.Defs
  - Mathlib.Topology.OpenPartialHomeomorph.Basic
  - Mathlib.Topology.OpenPartialHomeomorph.Composition
  - Mathlib.Topology.OpenPartialHomeomorph.Constructions
  - Mathlib.Topology.OpenPartialHomeomorph.Continuity
  - Mathlib.Topology.OpenPartialHomeomorph.IsImage
explains:
  E2: [OpenPartialHomeomorph, PartialHomeomorph, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.map_nhds_eq, OpenPartialHomeomorph.IsImage.iff_preimage_eq, OpenPartialHomeomorph.ofSet_trans, OpenPartialHomeomorph.isOpen_inter_preimage]
  E1: auto
families: []
requires: [V01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Partial homeomorphisms

### Overview

A chart of a manifold is not a homeomorphism of the whole space. It is a homeomorphism from an open subset of $X$ onto an open subset of $\mathbb{R}^n$. The inverse function theorem gives the same kind of object: a map that is a homeomorphism near a point. Mathlib calls such a map a partial homeomorphism, and it builds charts, the inverse function theorem and the trivializations of fibre bundles on it.

The library has two structures. A `PartialHomeomorph X Y` is a pair of maps $e : X \to Y$ and $e^{-1} : Y \to X$, with a source $S \subseteq X$ and a target $T \subseteq Y$, such that $e$ maps $S$ to $T$, $e^{-1}$ maps $T$ to $S$, the two maps are inverse on these sets, and both are continuous on them. An `OpenPartialHomeomorph X Y` adds that $S$ and $T$ are open. Most of the API is about the open version, because the restriction to open sets makes $e$ a local homeomorphism at each point of $S$, and the neighbourhood filters behave well. This section describes the definitions, the composition, the restriction, the constructions and the continuity lemmas. It uses the continuous maps and homeomorphisms of Section 3, and the neighbourhood filters of Chapter 2 in the lemmas on continuity.

### The library around it

#### The two structures

The structure `PartialHomeomorph X Y` in `Mathlib.Topology.PartialHomeomorph.Defs` extends `PartialEquiv X Y`. A partial equivalence has the fields `PartialEquiv.toFun`, `PartialEquiv.invFun`, `PartialEquiv.source`, `PartialEquiv.target`, and the four fields that say that the maps send the source to the target and back and are inverse there. The partial homeomorphism adds `PartialHomeomorph.continuousOn_toFun` and `PartialHomeomorph.continuousOn_invFun`. The structure `OpenPartialHomeomorph X Y` in `Mathlib.Topology.OpenPartialHomeomorph.Defs` extends `PartialHomeomorph X Y` with the fields `OpenPartialHomeomorph.open_source` and `OpenPartialHomeomorph.open_target`. The projection `OpenPartialHomeomorph.toPartialHomeomorph` forgets the openness.

Both structures have a coercion to functions, so a proof writes `e x` and `e.symm y`. The lemmas `OpenPartialHomeomorph.toFun_eq_coe` and `OpenPartialHomeomorph.invFun_eq_coe` move from the fields to the coercion, and the simp normal form uses the coercion. The inverse `OpenPartialHomeomorph.symm` exchanges the source and the target, and `OpenPartialHomeomorph.symm_symm` says that it is an involution. The basic facts are fields or direct consequences.

| Lean name | Statement |
|---|---|
| `OpenPartialHomeomorph.map_source` | $x \in S \Rightarrow e(x) \in T$ |
| `OpenPartialHomeomorph.map_target` | $y \in T \Rightarrow e^{-1}(y) \in S$ |
| `OpenPartialHomeomorph.left_inv` | $x \in S \Rightarrow e^{-1}(e(x)) = x$ |
| `OpenPartialHomeomorph.right_inv` | $y \in T \Rightarrow e(e^{-1}(y)) = y$ |
| `OpenPartialHomeomorph.continuousOn` | $e$ is continuous on $S$ |
| `OpenPartialHomeomorph.continuousOn_symm` | $e^{-1}$ is continuous on $T$ |
| `OpenPartialHomeomorph.open_source` | $S$ is open |
| `OpenPartialHomeomorph.image_source_eq_target` | $e(S) = T$ |
| `OpenPartialHomeomorph.injOn` | $e$ is injective on $S$ |

The extensionality lemma `OpenPartialHomeomorph.ext` asks for three things: the maps agree, the inverses agree, and the sources agree. Values of $e$ outside $S$ are part of the data, so two partial homeomorphisms that agree on $S$ need not be equal. The relation `OpenPartialHomeomorph.EqOnSource` identifies them: $e \approx e'$ if $S = S'$ and $e = e'$ on $S$. It is an equivalence relation, `OpenPartialHomeomorph.eqOnSourceSetoid`, and the notation $e \approx e'$ refers to it. Many identities of the library hold only up to this relation.

#### Sources of partial homeomorphisms

Several maps give partial homeomorphisms.

1. A homeomorphism $h : X \simeq Y$ gives `Homeomorph.toOpenPartialHomeomorph h`, with source and target the whole spaces.
2. An open embedding $f$ of a nonempty space gives `Topology.IsOpenEmbedding.toOpenPartialHomeomorph`, with source the whole space and target the range. The inverse is chosen outside the range.
3. An open set $U$ gives the inclusion `TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe`, from the subspace $U$ to $X$.
4. A partial equivalence that is continuous and open on an open source gives `OpenPartialHomeomorph.ofContinuousOpen`. The proof that the target is open uses the openness of the map.
5. An open set $s$ gives `OpenPartialHomeomorph.ofSet s hs`, the identity with source and target $s$.

For the version without openness, an embedding gives `Topology.IsEmbedding.toPartialHomeomorph`, and a set gives `Set.partialHomeomorphSubtypeCoe`. In the other direction, `OpenPartialHomeomorph.toHomeomorphSourceTarget` restricts $e$ to a homeomorphism of subspaces $S \simeq T$, and `OpenPartialHomeomorph.isOpenEmbedding_restrict` says that the restriction of $e$ to $S$ is an open embedding.

#### Composition

The composition `e.trans e'` of $e : X \to Y$ and $e' : Y \to Z$ is defined on the set of points where both steps make sense. The lemma `OpenPartialHomeomorph.trans_source` gives

$$\mathrm{source}(e \circ e') = S \cap e^{-1}(S'),$$

and `OpenPartialHomeomorph.trans_target` gives the target $T' \cap (e')^{-1}(T)$, where $(e')^{-1}$ is the inverse map. The source is open by `OpenPartialHomeomorph.isOpen_inter_preimage`: for an open $V \subseteq Y$, the set $S \cap e^{-1}(V)$ is open. The proof of this lemma is short. Since $e$ is continuous on the open set $S$, the preimage of $V$ under the restriction of $e$ to $S$ is open in $S$, so it is $S \cap W$ for an open $W$ of $X$. This set is open in $X$ because $S$ is open. The openness of $S$ is the reason the open version has a good composition.

The algebra of composition holds as in a groupoid, with some identities only up to $\approx$.

| Lean name | Statement |
|---|---|
| `OpenPartialHomeomorph.trans_assoc` | $(e \circ e') \circ e'' = e \circ (e' \circ e'')$ |
| `OpenPartialHomeomorph.refl_trans` | $\mathrm{id} \circ e = e$ |
| `OpenPartialHomeomorph.trans_refl` | $e \circ \mathrm{id} = e$ |
| `OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm` | $(e \circ e')^{-1} = (e')^{-1} \circ e^{-1}$ |
| `OpenPartialHomeomorph.self_trans_symm` | $e \circ e^{-1} \approx \mathrm{ofSet}\ S$ |
| `OpenPartialHomeomorph.symm_trans_self` | $e^{-1} \circ e \approx \mathrm{ofSet}\ T$ |
| `OpenPartialHomeomorph.ofSet_trans` | $\mathrm{ofSet}\ s \circ e = e$ restricted to $s$ |
| `OpenPartialHomeomorph.EqOnSource.trans'` | composition respects $\approx$ |

In Lean `e.trans e'` means "first $e$, then $e'$", in the order of a diagram. The identity $e \circ e^{-1} \approx \mathrm{ofSet}\ S$ is not an equality, because outside $S$ the composition and the identity can differ. For the formula of the inverse, both sides have the source $T' \cap (e')^{-1}(T)$, both maps are $e^{-1} \circ (e')^{-1}$, and both inverse maps are $e' \circ e$, so `OpenPartialHomeomorph.ext` applies.

The module `Mathlib.Topology.OpenPartialHomeomorph.Composition` also composes with homeomorphisms on the left, by `Homeomorph.transOpenPartialHomeomorph`, and `Mathlib.Topology.OpenPartialHomeomorph.Constructions` composes on the right, by `OpenPartialHomeomorph.transHomeomorph`. These keep the source or the target unchanged.

#### Restriction and images

The restriction `e.restr s` has source $S \cap \mathrm{int}(s)$, by `OpenPartialHomeomorph.restr_source`. The interior keeps the source open, so `OpenPartialHomeomorph.restr` takes any set. For an open $s$, the variant `OpenPartialHomeomorph.restrOpen` uses $S \cap s$. The lemma `OpenPartialHomeomorph.restr_univ` says that restriction to $X$ does nothing, and `OpenPartialHomeomorph.restr_eq_of_source_subset` says the same when $S \subseteq s$. Restriction respects $\approx$ by `OpenPartialHomeomorph.EqOnSource.restr`.

The predicate `OpenPartialHomeomorph.IsImage`, written `e.IsImage s t`, says that $e$ maps $s$ to $t$ inside the source: for each $x \in S$, $e(x) \in t$ if and only if $x \in s$. The lemma `OpenPartialHomeomorph.IsImage.iff_preimage_eq` restates it as $S \cap e^{-1}(t) = S \cap s$. It is a predicate and not a computation of $e(s)$, so it behaves well under the set operations. The module `Mathlib.Topology.OpenPartialHomeomorph.IsImage` proves `OpenPartialHomeomorph.IsImage.symm`, `OpenPartialHomeomorph.IsImage.inter`, `OpenPartialHomeomorph.IsImage.union`, `OpenPartialHomeomorph.IsImage.compl` and the topological forms `OpenPartialHomeomorph.IsImage.closure`, `OpenPartialHomeomorph.IsImage.interior` and `OpenPartialHomeomorph.IsImage.frontier`. The topological forms follow from `OpenPartialHomeomorph.preimage_closure`: on the open set $S$, the preimage of the closure is the closure of the preimage, since $e$ restricted to $S$ is a homeomorphism onto the open set $T$. If $e$ maps $s$ to $t$ and $S \cap s$ is open, then `OpenPartialHomeomorph.IsImage.restr` gives the partial homeomorphism from $S \cap s$ to $T \cap t$. The basic instance is `OpenPartialHomeomorph.isImage_source_target`: $e$ maps $S$ to $T$.

#### Constructions

The module `Mathlib.Topology.OpenPartialHomeomorph.Constructions` gives the standard constructions.

1. `OpenPartialHomeomorph.prod eX eY` is the product map with source $S_X \times S_Y$, by `OpenPartialHomeomorph.prod_source`. The lemma `OpenPartialHomeomorph.prod_trans` composes products factor by factor.
2. `OpenPartialHomeomorph.pi` is the product over a finite index type. Finiteness is needed: an infinite product of open sets is not open.
3. `OpenPartialHomeomorph.piecewise e e' s t` glues two partial homeomorphisms along sets $s$ and $t$. It needs `e.IsImage s t`, `e'.IsImage s t`, and the agreement of $e$ and $e'$ on the frontier of $s$. The special case `OpenPartialHomeomorph.disjointUnion` glues two partial homeomorphisms with disjoint sources and disjoint targets.
4. `OpenPartialHomeomorph.subtypeRestr` restricts $e$ to an open subspace $U$, as a partial homeomorphism from the type $U$ to $Y$.
5. `OpenPartialHomeomorph.lift_openEmbedding` extends a partial homeomorphism along an open embedding of its domain.
6. `OpenPartialHomeomorph.const` maps an isolated point to an isolated point.

#### Continuity and neighbourhoods

The module `Mathlib.Topology.OpenPartialHomeomorph.Continuity` gives the local behaviour. The main statement is `OpenPartialHomeomorph.map_nhds_eq`: for $x \in S$,

$$e_*\, \mathcal{N}(x) = \mathcal{N}(e(x)).$$

*Proof.* The inequality $e_* \mathcal{N}(x) \le \mathcal{N}(e(x))$ is the continuity of $e$ at $x$, which holds since $e$ is continuous on the open set $S$ and $x \in S$. For the reverse inequality, let $N$ be a neighbourhood of $x$. The set $N \cap S$ is a neighbourhood of $x$. Since $e^{-1}$ is continuous at $e(x) \in T$ and $T$ is open, the set $V = T \cap (e^{-1})^{-1}(N \cap S)$ is a neighbourhood of $e(x)$. Each $y \in V$ is $e(e^{-1}(y))$ with $e^{-1}(y) \in N$, so $V \subseteq e(N)$. Hence $e(N) \in \mathcal{N}(e(x))$. $\square$

The other lemmas of the module follow the same pattern.

| Lean name | Statement |
|---|---|
| `OpenPartialHomeomorph.continuousAt` | $e$ is continuous at each $x \in S$ |
| `OpenPartialHomeomorph.tendsto_symm` | $e^{-1}(y) \to x$ as $y \to e(x)$ |
| `OpenPartialHomeomorph.image_mem_nhds` | $e$ maps neighbourhoods of $x$ to neighbourhoods of $e(x)$ |
| `OpenPartialHomeomorph.eventually_left_inverse` | $e^{-1}(e(y)) = y$ for $y$ near $x$ |
| `OpenPartialHomeomorph.eventually_right_inverse` | $e(e^{-1}(y)) = y$ for $y$ near a point of $T$ |
| `OpenPartialHomeomorph.map_nhdsWithin_eq` | $e_*\, \mathcal{N}_s(x) = \mathcal{N}_{e(S \cap s)}(e(x))$ |
| `OpenPartialHomeomorph.continuousAt_iff_continuousAt_comp_right` | $f$ is continuous at $y \in T$ iff $f \circ e$ is continuous at $e^{-1}(y)$ |

The last family says that a property of continuity can move through a chart. This is the base of the definition of smooth maps on manifolds: a map is smooth if it is smooth in charts, and these lemmas show that the choice of chart does not matter for continuity. The lemma `OpenPartialHomeomorph.nhds_eq_comap_inf_principal` writes $\mathcal{N}(x)$ as the pullback of $\mathcal{N}(e(x))$ restricted to $S$.

The version without openness has fewer lemmas. Its Basic module gives the images of sets, the embedding `PartialHomeomorph.isEmbedding` for source the whole space, and the restriction `PartialHomeomorph.toHomeomorphSourceTarget`.

#### Common errors

1. `e.trans e'` applies $e$ first. The source is $S \cap e^{-1}(S')$, not $S$.
2. The identities $e \circ e^{-1} = \mathrm{id}$ and their relatives hold only up to $\approx$. A rewrite with an equality fails, and the proof uses `OpenPartialHomeomorph.EqOnSource` lemmas or works pointwise on the source.
3. `e.restr s` has source $S \cap \mathrm{int}(s)$, not $S \cap s$. For an open $s$ the two agree, and `OpenPartialHomeomorph.restrOpen` gives the simpler form.

### Exercises

1. (A) Show that the map $x \mapsto x^2$ is a partial homeomorphism from $\mathbb{R}$ to $\mathbb{R}$ with source $(0, \infty)$ and target $(0, \infty)$, and give its inverse.
2. (A) Compute the source and the target of `e.trans e.symm` and check `OpenPartialHomeomorph.self_trans_symm`.
3. (B) Prove `OpenPartialHomeomorph.IsImage.compl` from the definition of `OpenPartialHomeomorph.IsImage`.
4. (B) Show that the stereographic projection from the north pole is an open partial homeomorphism from the circle $S^1$ to $\mathbb{R}$, with source $S^1 \setminus \{N\}$.
5. (B) Prove that a map $e$ that is an open partial homeomorphism with source $X$ is an open embedding, as in `OpenPartialHomeomorph.isOpenEmbedding`.
6. (C) Let $e$ be a `PartialHomeomorph` whose source is not open. Give an example where $e$ maps a neighbourhood of a point $x$ of the source to a set that is not a neighbourhood of $e(x)$, so that `OpenPartialHomeomorph.map_nhds_eq` fails without openness.

### Reference

<?reference?>
