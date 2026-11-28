---
title: Bornologies, locally bounded maps and absorbing sets
kind: api
modules:
  - Mathlib.Topology.Bornology.Constructions
  - Mathlib.Topology.Bornology.Hom
  - Mathlib.Topology.Bornology.Real
  - Mathlib.Topology.Bornology.Absorbs
  - Mathlib.Topology.Baire.Absorbent
explains:
  E2: [Bornology.isBounded_prod, Bornology.forall_isBounded_image_eval_iff, Bornology.cobounded_prod, Bornology.induced, LocallyBoundedMap, LocallyBoundedMap.ofMapBounded, Absorbs, Absorbent, absorbent_iff_forall_absorbs_singleton, Absorbent.interior_nonempty]
  E1: auto
families: []
requires: [V04, V05, V13.C01, V13.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Bornologies, locally bounded maps and absorbing sets

### Overview

Section 1 gives the class `Bornology α` with the metric spaces. A bornology is a family of *bounded* sets that contains each finite set and is closed under subsets and finite unions. Mathlib stores it as the filter `Bornology.cobounded α` of complements of bounded sets. A metric space has the bornology of sets with finite diameter. The bornology is separate from the topology, so a space can have a topology and a bornology that do not come from the same metric.

This section describes the rest of the bornology library. There are three parts. The first part gives the bornologies on products, pi types, subtypes and induced types, with the rules for bounded sets. The second part gives the bundled maps that send bounded sets to bounded sets. The third part uses the bornology of a group with zero, for example a normed field, to define absorbing sets. A set $s$ *absorbs* a set $t$ if $t \subseteq a \cdot s$ for each scalar $a$ of sufficiently large norm. Absorbing sets are the basic tool of topological vector spaces.

The section uses filters from Chapter 2, the Baire spaces of Section 2, and group actions of Volume 5. The theory of locally convex spaces in Volume 16 uses absorbing sets and von Neumann bounded sets.

### The library around it

#### Bornologies on constructions

The module `Mathlib.Topology.Bornology.Constructions` gives the instances `Prod.instBornology`, `Pi.instBornology` and `instBornologySubtype`, and the type synonyms `instBornologyOrderDual`, `instBornologyAdditive` and `instBornologyMultiplicative`. The cobounded filters are:

- `Bornology.cobounded_prod`: the cobounded filter of $\alpha \times \beta$ is the coproduct of the two cobounded filters;
- `Bornology.cobounded_pi`: the cobounded filter of a pi type is `Filter.coprodᵢ` of the cobounded filters of the factors.

So a set of a product is bounded if and only if its two projections are bounded. The forms for sets are:

- `Bornology.isBounded_image_fst_and_snd` and `Bornology.forall_isBounded_image_eval_iff`: a set is bounded if and only if each projection is bounded;
- `Bornology.IsBounded.prod` and `Bornology.IsBounded.pi`: products of bounded sets are bounded;
- `Bornology.isBounded_prod`: the product $s \times t$ is bounded if and only if $s$ or $t$ is empty, or both are bounded. The form `Bornology.isBounded_prod_of_nonempty` removes the empty cases;
- `Bornology.isBounded_pi`: the same statement for `Set.univ.pi S`.

The empty cases are necessary: $\emptyset \times t$ is bounded for each $t$.

For a map $f : \alpha \to \beta$ into a type with a bornology, `Bornology.induced f` is the bornology on $\alpha$ whose bounded sets are the sets with bounded image. The criterion is `Bornology.isBounded_induced`, and `boundedSpace_induced_iff` says that $\alpha$ is a bounded space if and only if the range of $f$ is bounded. The subtype bornology is the special case of the inclusion of the subtype. The relations are `Bornology.isBounded_image_subtypeVal` and `boundedSpace_val_set_iff`: the subtype on $s$ is a `BoundedSpace` if and only if $s$ is bounded.

The module `Mathlib.Topology.Bornology.Real` gives `Real.instIsOrderBornology` and `NNReal.instIsOrderBornology`. The class `IsOrderBornology` says that the bounded sets are the sets that are bounded below and above. With it, `isBounded_iff_bddBelow_bddAbove` says that a set of real numbers is bounded for the metric if and only if it is bounded below and above. The module also gives `NNReal.instOrderTopology`.

#### Locally bounded maps

The module `Mathlib.Topology.Bornology.Hom` defines the structure `LocallyBoundedMap α β` of maps that send bounded sets to bounded sets. The field is stated with filters: the preimage of the cobounded filter of $\beta$ is at most the cobounded filter of $\alpha$. The class form is `LocallyBoundedMapClass F α β`, with the field `LocallyBoundedMapClass.comap_cobounded_le`.

- `LocallyBoundedMap.ofMapBounded` builds a locally bounded map from a proof that images of bounded sets are bounded;
- `Bornology.IsBounded.image` is the main use: the image of a bounded set under a locally bounded map is bounded;
- `LocallyBoundedMap.id` and `LocallyBoundedMap.comp` give the category of bornological spaces, with `LocallyBoundedMap.comp_assoc`, `LocallyBoundedMap.id_comp` and `LocallyBoundedMap.comp_id`;
- `LocallyBoundedMap.ext`, `LocallyBoundedMap.copy` and `LocallyBoundedMap.cancel_right` are the standard API of bundled maps.

The name means locally bounded in the sense of bornologies. It does not mean a map that is bounded on a neighborhood of each point. A continuous map between metric spaces is not locally bounded in this sense in general: the map $x \mapsto 1/x$ on $(0, 1]$ sends the bounded set $(0, 1]$ to an unbounded set.

#### Absorbing sets

The module `Mathlib.Topology.Bornology.Absorbs` takes a type $M$ with a bornology that acts on $\alpha$. The definitions are:

- `Absorbs M s t`: for each $a$ in a cobounded set of $M$, $t \subseteq a \cdot s$. For a normed field, this means that $t \subseteq a \cdot s$ for each $a$ of sufficiently large norm. The unfolded form is `Absorbs.eventually`;
- `Absorbent M s`: $s$ absorbs each point, `absorbent_iff_forall_absorbs_singleton`.

For a group with zero, `absorbs_iff_eventually_cobounded_mapsTo` gives the form with $a^{-1} \cdot x$: eventually, $a^{-1}$ maps $t$ into $s$. The form `absorbent_iff_inv_smul` is the same for points. The filter `Filter.absorbing G₀ u` has as its sets the sets that absorb $u$, with `Filter.mem_absorbing`.

The rules for the absorbed set are:

- `Absorbs.mono`, `Absorbs.mono_left` and `Absorbs.mono_right`;
- `Absorbs.union`, `absorbs_union`, `absorbs_iUnion` and `Set.Finite.absorbs_biUnion`: a set absorbs a finite union if and only if it absorbs each piece;
- `Absorbent.absorbs_finite`: an absorbent set absorbs each finite set.

For a group with zero, the rules for the absorbing set are `Absorbs.inter`, `absorbs_inter`, `absorbs_iInter` and `Set.Finite.absorbs_sInter`: finite intersections of sets that absorb $t$ also absorb $t$. In an additive group, `Absorbs.add`, `Absorbs.sub` and `Absorbs.neg_neg` follow the group operations, and `Absorbent.zero_mem` says that an absorbent set contains $0$ when the cobounded filter of $G_0$ is not trivial. If $M$ is a bounded space, each set absorbs each set by `Absorbs.of_boundedSpace`. This is why the scalars must be unbounded for the notion to have content.

**Proposition.** Let $s$ absorb $t_1$ and $t_2$. Then $s$ absorbs $t_1 \cup t_2$.

*Proof.* The condition `Absorbs M s t₁` gives a cobounded set $A_1$ of scalars with $t_1 \subseteq a \cdot s$ for $a \in A_1$. The same holds for $t_2$ with $A_2$. The intersection $A_1 \cap A_2$ is cobounded, because the cobounded sets form a filter, and $t_1 \cup t_2 \subseteq a \cdot s$ for each $a$ in it. This is `Absorbs.union`.

#### Absorbent closed sets in a Baire space

The module `Mathlib.Topology.Baire.Absorbent` has one theorem, `Absorbent.interior_nonempty`. Let $E$ be a nonempty Baire space with a continuous action of $G_0$, and let the cobounded filter of $G_0$ be countably generated and nontrivial. Then a closed absorbent set has a nonempty interior. The proof writes $E$ as the union of the closed sets $a_n \cdot s$ for a sequence $a_n$ that tends to infinity, and applies the Baire category theorem of Section 2. This is a typical use of the Baire category theorem for topological vector spaces.

#### Common errors

1. Applying `Bornology.isBounded_prod` without the empty cases. The product $\emptyset \times t$ is bounded for each $t$. Use `Bornology.isBounded_prod_of_nonempty` or `Bornology.IsBounded.fst_of_prod` with a nonemptiness hypothesis.
2. Reading `LocallyBoundedMap` as a map that is bounded near each point. The class is about the bornology only. For a map that is bounded on compact sets, use the topology and not this structure.
3. Using `Absorbs` with a bounded scalar type. If $M$ is a bounded space, `Absorbs.of_boundedSpace` makes the condition trivial. The scalars must be a normed field or another type with unbounded elements.

### Exercises

1. (A) Prove that a set of $\mathbb{R}^2$ is bounded if and only if its two projections are bounded, with `Bornology.isBounded_image_fst_and_snd`.
2. (A) Show that $s \times \emptyset$ is bounded for each set $s$, and find the case of `Bornology.isBounded_prod` that gives it.
3. (B) Let $f : \alpha \to \beta$ be a map into a metric space. Show that a set $s$ is bounded for `Bornology.induced f` if and only if $f(s)$ is bounded.
4. (B) In a real normed space, prove that the closed unit ball is absorbent, with `absorbent_iff_forall_absorbs_singleton`.
5. (B) Prove that a set $s$ absorbs a finite set $t$ if $s$ is absorbent, with `Absorbent.absorbs_finite`.
6. (C) Prove `Absorbent.interior_nonempty` for a real Banach space with the Baire category theorem of Section 2.

### Reference

<?reference?>
