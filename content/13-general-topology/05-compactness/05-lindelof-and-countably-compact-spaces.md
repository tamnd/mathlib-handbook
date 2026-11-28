---
title: Lindelöf and countably compact spaces
kind: api
modules:
  - Mathlib.Topology.Compactness.Lindelof
  - Mathlib.Topology.Compactness.CountablyCompact
  - Mathlib.Topology.Compactness.CompactSystem
explains:
  E2: [isLindelof_iff_countable_subcover, cluster_point_of_Lindelof, countable_cover_nhds, IsLindelof.countable, isCountablyCompact_iff_countable_open_cover, isCountablyCompact_iff_isSeqCompact, IsLindelof.isCompact, isCompactSystem_isCompact_isClosed, IsCompactSystem.iff_nonempty_iInter]
  E1: auto
families: []
requires: [V04, V13.C01, V13.C02, V13.C04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Lindelöf and countably compact spaces

### Overview

Compactness says that each open cover has a finite subcover. Two weaker conditions change the size of the subcover or the size of the cover. A set is *Lindelöf* if each open cover has a countable subcover. A set is *countably compact* if each countable open cover has a finite subcover. A set that is both Lindelöf and countably compact is compact, because a cover first becomes countable and then finite.

Mathlib defines both conditions with filters, in the same way as compactness in Section 1. Compactness asks for a cluster point of each proper filter on the set. The Lindelöf condition asks for a cluster point of each proper filter with the countable intersection property of Chapter 2. Countable compactness asks for a cluster point of each proper countably generated filter. The cover forms are theorems.

The section also gives compact systems. A family of sets is a compact system if each countable subfamily with empty intersection has a finite subfamily with empty intersection. This is a property of a family of sets and not of a topology, and measure theory uses it to build measures from content. The compact closed sets of a space form a compact system.

The section uses compact sets from Section 1, sequential compactness from Section 3, the countable intersection filters of Chapter 2 and first countable spaces of Chapter 1.

### The library around it

#### Lindelöf sets and spaces

The module `Mathlib.Topology.Compactness.Lindelof` defines `IsLindelof s`: for each proper filter $f$ with `CountableInterFilter f` and $f \le \mathcal{P}(s)$, there is $x \in s$ that is a cluster point of $f$. The classes are:

- `LindelofSpace X`: `Set.univ` is Lindelöf, with `isLindelof_univ_iff`;
- `NonLindelofSpace X`: `Set.univ` is not Lindelöf, with `not_LindelofSpace_iff`;
- `HereditarilyLindelofSpace X`: each subset is Lindelöf. The predicate on a set is `IsHereditarilyLindelof s`.

The cover forms are `isLindelof_iff_countable_subcover` and `isLindelof_iff_countable_subfamily_closed`. The elimination lemmas are `IsLindelof.elim_countable_subcover`, `IsLindelof.elim_nhds_subcover` and `IsLindelof.indexed_countable_subcover`, which gives a sequence of indices when the index type is nonempty. In a Lindelöf space, `countable_cover_nhds` gives a countable set $t$ of points such that the neighborhoods $U(x)$ for $x \in t$ cover $X$, and `cluster_point_of_Lindelof` gives a cluster point for each proper filter with countable intersections.

The closure rules follow the rules for compact sets:

- `IsCompact.isLindelof`, `IsSigmaCompact.isLindelof`, `Set.Countable.isLindelof`;
- `IsLindelof.of_isClosed_subset`, `IsLindelof.image`, `IsLindelof.union`, `isLindelof_iUnion`;
- `IsClosed.isLindelof` in a Lindelöf space, and `HereditarilyLindelofSpace.isLindelof` for each subset in a hereditarily Lindelöf space.

The instances give the standard examples. A compact space is Lindelöf (`instLindelofSpaceOfCompactSpace`), a σ-compact space is Lindelöf (`instLindelofSpaceOfSigmaCompactSpace`), a countable space is Lindelöf (`Countable.LindelofSpace`), and a second countable space is hereditarily Lindelöf (`SecondCountableTopology.toHereditarilyLindelof`). A hereditarily Lindelöf space is Lindelöf by `HereditarilyLindelof.to_Lindelof`. Quotients of a Lindelöf space are Lindelöf by `Quotient.lindelofSpace`.

Maps transfer the conditions in the same way as for compact sets. A continuous surjection sends a Lindelöf space onto a Lindelöf space (`LindelofSpace.of_continuous_surjective`). A closed embedding pulls the condition back (`Topology.IsClosedEmbedding.LindelofSpace`, `Topology.IsClosedEmbedding.isLindelof_preimage`). An inducing map does not change the condition on images (`Topology.IsInducing.isLindelof_iff`). For a subtype, `isLindelof_iff_lindelofSpace` turns the statement on a set into the class on the subspace, and `Subtype.isLindelof_iff` moves a set of the subtype to its image in $X$. For countable compactness, the corresponding lemmas are `IsCountablyCompact.image`, `Topology.IsInducing.isCountablyCompact_iff`, `Subtype.isCountablyCompact_iff` and `isCountablyCompact_iff_countablyCompactSpace`.

A discrete Lindelöf set is countable. The statement is `IsLindelof.countable`: if $s$ is Lindelöf and the subspace $s$ is discrete, then $s$ is countable. The proof covers $s$ by the open sets that meet $s$ in one point, and a countable subcover then lists all points of $s$. A related form for a discrete space is `countable_of_Lindelof_of_discrete`.

The filter `Filter.coLindelof X` is the analogue of `Filter.cocompact X`. Its sets are the sets that contain the complement of a Lindelöf set, by `mem_coLindelof` and `hasBasis_coLindelof`. The filter is `⊥` exactly when $X$ is Lindelöf (`Filter.coLindelof_eq_bot`, `Filter.coLindelof_neBot_iff`). The variant `Filter.coclosedLindelof X` uses only closed Lindelöf sets.

#### Countably compact sets

The module `Mathlib.Topology.Compactness.CountablyCompact` defines `IsCountablyCompact A`: for each proper countably generated filter $f$ with $f \le \mathcal{P}(A)$, there is $a \in A$ that is a cluster point of $f$. The class `CountablyCompactSpace E` says that `Set.univ` is countably compact, with `isCountablyCompact_univ_iff`.

There are three equivalent forms:

- `isCountablyCompact_iff_countable_open_cover`: each cover by a sequence of open sets has a finite subcover;
- `isCountablyCompact_iff_seq_clusterPt`: each sequence that is eventually in $A$ has a cluster point in $A$;
- `isCountablyCompact_iff_infinite_subset_has_accPt`: in a $T_1$ space, each infinite subset of $A$ has an accumulation point in $A$.

The relations with the other compactness conditions are:

- `IsCompact.isCountablyCompact` and `IsSeqCompact.isCountablyCompact`;
- `isCountablyCompact_iff_isSeqCompact`: in a first countable space, countable compactness and sequential compactness agree;
- `IsLindelof.isCompact`: a set that is Lindelöf and countably compact is compact;
- `IsCountablyCompact.isCompact`: in a hereditarily Lindelöf space, for example a second countable space, a countably compact set is compact;
- `LindelofSpace.compactSpace`: the same statement for spaces.

**Theorem.** A set $A$ that is Lindelöf and countably compact is compact.

*Proof sketch.* Let $U_i$ be an open cover of $A$. Since $A$ is Lindelöf, `IsLindelof.indexed_countable_subcover` gives a sequence of indices $i_n$ such that the sets $U_{i_n}$ cover $A$. Since $A$ is countably compact, `IsCountablyCompact.elim_finite_subcover` gives a finite set of $n$ such that the sets $U_{i_n}$ still cover $A$. Then `isCompact_of_finite_subcover` closes the proof.

The instances `instCountablyCompactSpaceSeqCompactSpace` and `instSeqCompactSpaceCountablyCompactSpace` link the class with `SeqCompactSpace`. The direction from countable compactness to sequential compactness needs a first countable space, or a sequential space by `instSeqCompactSpaceOfSequentialSpaceOfCountablyCompactSpace`.

#### Compact systems

The module `Mathlib.Topology.Compactness.CompactSystem` defines `IsCompactSystem S` for a family $S$ of subsets of a type $\alpha$. The definition says: for each sequence $C_n$ in $S$ with $\bigcap_n C_n = \emptyset$, there is $n$ with `Set.dissipate C n = ∅`, where `Set.dissipate C n` is $\bigcap_{k \le n} C_k$. The equivalent positive form is `IsCompactSystem.iff_nonempty_iInter`: if each finite intersection $\bigcap_{k \le n} C_k$ is nonempty, then $\bigcap_n C_n$ is nonempty. The form `isCompactSystem_iff_nonempty_iInter_of_directed` uses only decreasing sequences when $S$ is a π-system.

The topological examples are:

- `isCompactSystem_isCompact_isClosed`: the compact closed sets of a space form a compact system;
- `isCompactSystem_isCompact`: in a Hausdorff space, the compact sets form a compact system;
- `isCompactSystem_insert_univ_isCompact_isClosed`: the same family with `Set.univ` added.

The operations that keep the property are `IsCompactSystem.mono`, `IsCompactSystem.insert_empty`, `IsCompactSystem.insert_univ`, `IsCompactSystem.supClosure` for finite unions, `IsCompactSystem.infClosure` and `IsCompactSystem.countableInfClosure` for intersections, and `IsCompactSystem.prod` and `IsCompactSystem.pi` for products of sets. Volume 18 uses compact systems to prove that an additive content is σ-additive, and to build measures on infinite products in the theorem of Kolmogorov.

#### Common errors

1. Using a cover lemma with the wrong universe. The cover forms `isLindelof_iff_countable_subcover` and `isLindelof_of_countable_subcover` take index types in the universe of $X$. The elimination lemma `IsLindelof.elim_countable_subcover` takes any universe. Use the elimination lemma when a cover is given.
2. Expecting `IsCountablyCompact A` to give sequential compactness in any space. The implication `IsCountablyCompact.isSeqCompact` needs `FirstCountableTopology E`. Without it, only the cluster point form `IsCountablyCompact.seq_clusterPt` is available.
3. Using `isCompactSystem_isCompact` in a space that is not Hausdorff. In general only compact closed sets form a compact system. Use `isCompactSystem_isCompact_isClosed`, which needs no separation hypothesis.

### Exercises

1. (A) Show that each countable set is Lindelöf, and find the instance that makes `ℕ` a Lindelöf space.
2. (A) Use `isCountablyCompact_iff_isSeqCompact` to show that a sequentially compact set in a metric space is countably compact. Then find the shorter proof with `IsSeqCompact.isCountablyCompact`.
3. (B) Prove that the real line is Lindelöf in two ways: with second countability, and with σ-compactness.
4. (B) Prove that an uncountable discrete space is not Lindelöf, with `countable_of_Lindelof_of_discrete`.
5. (B) Let $X$ be Hausdorff and let $K_n$ be a sequence of nonempty compact sets with $K_{n+1} \subseteq K_n$. Prove that $\bigcap_n K_n$ is nonempty with `isCompactSystem_isCompact`.
6. (C) Prove `IsLindelof.isCompact` from the filter definitions, without the cover forms.

### Reference

<?reference?>
