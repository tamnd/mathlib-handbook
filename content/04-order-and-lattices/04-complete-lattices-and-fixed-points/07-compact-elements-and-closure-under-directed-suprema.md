---
title: Compact elements and closure under directed suprema
kind: api
modules:
  - Mathlib.Order.CompactlyGenerated.Basic
  - Mathlib.Order.CompactlyGenerated.Intervals
  - Mathlib.Order.CompletePartialOrder
  - Mathlib.Order.DirSupClosed
  - Mathlib.Order.CountableSupClosed
  - Mathlib.Order.BooleanGenerators
explains:
  E2: [IsCompactElement, isCompactElement_iff_exists_le_sSup_of_le_sSup, wellFoundedGT_characterisations, IsCompactlyGenerated, DirectedOn.inf_sSup_eq, complementedLattice_iff_isAtomistic, CompletePartialOrder, DirSupClosed, CountableSupClosed, IsCompactlyGenerated.BooleanGenerators.booleanAlgebraOfSSupEqTop]
  E1: auto
families: []
requires: [V04.C01, V04.C03]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Compact elements and closure under directed suprema

### Overview

In the lattice of submodules of a module, a finitely generated submodule has a special property: if it is contained in the union of a directed family of submodules, then it is contained in one member of the family. An element of a complete lattice with this property is *compact*. A lattice in which each element is a supremum of compact elements is *compactly generated*. The submodules of a module and the intermediate fields of a field extension are examples, and many arguments of algebra with Zorn's lemma use only this property.

This section describes six files. The first two define compact elements and compactly generated lattices, and prove the main results about them: the characterisations of the ascending chain condition, the law of upper continuity, and the theorem that a modular compactly generated lattice is complemented exactly when it is atomistic. The third file defines complete partial orders, in which only the directed sets need to have a supremum. The fourth and fifth files define the sets that are closed under directed suprema and under countable suprema. The last file gives a criterion for a compactly generated lattice to be a Boolean algebra. The files use the directed sets and the well-founded orders of Chapter 1, and the atoms, the modular lattices and the independent families of Chapter 3.

### The library around it

**Compact elements.** The file `Mathlib.Order.CompactlyGenerated.Basic` defines `IsCompactElement k` for an element $k$ of a preorder: for each nonempty directed set $s$ with a least upper bound $u$ and $k \le u$, some $x \in s$ satisfies $k \le x$. In a complete lattice the least upper bound is `sSup s`, and `isCompactElement_iff_le_of_directed_sSup_le` states the definition in this form. The second form removes the condition that the set is directed.

$$\operatorname{IsCompactElement} k \iff \forall s,\ k \le \sup s \to \exists\, t \subseteq s \text{ finite},\ k \le \sup t \qquad (\texttt{isCompactElement\_iff\_exists\_le\_sSup\_of\_le\_sSup}).$$

*Proof.* Suppose that $k$ is compact and $k \le \sup s$. The set of the suprema of the finite subsets of $s$ is nonempty and directed, and it has the same supremum as $s$. So $k$ is below the supremum of one finite subset. Conversely, let $s$ be nonempty and directed with $k \le \sup s$. A finite subset $t$ with $k \le \sup t$ has an upper bound $x$ in $s$, because $s$ is directed and nonempty, and then $k \le x$. $\square$

The indexed forms are `isCompactElement_iff_exists_le_iSup_of_le_iSup` and `IsCompactElement.exists_finset_of_le_iSup`. The bottom element is compact (`IsCompactElement.bot`), and the compact elements are closed under binary suprema (`IsCompactElement.sup`), so the supremum of a finite set of compact elements is compact: `isCompactElement_finsetSup` and `IsCompactElement.sSup`. If $k$ is compact and each element of a nonempty directed set $s$ is strictly below $k$, then $\sup s < k$ (`IsCompactElement.directed_sSup_lt_of_lt`).

In the lattice of submodules, the compact elements are the finitely generated submodules, by `Submodule.fg_iff_compact`. In `Set α` they are the finite sets. Each atom of a frame is compact, by `IsAtom.isCompactElement_of_frame`.

**The ascending chain condition.** Two more properties of a complete lattice α are defined in the file. The property `IsSupClosedCompact α` says that each nonempty set that is closed under $\sqcup$ contains its supremum. The property `IsSupFiniteCompact α` says that each set has a finite subset with the same supremum. The main theorem is that these properties are equivalent to the ascending chain condition and to the compactness of all elements.

$$\text{the four conditions } \operatorname{WellFoundedGT} \alpha,\ \operatorname{IsSupFiniteCompact} \alpha,\ \operatorname{IsSupClosedCompact} \alpha,\ \forall k,\ \operatorname{IsCompactElement} k \text{ are equivalent} \qquad (\texttt{wellFoundedGT\_characterisations}).$$

*Proof.* If $>$ is well founded, then for a set $s$ the set of the suprema of the finite subsets of $s$ has a maximal element $m$. Each $x \in s$ satisfies $x \sqcup m = m$, so $m = \sup s$. If each set has a finite subset with the same supremum, and $s$ is nonempty and closed under $\sqcup$, then $\sup s$ is a finite supremum of elements of $s$, so it is in $s$. If each nonempty set closed under $\sqcup$ contains its supremum, then the range of an increasing sequence contains its supremum, so the sequence is eventually constant. The equivalence with the compactness of all elements follows from the second form of compactness above. $\square$

The single implications are `WellFoundedGT.isSupFiniteCompact`, `IsSupFiniteCompact.isSupClosedCompact` and `IsSupClosedCompact.wellFoundedGT`, and `wellFoundedGT_iff_isSupFiniteCompact` and `isSupClosedCompact_iff_wellFoundedGT` are two of the equivalences. Under the ascending chain condition, each independent set is finite (`WellFoundedGT.finite_of_sSupIndep`).

**Compactly generated lattices.** The class `IsCompactlyGenerated α` has one field, `IsCompactlyGenerated.exists_isLUB`: each element is the least upper bound of a set of compact elements. In a complete lattice, `IsCompactlyGenerated.exists_sSup_eq` gives the form with `sSup`, and `sSup_compact_le_eq` says that each element is the supremum of the compact elements below it. Thus the order is fixed by the compact elements: `le_iff_forall_isCompactElement` says that $a \le b$ when each compact element below $a$ is below $b$. A lattice with the ascending chain condition is compactly generated by `IsCompactlyGenerated.of_wellFoundedGT`, and so is an atomistic frame, by the instance `instIsCompactlyGeneratedOfIsAtomistic`. The instance `Submodule.instIsCompactlyGenerated` covers submodules.

In a compactly generated lattice, $\sqcap$ distributes over directed suprema. This is the law of upper continuity.

$$a \sqcap \sup s = \bigsqcup_{b \in s} (a \sqcap b) \quad \text{for } s \text{ directed} \qquad (\texttt{DirectedOn.inf\_sSup\_eq}).$$

*Proof.* The right side is below the left side in each complete lattice. For the other inequality, let $c$ be a compact element below $a \sqcap \sup s$. Then $c \le \sup s$, so $c \le b$ for some $b \in s$, and $c \le a \sqcap b$. By `le_iff_forall_isCompactElement` the left side is below the right side. $\square$

The forms `Directed.inf_iSup_eq` and `DirectedOn.disjoint_sSup_right` follow. Upper continuity gives `sSupIndep_iff_finite`: a set is independent when each of its finite subsets is independent.

**Atoms and complements.** If $k$ is compact, then the interval $[\bot, k]$ is coatomic (`CompleteLattice.Iic_coatomic_of_compact_element`). In particular, if $\top$ is compact, then each element other than $\top$ is below a coatom (`CompleteLattice.coatomic_of_top_compact`). This is the lattice form of the theorem that each proper ideal of a ring is contained in a maximal ideal. In a compactly generated lattice, an atom is compact (`IsAtom.isCompactElement`), and in an atomistic one the compact elements are the finite suprema of atoms (`isCompactElement_iff_exists_finite_isAtom`). For a modular compactly generated lattice, the main structure theorem is the following.

$$\operatorname{ComplementedLattice} \alpha \iff \operatorname{IsAtomistic} \alpha \qquad (\texttt{complementedLattice\_iff\_isAtomistic}).$$

The direction from left to right uses `isAtomic_of_complementedLattice` and the modular law. The direction from right to left uses `exists_sSupIndep_isCompl_sSup_atoms`: for each $b$, Zorn's lemma gives an independent set of atoms whose supremum is a complement of $b$. For modules this theorem says that a module is semisimple exactly when it is a sum of simple submodules.

The file `Mathlib.Order.CompactlyGenerated.Intervals` passes these properties to the intervals $[\bot, a]$. An element of `Set.Iic a` is compact when it is compact in α (`Set.Iic.isCompactElement`), and `Set.Iic.instIsCompactlyGenerated` is the instance. The theorem `complementedLattice_of_complementedLattice_Iic` says that α is complemented if it is the supremum of a family of elements $f_i$ such that each interval $[\bot, f_i]$ is complemented.

**Complete partial orders.** The file `Mathlib.Order.CompletePartialOrder` defines the class `CompletePartialOrder α`: a partial order with a bottom element and an operation `sSup` such that `sSup d` is the least upper bound of each directed set $d$. The class gives no property of `sSup` on a set that is not directed. The lemmas `DirectedOn.isLUB_sSup`, `DirectedOn.le_sSup` and `DirectedOn.sSup_le` give the properties of the supremum, with the hypothesis that the set is directed. The constructor `CompletePartialOrder.ofLubOfDirected` takes a partial order and an operation `sSup` and defines the bottom element as `sSup ∅`. Each complete lattice is a complete partial order (`CompleteLattice.toCompletePartialOrder`), and each complete partial order is an ω-complete partial order of Section 4 (`CompletePartialOrder.toOmegaCompletePartialOrder`). In this class, Scott continuity has the simpler form `CompletePartialOrder.scottContinuous`: $f$ sends `sSup d` to the least upper bound of $f(d)$ for each nonempty directed $d$.

**Sets closed under directed suprema.** The file `Mathlib.Order.DirSupClosed` defines `DirSupClosed s` for a set $s$ of a preorder: for each nonempty directed $d \subseteq s$, each least upper bound of $d$ is in $s$. The dual notion is `DirSupInacc s`: if a least upper bound of a nonempty directed set $d$ is in $s$, then $d$ meets $s$. The two notions are complements of each other, by `dirSupClosed_compl` and `dirSupInacc_compl`. An upper set is closed under directed suprema (`IsUpperSet.dirSupClosed`), and so is each interval $\operatorname{Iic} a$ (`DirSupClosed.Iic`). Closed sets are stable under intersections (`DirSupClosed.inter`, `DirSupClosed.sInter`) and under binary unions (`DirSupClosed.union`). In a complete lattice, `dirSupClosed_iff_forall_sSup` gives the form with `sSup`. The variants `DirSupClosedOn D s` and `DirSupInaccOn D s` use only the directed sets in a family $D$. A lower set that is closed under directed suprema is a closed set of the Scott topology, which Volume 13 treats.

**Sets closed under countable suprema.** The file `Mathlib.Order.CountableSupClosed` defines `CountableSupClosed s`: each nonempty countable subset of $s$ with a least upper bound has this bound in $s$. Its dual is `CountableInfClosed`. Such a set is closed under $\sqcup$ (`CountableSupClosed.supClosed`) and so it is directed (`CountableSupClosed.directedOn`). The closure operator `countableSupClosure` gives the smallest such set that contains a given set, and in a complete lattice its elements are the suprema of sequences in the set, by `mem_countableSupClosure_iff_iSup`.

**Boolean generators.** The file `Mathlib.Order.BooleanGenerators` has the structure `IsCompactlyGenerated.BooleanGenerators S` for a set $S$ of a compactly generated lattice. It asks that each element of $S$ is an atom, and that each compact element below the supremum of a finite subset $s \subseteq S$ is the supremum of a subset of $s$. If $\sup S = \top$, then the lattice is a Boolean algebra.

$$\operatorname{BooleanGenerators} S \ \wedge\ \sup S = \top \implies \alpha \text{ is a Boolean algebra} \qquad (\texttt{IsCompactlyGenerated.BooleanGenerators.booleanAlgebraOfSSupEqTop}).$$

The parts of this result are `IsCompactlyGenerated.BooleanGenerators.isAtomistic_of_sSup_eq_top`, `IsCompactlyGenerated.BooleanGenerators.distribLatticeOfSSupEqTop` and `IsCompactlyGenerated.BooleanGenerators.complementedLattice_of_sSup_eq_top`. The lemma `IsCompactlyGenerated.BooleanGenerators.sSup_le_sSup_iff_of_atoms` says that $\sup X \le \sup Y$ exactly when $X \subseteq Y$, for subsets $X, Y$ of $S$, so the lattice is isomorphic to the subsets of $S$.

#### Common errors

1. Reading `IsCompactElement` as the compactness of a set. The predicate is a property of an element of an order. In `Set α` only the finite sets are compact elements, and `IsCompact` of Volume 13 is a different notion.
2. Using `DirectedOn.le_sSup` or `DirectedOn.isLUB_sSup` for a set that is not directed. In a `CompletePartialOrder` these lemmas need the hypothesis `DirectedOn (· ≤ ·) d`. In a complete lattice, use `le_sSup` and `isLUB_sSup`, which need no hypothesis.
3. Expecting an instance from `IsCompactlyGenerated.BooleanGenerators.booleanAlgebraOfSSupEqTop`. It is a definition with two hypotheses, so it must be put in place with `letI` or passed by hand.

### Exercises

1. (A) Show that each upper set of a preorder is closed under directed suprema, from the definition of `DirSupClosed`.
2. (A) Show that each finite subset of a type α is a compact element of `Set α`.
3. (B) In `ℕ∞`, show that each natural number is a compact element and that $\top$ is not compact. Deduce that `ℕ∞` is compactly generated.
4. (B) Show that in the closed interval $[0, 1]$ of real numbers, with its usual order, only $0$ is a compact element. Deduce that this complete lattice is not compactly generated.
5. (B) Prove `DirSupClosed.union`: consider whether each element of $d$ is below some element of $d \cap s$.
6. (C) Let α be a complete lattice in which $\top$ is compact and $\bot \ne \top$. Prove with Zorn's lemma of Chapter 1 that α has a coatom, as in `CompleteLattice.coatomic_of_top_compact`.

### Reference

<?reference?>
