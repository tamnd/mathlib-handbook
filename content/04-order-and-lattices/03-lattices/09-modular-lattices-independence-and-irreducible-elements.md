---
title: Modular lattices, independence and irreducible elements
kind: api
modules:
  - Mathlib.Order.ModularLattice
  - Mathlib.Order.SupIndep
  - Mathlib.Order.Irreducible
  - Mathlib.Order.Radical
explains:
  E2: [IsModularLattice, IsUpperModularLattice, infIccOrderIsoIccSup, Finset.SupIndep, iSupIndep, Finset.supIndep_iff_pairwiseDisjoint, Finset.SupIndep.sup_inter, SupPrime, exists_supIrred_decomposition, Order.radical]
  E1: auto
families: []
requires: [V04.C01, V04.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Modular lattices, independence and irreducible elements

### Overview

A lattice is modular when $a \le c$ gives $a \sqcup (b \sqcap c) = (a \sqcup b) \sqcap c$. Section 2 proves that each distributive lattice is modular and shows that $M_3$ is modular but not distributive. The lattices of subspaces of a vector space, of submodules of a module and of normal subgroups of a group are modular. So the theory of this section applies to linear algebra and group theory, where distributivity fails.

This section describes four modules. The first gives the modular law, its weak forms for covering relations, and the diamond isomorphism between two intervals. The second defines independent families: a family of elements in which each element is disjoint from the supremum of the others. For subspaces, this is the direct sum condition. The third defines sup-irreducible and sup-prime elements and their duals. The fourth defines the radical of a complete lattice, the infimum of its coatoms. The section uses the lattices of Section 1, the disjointness and complements of Section 2, and the coatoms of Section 5.

### The library around it

#### The modular law

The class `IsModularLattice α` has one field, `IsModularLattice.sup_inf_le_assoc_of_le`: for $x \le z$,
$$(x \sqcup y) \sqcap z \le x \sqcup (y \sqcap z).$$
The other inequality holds in each lattice, so `sup_inf_assoc_of_le` gives the equality $(x \sqcup y) \sqcap z = x \sqcup (y \sqcap z)$. The dual form is `inf_sup_assoc_of_le`: for $z \le x$, $x \sqcap y \sqcup z = x \sqcap (y \sqcup z)$. The instance `instIsModularLatticeOrderDual` says that the order dual of a modular lattice is modular, and `DistribLattice.instIsModularLattice` gives the instance for each distributive lattice. The criterion `isModularLattice_iff_inf_sup_inf_assoc` replaces the hypothesis $x \le z$ by the identity $x \sqcap z \sqcup y \sqcap z = (x \sqcap z \sqcup y) \sqcap z$ for all $x, y, z$.

A modular lattice has a cancellation property. If $x \le y$, $x \sqcap z = y \sqcap z$ and $x \sqcup z = y \sqcup z$, then $x = y$. Proof: $y = y \sqcap (y \sqcup z) = y \sqcap (x \sqcup z) = x \sqcup (y \sqcap z) = x \sqcup (x \sqcap z) = x$, where the third step is the modular law with $x \le y$. The library states this as `strictMono_inf_prod_sup`: the map $x \mapsto (x \sqcap z, x \sqcup z)$ is strictly monotone. The two consequences `wellFounded_lt_exact_sequence` and `wellFounded_gt_exact_sequence` are the order form of the facts that a module is Artinian or Noetherian when a submodule and the quotient are.

#### The diamond isomorphism

In a modular lattice, `infIccOrderIsoIccSup a b` is an order isomorphism between the intervals $[a \sqcap b, a]$ and $[b, a \sqcup b]$. It sends $x$ to $x \sqcup b$, and its inverse sends $y$ to $a \sqcap y$. To see that the two maps are inverse, let $a \sqcap b \le x \le a$. The dual modular law with $x \le a$ gives $a \sqcap (x \sqcup b) = x \sqcup (a \sqcap b) = x$. The other composition is the same argument in the order dual. For submodules, this is the lattice form of the second isomorphism theorem.

| Lean name | Statement |
|---|---|
| `infIccOrderIsoIccSup` | $[a \sqcap b, a] \simeq_o [b, a \sqcup b]$ |
| `infIccOrderIsoIccSup'` | $[a \sqcap b, b] \simeq_o [a, a \sqcup b]$ |
| `infIooOrderIsoIooSup` | the same isomorphism for the open intervals |
| `IsCompl.IicOrderIsoIci` | for complements $a$ and $b$, $\operatorname{Iic} a \simeq_o \operatorname{Ici} b$ |
| `IsModularLattice.isModularLattice_Iic` | an interval $\operatorname{Iic} a$ is again modular |
| `IsModularLattice.complementedLattice_Iic` | in a complemented modular lattice, $\operatorname{Iic} a$ is complemented |

The last line uses the modular law in a direct way. Let $x \le a$ and let $y$ be a complement of $x$ in the whole lattice. Then $a \sqcap y$ is a complement of $x$ in $\operatorname{Iic} a$, because $x \sqcup (a \sqcap y) = a \sqcap (x \sqcup y) = a \sqcap \top = a$. The lemma `IsModularLattice.exists_inf_eq_and_sup_eq` gives relative complements: for $a \le b \le c$ there is $b'$ with $b \sqcap b' = a$ and $b \sqcup b' = c$.

#### Weak forms of modularity

A weaker condition uses the covering relation $a \lessdot b$ of Chapter 1. The class `IsUpperModularLattice` asks that $a \sqcap b \lessdot a$ gives $b \lessdot a \sqcup b$, and `IsLowerModularLattice` is the dual. The classes `IsWeakUpperModularLattice` and `IsWeakLowerModularLattice` ask the same with two covering hypotheses. A modular lattice is upper and lower modular, by `IsModularLattice.to_isUpperModularLattice` and `IsModularLattice.to_isLowerModularLattice`, and the diamond isomorphism is the proof: it sends the two-element interval $[a \sqcap b, a]$ to the two-element interval $[b, a \sqcup b]$. The lemmas `CovBy.sup_of_inf_left` and `CovBy.inf_of_sup_left` are the forms with dot notation.

#### Independent families

For a finite set $s$ of indices and $f : \iota \to \alpha$, with $\alpha$ a lattice with a bottom element, `Finset.SupIndep s f` says that $f(i)$ is disjoint from $\sup_{j \in t} f(j)$ for each $t \subseteq s$ and each $i \in s \setminus t$. The form without a subset is `Finset.supIndep_iff_disjoint_erase`: each $f(i)$ is disjoint from the supremum over $s \setminus \{i\}$. For a complete lattice and an arbitrary index type, `iSupIndep f` says that $f(i)$ is disjoint from $\bigsqcup_{j \ne i} f(j)$ for each $i$. The set form is `sSupIndep`.

Independence is stronger than pairwise disjointness. The lemma `Finset.SupIndep.pairwiseDisjoint` gives the implication, and `Finset.supIndep_iff_pairwiseDisjoint` gives the converse in a distributive lattice. In the lattice of subspaces of $\mathbb{R}^2$, three distinct lines are pairwise disjoint, but each line is below the supremum of the other two. So the family is not independent. The frame form of the converse is `iSupIndep_iff_pairwiseDisjoint`.

| Lean name | Statement |
|---|---|
| `Finset.SupIndep.subset` | independence on $t$ gives independence on $s \subseteq t$ |
| `Finset.supIndep_pair` | for $i \ne j$, $\{i, j\}$ is independent iff $f(i)$ and $f(j)$ are disjoint |
| `Finset.SupIndep.disjoint_sup_sup` | for disjoint $u, v \subseteq s$, $\sup_u f$ and $\sup_v f$ are disjoint, in a modular lattice |
| `Finset.SupIndep.sup_inter` | $\sup_{s_1 \cap s_2} f = \sup_{s_1} f \sqcap \sup_{s_2} f$, in a modular lattice |
| `iSupIndep_iff_supIndep_univ` | for a finite index type, the two notions agree |
| `iSupIndep.comp` | independence passes to the composition with an injective map |
| `iSupIndep.le_iff_eq_of_iSup_eq_top` | in a modular lattice, if $\bigsqcup f = \top$ and $g$ is independent, then $f \le g$ iff $f = g$ |

The lemma `Finset.SupIndep.sup_inter` shows why modularity matters. Write $s_1 = (s_1 \cap s_2) \cup (s_1 \setminus s_2)$. Then $\sup_{s_1} f = A \sqcup B$, with $A = \sup_{s_1 \cap s_2} f$ and $B = \sup_{s_1 \setminus s_2} f$. Since $A \le \sup_{s_2} f$, the modular law gives $(A \sqcup B) \sqcap \sup_{s_2} f = A \sqcup (B \sqcap \sup_{s_2} f)$, and the last infimum is $\bot$ by `Finset.SupIndep.disjoint_sup_sup`. The converse `Finset.supIndep_iff_sup_inter_eq` also holds.

#### Irreducible and prime elements

An element $a$ of a join-semilattice is sup-irreducible, `SupIrred a`, when $a$ is not minimal and $b \sqcup c = a$ gives $b = a$ or $c = a$. It is sup-prime, `SupPrime a`, when $a$ is not minimal and $a \le b \sqcup c$ gives $a \le b$ or $a \le c$. The duals `InfIrred` and `InfPrime` are defined in a meet-semilattice, and lemmas such as `supIrred_toDual` move between the two. Section 6 uses `SupIrred` for the theorem of Birkhoff.

A sup-prime element is sup-irreducible, `SupPrime.supIrred`: if $b \sqcup c = a$, then $a \le b$ or $a \le c$, and with $b, c \le a$ this gives $b = a$ or $c = a$. The converse `SupIrred.supPrime` needs a distributive lattice. Proof: let $a \le b \sqcup c$. Then $a = a \sqcap (b \sqcup c) = (a \sqcap b) \sqcup (a \sqcap c)$, so $a = a \sqcap b$ or $a = a \sqcap c$, that is $a \le b$ or $a \le c$. In $M_3$ the atom $x$ is sup-irreducible but not sup-prime, since $x \le y \sqcup z$. In a linear order each element that is not minimal is sup-prime, `supPrime_iff_not_isMin`.

The finite forms `SupIrred.finset_sup_eq` and `SupPrime.le_finset_sup` extend the definitions to finite suprema. The theorem `exists_supIrred_decomposition` says that in a join-semilattice with a bottom element and a well-founded order $<$, each element is the supremum of a finite set of sup-irreducible elements. The proof is by well-founded induction: an element that is not sup-irreducible is either $\bot$, the empty supremum, or a supremum $b \sqcup c$ of two strictly smaller elements, and the induction hypothesis applies to $b$ and $c$.

#### The radical

For a complete lattice $\alpha$, `Order.radical α` is the infimum of the coatoms. In the lattice of subgroups of a group it is the Frattini subgroup, and in the lattice of ideals of a ring it is the Jacobson radical. The lemma `Order.radical_le_coatom` says that the radical is below each coatom, and `OrderIso.map_radical` says that an order isomorphism keeps it. The main fact is `Order.radical_nongenerating`: in a coatomic lattice, $a \sqcup \operatorname{radical} = \top$ gives $a = \top$. Proof: if $a \ne \top$, then $a$ is below a coatom $m$, and the radical is below $m$, so $a \sqcup \operatorname{radical} \le m < \top$.

#### Common errors

1. `IsModularLattice` is a class without data, and the modular law is the lemma `sup_inf_assoc_of_le` with the hypothesis $x \le z$. A rewrite with it fails when this hypothesis is not given in the right direction. The dual `inf_sup_assoc_of_le` takes $z \le x$.
2. `Finset.SupIndep` is not the same as `Set.PairwiseDisjoint`. Outside a distributive lattice, the converse `Finset.supIndep_iff_pairwiseDisjoint` is not available, and a proof of independence must bound each element against a supremum of the others.
3. `SupIrred` excludes the minimal elements, so `not_supIrred_bot` says that $\bot$ is not sup-irreducible. A decomposition of $\bot$ by `exists_supIrred_decomposition` uses the empty set.

### Exercises

1. (A) Prove `sup_inf_assoc_of_le` from the field `IsModularLattice.sup_inf_le_assoc_of_le` and the inequality that holds in each lattice.
2. (A) Find the sup-irreducible elements and the sup-prime elements of $N_5$ and of $M_3$.
3. (B) Show that $N_5$ is not modular by the cancellation property: find $x < y$ and $z$ with $x \sqcap z = y \sqcap z$ and $x \sqcup z = y \sqcup z$.
4. (B) Prove that three distinct lines through $0$ in $\mathbb{R}^2$ are pairwise disjoint in the lattice of subspaces but not independent, and conclude that this lattice is not distributive.
5. (B) Compute `Order.radical` for the lattice of the divisors of $12$, ordered by divisibility.
6. (C) Prove that the two maps of `infIccOrderIsoIccSup` are monotone and inverse to each other, with only the modular law.

### Reference

<?reference?>
