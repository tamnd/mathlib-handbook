---
title: The basic API of sets
kind: api
modules:
  - Mathlib.Data.Set.Defs
  - Mathlib.Data.Set.Operations
  - Mathlib.Data.Set.Basic
  - Mathlib.Data.Set.Notation
  - Mathlib.Data.Set.CoeSort
  - Mathlib.Data.Set.BooleanAlgebra
  - Mathlib.Data.Set.SymmDiff
  - Mathlib.Data.Set.Disjoint
  - Mathlib.Data.Set.Lattice
explains:
  E2: [Set.Subset.antisymm, Set.union_subset_iff, Set.subset_inter_iff, Set.not_nonempty_iff_eq_empty, Set.ssubset_iff_of_subset, Set.disjoint_left, Set.symmDiff_eq_empty]
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

## The basic API of sets

### Overview

The first two sections of this chapter use the operations on sets to prove the identities of images, preimages and indexed unions. This section describes the files that define those operations and hold the thousand small facts about them. A reader meets these files in each proof about sets, often without a look at them, because `simp` and the membership lemmas do the work. The section explains how the files are organized, how the lemmas are named, and which forms the simplifier prefers.

The files form a chain. `Mathlib.Data.Set.Defs` defines the type `Set α` and the notation for set builder, union, intersection and difference. `Mathlib.Data.Set.Operations` adds the image, the preimage, the range, the product and some other constructions, with their membership lemmas. `Mathlib.Data.Set.Basic` proves the laws of the lattice of sets: inclusion, union, intersection, the empty set, the universal set, nonempty sets and separation. The small files `Mathlib.Data.Set.CoeSort`, `Mathlib.Data.Set.Notation`, `Mathlib.Data.Set.BooleanAlgebra`, `Mathlib.Data.Set.SymmDiff` and `Mathlib.Data.Set.Disjoint` add the coercion of a set to a type, two pieces of notation, the Boolean algebra instance, the symmetric difference and the disjoint sets.

### The library around it

#### The type of sets and the set builder

In `Mathlib.Data.Set.Defs`, the type `Set α` is a structure with one field: a predicate `α → Prop`. The constructor is `Set.ofPred`, and the notation `{x | p x}` elaborates to `Set.ofPred fun x ↦ p x`. The membership `a ∈ s` is the instance `Set.instMembership`, and `Set.mem_ofPred` states $a \in \{x \mid p(x)\} \iff p(a)$. The form `Set.mem_ofPred_eq` is an equality of propositions, so `rw` and `simp` can use it under binders. The lemma `Set.ofPred_mem_eq` gives back the set from its predicate: $\{x \mid x \in s\} = s$. The structure also gives an equivalence `Set.memEquiv` between `Set α` and `α → Prop`. The lemma names that contain the word setOf come from an older design, and they are now deprecated aliases of the lemmas with ofPred. Use the new names.

Two sets are equal when they have the same elements. This is `Set.ext`, and `Set.ext_iff` is its form with "if and only if". The tactic `ext x` applies `Set.ext` and leaves the goal `x ∈ s ↔ x ∈ t`.

The file also defines the basic operations as functions: `Set.union`, `Set.inter`, `Set.compl`, `Set.diff`, `Set.insert`, `Set.singleton`, `Set.univ`, `Set.powerset` and `Set.image`. A user does not write these names. The instances `Set.instMax`, `Set.instMin`, `Set.instSDiff`, `Set.instInsert` and `Set.instSingletonSet` give the notation `s ∪ t`, `s ∩ t`, `s \ t`, `insert a s` and `{a}`, and `𝒫 s` is the notation for the power set. Since `∪` and `∩` are the binary maximum and minimum of the order of sets, the lattice lemmas of Volume 4 apply to them with no translation.

The predicate `Set.Nonempty s` means $\exists x, x \in s$. It is the preferred form of "$s$ is not empty" in Mathlib, because a proof of it carries a witness.

#### Membership lemmas and the simp normal form

`Mathlib.Data.Set.Operations` gives one membership lemma for each operation. Each lemma has the name `Set.mem_<operation>`, and the simplifier uses them all.

| Lean name | Statement |
|---|---|
| `Set.mem_union` | $x \in s \cup t \iff x \in s \lor x \in t$ |
| `Set.mem_inter_iff` | $x \in s \cap t \iff x \in s \land x \in t$ |
| `Set.mem_compl_iff` | $x \in s^c \iff x \notin s$ |
| `Set.mem_sdiff` | $x \in s \setminus t \iff x \in s \land x \notin t$ |
| `Set.mem_univ` | $x \in \mathrm{univ}$ |
| `Set.mem_empty_iff_false` | $x \in \emptyset \iff \mathrm{False}$ |
| `Set.mem_powerset_iff` | $t \in \mathcal{P}(s) \iff t \subseteq s$ |
| `Set.mem_prod` | $p \in s \times t \iff p_1 \in s \land p_2 \in t$ |
| `Set.mem_range` | $x \in \mathrm{range}(f) \iff \exists y, f(y) = x$ |

With these lemmas, `simp` turns a goal about sets into a goal of logic about one point, and the tactics of logic finish it. This is the method of the first section of the chapter. The difference has the name sdiff in the lemma names, as in `Set.mem_sdiff` and `Set.sdiff_eq` ($s \setminus t = s \cap t^c$). The older names with diff are deprecated.

The same file defines a list of constructions that later sections use. `Set.range f` is the image of the whole domain. `Set.image2 f s t` is the set of all $f(a, b)$ with $a \in s$ and $b \in t$. `Set.prod s t`, written `s ×ˢ t`, is the product, and `Set.prod_eq` writes it as $\mathrm{fst}^{-1}(s) \cap \mathrm{snd}^{-1}(t)$. `Set.pi` is the product of a family. `Set.diagonal α` is the set of pairs $(x, x)$, and `Set.offDiag s` is the set of pairs of distinct points of $s$. `Set.kernImage f s` is the set of $y$ whose whole fiber lies in $s$, the right adjoint of the preimage, by `Set.subset_kernImage_iff`. The file also defines the predicates on maps `Set.MapsTo`, `Set.InjOn`, `Set.SurjOn` and `Set.BijOn`, whose API is in the section on functions between sets. The maps `Set.rangeFactorization f` and `Set.imageFactorization f s` restrict the codomain of $f$ to its range or to the image of $s$. `Set.rangeSplitting f` chooses a preimage for each point of the range, and `Set.apply_rangeSplitting` says that it is a right inverse.

#### Inclusion and the laws of the lattice

`Mathlib.Data.Set.Basic` is the largest file of the group. It has about 300 lemmas, and most of them are laws of a distributive lattice with a top and a bottom, stated for sets. The instances `Set.instDistribLattice` and `Set.instBoundedOrder` make these laws also available as order lemmas, and the file `Mathlib.Data.Set.BooleanAlgebra` gives the full instance `Set.instCompleteAtomicBooleanAlgebra`. So a reader who knows a law of lattices can use the general lemma, for example `sup_comm`, or the special lemma, `Set.union_comm`.

The inclusion $s \subseteq t$ unfolds to $\forall x, x \in s \to x \in t$, by `Set.subset_def`. The order axioms are `Set.Subset.refl`, `Set.Subset.trans` and `Set.Subset.antisymm`. The last one is the usual way to prove an equality of sets by two inclusions.

**Theorem (`Set.Subset.antisymm`).** If $s \subseteq t$ and $t \subseteq s$, then $s = t$.

*Proof.* By `Set.ext`, it is enough to show $x \in s \iff x \in t$ for each $x$. The first inclusion gives the direction from left to right, and the second gives the other direction. $\square$

The union is the least upper bound and the intersection is the greatest lower bound for inclusion. This is the content of two lemmas.

**Theorem (`Set.union_subset_iff`, `Set.subset_inter_iff`).** $s \cup t \subseteq u \iff s \subseteq u \land t \subseteq u$, and $r \subseteq s \cap t \iff r \subseteq s \land r \subseteq t$.

*Proof.* For the first, $s \cup t \subseteq u$ means $\forall x, (x \in s \lor x \in t) \to x \in u$. An implication out of a disjunction is a conjunction of two implications, and the quantifier distributes over the conjunction. The second is the same with an implication into a conjunction. $\square$

The other lemmas follow one naming pattern. The name gives the left side of the equation, and the words come in the order of the expression: `Set.union_assoc`, `Set.inter_comm`, `Set.union_inter_distrib_left` for $s \cup (t \cap u) = (s \cup t) \cap (s \cup u)$, `Set.inter_union_distrib_right`, `Set.union_self`, `Set.inter_empty`, `Set.univ_inter`. The lemmas `Set.inter_eq_left` ($s \cap t = s \iff s \subseteq t$) and `Set.union_eq_right` ($s \cup t = t \iff s \subseteq t$) turn an equation into an inclusion. The lemmas `Set.subset_union_left`, `Set.inter_subset_right` and `Set.union_subset_union` give the monotonicity of the operations.

The strict inclusion $s \subset t$ means $s \subseteq t$ and $t \not\subseteq s$. The lemma `Set.ssubset_iff_subset_ne` gives the form with $s \ne t$.

**Theorem (`Set.ssubset_iff_of_subset`).** If $s \subseteq t$, then $s \subset t$ if and only if some $x \in t$ is not in $s$.

*Proof.* Given $s \subseteq t$, the condition $s \subset t$ says $t \not\subseteq s$. The negation of $\forall x \in t, x \in s$ is $\exists x \in t, x \notin s$. $\square$

#### Empty, universal and nonempty sets

The empty set and the universal set have their membership lemmas `Set.notMem_empty` and `Set.mem_univ`. The lemmas `Set.subset_empty_iff` and `Set.univ_subset_iff` give $s \subseteq \emptyset \iff s = \emptyset$ and $\mathrm{univ} \subseteq s \iff s = \mathrm{univ}$. The universal set is empty only on an empty type: `Set.univ_eq_empty_iff`.

The API of `Set.Nonempty` lives in the namespace of the predicate, so that dot notation works on a proof `hs : Set.Nonempty s`. For example, `hs.mono h` is `Set.Nonempty.mono` and gives `Set.Nonempty t` from `h : s ⊆ t`. The function `Set.Nonempty.some` chooses a point, and `Set.Nonempty.some_mem` says that the point lies in $s$. The bridge to the empty set is the next result.

**Theorem (`Set.not_nonempty_iff_eq_empty`).** A set is not nonempty if and only if it is empty.

*Proof.* The set $s$ is not nonempty when $\neg \exists x, x \in s$, that is, $\forall x, x \notin s$. By extensionality, this says $s = \emptyset$. $\square$

The lemmas `Set.nonempty_coe_sort` and `Set.isEmpty_coe_sort` relate the predicate on the set to the classes `Nonempty` and `IsEmpty` on its type. The lemma `Set.nonempty_of_mem` gives a nonempty set from a member, and `Set.Nonempty.ne_empty` gives $s \ne \emptyset$.

#### Separation, the power set and decidability

The separation $\{x \in s \mid p(x)\}$ is the set $\{x \mid x \in s \land p(x)\}$, and `Set.mem_sep_iff` is its membership lemma. The lemmas `Set.inter_ofPred_eq_sep`, `Set.sep_union`, `Set.sep_inter` and `Set.sep_subset` relate it to the other operations. The power set has the lemmas `Set.powerset_mono`, `Set.powerset_inter` ($\mathcal{P}(s \cap t) = \mathcal{P}(s) \cap \mathcal{P}(t)$), `Set.powerset_empty` and `Set.powerset_univ`. The file also has the instances `Set.decidableUnion`, `Set.decidableInter`, `Set.decidableCompl` and others. They decide the membership in a union from a decision for each part, so that `if x ∈ s ∪ t then ... else ...` makes sense.

#### Sets as types

A set $s$ of $\alpha$ is also a type, the subtype of the points of $s$. `Mathlib.Data.Set.CoeSort` defines this type as `Set.Elem s`, and the instance `Set.instCoeSortType` lets a user write `↥s` or just `s` where a type is expected. An element of the type is a pair of a point and a proof of membership, and the coercion `↑x : α` forgets the proof. By `Set.coe_eq_subtype`, the type is `{x // x ∈ s}`. The lemmas `SetCoe.forall` and `SetCoe.exists` turn a quantifier over the type into a quantifier over $\alpha$ with a membership hypothesis, and `SetCoe.ext` says that two elements with the same value are equal.

The file `Mathlib.Data.Set.Notation` has two scoped notations, which a user enables with `open Set.Notation`. For `t : Set s`, the coercion `(t : Set α)` is the image of `t` under the coercion of `s`. For two sets $A, B$ of $\alpha$, `A ↓∩ B` is the intersection of $A$ and $B$ seen as a set of the type `A`, that is, the preimage of $B$ under the coercion. The API of these notations is in the next section of the chapter.

#### Disjoint sets and the symmetric difference

`Disjoint s t` is the general order notion: each common lower bound of $s$ and $t$ is $\bot$. For sets, `Set.disjoint_iff_inter_eq_empty` turns it into $s \cap t = \emptyset$, and the next lemma gives the form that proofs use most.

**Theorem (`Set.disjoint_left`).** $s$ and $t$ are disjoint if and only if no element of $s$ lies in $t$.

*Proof.* By `Set.disjoint_iff_inter_eq_empty`, disjointness is $s \cap t = \emptyset$. By extensionality, this is $\forall x, \neg (x \in s \land x \in t)$, which is $\forall x, x \in s \to x \notin t$. $\square$

`Mathlib.Data.Set.Disjoint` has the rest of the API: `Set.disjoint_right` with the roles exchanged, `Set.not_disjoint_iff` ($\neg \mathrm{Disjoint}\, s\, t \iff \exists x \in s, x \in t$), `Set.disjoint_union_left`, `Set.disjoint_of_subset` (disjointness passes to subsets), `Set.disjoint_empty` and `Set.disjoint_univ`. The lemmas in the namespace of `Disjoint` work by dot notation on a hypothesis `h : Disjoint s t`: `Disjoint.notMem_of_mem_left`, `Disjoint.ne_of_mem` and `Disjoint.subset_left_of_subset_union`. For disjoint $s, t$, `Set.mem_union_of_disjoint` says that each point of $s \cup t$ lies in exactly one of the two sets.

The symmetric difference `symmDiff s t`, written $s \mathbin{\triangle} t$, is the general operation of a Boolean algebra. For sets, `Set.symmDiff_def` gives $s \mathbin{\triangle} t = (s \setminus t) \cup (t \setminus s)$, and `Set.mem_symmDiff` is the membership lemma. The file `Mathlib.Data.Set.SymmDiff` also has the distributive laws `Set.inter_symmDiff_distrib_left` and the inclusions `Set.union_symmDiff_subset` and `Set.symmDiff_union_subset`. The companion `bihimp s t` is the set of points that lie in both or in neither, by `Set.mem_bihimp_iff`.

**Theorem (`Set.symmDiff_eq_empty`).** $s \mathbin{\triangle} t = \emptyset$ if and only if $s = t$.

*Proof.* A point $x$ lies in $s \mathbin{\triangle} t$ when it lies in exactly one of the two sets. So the symmetric difference is empty when each $x$ lies in both or in neither, that is, $x \in s \iff x \in t$ for all $x$. By extensionality, this is $s = t$. $\square$

`Set.symmDiff_nonempty` is the negated form: the symmetric difference is nonempty if and only if $s \ne t$.

#### The import file

The file `Mathlib.Data.Set.Lattice` has no declarations of its own: it imports the files on indexed unions and intersections of the second section of the chapter, so that one import gives the whole complete lattice of sets.

#### Common errors

1. A learner writes `s ⊆ t ∧ t ⊆ s` and then looks for a lemma to get `s = t`. The lemma is `Set.Subset.antisymm`, and `Set.Subset.antisymm_iff` is the form with "if and only if". The general lemma `le_antisymm` also works, because `⊆` on sets is the order `≤`.
2. A learner uses `s ≠ ∅` where Mathlib uses `Set.Nonempty s`. Most lemmas take `Set.Nonempty`. Convert with `Set.nonempty_iff_ne_empty'` on the subtype, or with `Set.not_nonempty_iff_eq_empty` and `Set.Nonempty.ne_empty`.
3. A learner confuses the set `s` with its type `↥s`. A lemma about `x : ↥s` needs the point and its proof of membership. Write `⟨x, hx⟩` to build the element and `Subtype.mem x` to get the proof back.

### Exercises

1. (A) Prove $s \cap (t \setminus s) = \emptyset$ with `Set.ext` and the membership lemmas of the table.
2. (A) Show that $s \cup t \subseteq u$ follows from $s \subseteq u$ and $t \subseteq u$, first with `Set.union_subset_iff` and then by a direct proof on points.
3. (A) Prove that $s \mathbin{\triangle} t = (s \cup t) \setminus (s \cap t)$.
4. (B) Show that $s \subseteq t$ if and only if $s \cap t^c = \emptyset$, and state the result with `Disjoint`.
5. (B) Show that the power set preserves intersections but not unions: give sets $s, t$ of $\mathbb{N}$ with $\mathcal{P}(s \cup t) \ne \mathcal{P}(s) \cup \mathcal{P}(t)$.
6. (C) Show that the symmetric difference is associative, and conclude that the sets of a type form a group under $\triangle$ with neutral element $\emptyset$.

### Reference

<?reference?>
