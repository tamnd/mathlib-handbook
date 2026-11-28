---
title: "Instances of Fintype: functions, subsets, sets of a finite type and quotients"
kind: api
modules:
  - Mathlib.Data.Fintype.Basic
  - Mathlib.Data.Fintype.Pi
  - Mathlib.Data.Fintype.Sigma
  - Mathlib.Data.Fintype.Powerset
  - Mathlib.Data.Fintype.Sets
  - Mathlib.Data.Fintype.Vector
  - Mathlib.Data.Fintype.List
  - Mathlib.Data.Fintype.Quotient
  - Mathlib.Data.Fintype.Shrink
  - Mathlib.Data.Fintype.OfMap
  - Mathlib.Data.Fintype.Fin
  - Mathlib.Data.Fintype.Parity
  - Mathlib.Data.Fintype.Units
  - Mathlib.Data.SetLike.Fintype
  - Mathlib.Data.SetLike.Basic
explains:
  E2: [Fintype.piFinset, Fintype.mem_piFinset, Fintype.card_finset, Fintype.card_finset_len, Set.toFinset, Set.mem_toFinset, Fintype.ofInjective, Fintype.ofSurjective, Quotient.finChoice, Fin.univ_succ]
  E1: auto
families: []
requires: [V03.C02, V03.C03]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Instances of Fintype: functions, subsets, sets of a finite type and quotients

### Overview

Section 1 gives the class `Fintype` and the card of the standard constructions. This section gives the instances behind those cards and the tools to make new instances. A type built from finite types by functions, dependent pairs, subtypes, finsets, sets, vectors or quotients is again finite, and the library finds the instance with no help. For a type that is not built in this way, an instance comes from a map: an injection into a finite type or a surjection from one.

The section also gives the finset `Set.toFinset s` of a set with a `Fintype` instance, the finset of functions `Fintype.piFinset t`, the lists of `Finset.univ` for `Fin n`, and the choice of representatives for a finite family of quotients.

### The library around it

#### Instances from a map

The module `Mathlib.Data.Fintype.OfMap` makes an instance from a map. These are definitions, not instances, because the map is data that the library cannot guess:

1. `Fintype.ofInjective f hf` for an injection $f : \alpha \to \beta$ into a finite type, with no other condition;
2. `Fintype.ofSurjective f hf` for a surjection $f : \alpha \to \beta$ from a finite type, with decidable equality on $\beta$;
3. `Fintype.ofBijective` and `Fintype.ofEquiv` for a bijection or an equivalence;
4. `Fintype.ofList` and `Fintype.ofMultiset` from a list or a multiset that contains each element;
5. `Fintype.ofIsEmpty` and `Fintype.ofSubsingleton` for an empty type and a type with at most one element, with `Fintype.univ_ofSubsingleton` giving `Finset.univ` as $\{a\}$.

Use them with `letI := Fintype.ofInjective f hf` in a proof. Two instances of `Fintype α` are equal (`Fintype.subsingleton` of Section 1), but they are not equal by definition, so a goal can need `convert` when two instances meet. The empty types `Empty` and `PEmpty` have the instances `Fintype.instEmpty` and `Fintype.instPEmpty`.

#### The basic instances

The module `Mathlib.Data.Fintype.Basic` gives the instances for the small types: `Unit.fintype`, `PUnit.fintype`, `ULift.fintype`, `PLift.fintype`, `Unique.fintype` for a type with one element, and `Quotient.fintype` for a quotient by a decidable relation. The universe finsets of the small types are given by rules: `Fintype.univ_unit`, `Fintype.univ_bool` (the finset of the two booleans) and `Fintype.univ_empty`. The rule `nonempty_fintype` says that a type with the proposition `Finite α` has some instance, and `Fintype.prodLeft` recovers an instance on $\alpha$ from one on $\alpha \times \beta$ with $\beta$ nonempty.

A finite type has a useful property for sequences. If each finset of points with a property $P$ has a point with $P$ above all of them for a relation $r$, then there is a sequence of points with $P$ that is increasing for $r$. This is `exists_seq_of_forall_finset_exists`, and it builds infinite sequences in proofs about infinite types.

#### Functions and dependent pairs

For a finite type $\alpha$ with decidable equality and finite types $\beta(a)$, the type of dependent functions is finite (`Pi.instFintype`), and so are the types of embeddings (`Function.Embedding.fintype`) and of relation homomorphisms (`RelHom.instFintype`). The finset of functions with values in given finsets is `Fintype.piFinset t`:

$$f \in \operatorname{piFinset}(t) \iff \forall a,\ f(a) \in t(a).$$

This is `Fintype.mem_piFinset`, and `Fintype.coe_piFinset` says that the set of this finset is the product `Set.pi` of the sets $t(a)$ over all $a$. The card is $\prod_a |t(a)|$ (`Fintype.card_piFinset`, in the module `Mathlib.Data.Fintype.BigOperators`). The finset is nonempty if and only if each $t(a)$ is (`Fintype.piFinset_nonempty`), it is monotone (`Fintype.piFinset_subset`), and for $t(a) = $ `Finset.univ` it is `Finset.univ` (`Fintype.piFinset_univ`). The images under an evaluation give back the factors: `Fintype.eval_image_piFinset`.

The module `Mathlib.Data.Fintype.Sigma` gives `Sigma.instFintype` and `PSigma.instFintype` for dependent pairs, and `Finset.univ_sigma_univ` writes `Finset.univ` of a sigma type as a sigma of universe finsets.

#### Finsets, sets and subtypes

For a finite type $\alpha$, the types `Finset α` and `Set α` are finite (`Finset.fintype`, `Set.fintype`), with the cards

$$|\operatorname{Finset}(\alpha)| = 2^{|\alpha|}, \qquad |\{s : \operatorname{Finset}(\alpha) \mid |s| = k\}| = \binom{|\alpha|}{k}.$$

These are `Fintype.card_finset` and `Fintype.card_finset_len`, with `Fintype.card_set` for sets. The powerset of `Finset.univ` is `Finset.univ` (`Finset.powerset_univ`), and the finsets of card $k$ are `Finset.powersetCard k Finset.univ` (`Finset.univ_filter_card_eq`). The equivalence `Fintype.finsetEquivSet` and the order isomorphism `Fintype.finsetOrderIsoSet` identify the finsets and the sets of a finite type.

A subtype $\{x \mid p(x)\}$ of a finite type with a decidable predicate is finite (`Subtype.fintype`). The members of a finset, of a list and of a multiset form finite types (`Finset.fintypeCoeSort`, `List.Subtype.fintype`, `Multiset.Subtype.fintype`), and `Finset.univ_eq_attach` says that `Finset.univ` of the type of members of $s$ is `Finset.attach s`.

#### The finset of a set

A set $s$ with an instance `Fintype s` has a finset of its elements, `Set.toFinset s`:

$$a \in \operatorname{toFinset}(s) \iff a \in s.$$

This is `Set.mem_toFinset`, and `Set.coe_toFinset` gives back the set. Its card is the card of the type (`Set.toFinset_card`). The operations go through: `Set.toFinset_union`, `Set.toFinset_inter`, `Set.toFinset_sdiff`, `Set.toFinset_compl`, `Set.toFinset_insert` and `Set.toFinset_image`. The order goes through as well: `Set.toFinset_subset_toFinset` gives $\operatorname{toFinset}(s) \subseteq \operatorname{toFinset}(t) \iff s \subseteq t$, and `Set.toFinset_nonempty` gives the nonempty case.

The finset depends on the instance, and each rule above takes the instances as arguments. If the instances in the goal and in the rule are not the same, a rewrite fails. Use `Set.toFinset_congr` or `convert`. For a set that is only known to be finite, the finset `Set.Finite.toFinset` of Chapter 5 is the better tool.

#### Vectors, lists, quotients and universes

The module `Mathlib.Data.Fintype.Vector` gives the instances for vectors of a fixed length, `List.Vector.instFintype`, and for the symmetric powers of Chapter 2, `Sym.instFintype`. The module `Mathlib.Data.Fintype.List` gives the instance `fintypeNodupList` for the lists with no duplicate of a finite type, and the multiset `Multiset.lists s` of the lists in the class of $s$ (`Multiset.mem_lists_iff`). The module `Mathlib.Data.Fintype.Shrink` gives `Shrink.instFintype` for a copy of a finite type in a smaller universe, with `Fintype.card_shrink`.

A function on a finite product of quotients is defined on representatives. The definition `Quotient.finChoice` turns a family of classes $(q_i)_{i \in \iota}$ into the class of a family, for $\iota$ finite:

$$\operatorname{finChoice}(i \mapsto [a_i]) = [a].$$

This is `Quotient.finChoice_eq`. It needs no axiom of choice, because $\iota$ is finite. The rule `Quotient.induction_on_fintype_pi` proves a statement about a family of classes from the statement about families of representatives, and `Quotient.finLiftOn` and `Trunc.finChoice` are the forms for functions and for `Trunc`.

#### The type Fin n and three small modules

The module `Mathlib.Data.Fintype.Fin` and the end of `Mathlib.Data.Fintype.Basic` describe `Finset.univ` of `Fin n`. The step rule is

$$\operatorname{univ}_{\operatorname{Fin}(n+1)} = \{0\} \cup \operatorname{succ}(\operatorname{univ}_{\operatorname{Fin}(n)}).$$

This is `Fin.univ_succ`, with `Fin.univ_castSuccEmb` for the form with the last element and `Fin.univ_succAbove` for any element. The image of the value map $\operatorname{Fin}(n) \to \mathbb{N}$ is `Finset.range n` (`Finset.image_fin_univ`), and `Finset.univ_fin2` gives $\{0, 1\}$. The sums over `Fin (n + 1)` of Chapter 6 use these rules.

The module `Mathlib.Data.Fintype.Parity` gives the decidable instance `Fintype.IsSquare.decidablePred` for the squares of a finite type with a multiplication. The module `Mathlib.Data.SetLike.Fintype` gives `SetLike.instFintype`: for a finite type $B$ and a type $A$ of subobjects of $B$, the type $A$ is finite, because a subobject is determined by its set. So a finite group has finitely many subgroups. The modules `Mathlib.Data.Fintype.Units` and `Mathlib.Data.SetLike.Basic` are deprecated and only import their new places, `Mathlib.Algebra.GroupWithZero.Units.Fintype` and `Mathlib.Basic.SetLike.Basic`.

#### Common errors

1. A learner writes `instance : Fintype β := Fintype.ofInjective f hf` as a global instance. Then two instances of `Fintype β` can meet and a rewrite fails. Use `letI` inside the proof, or use `Finite β` with `Finite.of_injective`.
2. A learner rewrites with `Set.mem_toFinset` and gets the error that the motive is not type correct, or no progress. The `Fintype` instance in the goal is not the one that the rule expects. Use `simp` with `Set.mem_toFinset`, or `convert`.
3. A learner expects the finset of all functions $f : \alpha \to \beta$ with $f(a) \in t(a)$ to be `Finset.pi`. That finset holds functions with a proof of membership as a second argument. For total functions on a finite type, use `Fintype.piFinset`.

### Exercises

1. (A) Use `Fintype.card_finset_len` to count the subsets with three elements of `Fin 5`.
2. (A) Write `Finset.univ : Finset (Fin 3)` with `Fin.univ_succ` twice.
3. (B) Give a `Fintype` instance on the type of even numbers less than $10$ with `Fintype.ofInjective`, and check its card.
4. (B) Prove $|\operatorname{piFinset}(t)| = 0$ when some $t(a)$ is empty, with `Fintype.piFinset_nonempty`.
5. (B) Prove that `Set.toFinset {x : Fin 6 | x.val % 2 = 0}` is $\{0, 2, 4\}$ with `Set.mem_toFinset` and `decide`.
6. (C) Use `exists_seq_of_forall_finset_exists` to prove that an infinite type has an injective sequence $\mathbb{N} \to \alpha$.

### Reference

<?reference?>
