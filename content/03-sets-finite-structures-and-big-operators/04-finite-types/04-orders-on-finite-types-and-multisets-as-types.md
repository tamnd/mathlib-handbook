---
title: Orders on finite types, inverses of bijections and multisets as types
kind: api
modules:
  - Mathlib.Data.Fintype.Inv
  - Mathlib.Data.Fintype.Order
  - Mathlib.Data.Fintype.Lattice
  - Mathlib.Data.Fintype.WithTopBot
  - Mathlib.Data.Fintype.Sort
  - Mathlib.Data.Multiset.Fintype
explains:
  E2: [Fintype.choose, Fintype.bijInv, Fintype.toCompleteLattice, Finite.le_ciSup, Finite.ciSup_lt_iff, Directed.finite_le, Finite.exists_max, monoEquivOfFin, Multiset.ToType, Multiset.mem_toEnumFinset]
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

## Orders on finite types, inverses of bijections and multisets as types

### Overview

On a finite type, a search through all elements always ends. So a finite type with decidable predicates has computable forms of results that need the axiom of choice in general: the unique element with a property, the inverse of a bijection, and the inverse of an injection on its range. The first module of this section gives these.

A finite order has more structure than a general order. A finite nonempty lattice has a top and a bottom, and a finite bounded lattice is complete. A finite family in a conditionally complete lattice is bounded, so its supremum behaves as a maximum. A finite linear order with $k$ elements is isomorphic to `Fin k`. The other modules give these results, and the last module makes a multiset into a type, with one term for each copy of each element, so that a sum over a multiset becomes a sum over a finite type.

### The library around it

#### Choice and inverses on a finite type

Let $\alpha$ be a finite type and $p$ a decidable predicate with a unique solution. The definition `Fintype.choose p hp` gives the solution, with no axiom of choice, and

$$p(\operatorname{choose}(p, h)).$$

This is `Fintype.choose_spec`. The form `Fintype.chooseX` gives the solution with its proof as a term of the subtype.

For a bijection $f : \alpha \to \beta$ from a finite type into a type with decidable equality, `Fintype.bijInv hf` is the inverse map, found by a search of $\alpha$. The rules `Fintype.leftInverse_bijInv`, `Fintype.rightInverse_bijInv` and `Fintype.bijective_bijInv` say that it is a two sided inverse and a bijection. For an injection, `Function.Injective.invOfMemRange` is the inverse on the range, a map from `Set.range f` to $\alpha$, with `Function.Injective.left_inv_of_invOfMemRange` and `Function.Injective.right_inv_of_invOfMemRange`. The forms for an embedding are `Function.Embedding.invOfMemRange` and the rules with the same names under `Function.Embedding`.

These definitions compute. The general inverse `Function.invFun` uses the axiom of choice and does not; the rule `Function.Injective.invFun_restrict` says that the two agree on the range.

#### Complete lattices from finite lattices

The module `Mathlib.Data.Fintype.Order` turns a finite order into a complete one. The results are definitions of the abbreviation kind, not instances, because the type can already have another structure of the same kind:

1. `Fintype.toOrderBot` and `Fintype.toOrderTop`: a finite nonempty meet or join semilattice has a bottom or a top, the meet or the join of all elements;
2. `Fintype.toBoundedOrder`: a finite nonempty lattice is bounded;
3. `Fintype.toCompleteLattice`: a finite bounded lattice is complete, with $\sup S$ the finite join of $S$;
4. `Fintype.toCompleteLatticeOfNonempty`: a finite nonempty lattice is complete;
5. `Fintype.toCompleteDistribLattice`, `Fintype.toCompleteLinearOrder` and `Fintype.toCompleteBooleanAlgebra` for the stronger structures.

Use them with `letI := Fintype.toCompleteLattice α`. Some types get a real instance: `Fin.completeLinearOrder` for `Fin n` with $n \ne 0$, and `Bool.completeLinearOrder` and `Bool.completeAtomicBooleanAlgebra` for `Bool`.

#### Suprema of finite families

A finite family in a conditionally complete lattice is bounded above, so the indexed supremum $\bigsqcup_i f(i)$ is an upper bound of the family. This is the main point, because in a general conditionally complete lattice the rule needs a proof that the range is bounded:

$$f(i) \le \bigsqcup_j f(j).$$

This is `Finite.le_ciSup`, with `Finite.ciInf_le` for the infimum. In a conditionally complete linear order, the supremum of a finite nonempty family is attained, so it is below $a$ exactly when each term is:

$$\bigsqcup_i f(i) < a \iff \forall i,\ f(i) < a.$$

This is `Finite.ciSup_lt_iff`, with `Finite.le_ciSup_iff` and the forms for infima. The supremum is monotone (`Finite.ciSup_mono`), it splits over products (`Finite.ciSup_prod`), and a monotone map passes through it: `Finite.map_iSup_of_monotone` gives $g(\bigsqcup_i f(i)) = \bigsqcup_i g(f(i))$. The real numbers are a conditionally complete linear order, so these rules give the maximum of finitely many real numbers with no proof of boundedness.

The same module gives the result for directed families. If $f$ is directed for a transitive relation $r$, each finite part of the family has an upper bound in the family:

$$\forall g : \kappa \to \iota \text{ with } \kappa \text{ finite},\ \exists z,\ \forall i,\ r(f(g(i)), f(z)).$$

This is `Directed.finite_le`, and `Directed.finite_set_le` is the form with a finset of indices. The order forms are `Finite.exists_le` (a finite family in a directed order has an upper bound) and `Set.Finite.exists_le` for a finite set. A set covered by a directed union of finitely many sets is in one of them: `Set.subset_iUnion_iff_of_directed`.

#### Maxima and lattice operations on a finite type

The module `Mathlib.Data.Fintype.Lattice` gives the existence of extreme values. For a nonempty finite type and $f$ into a linear order:

$$\exists x_0,\ \forall x,\ f(x) \le f(x_0).$$

This is `Finite.exists_max`, and `Finite.exists_min` is the dual. The finset sup over `Finset.univ` is the indexed supremum in a complete lattice: `Finset.sup_univ_eq_iSup` and `Finset.inf_univ_eq_iInf`. For finsets of a finite type, `Finset.mem_inf` says that $a$ is in the inf of $f$ over $s$ if and only if $a \in f(i)$ for each $i \in s$.

The module `Mathlib.Data.Fintype.WithTopBot` gives the instances `instFintypeWithTop` and `instFintypeWithBot`: adding a top or a bottom to a finite type gives a finite type, with one more element. The forms for `Finite` are `instFiniteWithTop` and `instFiniteWithBot`.

#### Finite linear orders and Fin

A finite linear order with $k$ elements is order isomorphic to `Fin k`:

$$|\alpha| = k \implies \operatorname{Fin}(k) \simeq_o \alpha.$$

This is `monoEquivOfFin`. The isomorphism sends $i$ to the element of $\alpha$ with exactly $i$ elements below it. The related `finSumEquivOfFinset` splits a finite linear order along a finset $s$ of card $m$ with complement of card $n$: it is an equivalence from `Fin m ⊕ Fin n` to $\alpha$ that is monotone on each part. Both definitions use the sort of finsets of Chapter 3.

#### Multisets as types

For a multiset $m$ with decidable equality, the type `Multiset.ToType m` has one term for each copy of each element: a term is a pair $(x, i)$ with $x \in m$ and $i < \operatorname{count}(x, m)$. The coercion `Multiset.instCoeSortType` lets the multiset $m$ stand for this type. The type is finite (`Multiset.fintypeCoe`), with card $|m|$ (`Multiset.card_coe`). The term for the copy $i$ of $x$ is `Multiset.mkToType m x i`, and `Multiset.coe_mk` gives its first entry.

The finset of the pairs is `Multiset.toEnumFinset m`, a finset of $\alpha \times \mathbb{N}$:

$$(x, i) \in \operatorname{toEnumFinset}(m) \iff i < \operatorname{count}(x, m).$$

This is `Multiset.mem_toEnumFinset`. Its card is $|m|$ (`Multiset.card_toEnumFinset`), it is monotone in $m$ (`Multiset.toEnumFinset_mono`), and its first projections give back $m$ (`Multiset.map_toEnumFinset_fst`). The product and the sum of a multiset become products and sums over the type or the finset:

$$\prod m = \prod_{x : m} x_1.$$

This is `Multiset.prod_eq_prod_coe`, with `Multiset.prod_eq_prod_toEnumFinset` and `Multiset.sum_eq_sum_coe` for the other forms. The equivalence `Multiset.consEquiv` identifies the type of $v ::_m m$ with `Option` of the type of $m$, which is the step of an induction, and `Multiset.mapEquiv` connects the types of $m$ and of its image under a map.

#### Common errors

1. A learner writes `instance := Fintype.toCompleteLattice α` for a type that already has a lattice structure from somewhere else, and gets two different orders. Use `letI` in the proof, and only on a type with no other complete lattice structure.
2. A learner applies `le_ciSup` to a finite family and gets a goal `BddAbove (Set.range f)`. For a finite index type use `Finite.le_ciSup`, which needs no boundedness.
3. A learner uses `Multiset.ToType` and expects the terms to be the elements of $m$. A term is a pair: the element and the number of its copy. Use the first projection for the element.

### Exercises

1. (A) Give `Fintype.choose` for the predicate $2x = 1$ on `Fin 5` with the arithmetic of `Fin 5`, and explain why the solution is unique.
2. (A) List the terms of `Multiset.ToType {1, 1, 2}` as pairs, and check `Multiset.card_coe`.
3. (B) Prove $\bigsqcup_{i < 3} f(i) = \max(f(0), f(1), f(2))$ for $f : \operatorname{Fin}(3) \to \mathbb{R}$ with `Finite.le_ciSup` and `Finite.ciSup_lt_iff`.
4. (B) Use `Finite.exists_max` to prove that a function from a nonempty finite type to $\mathbb{N}$ is bounded.
5. (B) Describe `monoEquivOfFin` for the set $\{2, 5, 7\}$ as a linear order with three elements.
6. (C) Use `Directed.finite_le` to prove that for an increasing sequence of sets $(A_n)$, each finite set contained in $\bigcup_n A_n$ is contained in some $A_n$.

### Reference

<?reference?>
