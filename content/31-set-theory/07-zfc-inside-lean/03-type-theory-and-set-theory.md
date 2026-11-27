---
title: Type theory and set theory
kind: theory
modules:
  - Mathlib.SetTheory.Lists
  - Mathlib.SetTheory.Descriptive.Tree
explains:
  E3: [Lists, Finsets, Descriptive.tree]
  E2: [Lists', Lists.Equiv, Lists.atom, Lists.ofList, Lists.toList, Lists.Equiv.antisymm_iff, Lists.Equiv.trans, Lists.equiv_atom, Lists.isList_of_mem, Descriptive.Tree.mem_of_prefix, Descriptive.Tree.tree_eq_bot, Descriptive.Tree.subAt, Descriptive.Tree.mem_subAt, Descriptive.Tree.pullSub, Descriptive.Tree.pullSub_adjunction, Descriptive.Tree.subAt_pullSub, Descriptive.Tree.pullSub_subAt]
  E1: auto
families: [Lists'.*, Descriptive.Tree.*]
requires: [V01.C01, V01.C03, V04.C06, V31.C01, V31.C02, V31.C06]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Type theory and set theory

### Overview

Lean is not based on set theory. Its foundation is a dependent type theory with a hierarchy of universes, inductive types, quotient types and three axioms: propositional extensionality, the soundness of quotients and choice. Sections 1 and 2 built a model of ZFC inside this theory. This section compares the two foundations as far as the library makes the comparison precise. It treats universes and small types, the inaccessible cardinal that each universe gives, the difference between a typed membership and the global membership of ZFC, and two smaller set-like structures in the library: the hereditarily finite lists `Lists α`, a computable model of set theory with atoms and without infinity, and the trees of descriptive set theory. The section also states what the index of this edition does not contain.

### Definitions

**Definition (Small type).** Let $w$ be a universe. A type $\alpha$ is *$w$-small* if it is equivalent to a type in the universe $w$. A universe $u$ is *at most* $v$ if every type in $u$ is $v$-small.

::: mathlib
`Small` · `Mathlib.Logic.Small.Defs`

`Small.{w} α` is a class with the field `equiv_small : ∃ S : Type w, Nonempty (α ≃ S)`. For a small type, `Shrink α : Type w` is a chosen equivalent type and `equivShrink α : α ≃ Shrink α` the equivalence. The class `UnivLE.{u, v}` of `Mathlib.Basic.UnivLE` says that every `α : Type u` is `Small.{v}`.

<?decl Small?>
:::

The connection with Section 2 is the equivalence `ZFSet.coeEquiv : ZFSet.{u} ≃ {s : Set ZFSet.{u} // Small.{u} s}`. A class of ZFC sets of level $u$ is a set exactly when the type of its elements is $u$-small. So in this model "set" means "small class", and "proper class" means "class that is not small". Replacement says that the image of a small type is small.

**Definition (ZFA lists).** Let $\alpha$ be a type, the type of *atoms*. A *ZFA prelist* is either an atom $a \in \alpha$, or a *proper* prelist, built from the empty prelist $[\,]$ by adding a prelist (atom or proper) at the front of a proper prelist. A *ZFA list* is a prelist together with the flag that says whether it is an atom or proper. Two ZFA lists are *equivalent* when they are the same atom, or when they are proper and each is a subset of the other, where $l_1 \subseteq l_2$ means that each entry of $l_1$ is equivalent to an entry of $l_2$. The type $\mathrm{Finsets}(\alpha)$ is the quotient of the ZFA lists by this equivalence.

A ZFA list is a finite tree whose leaves may be atoms, and the equivalence forgets order and repetitions, as the equivalence of pre-sets does. For instance `Lists ℕ` contains the atom $23$ and the proper lists $[\,]$, $[37]$ and $[1, [[2], 3], 4]$.

::: mathlib
`Lists` · `Mathlib.SetTheory.Lists`

`Lists' α : Bool → Type u` is the inductive type of prelists, with the constructors `atom : α → Lists' α false`, `nil : Lists' α true` and `cons' : Lists' α b → Lists' α true → Lists' α true`. `Lists α` is the sigma type `Σ b, Lists' α b`. The functions `Lists.atom`, `Lists.ofList` and `Lists.toList` convert between ZFA lists, atoms and lists of ZFA lists, and `Lists.IsList l` says that `l` is proper.

<?decl Lists?>
:::

**Definition (Tree).** Let $A$ be a type. A *tree on $A$* is a set $T$ of finite sequences of elements of $A$ that is closed under prefixes: if $x \in T$ and $y$ is a prefix of $x$, then $y \in T$. For a tree $T$ and a sequence $x$, the *subtree at $x$* is $T_x = \{y \mid x \frown y \in T\}$, where $\frown$ is concatenation. The *tree pulled back along $x$* is $x \frown S$, the set of all prefixes of $x$ (when $[\,] \in S$) together with all $x \frown z$ for $z \in S$.

Trees on $\mathbb{N}$ are the basic objects of descriptive set theory: the closed subsets of the Baire space $\mathbb{N}^{\mathbb{N}}$ are exactly the sets of infinite branches of trees.

::: mathlib
`Descriptive.tree` · `Mathlib.SetTheory.Descriptive.Tree`

`Descriptive.tree A` is a `CompleteSublattice (Set (List A))`, given by the condition `x ++ [a] ∈ T → x ∈ T`, which is equivalent to closure under prefixes (`Descriptive.Tree.mem_of_prefix`). So arbitrary unions and intersections of trees are trees. The operations are `Descriptive.Tree.subAt T x` and `Descriptive.Tree.pullSub T x`.

<?decl Descriptive.tree?>
:::

### Theorems and proofs

**Theorem (Each universe gives an inaccessible cardinal).** Let $\kappa_u$ be the cardinality of the type of ordinals of universe $u$, measured as a cardinal of a larger universe. Then $\kappa_u$ is strongly inaccessible: it is uncountable, regular, and $2^\lambda < \kappa_u$ for each $\lambda < \kappa_u$.

*Proof.* This is a sketch of the argument in Mathlib, with the details in Chapter 2 and Chapter 6. The cardinals below $\kappa_u$ are, up to the lift, exactly the cardinals of types in universe $u$. A cardinal of universe $u$ that is at least $\aleph_0$ exists, so $\kappa_u > \aleph_0$. If $\lambda < \kappa_u$, then $\lambda$ is the cardinal of a type $\alpha$ in universe $u$, and $2^\lambda$ is the cardinal of the type $\alpha \to \mathrm{Prop}$, which is again in universe $u$. So $2^\lambda < \kappa_u$. For regularity, let $(\lambda_i)_{i \in I}$ be a family of cardinals below $\kappa_u$ with $|I| < \kappa_u$. Then $I$ and each $\lambda_i$ come from types in universe $u$, and the sigma type of the family is in universe $u$. So $\sum_i \lambda_i < \kappa_u$, and $\kappa_u$ is not a supremum of fewer than $\kappa_u$ smaller cardinals. $\square$

::: mathlib
`Cardinal.IsInaccessible.univ` · `Mathlib.SetTheory.Cardinal.Regular`

`Cardinal.univ.{u, v} : Cardinal.{max (u + 1) v}` is the lift of `#Ordinal.{u}`, and `Cardinal.IsInaccessible.univ` says that it is inaccessible. The docstring says that Lean's foundations prove the existence of `v` inaccessibles in universe `v`: the universes below `v` give one inaccessible each.

<?decl Cardinal.IsInaccessible.univ?>
:::

The theorem shows that Lean with its universes proves more than ZFC. In ZFC, the existence of an inaccessible cardinal is not provable if ZFC is consistent, because $V_\kappa$ for an inaccessible $\kappa$ is a model of ZFC, and Gödel's second incompleteness theorem forbids ZFC to prove its own consistency. In Lean the type `ZFSet.{0}` of Section 1 plays the part of $V_\kappa$ for $\kappa = \kappa_0$: it lives in `Type 1`, and Sections 1 and 2 checked each axiom of ZFC for it. The library proves these axioms as separate theorems about `ZFSet`. The index of this edition has no declaration that states ZFC as a first-order theory, or that proves its consistency in the sense of first-order logic.

In the other direction, the type theory can be interpreted in set theory. Werner, in *Sets in types, types in sets* (1997), related the calculus of inductive constructions with finitely many universes to ZFC with a corresponding number of inaccessible cardinals, in both directions. Carneiro, in his thesis *The Type Theory of Lean* (2019), gave a model of Lean's type theory in ZFC with inaccessible cardinals, one for each universe. So a contradiction in Lean would give a contradiction in ZFC with enough inaccessibles. These results are about the type theory, outside Mathlib, and the handbook does not prove them.

**Theorem (Equivalence of ZFA lists is decidable).** If $\alpha$ has decidable equality, then the equivalence of ZFA lists over $\alpha$ is decidable, and so is equality in $\mathrm{Finsets}(\alpha)$.

*Proof.* By recursion on the sum of the sizes of the two lists. Two atoms are equivalent exactly when they are equal (`Lists.equiv_atom`), which is decidable by hypothesis. An atom is never equivalent to a proper list. Two proper lists $l_1$ and $l_2$ are equivalent exactly when $l_1 \subseteq l_2$ and $l_2 \subseteq l_1$ (`Lists.Equiv.antisymm_iff`). The relation $l_1 \subseteq l_2$ holds when each of the finitely many entries of $l_1$ is equivalent to one of the finitely many entries of $l_2$. Each entry is smaller than the list, so the recursion decides each test, and a finite conjunction of finite disjunctions of decidable statements is decidable. Equality of classes in the quotient is the equivalence of representatives. $\square$

This is the main difference from the pre-sets of Section 1. A pre-set may branch over an infinite type, and the equivalence of two pre-sets is a statement about all elements of their index types, which in general has no decision procedure. In ZFA lists each node has finitely many children, so the model has no infinite set. That is why the docstring of the file calls it a computable model of ZFA without infinity.

**Theorem (Adjunction of trees).** Let $S$ and $T$ be trees on $A$ and $x$ a finite sequence. Then $x \frown S \subseteq T$ if and only if $S \subseteq T_x$. So pulling back along $x$ is left adjoint to taking the subtree at $x$, a Galois connection in the sense of Volume 4, Chapter 6.

*Proof.* Assume $x \frown S \subseteq T$ and let $z \in S$. Then $x \frown z \in x \frown S \subseteq T$, so $z \in T_x$. Conversely, assume $S \subseteq T_x$. Let $y \in x \frown S$. If $y = x \frown z$ with $z \in S$, then $z \in T_x$, so $y \in T$. Otherwise $y$ is a prefix of $x$ and $[\,] \in S$. Then $[\,] \in T_x$, which means $x \in T$, and $y \in T$ since $T$ is closed under prefixes. $\square$

### Examples

**Example (Typed and untyped membership).** In ZFC every object is a set, so the statement $1 \in 2$ is meaningful and true for the von Neumann numerals, and $\pi \in 3$ has some truth value that depends on the coding of the reals. In Lean, `(1 : ℕ) ∈ (2 : ℕ)` does not typecheck, since `ℕ` has no membership instance. Membership is a relation between a term `a : α` and a set `s : Set α`, so the type of the elements is fixed. Inside the model, `ZFSet` restores the global membership: for `x y : ZFSet`, `x ∈ y` is meaningful, and the natural number $n$ corresponds to the set $\overline{n}$ of Section 2 with $\overline{1} \in \overline{2}$. The two kinds of objects do not mix: a natural number is not a ZFC set, and the map $n \mapsto \overline{n}$ is an explicit injection.

**Example (Equivalent ZFA lists).** In `Lists ℕ`, let $l_1 = [[\,], [\,], 5]$ and $l_2 = [5, [\,]]$. Each entry of $l_1$ is equivalent to an entry of $l_2$: $[\,]$ to $[\,]$, and $5$ to $5$. Each entry of $l_2$ is equivalent to an entry of $l_1$. So $l_1$ and $l_2$ are equivalent and define the same element $\{5, \emptyset\}$ of `Finsets ℕ`. The atom $5$ and the proper list $[5]$ are not equivalent: one is an atom and the other a set with one element.

**Example (A tree and its subtree).** On $A = \{0, 1\}$, let $T$ be the set of sequences that contain no two consecutive $1$s. The set $T$ is closed under prefixes, so it is a tree. The subtree at $x = [1]$ is $T_x = \{y \mid [1] \frown y \in T\}$: the sequences in $T$ that are empty or begin with $0$. Pulling it back along $[1]$ gives $[1] \frown T_x = \{[\,], [1]\} \cup \{[1] \frown z \mid z \in T_x\}$, a subtree of $T$, in agreement with the adjunction applied to $T_x \subseteq T_x$ (`Descriptive.Tree.pullSub_subAt`).

**Counterexample (A set that is not a tree).** The set $\{[0, 1]\}$ of sequences on $\{0, 1\}$ is not a tree, because its element $[0, 1]$ has the prefix $[0]$, which is not in it. The least tree that contains it is $\{[\,], [0], [0, 1]\}$, the intersection of all trees that contain it, which is a tree because `Descriptive.tree A` is a complete sublattice.

### The library around it

The file `Mathlib.SetTheory.Lists` has the prelists `Lists'`, the lists `Lists`, the mutual inductive definition of `Lists.Equiv` and `Lists'.Subset`, the decidability instances, and `Finsets` with its empty element and decidable equality. It has no union, power set or separation for `Finsets`. The file `Mathlib.SetTheory.Descriptive.Tree` has the tree lattice, `Descriptive.Tree.take` and `Descriptive.Tree.drop` for the elements of a tree, and the operations `subAt` and `pullSub` with their laws: `subAt_append`, `pullSub_append`, `subAt_pullSub` and the adjunction. The index of this edition has no declaration for the infinite branches of a tree or for well-founded trees.

What the index of this edition does not have:

- The index of this edition has no declaration for combinatorial games, pre-games, nimbers or surreal numbers. Earlier versions of Mathlib had these topics under `Mathlib/SetTheory`, but they are not in this edition, so the handbook has no chapter on them.
- The index of this edition has no declaration for forcing, for the constructible universe $L$, or for the independence of the continuum hypothesis. The continuum hypothesis can be stated with the cardinals of Chapter 5. Han and van Doorn proved its independence from ZFC in Lean 3 in the Flypitch project (2020), outside Mathlib.
- The index of this edition has no declaration that states ZFC as a first-order theory in the model theory of Mathlib, or that relates `ZFSet` to such a theory.

Common errors of a learner:

- `Cardinal.univ` and `Ordinal.univ` take two universe parameters, and an expression without explicit universes may elaborate to a different one than intended. Write `univ.{u, u+1}` when the level matters.
- `Lists α` includes atoms. A proper list is one with `IsList`, and only proper lists have elements.
- The trees of `Mathlib.SetTheory.Descriptive.Tree` are sets of finite sequences. They are not the inductive trees of computer science, and not the trees of graph theory.

See the reference table for the full list.

### Exercises

1. (A) Show that `Small.{u} α` holds for each `α : Type u`, and that `ULift.{v} α` is `Small.{u}` for `α : Type u`.
2. (A) Decide by hand whether the ZFA lists $[[\,], [[\,]]]$ and $[[[\,]], [\,], [\,]]$ are equivalent, and whether $[[1, 2]]$ and $[[2, 1], [1, 1, 2]]$ are equivalent.
3. (A) Prove that $T_{x \frown y} = (T_x)_y$ and $T_{[\,]} = T$ for trees.
4. (B) Prove that the empty set is the only tree that does not contain the empty sequence, and that a nonempty tree contains $[\,]$.
5. (B) Let $\kappa$ be a strongly inaccessible cardinal. Prove that $\kappa$ is a fixed point of the beth function on its initial ordinal, $\beth'_\kappa = \kappa$. Use the size theorem of Section 2 to deduce $|V_\kappa| = \kappa$.
6. (B) Explain why the proof that `Cardinal.univ` is a strong limit uses that the type `α → Prop` is in the same universe as `α`. Which feature of Lean's type theory is used here?
7. (C) Define a map from the proper ZFA lists over the empty type to `ZFSet.{0}` by recursion, and prove that two lists are equivalent if and only if their images are equal. Deduce that `Finsets Empty` is in bijection with the hereditarily finite sets $V_\omega$.

### Notes and history

Zermelo's axioms of 1908 allowed urelements, objects that are not sets, and the theory with atoms is called ZFA. Aczel interpreted constructive set theory in Martin-Löf type theory in 1978, with sets as well-founded trees up to bisimulation; the pre-sets of Section 1 follow this idea. The comparison of universes and inaccessibles is due to Werner (1997) for the calculus of inductive constructions, and Carneiro's thesis (2019) treats the type theory of Lean. The independence of the continuum hypothesis was proved by Gödel (consistency, 1938) and Cohen (independence, 1963). Han and van Doorn formalized Cohen's forcing proof in Lean 3, in work presented at the conference CPP in 2020.

### Reference

<?reference?>
