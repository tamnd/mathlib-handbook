---
title: Insertion, singletons, subsingletons and inclusion maps
kind: api
modules:
  - Mathlib.Data.Set.Insert
  - Mathlib.Data.Set.Subsingleton
  - Mathlib.Data.Set.Subset
  - Mathlib.Data.Set.Inclusion
  - Mathlib.Data.Set.Opposite
  - Mathlib.Data.Set.List
  - Mathlib.Data.Set.Enumerate
explains:
  E2: [Set.insert_subset_iff, Set.pair_eq_pair_iff, Set.subsingleton_iff_eq_empty_or_singleton, Set.subsingleton_or_nontrivial, Set.preimage_val_image_val_eq_self, Set.inclusion_injective, Set.enumerate_inj]
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

## Insertion, singletons, subsingletons and inclusion maps

### Overview

The finite sets of a first course are written by their elements: $\{a\}$, $\{a, b\}$, $\{a, b, c\}$. In Mathlib, these sets come from two operations, the singleton $\{a\}$ and the insertion $\mathrm{insert}\ a\ s = \{a\} \cup s$. The notation `{a, b, c}` is `insert a (insert b {c})`. This section describes the API of these two operations, and of the two predicates that measure the size of a set without a count: a set is a *subsingleton* when it has at most one element, and it is *nontrivial* when it has two distinct elements.

The section then turns to sets inside a subset. A set $s$ of $\alpha$ is also a type, as the previous section explains, and a set of that type is a set "inside $s$". The files `Mathlib.Data.Set.Subset` and `Mathlib.Data.Set.Inclusion` move sets and points between $s$ and $\alpha$, and between $s$ and a larger set $t$. Three small files finish the group: the opposite of a set, the ranges of some functions on lists, and an enumeration of a set by a choice function. The finite sets of Chapter 3 and Chapter 5 use the insertion as the step of induction, so the lemmas of this section come back there with the same names.

### The library around it

#### Insertion and singletons

`Mathlib.Data.Set.Insert` gives the membership lemmas first. `Set.mem_insert_iff` states $x \in \mathrm{insert}\ a\ s \iff x = a \lor x \in s$, and `Set.mem_singleton_iff` states $x \in \{b\} \iff x = b$. The lemmas `Set.mem_insert` ($a \in \mathrm{insert}\ a\ s$) and `Set.mem_insert_of_mem` give membership directly, and `Set.mem_of_mem_insert_of_ne` removes the new point. The definitions unfold by `Set.insert_def` and `Set.singleton_def` ($\{a\} = \mathrm{insert}\ a\ \emptyset$), and `Set.insert_eq` writes the insertion as a union.

The simp normal form of a union with a singleton is the insertion: `Set.singleton_union` and `Set.union_singleton` rewrite $\{a\} \cup s$ and $s \cup \{a\}$ to $\mathrm{insert}\ a\ s$. The main algebraic rules follow.

| Lean name | Statement |
|---|---|
| `Set.insert_eq_of_mem` | $a \in s \Rightarrow \mathrm{insert}\ a\ s = s$ |
| `Set.insert_comm` | $\mathrm{insert}\ a\ (\mathrm{insert}\ b\ s) = \mathrm{insert}\ b\ (\mathrm{insert}\ a\ s)$ |
| `Set.insert_idem` | inserting the same point twice is inserting it once |
| `Set.insert_ne_self` | $\mathrm{insert}\ a\ s \ne s \iff a \notin s$ |
| `Set.insert_inter_distrib` | $\mathrm{insert}\ a\ (s \cap t) = \mathrm{insert}\ a\ s \cap \mathrm{insert}\ a\ t$ |
| `Set.insert_union_distrib` | the same law for the union |
| `Set.ssubset_insert` | $a \notin s \Rightarrow s \subset \mathrm{insert}\ a\ s$ |
| `Set.insert_nonempty` | $\mathrm{insert}\ a\ s$ is nonempty |
| `Set.singleton_eq_singleton_iff` | $\{x\} = \{y\} \iff x = y$ |
| `Set.powerset_singleton` | $\mathcal{P}(\{x\}) = \{\emptyset, \{x\}\}$ |

The inclusions of an insertion and of a singleton reduce to membership.

**Theorem (`Set.insert_subset_iff`).** $\mathrm{insert}\ a\ s \subseteq t \iff a \in t \land s \subseteq t$.

*Proof.* The left side says: for each $x$, if $x = a$ or $x \in s$, then $x \in t$. The case $x = a$ gives $a \in t$, and the case $x \in s$ gives $s \subseteq t$. Conversely, the two facts cover both cases. $\square$

The special case $s = \emptyset$ is `Set.singleton_subset_iff`: $\{a\} \subseteq s \iff a \in s$. In the other direction, `Set.subset_singleton_iff_eq` says that the subsets of $\{x\}$ are $\emptyset$ and $\{x\}$, and `Set.Nonempty.subset_singleton_iff` gives $s = \{x\}$ for a nonempty $s \subseteq \{x\}$. The strict inclusions have `Set.ssubset_iff_insert`: $s \subset t$ if and only if some $a \notin s$ has $\mathrm{insert}\ a\ s \subseteq t$.

The quantifiers over an insertion split into two parts, by `Set.forall_mem_insert` and `Set.exists_mem_insert`. This is the form that an induction on a finite set uses. The disjointness has `Set.disjoint_singleton_left` ($\{a\}$ and $s$ are disjoint if and only if $a \notin s$) and `Set.disjoint_insert_left`. The intersections with a singleton have `Set.inter_singleton_of_mem` and `Set.inter_singleton_eq_empty`.

The pairs $\{a, b\}$ have their own lemmas: `Set.pair_comm` ($\{a, b\} = \{b, a\}$), `Set.pair_eq_singleton` ($\{a, a\} = \{a\}$) and `Set.subset_pair_iff`. The equality of two pairs is the classical fact behind the definition of an ordered pair in set theory.

**Theorem (`Set.pair_eq_pair_iff`).** $\{x, y\} = \{z, w\}$ if and only if $x = z \land y = w$, or $x = w \land y = z$.

*Proof.* The direction from right to left is `Set.pair_comm` in the second case. For the other direction, $x \in \{z, w\}$, so $x = z$ or $x = w$. Take $x = z$. Then $y \in \{z, w\}$. If $y = w$, the first case holds. If $y = z = x$, the left side is $\{x\}$, so $w \in \{x\}$, and $w = x = y$; again the first case holds. The case $x = w$ is symmetric and gives the second case. $\square$

Two definitions of the file connect insertion with types. `Set.uniqueSingleton` is the instance that says the type of $\{a\}$ has exactly one element. For $x \notin t$, `Set.subtypeInsertEquivOption` is an equivalence between the type of $\mathrm{insert}\ x\ t$ and `Option t`: the new point goes to `none`. The cardinality of a finite type uses this equivalence in the step $|t \cup \{x\}| = |t| + 1$.

#### Subsingletons and nontrivial sets

`Mathlib.Data.Set.Subsingleton` defines `Set.Subsingleton s`, which means $\forall x \in s, \forall y \in s, x = y$, and `Set.Nontrivial s`, which means $\exists x \in s, \exists y \in s, x \ne y$. These are set versions of the classes `Subsingleton` and `Nontrivial` on types, and the lemmas `Set.subsingleton_coe` and `Set.nontrivial_coe_sort` relate the two. `Set.not_subsingleton_iff` says that a set is nontrivial exactly when it is not a subsingleton.

**Theorem (`Set.subsingleton_iff_eq_empty_or_singleton`).** A set is a subsingleton if and only if it is empty or a singleton.

*Proof.* The empty set and each singleton are subsingletons, by `Set.subsingleton_empty` and `Set.subsingleton_singleton`. Conversely, let $s$ be a subsingleton. If $s$ is empty, the first case holds. Otherwise take $x \in s$. Each $y \in s$ equals $x$, so $s \subseteq \{x\}$, and $\{x\} \subseteq s$ because $x \in s$. So $s = \{x\}$. $\square$

**Theorem (`Set.subsingleton_or_nontrivial`).** Each set is a subsingleton or nontrivial.

*Proof.* This is the excluded middle for the statement $\forall x \in s, \forall y \in s, x = y$, whose negation is $\exists x \in s, \exists y \in s, x \ne y$. $\square$

The rest of the API is in the namespaces `Set.Subsingleton` and `Set.Nontrivial`, for dot notation. A subsingleton stays a subsingleton under a smaller set, by `Set.Subsingleton.anti`, and a nontrivial set stays nontrivial under a larger set, by `Set.Nontrivial.mono`. `Set.Subsingleton.induction_on` proves a property of a subsingleton from the cases $\emptyset$ and $\{x\}$. `Set.Nontrivial.exists_ne` finds, for each $z$, a point of $s$ different from $z$, and `Set.Nontrivial.exists_lt` finds $x < y$ in $s$ for a linear order. `Set.nontrivial_iff_pair_subset` says that a set is nontrivial when it contains a pair of distinct points. `Set.Nonempty.exists_eq_singleton_or_nontrivial` is the useful case split for a nonempty set. A function is monotone and strictly monotone on a subsingleton for free: `Set.Subsingleton.monotoneOn` and `Set.Subsingleton.strictMonoOn`. `Set.subsingleton_univ_iff` connects the universal set with the class `Subsingleton` of the type.

#### Sets inside a subset

Let $A$ be a set of $\alpha$. A set $D$ of the type $A$ has an image in $\alpha$ under the coercion `Subtype.val`, and a set $B$ of $\alpha$ has a preimage in $A$. With `open Set.Notation`, the image is written `↑D` and the preimage `A ↓∩ B`. The lemma names call the image `image_val` and the preimage `preimage_val`. `Mathlib.Data.Set.Subset` gives the rules.

| Lean name | Statement |
|---|---|
| `Set.image_val_union` | $\uparrow(D \cup E) = \uparrow D \cup \uparrow E$ |
| `Set.image_val_inter` | $\uparrow(D \cap E) = \uparrow D \cap \uparrow E$ |
| `Set.image_val_sdiff` | $\uparrow(D \setminus E) = \uparrow D \setminus \uparrow E$ |
| `Set.image_val_compl` | $\uparrow(D^c) = A \setminus \uparrow D$ |
| `Set.image_val_iUnion` | the image of an indexed union is the union of the images |
| `Set.image_val_inj` | $\uparrow D = \uparrow E \iff D = E$ |
| `Set.image_val_union_self_left_eq` | $\uparrow D \cup A = A$ |
| `Set.preimage_val_eq_univ_of_subset` | $A \subseteq B \Rightarrow A \mathbin{\downarrow\cap} B = \mathrm{univ}$ |

The image keeps intersections and differences here, although Section 1 shows that an image need not keep them. The reason is that the coercion is injective. The preimage undoes the image.

**Theorem (`Set.preimage_val_image_val_eq_self`).** For $D$ a set of $A$, $A \mathbin{\downarrow\cap} \uparrow D = D$.

*Proof.* Section 1 gives $D \subseteq f^{-1}(f(D))$ for each $f$. For the other inclusion, let $x \in A$ with $\uparrow x \in \uparrow D$. Then $\uparrow x = \uparrow y$ for some $y \in D$. The coercion is injective, so $x = y \in D$. $\square$

The same argument gives `Set.image_val_injective` and `Set.subset_preimage_val_image_val_iff`. So the sets of $A$ are the same as the sets of $\alpha$ that lie inside $A$, and the two notations go back and forth between them.

#### Inclusion maps

For $h : s \subseteq t$, `Set.inclusion h` is the map from the type $s$ to the type $t$ that keeps the point and changes the proof of membership. `Mathlib.Data.Set.Inclusion` gives its API. `Set.coe_inclusion` says that the map keeps the value, and `Set.val_comp_inclusion` says the same for the composite with the coercion. The inclusion of $s$ in itself is the identity, by `Set.inclusion_eq_id`, and two inclusions compose to one, by `Set.inclusion_comp_inclusion` and `Set.inclusion_inclusion`.

**Theorem (`Set.inclusion_injective`).** For $h : s \subseteq t$, the map `Set.inclusion h` is injective.

*Proof.* If two points of $s$ have the same image in $t$, they have the same value in $\alpha$ by `Set.coe_inclusion`. Two elements of a subtype with the same value are equal. $\square$

The map also keeps and reflects the order: `Set.inclusion_le_inclusion` and `Set.inclusion_lt_inclusion`. `Set.inclusion_eq_subtype_map` identifies it with the general `Subtype.map id h`. Later volumes use the inclusion maps to restrict a structure on $t$ to $s$, for example a subgroup inside a larger subgroup.

#### Opposites, lists and enumeration

`Mathlib.Data.Set.Opposite` defines `Set.op s`, the set of the opposites of the points of $s$ in the type `αᵒᵖ`, and its inverse `Set.unop`. `Set.mem_op` and `Set.mem_unop` are the membership lemmas, `Set.op_unop` and `Set.unop_op` say that the two maps are inverse, and `Set.opEquiv` bundles them. `Set.opEquiv_self s` is the equivalence between the types of $s$ and of its opposite. The singletons have `Set.singleton_op` and `Set.singleton_unop`. The opposite type is the dual of a monoid in the volume on groups.

`Mathlib.Data.Set.List` computes some ranges of functions on lists. `Set.range_list_get` says that the range of `List.get` is the set of the members of the list, and `Set.range_list_map` says that the range of `List.map f` is the set of lists with all members in the range of $f$. The instance `List.canLift` lets the tactic `lift` turn a list of values into a list of a subtype when all its members satisfy the predicate. The file `Mathlib.Data.Set.Insert` has the converse question: by `Set.ofPred_mem_list_eq_replicate`, the members of a list form a singleton $\{a\}$ exactly when the list is a repetition of $a$.

`Mathlib.Data.Set.Enumerate` defines `Set.enumerate sel s n`. Here `sel` is a choice function of type `Set α → Option α`. The value at $0$ is `sel s`, and the value at $n + 1$ is the value at $n$ for $s \setminus \{a\}$, where $a$ is the point chosen in $s$. So the enumeration lists the points that `sel` picks one after another, and it stops with `none` when `sel` gives `none`. `Set.enumerate_eq_none` says that after the first `none` all values are `none`, and `Set.enumerate_mem` says that each value lies in $s$ when `sel` chooses inside its argument.

**Theorem (`Set.enumerate_inj`).** If `sel` chooses inside its argument and `Set.enumerate sel s n₁ = some a = Set.enumerate sel s n₂`, then $n_1 = n_2$.

*Proof sketch.* Take $n_1 < n_2$. At step $n_1$ the enumeration picks $a$ in a set $s'$, and the steps after it work inside $s' \setminus \{a\}$. By `Set.enumerate_mem` for that set, the value at $n_2$ is in $s' \setminus \{a\}$, so it is not $a$. This is a contradiction. $\square$

#### Common errors

1. A learner writes `{a} ∪ s` and expects `simp` to keep it. The simp normal form is `insert a s`, by `Set.singleton_union`, so a lemma stated with `{a} ∪ s` does not fire after `simp`.
2. A learner proves `s ≠ ∅` and `∀ x ∈ s, ∀ y ∈ s, x = y` and then looks for a lemma with these two hypotheses. Mathlib states the result as `Set.exists_eq_singleton_iff_nonempty_subsingleton`, with `Set.Nonempty` and `Set.Subsingleton`.
3. A learner applies a lemma about the image of a set in a subtype to `f '' D` for a general `f`. The `image_val` lemmas hold for the coercion `Subtype.val` only; they use its injectivity.

### Exercises

1. (A) Show that $\{1, 2, 3\} = \{3, 1, 2\}$ as sets of $\mathbb{N}$ with `Set.insert_comm` and `Set.pair_comm`.
2. (A) Prove `Set.singleton_subset_iff` from `Set.insert_subset_iff`.
3. (A) Show that $\{x, y\}$ is nontrivial if and only if $x \ne y$.
4. (B) Show that the image of a subsingleton under a function is a subsingleton, and that the image of a nontrivial set under an injective function is nontrivial.
5. (B) Let $s \subseteq t$ be sets of $\alpha$. Describe the range of `Set.inclusion h` as a set of the type $t$, and prove the description.
6. (C) Let `sel` choose the least element of a nonempty set of $\mathbb{N}$, and `none` for the empty set. Compute `Set.enumerate sel s n` for the set $s$ of even numbers, and prove that each point of $s$ appears.

### Reference

<?reference?>
