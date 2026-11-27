---
title: Indexed unions, pairwise disjoint families and partitions
kind: theory
modules:
  - Mathlib.Data.Set.Lattice.Indexed
  - Mathlib.Data.Set.Lattice.Image
  - Mathlib.Data.Set.Pairwise.Basic
explains:
  E3: [Set.compl_iUnion, Set.PairwiseDisjoint]
  E2: [Set.compl_iInter, Set.iUnion_subset_iff, Set.inter_iUnion, Set.preimage_iUnion, Set.image_iUnion, Set.image_iInter_subset, Set.PairwiseDisjoint.elim, Set.pairwiseDisjoint_fiber]
  E1: auto
families: []
requires: [V01.C02, V01.C03]
reads_with: ["MIL"]
lean:
  - MathlibHandbook/V03/C01/Examples.lean
  - MathlibHandbook/V03/C01/Exercises.lean
  - MathlibHandbook/V03/C01/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Indexed unions, pairwise disjoint families and partitions

### Overview

The union of two sets is not enough for most of mathematics. A measure is additive on a sequence of disjoint sets, a topology is closed under arbitrary unions, and a countable union of countable sets is countable. All these statements use a family $(A_i)_{i \in I}$ of sets, indexed by a set or a type $I$, and its union $\bigcup_i A_i$ and intersection $\bigcap_i A_i$. This section gives the indexed operations, the rules that extend the rules of the previous section to them, and two ideas that the rest of the volume uses all the time: a family of pairwise disjoint sets, and a partition of a set.

The membership in $\bigcup_i A_i$ is an existential statement, "there is $i$ with $x \in A_i$", and the membership in $\bigcap_i A_i$ is a universal statement, "for each $i$, $x \in A_i$". So the laws of the indexed operations are the laws of the quantifiers $\exists$ and $\forall$. The main theorems are the laws of De Morgan for families, the rule that the preimage keeps every union and intersection, and the theorem that the classes of an equivalence relation form a partition. Chapter 3 and Chapter 6 use it to cut a finite set into disjoint pieces and add the sizes of the pieces.

### Definitions

In this section $\alpha$ is a type, $I$ is a type of indices, and $A : I \to \mathcal{P}(\alpha)$ is a family of sets, written $(A_i)_{i \in I}$.

**Definition (Indexed union and intersection).** The union and the intersection of the family are $$\bigcup_{i \in I} A_i = \{x \in \alpha \mid \exists i \in I,\ x \in A_i\}, \qquad \bigcap_{i \in I} A_i = \{x \in \alpha \mid \forall i \in I,\ x \in A_i\}.$$

*Remarks.* The two sets of the previous section are a special case: $A_1 \cup A_2$ is the union of the family indexed by $I = \{1, 2\}$. When $I$ is empty, the union is $\emptyset$ and the intersection is the whole type $\alpha$, because a universal statement over no index is true. A text in set theory often leaves $\bigcap_{i \in \emptyset} A_i$ undefined. In a type theory the intersection is inside the type $\alpha$, so the empty intersection is $\alpha$.

::: mathlib
`Set.iUnion` · `Mathlib.Order.SetNotation`

The notation `⋃ i, s i` is `Set.iUnion s` for `s : ι → Set α`, and `⋂ i, s i` is `Set.iInter s`. The index type `ι` is a `Sort`, so it can be a proposition. This is how Mathlib writes a union over the elements of a set: `⋃ i ∈ t, s i` is `⋃ i, ⋃ (h : i ∈ t), s i`, a union over `i` and then over the proofs of `i ∈ t`. The membership lemmas are `Set.mem_iUnion` and `Set.mem_iInter`, and the forms for two indices are `Set.mem_iUnion₂` and `Set.mem_iInter₂`. The union of a set of sets, $\bigcup \mathcal{S}$, is `⋃₀ S`, that is `Set.sUnion`.

<?decl Set.iUnion?>
:::

**Definition (Pairwise disjoint family).** Two sets $B$ and $C$ are disjoint when $B \cap C = \emptyset$. A family $(A_i)_{i \in I}$ is pairwise disjoint on a set $S \subseteq I$ when $A_i \cap A_j = \emptyset$ for all $i, j \in S$ with $i \neq j$.

*Remarks.* The words "pairwise disjoint" are about the indices, not about the sets. If $A_1 = A_2 = \emptyset$, the family $(A_1, A_2)$ is pairwise disjoint. If $A_1 = A_2 = \{0\}$, it is not, although the set of sets $\{A_1, A_2\} = \{\{0\}\}$ has one element and so has no two different members that meet. The two notions differ only by repetitions in the family.

::: mathlib
`Set.PairwiseDisjoint` · `Mathlib.Data.Set.Pairwise.Basic`

The predicate `s.PairwiseDisjoint f` takes a set of indices `s : Set ι` and a family `f : ι → α` with values in any partial order with a least element. The disjointness is the order notion `Disjoint` of Volume 4. For sets, `Set.disjoint_iff_inter_eq_empty` turns it into $B \cap C = \emptyset$, and `Set.disjoint_left` into "no point of $B$ is in $C$". The same predicate serves for families of finsets in Chapter 3. The set of indices is part of the data so that a proof can restrict a family to a part of its indices, with `Set.PairwiseDisjoint.subset`.

<?decl Set.PairwiseDisjoint?>
:::

**Definition (Partition).** A partition of $\alpha$ is a set $\mathcal{P}$ of subsets of $\alpha$ such that each member of $\mathcal{P}$ is nonempty, and each $x \in \alpha$ is in exactly one member of $\mathcal{P}$. The members of $\mathcal{P}$ are the blocks of the partition.

**Definition (Equivalence classes).** Let $\sim$ be an equivalence relation on $\alpha$, that is, a relation that is reflexive, symmetric and transitive. The class of $x$ is $[x] = \{y \in \alpha \mid y \sim x\}$, and $\alpha/{\sim}$ is the set of the classes.

::: mathlib
`Setoid.IsPartition` · `Mathlib.Order.Setoid.Partition`

An equivalence relation in Mathlib is a `Setoid α`. The set of its classes is `Setoid.classes r`, and `Setoid.IsPartition c` says that `∅ ∉ c` and that each point is in a unique member of `c`. The theorem `Setoid.isPartition_classes` is the theorem on classes below. The quotient type `Quotient r` of Volume 1 is the type form of $\alpha/{\sim}$.

<?decl Setoid.IsPartition?>
:::

### Theorems and proofs

**Theorem (The universal properties).** For a set $B \subseteq \alpha$, $$\bigcup_{i} A_i \subseteq B \iff \forall i,\ A_i \subseteq B, \qquad B \subseteq \bigcap_{i} A_i \iff \forall i,\ B \subseteq A_i.$$ So the union is the least set that contains each $A_i$, and the intersection is the largest set contained in each $A_i$.

*Proof.* Suppose that $\bigcup_i A_i \subseteq B$, and fix $i$. Each $x \in A_i$ is in the union, with the witness $i$, so $x \in B$. Conversely, suppose $A_i \subseteq B$ for each $i$, and let $x \in \bigcup_i A_i$. Then $x \in A_j$ for some $j$, and $A_j \subseteq B$ gives $x \in B$.

For the second statement, suppose that $B \subseteq \bigcap_i A_i$, fix $i$ and let $x \in B$. Then $x$ is in each $A_j$, in particular in $A_i$. Conversely, if $B \subseteq A_i$ for each $i$ and $x \in B$, then $x \in A_i$ for each $i$, so $x \in \bigcap_i A_i$. $\square$

::: mathlib
`Set.iUnion_subset_iff` · `Mathlib.Data.Set.Lattice.Indexed`

The first universal property, a special case of `iSup_le_iff` for the complete lattice `Set α`. The one-direction forms `Set.iUnion_subset` and `Set.subset_iInter` are the ones to `apply` in a proof. The inclusions `Set.subset_iUnion` and `Set.iInter_subset` say that each $A_i$ is between the intersection and the union.

<?decl Set.iUnion_subset_iff?>
:::

**Theorem (De Morgan for families).** $$\Bigl(\bigcup_i A_i\Bigr)^c = \bigcap_i A_i^c, \qquad \Bigl(\bigcap_i A_i\Bigr)^c = \bigcup_i A_i^c.$$

*Proof.* Let $x \in \alpha$. The point $x$ is in the left side of the first law when it is not true that there is $i$ with $x \in A_i$. This is the same as: for each $i$, $x \notin A_i$, that is, $x \in A_i^c$ for each $i$. This is the right side. For the second law, $x$ is in the left side when it is not true that $x \in A_i$ for each $i$. By classical logic, this means that there is $i$ with $x \notin A_i$, that is, $x \in \bigcup_i A_i^c$. $\square$

The first law uses only intuitionistic logic. The second law needs classical logic, because it obtains a witness $i$ from $\lnot \forall i, P(i)$.

::: mathlib
`Set.compl_iUnion` · `Mathlib.Data.Set.Lattice.Indexed`

The first law of De Morgan for an indexed family. Its partner is `Set.compl_iInter`. Both have the `simp` attribute, so `simp` pushes a complement inside an indexed union. The forms for a union over a set of indices, `⋃ i ∈ t, s i`, are `Set.compl_iUnion₂` and `Set.compl_iInter₂`.

<?decl Set.compl_iUnion?>
:::

**Theorem (Distributive law).** For a set $B \subseteq \alpha$, $$B \cap \bigcup_i A_i = \bigcup_i (B \cap A_i), \qquad B \cup \bigcap_i A_i = \bigcap_i (B \cup A_i).$$

*Proof.* The point $x$ is in $B \cap \bigcup_i A_i$ when $x \in B$ and there is $i$ with $x \in A_i$. This is the same as: there is $i$ with $x \in B$ and $x \in A_i$, since the statement $x \in B$ does not depend on $i$. That is the membership in $\bigcup_i (B \cap A_i)$. For the second law, if $x \in B$ then $x$ is in both sides. If $x \notin B$, then $x$ is in the left side when $x \in A_i$ for each $i$, and in the right side when $x \in B \cup A_i$, that is $x \in A_i$, for each $i$. So both sides agree in both cases. $\square$

::: mathlib
`Set.inter_iUnion` · `Mathlib.Data.Set.Lattice.Indexed`

The distributive law $B \cap \bigcup_i A_i = \bigcup_i (B \cap A_i)$. The form with the union on the left is `Set.iUnion_inter`, and the law for two unions is `Set.iUnion_inter_iUnion`. The dual law is `Set.union_iInter`.

<?decl Set.inter_iUnion?>
:::

**Theorem (Images and preimages of families).** For $f : \alpha \to \beta$ and a family $(B_i)$ of subsets of $\beta$, $$f^{-1}\Bigl(\bigcup_i B_i\Bigr) = \bigcup_i f^{-1}(B_i), \qquad f^{-1}\Bigl(\bigcap_i B_i\Bigr) = \bigcap_i f^{-1}(B_i).$$ For a family $(A_i)$ of subsets of $\alpha$, $$f\Bigl(\bigcup_i A_i\Bigr) = \bigcup_i f(A_i), \qquad f\Bigl(\bigcap_i A_i\Bigr) \subseteq \bigcap_i f(A_i).$$

*Proof.* For the preimage of a union: $x$ is in the left side when $f(x) \in B_i$ for some $i$, that is, $x \in f^{-1}(B_i)$ for some $i$. The intersection is the same with "for each $i$".

For the image of a union, let $y$ be in the left side. Then $y = f(x)$ with $x \in A_i$ for some $i$, so $y \in f(A_i)$. Conversely, if $y \in f(A_i)$, then $y = f(x)$ with $x \in A_i \subseteq \bigcup_j A_j$, so $y$ is in the left side.

For the image of an intersection, let $y = f(x)$ with $x \in A_i$ for each $i$. Then $y \in f(A_i)$ for each $i$. $\square$

The inclusion for the intersection can be strict for two reasons. The first reason is the same as for two sets: $f$ is not injective. The second reason is new. If $I$ is empty, the left side is $f(\alpha)$, the range, and the right side is $\beta$. So even an injective $f$ gives a strict inclusion when it is not surjective and $I$ is empty. For this reason the equality in Mathlib, `Set.image_iInter`, takes a bijective $f$. With a nonempty index type an injective $f$ is enough, and this form is `Set.InjOn.image_iInter_eq`.

::: mathlib
`Set.preimage_iUnion` · `Mathlib.Data.Set.Lattice.Image`

The preimage of an indexed union, a `simp` lemma, with the partner `Set.preimage_iInter`.

<?decl Set.preimage_iUnion?>
:::

::: mathlib
`Set.image_iUnion` · `Mathlib.Data.Set.Lattice.Image`

The image of an indexed union. It follows from the adjunction `Set.image_preimage`, since a left adjoint keeps each supremum.

<?decl Set.image_iUnion?>
:::

**Theorem (Equivalence classes form a partition).** Let $\sim$ be an equivalence relation on $\alpha$. Then the set $\alpha/{\sim}$ of the classes is a partition of $\alpha$. Two classes are equal or disjoint, and $[x] = [y]$ if and only if $x \sim y$.

*Proof.* The proof has three steps: the classes are nonempty, each point is in a class, and two classes that meet are equal.

Each class $[x]$ contains $x$, because $x \sim x$ by reflexivity. So each class is nonempty, and each point $x$ is in at least one class, the class $[x]$.

Now let $x \sim y$. Take $z \in [x]$, so $z \sim x$. Transitivity with $x \sim y$ gives $z \sim y$, so $z \in [y]$. Thus $[x] \subseteq [y]$. By symmetry $y \sim x$, and the same argument gives $[y] \subseteq [x]$. So $x \sim y$ implies $[x] = [y]$. Conversely, if $[x] = [y]$ then $x \in [x] = [y]$, so $x \sim y$.

Suppose that two classes $[x]$ and $[y]$ have a common point $z$. Then $z \sim x$ and $z \sim y$. By symmetry and transitivity $x \sim y$, so $[x] = [y]$ by the previous step. Thus two different classes are disjoint, and a point $z$ is in only one class, the class $[z]$. $\square$

The converse is Exercise 7: a partition gives the equivalence relation "in the same block". So equivalence relations and partitions of $\alpha$ are the same thing in two forms. Mathlib has this correspondence as `Setoid.Partition.orderIso`.

**Theorem (The fibers of a function).** Let $f : \alpha \to \beta$. The fibers $f^{-1}(\{b\})$, for $b \in \beta$, form a pairwise disjoint family with union $\alpha$. The nonempty fibers form a partition of $\alpha$, and it is the partition of the equivalence relation $x \sim y \iff f(x) = f(y)$.

*Proof.* Let $b \neq b'$. A point $x$ in both fibers has $f(x) = b$ and $f(x) = b'$, so $b = b'$, a contradiction. So the fibers are pairwise disjoint. Each point $x$ is in the fiber of $f(x)$, so the union is $\alpha$. The relation $f(x) = f(y)$ is an equivalence relation, because equality is one. The class of $x$ is $\{y \mid f(y) = f(x)\} = f^{-1}(\{f(x)\})$, a nonempty fiber, and each nonempty fiber $f^{-1}(\{b\})$ with $x$ in it is the class of $x$. $\square$

::: mathlib
`Set.pairwiseDisjoint_fiber` · `Mathlib.Data.Set.Pairwise.Basic`

The fibers of `f : ι → α` over the points of any set `s : Set α` are pairwise disjoint. The Finset form of the same fact gives the rule "a sum over a set is the sum over the fibers" of Chapter 6.

<?decl Set.pairwiseDisjoint_fiber?>
:::

::: mathlib
`Set.PairwiseDisjoint.elim` · `Mathlib.Data.Set.Pairwise.Basic`

The way to use a hypothesis of pairwise disjointness: if the sets of two indices of `s` are not disjoint, the two indices are equal. For a family of sets, `Set.pairwiseDisjoint_iff` gives the form "if $f(i) \cap f(j)$ is nonempty then $i = j$".

<?decl Set.PairwiseDisjoint.elim?>
:::

### Examples

**Example (A union of intervals).** In $\mathbb{N}$ let $A_n = \{0, 1, \ldots, n\}$. Then $\bigcup_n A_n = \mathbb{N}$, since $m \in A_m$. Let $B_n = \{m \mid m \ge n\}$. Then $\bigcap_n B_n = \emptyset$: a point $m$ is not in $B_{m+1}$. By De Morgan, $\bigcup_n B_n^c = \bigcup_n \{0, \ldots, n - 1\} = \mathbb{N}$, which agrees with $(\bigcap_n B_n)^c = \emptyset^c = \mathbb{N}$.

**Example (A nested intersection in the reals).** Let $C_n = (-\frac{1}{n+1}, \frac{1}{n+1}) \subseteq \mathbb{R}$. Then $\bigcap_n C_n = \{0\}$. The point $0$ is in each interval. For $x \neq 0$, take $n$ with $\frac{1}{n+1} \le |x|$, which exists by the Archimedean property, and then $x \notin C_n$. So an intersection of open intervals need not be open. This example comes back in the topology of Volume 13.

**Example (The classes of the residue mod 3).** On $\mathbb{Z}$ let $x \sim y$ when $3$ divides $x - y$. This is the relation $f(x) = f(y)$ for $f(x) = x \bmod 3$, with values in $\{0, 1, 2\}$. So the classes are the three fibers $$\{\ldots, -3, 0, 3, 6, \ldots\}, \quad \{\ldots, -2, 1, 4, 7, \ldots\}, \quad \{\ldots, -1, 2, 5, 8, \ldots\}.$$ They are pairwise disjoint, and their union is $\mathbb{Z}$. For example $-7 = 3 \cdot (-3) + 2$, so $-7$ is in the third class, and only there.

**Counterexample (The image of an intersection of a family).** Let $f : \mathbb{N} \to \mathbb{N}$ be the constant $0$, and $B_n = \{m \mid m \ge n\}$ as above. Then $\bigcap_n B_n = \emptyset$, so $f(\bigcap_n B_n) = \emptyset$. But $f(B_n) = \{0\}$ for each $n$, so $\bigcap_n f(B_n) = \{0\}$. For an injective example, take the inclusion $\mathbb{N} \to \mathbb{Z}$ and an empty index type: the image of the empty intersection is $\mathbb{N} \ne \mathbb{Z}$.

**Counterexample (Disjoint as a set of sets but not as a family).** Let $A_1 = A_2 = \{0\}$ in $\mathbb{N}$. The family $(A_1, A_2)$ is not pairwise disjoint, since $A_1 \cap A_2 = \{0\}$. The sum of the sizes is $2$ and the size of the union is $1$. So the rule "the size of a disjoint union is the sum of the sizes" needs pairwise disjointness of the family, with the repetitions counted.

### Common errors

A learner often confuses $\bigcap_{i \in \emptyset} A_i$ with $\emptyset$; it is the whole type. A second error is to state $f(\bigcap_i A_i) = \bigcap_i f(A_i)$ for an injective $f$ with no check that the index type is nonempty. In Lean, `Set.mem_iUnion` applied to `⋃ i ∈ s, A i` gives the nested form `∃ i, ∃ (_ : i ∈ s), x ∈ A i`; the lemma `Set.mem_iUnion₂` gives `∃ i ∈ s, x ∈ A i`.

### The library around it

The lemmas of indexed unions follow one naming pattern. A name with `iUnion` or `iInter` is about `⋃ i, s i` or `⋂ i, s i`; the suffix `₂` is about a union with two indices, which covers `⋃ i ∈ t, s i`; and `sUnion` and `sInter` are about `⋃₀ S`. So there are families such as `Set.mem_iUnion`, `Set.mem_iUnion₂`, `Set.mem_sUnion` and `Set.compl_iUnion`, `Set.compl_iUnion₂`, `Set.compl_sUnion`. The lemma `Set.sUnion_eq_biUnion` moves between the forms, and `Set.iUnion_eq_univ_iff` says that a family covers the type. The lattice lemmas of Volume 4, such as `iSup_le_iff`, apply to `Set α`. The predicate `Set.PairwiseDisjoint` has the API `Set.PairwiseDisjoint.subset`, `Set.PairwiseDisjoint.elim` and `Set.pairwiseDisjoint_iff`. The table at the end lists the declarations of the section.

### Exercises

1. (A) Compute $\bigcup_{n \ge 1} [\frac{1}{n}, 1]$ and $\bigcap_{n \ge 1} [0, \frac{1}{n})$ in $\mathbb{R}$.
2. (A) Show that $\bigcup_i (A_i \cup B_i) = \bigcup_i A_i \cup \bigcup_i B_i$.
3. (A) Give the classes of the relation $x \sim y \iff x^2 = y^2$ on $\mathbb{Z}$. Hint: it is the relation of the fibers of a function.
4. (B) Show that $\bigcup_i A_i \cap \bigcup_j B_j = \bigcup_{i,j} (A_i \cap B_j)$.
5. (B) Let $(A_n)_{n \in \mathbb{N}}$ be any family of sets. Put $D_0 = A_0$ and $D_n = A_n \setminus (A_0 \cup \cdots \cup A_{n-1})$ for $n \ge 1$. Show that the $D_n$ are pairwise disjoint and that $\bigcup_n D_n = \bigcup_n A_n$. This is the disjointing trick of measure theory.
6. (B) Show that $f(\bigcap_i A_i) = \bigcap_i f(A_i)$ when $f$ is injective and the index type is nonempty. Hint: take $i_0$ and a witness $x_{i}$ for each $i$, and show that all the $x_i$ are equal to $x_{i_0}$.
7. (B) Let $\mathcal{P}$ be a partition of $\alpha$. Show that the relation "in the same block" is an equivalence relation, and that its classes are the blocks.
8. (C) Show that the number of partitions of a set with $n$ elements is $1, 1, 2, 5, 15$ for $n = 0, 1, 2, 3, 4$, and list the $5$ partitions of $\{1, 2, 3\}$. These are the Bell numbers.
### Notes and history

Cantor used unions of families of sets in his papers on the topology of the real line in the 1870s, and Hausdorff gave the rules of the indexed operations in *Grundzüge der Mengenlehre* (1914). The correspondence between equivalence relations and partitions is classical. The disjointing trick of Exercise 5 is a standard step in the construction of measures, for example in Folland, *Real Analysis*, Section 1.2.

In Mathlib the indexed operations are the special case for `Set α` of the operations `⨆` and `⨅` of a complete lattice. The Lean 3 file `data/set/lattice.lean` became `Mathlib/Data/Set/Lattice.lean` at the port, and it was later split into the files `Indexed`, `Image` and others. The names `iUnion` and `iInter` replaced the Lean 3 names `Union` and `Inter` at the port to Lean 4. The predicate `Set.PairwiseDisjoint` is stated for any order with a bottom element, so that one predicate serves for sets, finsets and other lattices.

### Reference

<?reference?>
