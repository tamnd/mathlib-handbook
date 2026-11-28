---
title: Cosets, the index and the theorem of Lagrange
kind: theory
modules:
  - Mathlib.GroupTheory.Coset.Card
  - Mathlib.GroupTheory.Index
  - Mathlib.GroupTheory.Commensurable
  - Mathlib.GroupTheory.Coset.Defs
  - Mathlib.GroupTheory.Coset.Basic
  - Mathlib.GroupTheory.DoubleCoset
  - Mathlib.GroupTheory.CosetCover
  - Mathlib.GroupTheory.IndexNSmul
explains:
  E3: [Subgroup.card_subgroup_dvd_card]
  E2: [Subgroup.index, Subgroup.card_mul_index, QuotientGroup.leftRel, QuotientGroup.leftRel_apply, Subgroup.leftCosetEquivSubgroup, Subgroup.card_eq_card_quotient_mul_card_subgroup, Subgroup.relIndex_mul_index, Subgroup.index_dvd_card]
  E1: auto
families: []
requires: [V05.C03]
reads_with: ["MIL"]
lean:
  - MathlibHandbook/V05/C04/Examples.lean
  - MathlibHandbook/V05/C04/Exercises.lean
  - MathlibHandbook/V05/C04/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Cosets, the index and the theorem of Lagrange

### Overview

A subgroup $H$ of $G$ cuts $G$ into pieces of equal size, the cosets of $H$. The number of pieces is the index of $H$. The count of the elements of $G$ piece by piece gives the theorem of Lagrange: the order of a subgroup of a finite group divides the order of the group. This is the first theorem that relates the structure of a group to arithmetic. It forbids many subgroups at once. For example, a group of order $10$ has no subgroup of order $3$ or $4$.

This section defines the cosets as the classes of an equivalence relation, proves that each class has $|H|$ elements, and proves Lagrange's theorem and the tower law for the index. The next section applies the theorem to the order of an element. Chapter 5 turns the set of cosets into a group when $H$ is normal.

### Definitions

**Definition (Coset).** Let $H$ be a subgroup of $G$ and $g \in G$. The left coset of $g$ is $g H = \{g h : h \in H\}$. The right coset is $H g = \{h g : h \in H\}$.

**Definition (Left coset relation).** For $a, b \in G$, write $a \sim_H b$ if $a^{-1} b \in H$.

::: mathlib
`QuotientGroup.leftRel` · `Mathlib.GroupTheory.Coset.Defs`

The relation $\sim_H$ as a `Setoid G`. The type of its classes is the quotient `G ⧸ H`, the set of the left cosets. The notation `⧸` is the symbol `\quot`, not the slash `/`. The right coset relation is `QuotientGroup.rightRel`.

<?decl QuotientGroup.leftRel?>
:::

::: mathlib
`QuotientGroup.leftRel_apply` · `Mathlib.GroupTheory.Coset.Defs`

The unfolding of the relation: `leftRel H x y ↔ x⁻¹ * y ∈ H`. Note the order of the factors: the inverse is on the left element.

<?decl QuotientGroup.leftRel_apply?>
:::

**Definition (Index).** The index $[G : H]$ is the number of left cosets of $H$ in $G$, if this number is finite.

::: mathlib
`Subgroup.index` · `Mathlib.GroupTheory.Index`

The index as a natural number: `H.index = Nat.card (G ⧸ H)`, by `Subgroup.index_eq_card`. The convention of `Nat.card` is that an infinite type has cardinality `0`. So `H.index = 0` means that the index is infinite. The index of `⊥` is the order of the group, by `Subgroup.index_bot`, and `H.index = 1 ↔ H = ⊤` is `Subgroup.index_eq_one`.

<?decl Subgroup.index?>
:::

### Theorems and proofs

**Theorem (Cosets are equivalence classes).** The relation $\sim_H$ is an equivalence relation. The class of $a$ is the coset $a H$. For $a, b \in G$ the following are equivalent: $a H = b H$; $b \in a H$; $a^{-1} b \in H$. Two left cosets are equal or disjoint.

*Proof.* Reflexive: $a^{-1} a = 1 \in H$. Symmetric: if $a^{-1} b \in H$, then $(a^{-1} b)^{-1} = b^{-1} a \in H$. Transitive: if $a^{-1} b \in H$ and $b^{-1} c \in H$, then $a^{-1} c = (a^{-1} b)(b^{-1} c) \in H$. The class of $a$ is $\{b : a^{-1} b \in H\}$. Here $a^{-1} b = h \in H$ if and only if $b = a h$, so the class is $a H$. The three statements are equivalent: $b \in a H$ means $a^{-1} b \in H$, as just shown; and two classes of an equivalence relation are equal exactly when the second element is in the first class. Classes of an equivalence relation are equal or disjoint. $\square$

**Theorem (Each coset has $|H|$ elements).** For each $g \in G$, the map $h \mapsto g h$ is a bijection $H \to g H$.

*Proof.* The map is onto $g H$ by the definition of $g H$. It is injective by cancellation: $g h = g h'$ gives $h = h'$. $\square$

::: mathlib
`Subgroup.leftCosetEquivSubgroup` · `Mathlib.GroupTheory.Coset.Basic`

The bijection of the theorem in the other direction, as an equivalence of types from the coset `g • (H : Set G)` to `↥H`. In Mathlib the left coset $g H$ is the pointwise product `g • (H : Set G)`.

<?decl Subgroup.leftCosetEquivSubgroup?>
:::

**Theorem (Lagrange).** Let $G$ be a finite group and $H \le G$. Then $|G| = [G : H] \cdot |H|$. So $|H|$ divides $|G|$, and $[G : H]$ divides $|G|$.

*Proof.* Let $g_1 H, \ldots, g_k H$ be the distinct left cosets, with $k = [G : H]$. They cover $G$, because $g \in g H$. They are pairwise disjoint, by the first theorem. So $|G| = \sum_{i=1}^{k} |g_i H|$. Each term is $|H|$, by the second theorem. So $|G| = k |H|$. $\square$

::: mathlib
`Subgroup.card_eq_card_quotient_mul_card_subgroup` · `Mathlib.GroupTheory.Coset.Card`

The form `Nat.card G = Nat.card (G ⧸ H) * Nat.card H`. The proof in Mathlib is a bijection between `G` and the product `(G ⧸ H) × H`. It needs a choice of one element in each coset, which is the choice of the $g_i$ above. It holds for an infinite group too, with the convention that `Nat.card` is `0` there.

<?decl Subgroup.card_eq_card_quotient_mul_card_subgroup?>
:::

::: mathlib
`Subgroup.card_mul_index` · `Mathlib.GroupTheory.Index`

The same theorem with the index: `Nat.card H * H.index = Nat.card G`. The version with the factors in the other order is `Subgroup.index_mul_card`.

<?decl Subgroup.card_mul_index?>
:::

::: mathlib
`Subgroup.card_subgroup_dvd_card` · `Mathlib.GroupTheory.Coset.Card`

The theorem of Lagrange as a divisibility: `Nat.card H ∣ Nat.card G`. For a finite group with a `Fintype` instance the statement is about `Fintype.card` through `Nat.card_eq_fintype_card`. For two subgroups with `H ≤ K`, the lemma `Subgroup.card_dvd_of_le` gives `Nat.card H ∣ Nat.card K`.

<?decl Subgroup.card_subgroup_dvd_card?>
:::

::: mathlib
`Subgroup.index_dvd_card` · `Mathlib.GroupTheory.Index`

The index divides the order: `H.index ∣ Nat.card G`. For an infinite group the right side is `0`, and each number divides `0`, so the lemma has no finiteness hypothesis.

<?decl Subgroup.index_dvd_card?>
:::

**Theorem (Left and right cosets).** The map $a H \mapsto H a^{-1}$ is a well defined bijection from the left cosets to the right cosets. So $H$ has as many right cosets as left cosets.

*Proof.* The inverse map of sets sends $a H$ to $(a H)^{-1} = \{h^{-1} a^{-1} : h \in H\} = H a^{-1}$, because $h \mapsto h^{-1}$ is a bijection of $H$. So the coset $H a^{-1}$ depends only on the set $a H$, and the map is well defined. The inverse map of sets is its own inverse, and it sends right cosets to left cosets by the same computation. So it is a bijection. $\square$

**Theorem (Tower law).** Let $G$ be a finite group and $H \le K \le G$. Then $[G : H] = [G : K] \cdot [K : H]$.

*Proof.* By Lagrange's theorem for $H \le G$, for $K \le G$ and for $H \le K$:
$$[G : H] = \frac{|G|}{|H|} = \frac{|G|}{|K|} \cdot \frac{|K|}{|H|} = [G : K] \cdot [K : H].$$
The orders are positive, since each subgroup contains $1$. $\square$

The tower law holds for infinite groups too, when the indices are finite. The proof chooses representatives $g_i$ for the cosets of $K$ in $G$ and $k_j$ for the cosets of $H$ in $K$, and shows that the cosets $g_i k_j H$ are distinct and cover $G$.

::: mathlib
`Subgroup.relIndex_mul_index` · `Mathlib.GroupTheory.Index`

The tower law for `H ≤ K`: `H.relIndex K * K.index = H.index`. Here `H.relIndex K` is the index of `H ⊓ K` in `K`, as a subgroup of the type `↥K`. The lemma has no finiteness hypothesis, by the convention that an infinite index is `0`.

<?decl Subgroup.relIndex_mul_index?>
:::

**Corollary (Indices of a chain).** If $H \le K \le G$ with $G$ finite, then $[G : K]$ divides $[G : H]$, and $|H|$ divides $|K|$.

*Proof.* The first claim is the tower law. The second claim is Lagrange's theorem for the group $K$ and its subgroup $H$. $\square$

### Examples

**Example (Cosets of $3\mathbb{Z}$).** In $(\mathbb{Z}, +)$ the cosets are written $a + 3\mathbb{Z}$. There are three: $3\mathbb{Z}$, $1 + 3\mathbb{Z}$ and $2 + 3\mathbb{Z}$, the classes of the remainders modulo $3$. So $[\mathbb{Z} : 3\mathbb{Z}] = 3$, while both groups are infinite. In Mathlib this is the fact that `(AddSubgroup.zmultiples (3 : ℤ)).index = 3`.

**Example (Cosets in $S_3$).** Let $H = \{e, (1\,2)\} \le S_3$, with products that act on the right first. The left cosets are
$$H = \{e, (1\,2)\}, \quad (1\,3) H = \{(1\,3), (1\,2\,3)\}, \quad (2\,3) H = \{(2\,3), (1\,3\,2)\}.$$
For example $(1\,3)(1\,2)$ sends $1 \mapsto 2$, $2 \mapsto 1 \mapsto 3$ and $3 \mapsto 1$, so it is $(1\,2\,3)$. There are $3$ cosets of size $2$, and $3 \cdot 2 = 6 = |S_3|$, as Lagrange's theorem says.

**Counterexample (Left cosets are not right cosets).** In the last example, the right cosets are
$$H, \quad H (1\,3) = \{(1\,3), (1\,3\,2)\}, \quad H (2\,3) = \{(2\,3), (1\,2\,3)\}.$$
So $(1\,3) H \neq H (1\,3)$. The left and the right partitions of $S_3$ differ, although both have three parts. For the subgroup $A_3 = \{e, (1\,2\,3), (1\,3\,2)\}$ the two partitions are the same: both are $\{A_3, S_3 \setminus A_3\}$. Chapter 5 shows that this happens exactly for the normal subgroups.

**Example (Fibres of the determinant).** Let $H = \mathrm{SL}_2(\mathbb{R}) \le \mathrm{GL}_2(\mathbb{R})$. Two matrices $A$ and $B$ are in the same left coset if and only if $A^{-1} B \in H$, that is, $\det B = \det A$. So the cosets are the sets $\{A : \det A = t\}$ for $t \in \mathbb{R}^\times$, and the cosets correspond to the elements of $\mathbb{R}^\times$. The index is infinite.

**Example (Forbidden orders).** By Lagrange's theorem, a subgroup of $D_5$, of order $10$, has order $1$, $2$, $5$ or $10$. A subgroup of $S_4$, of order $24$, has order dividing $24$. The converse fails: $A_4$ has order $12$ and no subgroup of order $6$, as the next section proves.

**Example (Lagrange's theorem in Lean).**

<?lean MathlibHandbook/V05/C04/Examples.lean#lagrange?>

**Example (The index in Lean).**

<?lean MathlibHandbook/V05/C04/Examples.lean#index?>

### The library around it

The theory of cosets is in `Mathlib.GroupTheory.Coset.Defs`, `Mathlib.GroupTheory.Coset.Basic` and `Mathlib.GroupTheory.Coset.Card`. The index and its many lemmas are in `Mathlib.GroupTheory.Index`. The lemma `Subgroup.index_eq_two_iff` characterizes subgroups of index $2$, and `Subgroup.index_ne_zero_of_finite` gives a nonzero index from a finite quotient. The left cosets `G ⧸ H` carry an action of `G`, the subject of Chapter 6. The map `QuotientGroup.mk : G → G ⧸ H` sends `g` to its coset, and the coercion `(g : G ⧸ H)` is this map.

Two subgroups $H$ and $K$ are commensurable when $H \cap K$ has finite index in $H$ and in $K$. The module `Mathlib.GroupTheory.Commensurable` defines this relation as `Subgroup.Commensurable` and proves that it is an equivalence relation, by `Subgroup.Commensurable.equivalence`. The proof of `Subgroup.Commensurable.trans` uses the multiplicativity of the relative index. A subgroup is commensurable with $G$ if and only if it has finite index (`Subgroup.Commensurable.top_left_iff`), and it is commensurable with $\bot$ if and only if it is finite (`Subgroup.Commensurable.bot_left_iff`). The relation is invariant under conjugation and under automorphisms, by `Subgroup.Commensurable.smul_iff`. The commensurator `Subgroup.Commensurable.commensurator H` is the subgroup of the elements $g$ with $g H g^{-1}$ commensurable with $H$, by `Subgroup.Commensurable.commensurator_mem_iff`. For example, the subgroups $4\mathbb{Z}$ and $6\mathbb{Z}$ of $\mathbb{Z}$ are commensurable, because their intersection $12\mathbb{Z}$ has index $3$ in $4\mathbb{Z}$ and index $2$ in $6\mathbb{Z}$.

The module `Mathlib.GroupTheory.Coset.Defs` sets up the quotient `G ⧸ H` for each subgroup `H`, normal or not. The relations are `QuotientGroup.leftRel` and `QuotientGroup.rightRel`, with `QuotientGroup.leftRel_apply` and `QuotientGroup.rightRel_apply` to unfold them: $x \sim y$ means $x^{-1} y \in H$ on the left and $y x^{-1} \in H$ on the right. The main rewriting rule is `QuotientGroup.eq`: two cosets `(a : G ⧸ H)` and `(b : G ⧸ H)` are equal if and only if $a^{-1} b \in H$. The rules `QuotientGroup.mk_surjective`, `QuotientGroup.induction_on` and `QuotientGroup.forall_mk` reduce a statement about all cosets to a statement about all elements. A chosen representative is `Quotient.out`, and `QuotientGroup.mk_out_eq_mul` says that it differs from $g$ by an element of $H$. The map $g \mapsto g^{-1}$ exchanges left and right cosets, and `QuotientGroup.quotientRightRelEquivQuotientLeftRel` is the resulting bijection between the two quotients. Equal subgroups give equivalent quotients by `Subgroup.quotientEquivOfEq`.

The module `Mathlib.GroupTheory.Coset.Basic` treats the cosets as sets. In Mathlib the left coset $a H$ is `a • (H : Set G)` and the right coset $H a$ is `MulOpposite.op a • (H : Set G)`. The lemmas `mem_leftCoset_iff` and `leftCoset_eq_iff` give $x \in a s \iff a^{-1} x \in s$ and $x H = y H \iff x^{-1} y \in H$, with the right-hand forms `mem_rightCoset_iff` and `rightCoset_eq_iff`. A subgroup is normal if and only if each left coset is the right coset of the same element (`normal_iff_eq_cosets`). The module also gives the bijections behind the counting of the section: `Subgroup.leftCosetEquivSubgroup` and `Subgroup.rightCosetEquivSubgroup` for one coset, `Subgroup.groupEquivQuotientProdSubgroup` for $G \simeq (G/H) \times H$, and `Subgroup.quotientEquivProdOfLE` for $G/H \simeq (G/K) \times (K/H)$ when $H \le K$, the form of the tower law for sets. The fibres of a homomorphism $f$ are cosets of the kernel, and `MonoidHom.fiberEquivKer` is the bijection $f^{-1}(f(a)) \simeq \ker f$. For a family of subgroups $H_i$, the map $G / \bigcap_i H_i \to \prod_i G/H_i$ is injective, by `Subgroup.quotientiInfEmbedding`.

A double coset of two subgroups $H$ and $K$ is a set $H a K = \{h a k\}$. The module `Mathlib.GroupTheory.DoubleCoset` defines it as `DoubleCoset.doubleCoset a H K` and the quotient as `DoubleCoset.Quotient H K`, the classes of the relation of `DoubleCoset.rel_iff`. Two double cosets are equal or disjoint (`DoubleCoset.disjoint_out` and `DoubleCoset.doubleCoset_eq_of_mem`), and `DoubleCoset.eq` gives the criterion $H a K = H b K \iff b = h a k$ for some $h \in H$, $k \in K$. Each double coset is a union of left cosets of $K$ (`DoubleCoset.doubleCoset_union_leftCoset`) and of right cosets of $H$. With $H = \bot$ the double cosets are the left cosets of $K$, by `DoubleCoset.left_bot_eq_left_quot`.

The module `Mathlib.GroupTheory.CosetCover` proves a lemma of B. H. Neumann. Suppose that $G$ is the union of $n$ left cosets $g_1 H_1, \dots, g_n H_n$. Then one of the $H_i$ has finite index at most $n$ (`Subgroup.exists_index_le_card_of_leftCoset_cover`), and $\sum_i 1/[G : H_i] \ge 1$ (`Subgroup.one_le_sum_inv_index_of_leftCoset_cover`). The cosets of the subgroups of infinite index can be removed from the cover (`Subgroup.leftCoset_cover_filter_FiniteIndex`). When all $H_i$ are one subgroup $H$, the bound is $[G : H] \le n$, by `Subgroup.index_le_of_leftCoset_cover_const`. The proof of this case is a count: the cosets of $H$ partition $G$, so a cover by $n$ of them needs each of the $[G : H]$ cosets.

The module `Mathlib.GroupTheory.IndexNSmul` computes an index in a free abelian group of finite rank $r$: the subgroup $n M$ of the multiples of $n$ has index $n^r$, by `AddSubgroup.index_range_nsmul`. A subgroup of finite index in a finitely generated torsion-free abelian group has the same rank, by `AddSubgroup.finrank_eq_of_finiteIndex`.

Common errors of a learner:

- The theorem uses `Nat.card`, so for an infinite group it is a statement about `0`. A proof that divides by `Nat.card H` must first show that this number is not `0`, for example with `Nat.card_pos`.
- The relation $\sim_H$ is $a^{-1} b \in H$, not $a b^{-1} \in H$. The second one is the right coset relation, which gives other classes when $H$ is not normal.
- The type `G ⧸ H` is not a group for each `H`. It is a group only when `H` is normal, in Chapter 5.

### Exercises

1. (A) List the cosets of $\langle 4 \rangle$ in $\mathbb{Z}/12$.
2. (A) Show that a group of prime order $p$ has only the subgroups $\{1\}$ and $G$.
3. (A) Show that $g H = H$ if and only if $g \in H$.
4. (B) Let $H$ and $K$ be subgroups of a finite group with coprime orders. Show that $H \cap K = \{1\}$. Hint: $H \cap K$ is a subgroup of both.
5. (B) Let $H$ and $K$ be two distinct subgroups of order $7$ in a group $G$. Show that $H \cap K = \{1\}$, and that the set $H K$ has $49$ elements. Deduce that a group of order $35$ has at most one subgroup of order $7$. Hint: $h k = h' k'$ gives $h'^{-1} h = k' k^{-1} \in H \cap K$.
6. (B) Find the left and the right cosets of $\{e, s\}$ in $D_4$, and check that they differ.
7. (C) Prove the tower law for a group $G$ that may be infinite, when $[G : K]$ and $[K : H]$ are finite. Hint: show that the cosets $g_i k_j H$ are distinct and cover $G$.
8. (L) Prove that the index of a subgroup divides the order of the group. The solution is `index_dvd_example`.

### Notes and history

Lagrange proved in 1771, in his "Réflexions sur la résolution algébrique des équations", that the number of values of a rational function of $n$ variables under the permutations divides $n!$. In modern words, this is the theorem for subgroups of $S_n$. The general theorem for abstract groups, with cosets, is due to Galois and to Jordan, and the name "theorem of Lagrange" came later. Galois saw that a subgroup gives a partition into cosets, and that the left and right partitions agree for the subgroups he called proper decompositions, the normal subgroups of today.

In Mathlib, the left cosets are a quotient by a `Setoid`, not a set of subsets. This makes `G ⧸ H` a type, and it lets Chapter 5 put a group structure on it with no new construction.

### Reference

<?reference?>
