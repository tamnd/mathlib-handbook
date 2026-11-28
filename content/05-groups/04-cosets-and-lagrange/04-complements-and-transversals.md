---
title: Complements and transversals
kind: api
modules:
  - Mathlib.GroupTheory.Complement
explains:
  E2: [Subgroup.IsComplement, Subgroup.IsComplement.card_left, Subgroup.IsComplement.card_mul_card, Subgroup.isComplement'_of_card_mul_and_disjoint, Subgroup.isComplement'_of_coprime, Subgroup.IsComplement'.QuotientMulEquiv, Subgroup.isComplement'_stabilizer]
  E1: auto
families: []
requires: [V05.C01, V05.C03]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Complements and transversals

### Overview

Let $H$ be a subgroup of $G$. A left transversal of $H$ is a set $S$ that contains exactly one element of each left coset $gH$. Then each $g \in G$ is a product $g = sh$ with $s \in S$ and $h \in H$, in exactly one way. Section 1 counts the cosets: a transversal has $[G : H]$ elements. This section gives the library of transversals, and of the more general notion behind them.

Two subsets $S$ and $T$ of $G$ are complements when the multiplication map $S \times T \to G$, $(s, t) \mapsto st$, is a bijection. A left transversal of $H$ is a complement $S$ of $H$ on the left, and a right transversal is a complement of $H$ on the right. When $S$ and $T$ are both subgroups, they are complementary subgroups, and $G$ is then a product $G = HK$ with $H \cap K = 1$. This is the situation of a semidirect product: $S_3$ is the product of $A_3$ and the subgroup $\langle (1\,2) \rangle$. Complements appear again in the transfer homomorphism and in the theorem of Schur and Zassenhaus, which other modules of the library prove.

### The library around it

#### The definition and its forms

The predicate `Subgroup.IsComplement S T` for sets $S, T \subseteq G$ says that the function $(s, t) \mapsto st$ on $S \times T$ is bijective. The predicate `Subgroup.IsComplement' H K` is the same for two subgroups, through their coercions to sets. The additive form is `AddSubgroup.IsComplement`, with sums in place of products.

The definition is a bijectivity statement. The library gives several equivalent forms, and a proof uses the one that fits.

| Lean name | Statement |
|---|---|
| `Subgroup.isComplement_iff_bijective` | the unfolding for subgroups and other `SetLike` types |
| `Subgroup.isComplement_iff_existsUnique` | each $g$ is $st$ for exactly one pair $(s, t)$ |
| `Subgroup.isComplement_iff_existsUnique_inv_mul_mem` | for each $g$ there is exactly one $s \in S$ with $s^{-1} g \in T$ |
| `Subgroup.isComplement_subgroup_right_iff_bijective` | $S$ is a complement of $H$ on the left if and only if $S \to G/H$ is bijective |
| `Subgroup.isComplement_subgroup_left_iff_bijective` | $T$ is a complement of $H$ on the right if and only if $T$ maps bijectively to the right cosets |

The third form, applied with $T = H$, is the transversal condition: $s^{-1} g \in H$ says that $s$ lies in the coset $gH$. The fourth form names the side of the subgroup, not the side of the set: in `Subgroup.isComplement_subgroup_right_iff_bijective` the subgroup is on the right of the product.

Simple cases fix the edge behaviour. A single point $\{g\}$ and the whole group are complements in both orders (`Subgroup.isComplement_univ_singleton` and `Subgroup.isComplement_singleton_univ`). A complement of a point is the whole group (`Subgroup.isComplement_singleton_left`), and a complement of the whole group is a point (`Subgroup.isComplement_univ_left`). The empty set is never a complement (`Subgroup.not_isComplement_empty_left`), so each side of a complement is nonempty (`Subgroup.IsComplement.nonempty_left`). For subgroups, $G$ and $1$ are complements (`Subgroup.isComplement'_top_bot`), and `Subgroup.isComplement'_bot_left` says that the only complement of the trivial subgroup is $G$. The relation is symmetric for subgroups (`Subgroup.IsComplement'.symm`), but not for sets in general.

#### Counting

**Theorem.** If $S$ and $T$ are complements, then $|S| \cdot |T| = |G|$, with `Nat.card`. If $S$ is a left complement of the subgroup $H$, then $|S| = [G : H]$.

*Proof.* The multiplication map is a bijection $S \times T \to G$, so the two sides have the same cardinality. For the second claim, $S$ maps bijectively to $G/H$ by the table above, and $|G/H| = [G : H]$ by definition of the index. $\square$

The names are `Subgroup.IsComplement.card_mul_card` and `Subgroup.IsComplement.card_left`, with `Subgroup.IsComplement.card_right` for a right complement. The forms `Subgroup.IsComplement.ncard_left` and `Subgroup.IsComplement.encard_left` count with `Set.ncard` and `Set.encard`. A complement of $H$ is finite if and only if $H$ has finite index (`Subgroup.IsComplement.finite_left_iff`). The translates $sT$ for $s \in S$ are pairwise disjoint and cover $G$ (`Subgroup.IsComplement.pairwiseDisjoint_smul` and `Subgroup.IsComplement.mul_eq`).

#### Existence of transversals

Each subgroup has transversals, by the axiom of choice: choose one element in each coset. The lemma `Subgroup.isComplement_range_left` says that the range of a section $f : G/H \to G$ of the quotient map is a left complement of $H$. The lemma `Subgroup.exists_isComplement_left` adds a condition: for each $g \in G$ there is a left transversal that contains $g$. The right forms are `Subgroup.exists_isComplement_right` and `Subgroup.isComplement_range_right`. For a chain $H' \le H$ of subgroups, `Subgroup.exists_left_transversal_of_le` gives a set $S$ with $S H' = H$ and $|S| \cdot |H'| = |H|$, a transversal of $H'$ inside $H$.

The library also names the types of all transversals: `Subgroup.LeftTransversal H` is the subtype of the sets $S$ with `Subgroup.IsComplement S H`, and `Subgroup.RightTransversal H` is the right form. Both types are inhabited, by the range of `Quotient.out`.

#### The decomposition of an element

A complement gives a decomposition of each element. The equivalence `Subgroup.IsComplement.equiv` is the inverse bijection $G \to S \times T$, so $g = s t$ with $(s, t)$ its value at $g$ (`Subgroup.IsComplement.equiv_fst_mul_equiv_snd`). The lemmas in the namespace describe the two components. For a left complement $S$ of $K$, the first component depends only on the left coset of $g$ (`Subgroup.IsComplement.equiv_fst_eq_iff_leftCosetEquivalence`), and right multiplication by $k \in K$ changes only the second component (`Subgroup.IsComplement.equiv_mul_right`). When $1 \in S$ and $1 \in T$, the decomposition of $1$ is $(1, 1)$ (`Subgroup.IsComplement.equiv_one`).

For a left transversal $S$ of $H$ there are two derived maps.

1. `Subgroup.IsComplement.leftQuotientEquiv` is the bijection $G/H \to S$ that sends a coset to its representative.
2. `Subgroup.IsComplement.toLeftFun` is the map $G \to S$ that sends $g$ to the representative of $gH$. The lemma `Subgroup.IsComplement.inv_toLeftFun_mul_mem` says $s^{-1} g \in H$ for this representative $s$.

The right forms are `Subgroup.IsComplement.rightQuotientEquiv` and `Subgroup.IsComplement.toRightFun`.

#### Actions on transversals

Let a group $F$ act on $G$ such that the action sends left cosets of $H$ to left cosets of $H$. This is the class `MulAction.QuotientAction F H`, for example the action of $G$ on itself by left multiplication. Then $F$ acts on the left transversals of $H$: $f \cdot S$ is again a left transversal. The representatives move with the action: `Subgroup.smul_toLeftFun` says that $f$ sends the representative of $gH$ in $S$ to the representative of $(f g)H$ in $f \cdot S$, and `Subgroup.smul_leftQuotientEquiv` says the same for cosets. These lemmas are the tools of the transfer homomorphism, which compares two transversals.

#### Complementary subgroups

Let $H$ and $K$ be subgroups. If they are complements, then $H \cap K = 1$ and $H \sqcup K = G$ in the lattice of subgroups (`Subgroup.IsComplement'.isCompl`, with the parts `Subgroup.IsComplement'.disjoint` and `Subgroup.IsComplement'.sup_eq_top`). The converse fails. In $S_3$ the subgroups $\langle (1\,2) \rangle$ and $\langle (1\,3) \rangle$ meet in $1$ and generate $S_3$, but they have $2 \cdot 2 = 4 < 6$ products, so they are not complements. The correct converse asks for $HK = G$ as a set: `Subgroup.isComplement'_of_disjoint_and_mul_eq_univ`.

**Theorem.** Let $G$ be finite and let $H, K$ be subgroups with $H \cap K = 1$ and $|H| \cdot |K| = |G|$. Then $H$ and $K$ are complements. This is `Subgroup.isComplement'_of_card_mul_and_disjoint`.

*Proof.* The multiplication map $H \times K \to G$ is injective. If $hk = h'k'$, then $h'^{-1} h = k' k^{-1}$ lies in $H \cap K = 1$, so $h = h'$ and $k = k'$. An injective map between finite sets of the same cardinality is bijective. $\square$

The lemma `Subgroup.isComplement'_iff_card_mul_and_disjoint` is the equivalence. With the theorem of Lagrange, a condition on the orders is enough.

**Corollary.** If $|H| \cdot |K| = |G|$ and $\gcd(|H|, |K|) = 1$, then $H$ and $K$ are complements. This is `Subgroup.isComplement'_of_coprime`.

*Proof.* The order of $H \cap K$ divides $|H|$ and $|K|$, by Lagrange, so it is $1$ (`Subgroup.disjoint_of_coprime_natCard`). Apply the theorem. $\square$

For example, $A_3$ and $\langle (1\,2) \rangle$ in $S_3$ have orders $3$ and $2$, so they are complements. The Klein group $V_4$ in $A_4$ and the subgroup $\langle (1\,2\,3) \rangle$ have orders $4$ and $3$, so they are complements too.

If $K$ is normal and $H$ is a complement of $K$, then $H$ maps isomorphically onto the quotient: `Subgroup.IsComplement'.QuotientMulEquiv` is an isomorphism $G/K \cong H$. The quotient groups are the subject of Chapter 5. The proof is short: $H$ is a left transversal of $K$, so `Subgroup.IsComplement.leftQuotientEquiv` is a bijection $G/K \to H$, and the product of two cosets $h_1 K \cdot h_2 K = h_1 h_2 K$ has the representative $h_1 h_2$. The index of $K$ is then the order of $H$ (`Subgroup.IsComplement'.index_eq_card`).

**A complement from an action.** Let $G$ act on a set $X$, let $a \in X$, and let $H$ be a subgroup. Assume that only $1 \in H$ fixes $a$, and that for each $g$ some $h \in H$ moves $g \cdot a$ back to $a$. Then $H$ is a complement of the stabilizer of $a$ (`Subgroup.isComplement'_stabilizer`). The two conditions say that $H$ acts simply transitively on the orbit of $a$. For example, in $S_n$ the cyclic subgroup generated by the cycle $(1\,2\,\cdots\,n)$ is a complement of the stabilizer of the point $n$, which is a copy of $S_{n-1}$. The actions are the subject of Chapter 6.

#### Common errors

1. `Subgroup.IsComplement S T` is not symmetric in $S$ and $T$ for sets, because $st \ne ts$ in general. A left transversal of $H$ is `Subgroup.IsComplement S H`, with $S$ first, and a right transversal is `Subgroup.IsComplement H T`.
2. The word *left* or *right* in a name such as `Subgroup.IsComplement.card_left` refers to the position of the set in the product, and the words *subgroup right* refer to the position of the subgroup. Read the statement before using a lemma with such a name.
3. Disjointness and $H \sqcup K = G$ do not make two subgroups complements. Use `Subgroup.isComplement'_of_disjoint_and_mul_eq_univ` or, in a finite group, the cardinality form.

### Exercises

1. (A) Find a left transversal of $\langle (1\,2) \rangle$ in $S_3$ that is not a right transversal.
2. (A) Use `Subgroup.IsComplement.card_left` to prove that each left transversal of $H$ has the same number of elements as each right transversal.
3. (B) Show that a set $S$ is a left and a right transversal of a normal subgroup $N$ as soon as it is a left transversal.
4. (B) Show that the subgroup $\{0, 2\}$ of $\mathbb{Z}/4$ has no complementary subgroup, although it has transversals.
5. (B) Let $p^k$ be the largest power of a prime $p$ that divides $|G|$. Prove that a subgroup of order $p^k$ and a subgroup of order $|G|/p^k$ are complements.
6. (C) Let $H$ be a complement of a normal subgroup $K$. Prove that $G$ is isomorphic to a semidirect product of $K$ and $H$, with $H$ acting on $K$ by conjugation.

### Reference

<?reference?>
