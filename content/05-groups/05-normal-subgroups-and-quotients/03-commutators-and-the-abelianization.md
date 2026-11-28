---
title: Commutators and the abelianization
kind: api
modules:
  - Mathlib.GroupTheory.Commutator.Basic
  - Mathlib.GroupTheory.Commutator.Finite
  - Mathlib.GroupTheory.Abelianization.Defs
  - Mathlib.GroupTheory.Abelianization.Finite
  - Mathlib.GroupTheory.CommutingProbability
explains:
  E2: [commutator_eq_bot_iff, Subgroup.commutator_le, Subgroup.Normal.quotient_commutative_iff_commutator_le, Subgroup.commutator_commutator_eq_bot_of_rotate, Group.Abelianization.lift, Group.Abelianization.ker_of, commProb_def', DihedralGroup.commProb_odd]
  E1: auto
families: []
requires: [V05.C03, V05.C04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Commutators and the abelianization

### Overview

The commutator of two elements $g, h$ of a group $G$ is $[g, h] = g h g^{-1} h^{-1}$. It is $1$ exactly when $g$ and $h$ commute, so it measures how far the pair is from commuting. The commutators generate a subgroup $[G, G]$, the commutator subgroup or derived subgroup. It is the smallest normal subgroup with a commutative quotient. The quotient $G / [G, G]$ is the abelianization of $G$: the largest commutative quotient of $G$, with a universal property for homomorphisms to commutative groups.

This section describes the library for these objects. The module `Mathlib.GroupTheory.Commutator.Basic` has the identities for commutators of elements and the lattice theory of the commutator $[H_1, H_2]$ of two subgroups. The module `Mathlib.GroupTheory.Abelianization.Defs` builds the abelianization and its universal property. The module `Mathlib.GroupTheory.CommutingProbability` counts the commuting pairs of a finite group. The section uses subgroups and closures from Chapter 3, the index from Chapter 4, and the quotient groups of Section 1 of this chapter.

### The library around it

#### Commutators of elements

The bracket notation `⁅g, h⁆` comes from the class `Bracket`, and the instance `commutatorElement` gives it the value $g h g^{-1} h^{-1}$ in a group. The lemma `commutatorElement_def` unfolds it. The same bracket notation also serves for the Lie bracket of a Lie algebra. The basic identities have names that start with `commutatorElement`.

| Lean name | Statement |
|---|---|
| `commutatorElement_eq_one_iff_mul_comm` | $[g, h] = 1 \iff g h = h g$ |
| `commutatorElement_eq_one_iff_commute` | $[g, h] = 1 \iff$ `Commute g h` |
| `commutatorElement_inv` | $[g, h]^{-1} = [h, g]$ |
| `commutatorElement_one_left` | $[1, g] = 1$ |
| `commutatorElement_self` | $[g, g] = 1$ |
| `commutatorElement_mul_left_eq_conj_mul` | $[a b, c] = a [b, c] a^{-1} [a, c]$ |
| `commutatorElement_mul_right_eq_mul_conj` | $[a, b c] = [a, b] \, b [a, c] b^{-1}$ |
| `conjugate_commutatorElement` | $g [a, b] g^{-1} = [g a g^{-1}, g b g^{-1}]$ |
| `conj_eq_commutatorElement_mul` | $g h g^{-1} = [g, h] \, h$ |
| `map_commutatorElement` | $f([a, b]) = [f(a), f(b)]$ for a homomorphism $f$ |

Each identity is a direct computation with the group axioms. For example, $[a, b]^{-1} = (a b a^{-1} b^{-1})^{-1} = b a b^{-1} a^{-1} = [b, a]$. The tactic *group* proves all of them. The lemmas `Commute.commutatorElement_pow_left` and `Commute.commutatorElement_pow_right` say that $[a, b]^n = [a^n, b]$ when $a$ commutes with $[a, b]$.

The Hall and Witt identity is a relation between three double commutators. The library states it in three forms: `commutatorElement_commutatorElement_conj_mul`, `commutatorElement_conj_commutatorElement_mul` and `conj_commutatorElement_left_commutatorElement_mul`. The first form says

$$[[a, b], b c b^{-1}] \, [[b, c], c a c^{-1}] \, [[c, a], a b a^{-1}] = 1.$$

The set of all commutators is `commutatorSet G`, with the membership lemma `mem_commutatorSet_iff`. It is not a subgroup in general: there are finite groups in which a product of two commutators is not a commutator. The lemma `mem_commutatorSet_of_isConj_sq` gives a less obvious member: if $g$ is conjugate to $g^2$, say $g^2 = x g x^{-1}$, then $g = x g x^{-1} g^{-1} = [x, g]$.

#### The commutator of two subgroups

For subgroups $H_1, H_2$ of $G$, the commutator $[H_1, H_2]$ is the subgroup that the commutators $[h_1, h_2]$ with $h_1 \in H_1$ and $h_2 \in H_2$ generate. The instance `Subgroup.commutator` gives the bracket on `Subgroup G`, and `Subgroup.commutator_def` unfolds it as a `Subgroup.closure`. The commutator subgroup of the group is `commutator G`, and `commutator_def` says that it is `⁅⊤, ⊤⁆`. The main tool for these subgroups is the characterization by generators.

**Proposition (`Subgroup.commutator_le`).** $[H_1, H_2] \le K$ if and only if $[h_1, h_2] \in K$ for all $h_1 \in H_1$ and $h_2 \in H_2$.

*Proof.* The subgroup $[H_1, H_2]$ is the closure of the set of these commutators. A closure lies in $K$ if and only if its generating set lies in $K$. $\square$

Most of the lattice lemmas follow from this one. The commutator is monotone in each argument (`Subgroup.commutator_mono`) and symmetric (`Subgroup.commutator_comm`), because $[h_1, h_2]^{-1} = [h_2, h_1]$. For normal subgroups, $[H_1, H_2] \le H_1 \cap H_2$ (`Subgroup.commutator_le_inf`), since $h_1 (h_2 h_1^{-1} h_2^{-1})$ lies in $H_1$ and $(h_1 h_2 h_1^{-1}) h_2^{-1}$ lies in $H_2$. The commutator of two normal subgroups is normal (`Subgroup.commutator_normal`), and of two characteristic subgroups is characteristic (`Subgroup.commutator_characteristic`). The other lemmas of the family are listed here.

| Lean name | Statement |
|---|---|
| `Subgroup.commutator_eq_bot_iff_le_centralizer` | $[H_1, H_2] = 1 \iff H_1 \le C_G(H_2)$ |
| `Subgroup.commutator_self_eq_bot_iff` | $[H, H] = 1 \iff H$ is commutative |
| `Subgroup.commutator_top_left_le_iff` | $[G, H] \le H \iff H$ is normal |
| `Subgroup.commutator_center_left` | $[Z(G), H] = 1$ |
| `Subgroup.commutator_eq_bot_of_disjoint` | normal $H_1, H_2$ with $H_1 \cap H_2 = 1$ commute |
| `Subgroup.map_commutator` | $f([H_1, H_2]) = [f(H_1), f(H_2)]$ |
| `Subgroup.commutator_prod_prod` | $[H_1 \times K_1, H_2 \times K_2] = [H_1, H_2] \times [K_1, K_2]$ |
| `Subgroup.commutator_sup_left` | $[N, H \sqcup K] = [N, H] \sqcup [N, K]$ for normal $N$ |

The three subgroups lemma is `Subgroup.commutator_commutator_eq_bot_of_rotate`: if $[[H_2, H_3], H_1] = 1$ and $[[H_3, H_1], H_2] = 1$, then $[[H_1, H_2], H_3] = 1$. Its proof applies the Hall and Witt identity to the generators. One consequence is `commutator_centralizer_commutator_le_center`: the centralizer $C$ of $[G, G]$ has $[C, C] \le Z(G)$.

#### The commutator subgroup and commutative quotients

The subgroup `commutator G` is normal (`instNormalCommutator`) and characteristic (`instCharacteristicCommutator`). The lemmas `commutator_eq_closure` and `commutator_eq_normalClosure` say that it is the closure of `commutatorSet G` and also its normal closure. A group is commutative if and only if its commutator subgroup is trivial (`commutator_eq_bot_iff`), because $[G, G] = 1$ means $[g, h] = 1$ for all $g, h$. The commutativity is the class `IsMulCommutative G`, which a `CommGroup` instance provides.

**Theorem (`Subgroup.Normal.quotient_commutative_iff_commutator_le`).** Let $N$ be a normal subgroup of $G$. The quotient $G/N$ is commutative if and only if $[G, G] \le N$.

*Proof.* In $G/N$ the commutator of the classes $\bar g, \bar h$ is the class of $[g, h]$. So $G/N$ is commutative if and only if each $[g, h]$ lies in $N$. By `Subgroup.commutator_le`, this says $[G, G] \le N$. $\square$

The lemma `Subgroup.Normal.of_commutator_le` gives the converse direction for subgroups: each subgroup that contains $[G, G]$ is normal. Indeed $g h g^{-1} = [g, h] h$, and both factors lie in the subgroup. The images of the commutator subgroup are computed by `map_commutator_eq` and `map_commutator_of_surjective`: a surjective homomorphism sends $[G, G]$ onto $[G', G']$.

#### The abelianization

The abelianization is `Group.Abelianization G`, defined as the quotient `G ⧸ commutator G`. It is a commutative group by the instance `Group.instCommGroupAbelianization`. The quotient map is the homomorphism `Group.Abelianization.of`, which is surjective (`Group.Abelianization.surjective_of`) with kernel `commutator G` (`Group.Abelianization.ker_of`).

**Theorem (`Group.Abelianization.lift`).** Let $A$ be a commutative group. Composition with the quotient map is a bijection from the homomorphisms $G^{\mathrm{ab}} \to A$ to the homomorphisms $G \to A$.

*Proof.* Let $f \colon G \to A$. Each commutator lies in the kernel of $f$, since $f([g, h]) = [f(g), f(h)] = 1$ in $A$. So $[G, G] \le \ker f$ (`Group.Abelianization.commutator_le_ker`), and $f$ factors through the quotient. The factorization is unique because the quotient map is surjective. $\square$

In Lean, `Group.Abelianization.lift` is an equivalence `(G →* A) ≃ (Group.Abelianization G →* A)`. The lemma `Group.Abelianization.lift_apply_of` computes it on the image of an element, `Group.Abelianization.lift_unique` gives the uniqueness, and `Group.Abelianization.hom_ext` is the extensionality principle for homomorphisms out of the abelianization. The functor is `Group.Abelianization.map`: a homomorphism $f \colon G \to H$ induces $G^{\mathrm{ab}} \to H^{\mathrm{ab}}$, with `Group.Abelianization.map_of`, `Group.Abelianization.map_id` and `Group.Abelianization.map_comp`. Its kernel is the image of $f^{-1}([H, H])$ (`Group.Abelianization.ker_map`). An isomorphism gives an isomorphism `MulEquiv.abelianizationCongr`. A commutative group is its own abelianization, by `Group.Abelianization.equivOfComm`. The isomorphism `Group.Abelianization.quotientMulEquiv` identifies the abelianization of $G/N$ with the quotient of $G^{\mathrm{ab}}$ by the image of $N$.

The module `Mathlib.GroupTheory.Abelianization.Finite` gives the instance `instFiniteAbelianization`: the abelianization of a finite group is finite.

#### Finiteness results

The module `Mathlib.GroupTheory.Commutator.Finite` proves `Subgroup.commutator_pi_pi_of_finite`: for a finite family of groups, the commutator of two product subgroups is the product of the commutators. For an infinite family only the inclusion `Subgroup.commutator_pi_pi_le` holds, because an element of the product of the commutators may need unboundedly many commutators in its coordinates.

The last part of `Mathlib.GroupTheory.Commutator.Basic` treats groups with finitely many commutators. The set `commutatorRepresentatives G` chooses a pair $(g_1, g_2)$ for each commutator, and `closureCommutatorRepresentatives G` is the subgroup that these pairs generate. It has the same commutator subgroup up to cardinality (`card_commutator_closureCommutatorRepresentatives`). When `commutatorSet G` is finite, the commutator subgroup is finitely generated with `Subgroup.rank_commutator_le_card`, and for a finitely generated group the center has finite index, bounded by `Subgroup.index_center_le_pow`:

$$[G : Z(G)] \le |\mathrm{commutatorSet}(G)|^{\mathrm{rank}(G)}.$$

#### The commuting probability

For a finite type $M$ with a multiplication, `commProb M` is the rational number

$$\mathrm{commProb}(M) = \frac{|\{(x, y) \in M \times M : x y = y x\}|}{|M|^2},$$

the chance that two random elements commute (`commProb_def`). For an infinite type the value is $0$ by convention (`commProb_eq_zero_of_infinite`). It lies in $(0, 1]$ for a finite nonempty type (`commProb_pos`, `commProb_le_one`), and it is $1$ if and only if the multiplication is commutative (`commProb_eq_one_iff`).

**Theorem (`commProb_def'`).** For a finite group $G$, $\mathrm{commProb}(G) = k(G) / |G|$, where $k(G)$ is the number of conjugacy classes.

*Proof.* The pairs $(x, y)$ with $x y = y x$ are the pairs with $y \in C_G(x)$. So their number is $\sum_x |C_G(x)|$. By orbit-stabilizer, $|C_G(x)| = |G| / |\mathrm{cl}(x)|$. Each class $c$ contributes $|c| \cdot |G| / |c| = |G|$ to the sum. So the sum is $k(G) \, |G|$, and dividing by $|G|^2$ gives the claim. $\square$

The function is multiplicative on products: `commProb_prod` and `commProb_pi`. It grows when one passes to a quotient (`Subgroup.commProb_quotient_le`), and for a subgroup $H$ the bound `Subgroup.commProb_subgroup_le` says $\mathrm{commProb}(H) \le \mathrm{commProb}(G) \, [G : H]^2$. The bound `inv_card_commutator_le_commProb` says $1 / |[G, G]| \le \mathrm{commProb}(G)$.

For the dihedral group of order $2n$ with $n$ odd, `DihedralGroup.commProb_odd` gives $\mathrm{commProb}(D_n) = (n + 3) / (4 n)$. This follows from `commProb_def'`: the group has $(n + 3)/2$ conjugacy classes, namely $\{1\}$, the $(n - 1)/2$ pairs $\{r^i, r^{-i}\}$, and one class of all $n$ reflections. The module uses this to show that each number $1/n$ is a commuting probability: `DihedralGroup.commProb_reciprocal` builds a product of dihedral groups, `DihedralGroup.Product (DihedralGroup.reciprocalFactors n)`, with commuting probability $1/n$.

#### Common errors

1. The name `Abelianization` without a namespace is a deprecated alias. Use `Group.Abelianization`, `Group.Abelianization.of` and `Group.Abelianization.lift`. The additive version is `AddGroup.Abelianization`.
2. `commutatorSet G` is a set and not a subgroup. A statement about the subgroup must use `commutator G`, which is its closure.
3. The bracket of subgroups `⁅H₁, H₂⁆` is the subgroup generated by commutators, not the set of commutators. To prove that it lies in a subgroup $K$, apply `Subgroup.commutator_le` and check the generators.

### Exercises

1. (A) Prove `commutatorElement_inv` and `conjugate_commutatorElement` by hand from the definition $[g, h] = g h g^{-1} h^{-1}$.
2. (A) Compute $[S_3, S_3]$ and show that the abelianization of $S_3$ has order $2$.
3. (B) Show that each subgroup of $G$ that contains $[G, G]$ is normal, and deduce that $H/[G, G]$ corresponds to a subgroup of the abelianization.
4. (B) Use `commProb_def'` to compute the commuting probability of $S_3$, of the quaternion group of order $8$ and of $A_4$.
5. (B) Prove that $\mathrm{commProb}(G) \le 5/8$ for a finite group $G$ that is not commutative. Use that $G/Z(G)$ is not cyclic.
6. (C) Prove the three subgroups lemma from the Hall and Witt identity.

### Reference

<?reference?>
