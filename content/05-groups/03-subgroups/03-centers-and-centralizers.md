---
title: Centers, centralizers and submonoids of inverses
kind: api
modules:
  - Mathlib.GroupTheory.Subsemigroup.Center
  - Mathlib.GroupTheory.Subsemigroup.Centralizer
  - Mathlib.GroupTheory.Subsemigroup.Lemmas
  - Mathlib.GroupTheory.Submonoid.Center
  - Mathlib.GroupTheory.Submonoid.Centralizer
  - Mathlib.GroupTheory.Subgroup.Center
  - Mathlib.GroupTheory.Subgroup.Centralizer
  - Mathlib.GroupTheory.Submonoid.Inverses
explains:
  E2: [Subgroup.centralizer, Subgroup.mem_centralizer_iff, Subgroup.centralizer_le, Subgroup.centralizer_closure, Subgroup.le_centralizer_iff, Subgroup.centralizer_univ, Submonoid.centralizer_centralizer_centralizer, Subgroup.normalizerMonoidHom_ker, Submonoid.leftInv, Submonoid.leftInv_leftInv_eq]
  E1: auto
families: []
requires: [V01, V05.C01, V05.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Centers, centralizers and submonoids of inverses

### Overview

The center of a group $G$ is the set of the elements that commute with every element of $G$. The centralizer of a subset $S$ is the set of the elements that commute with every element of $S$. So the center is the centralizer of the whole group. These sets measure how far a group is from being commutative. The center is all of $G$ exactly when $G$ is commutative, and the centralizer of one element $g$ contains the cyclic subgroup $\langle g \rangle$.

Mathlib defines the center and the centralizer three times: as a subsemigroup of a semigroup, as a submonoid of a monoid and as a subgroup of a group. The underlying set is always `Set.center M` or `Set.centralizer S`, so the three versions agree, and the library has lemmas that pass from one to the next. This section describes the three layers, their common lemmas, and the conjugation map of a normalizer, whose kernel is a centralizer. It ends with the submonoid of left inverses of a submonoid, a small construction that turns a submonoid of units into a group.

The section uses the subgroups, the closure and the lattice `Subgroup G` of Section 1. Chapter 5 proves that the center is a normal subgroup, and Chapter 6 identifies the centralizer of an element with its stabilizer under conjugation.

### The library around it

#### The three layers

The definitions are in the modules `Mathlib.GroupTheory.Subsemigroup.Center`, `Mathlib.GroupTheory.Submonoid.Center` and `Mathlib.GroupTheory.Subgroup.Center`. For a type with a multiplication, `Subsemigroup.center M` is the subsemigroup with carrier `Set.center M`. For a monoid, `Submonoid.center M` adds the unit, and for a group, `Subgroup.center G` adds the inverses. The membership lemmas have the same form in the three layers.

| Lean name | Statement |
|---|---|
| `Subsemigroup.mem_center_iff` | $z \in Z(M) \iff \forall g,\ g z = z g$, in a semigroup |
| `Submonoid.mem_center_iff` | the same statement in a monoid |
| `Subgroup.mem_center_iff` | the same statement in a group |
| `Submonoid.coe_center` | the carrier of `Submonoid.center M` is `Set.center M` |
| `Subgroup.coe_center` | the carrier of `Subgroup.center G` is `Set.center G` |
| `Submonoid.center_toSubsemigroup` | the submonoid center, as a subsemigroup, is the subsemigroup center |
| `Subgroup.center_toSubmonoid` | the subgroup center, as a submonoid, is the submonoid center |

In a semigroup or a monoid, `Set.center M` is defined by the structure `IsMulCentral`, which also asks for some associativity conditions. These conditions hold for free when the multiplication is associative, and this is why the three membership lemmas above need a `Semigroup`, a `Monoid` or a `Group`. In a type with only a multiplication, use `Set.mem_center_iff`, which states membership as `IsMulCentral z`.

The center is commutative. The instances `Subsemigroup.center.commSemigroup`, `Submonoid.center.commMonoid` and `Subgroup.center.isMulCommutative` record this. The center is all of $M$ exactly when $M$ is commutative: `Subsemigroup.center_eq_top`, `Submonoid.center_eq_top` and `CommGroup.center_eq_top` give one direction, and `Subgroup.center_eq_top_iff` states the equivalence with the class `IsMulCommutative G`. In the other direction, `Group.commGroupOfCenterEqTop` builds a `CommGroup` structure from the equation `center G = ⊤`.

Membership in the center is decidable when the defining statement is decidable, by the instances `Subsemigroup.decidableMemCenter`, `Submonoid.decidableMemCenter` and `Subgroup.decidableMemCenter`. In a finite group with decidable equality, the tactic `decide` can then test whether an element is central.

#### Centers of products and transport

The center of a product is the product of the centers: $Z(G \times H) = Z(G) \times Z(H)$. The proof is one line: $(g, h)$ commutes with every $(g', h')$ if and only if $g$ commutes with every $g'$ and $h$ with every $h'$, because the operations of $G \times H$ act in each coordinate. The library states this as `Subgroup.center_prod`, `Submonoid.center_prod` and `Subsemigroup.center_prod`. The last one is in the module `Mathlib.GroupTheory.Subsemigroup.Lemmas`, with its additive form `AddSubsemigroup.center_sum`. For an indexed product, `Subgroup.center_pi` and `Submonoid.center_pi` give $Z(\prod_i G_i) = \prod_i Z(G_i)$.

An isomorphism $e : G \cong H$ sends the center onto the center. The equivalence `Subgroup.centerCongr e` restricts $e$ to the centers, and `Subgroup.map_center_eq` states the equality of subgroups. A surjective homomorphism maps the center into the center, by `Subgroup.map_center_le_center`, but the image can be smaller than the center of the target. An injective homomorphism pulls the center of the target back into the center of the source, by `Subgroup.comap_center_le_center`. The center of $G$ and of the opposite group $G^{\mathrm{op}}$ are isomorphic, by `Subgroup.centerToMulOpposite`. The monoid and semigroup layers have the same maps: `Submonoid.centerCongr`, `Subsemigroup.centerCongr`, `Submonoid.centerToMulOpposite` and `Subsemigroup.centerToMulOpposite`.

For a monoid $M$, a unit of the center is a central unit of $M$. The homomorphism `unitsCenterToCenterUnits M` sends `(center M)ˣ` to `center Mˣ`, and `unitsCenterToCenterUnits_injective` says that it is injective. The center also acts on each `MulAction` of $M$ in a way that commutes with $M$: this is the content of the instances `Submonoid.center.smulCommClass_left` and `Submonoid.instSMulCommClassSubtypeMemCenter`.

Two facts link the center to the subgroups of Chapter 5. Each subgroup of the center is normal, by `Subgroup.normal_of_le_center`, and the center is normal and characteristic, by the instances `Subgroup.instNormalCenter` and `Subgroup.centerCharacteristic`. The center is contained in each normalizer, by `Subgroup.center_le_normalizer`. The module also gives `ConjClasses.mk_bijOn`: the map $z \mapsto [z]$ is a bijection from the center onto the set of conjugacy classes with one element. This is the first step of the class equation of Chapter 6.

#### Centralizers

For a subset $S$ of a group $G$, the centralizer is
$$C_G(S) = \{ g \in G : g s = s g \text{ for all } s \in S \}.$$
It is `Subgroup.centralizer S`, with `Submonoid.centralizer S` and `Subsemigroup.centralizer S` for monoids and semigroups. The carrier is `Set.centralizer S`, by `Submonoid.coe_centralizer` and `Subsemigroup.coe_centralizer`. The membership lemma `Subgroup.mem_centralizer_iff` states $g \in C_G(S) \iff \forall h \in S,\ h g = g h$. Note the order: the element of $S$ comes first. For one element, `Subgroup.mem_centralizer_singleton_iff` states $k \in C_G(\{g\}) \iff$ `Commute k g`. The forms `Subgroup.mem_centralizer_iff_commutator_eq_one` and `Subgroup.mem_centralizer_iff_commutator_eq_one'` use the commutator $[h, g] = h g h^{-1} g^{-1}$.

The centralizer reverses inclusion: if $S \subseteq T$ then $C_G(T) \le C_G(S)$, by `Subgroup.centralizer_le`. The proof is immediate: an element that commutes with all of $T$ commutes with all of $S$. The centralizer of everything is the center, by `Subgroup.centralizer_univ`, and the center lies in each centralizer, by `Subgroup.center_le_centralizer`. A centralizer is all of $G$ exactly when $S$ is central, by `Subgroup.centralizer_eq_top_iff_subset`.

**Proposition.** For each subset $S$ of $G$, $C_G(\langle S \rangle) = C_G(S)$.

*Proof.* Since $S \subseteq \langle S \rangle$, the centralizer of $\langle S \rangle$ is contained in $C_G(S)$. Conversely, let $g \in C_G(S)$. The set of the elements that commute with $g$ is $C_G(\{g\})$, a subgroup. It contains $S$, so it contains $\langle S \rangle$. So $g$ commutes with each element of $\langle S \rangle$. $\square$

This is `Subgroup.centralizer_closure`. A useful consequence is `Subgroup.center_eq_iInf`: if $S$ generates $G$, then $Z(G) = \bigcap_{g \in S} C_G(\{g\})$, so an element is central as soon as it commutes with a set of generators.

The relation "$H$ commutes with $K$" is symmetric. In Lean, $H \le C_G(K) \iff K \le C_G(H)$ is `Subgroup.le_centralizer_iff`. A subgroup lies in its own centralizer exactly when it is commutative, by `Subgroup.le_centralizer_iff_isMulCommutative`. From the symmetry, $S \subseteq C(C(S))$, and then $C(C(C(S))) = C(S)$ by the reversal of inclusion. In the monoid layer this is `Submonoid.centralizer_centralizer_centralizer`, and `Subgroup.closure_le_centralizer_centralizer` states that the double centralizer contains the closure of $S$. A set of pairwise commuting elements generates a commutative subgroup, by `Subgroup.isMulCommutative_closure`, with the monoid and semigroup forms `Submonoid.isMulCommutative_closure` and `Subsemigroup.isMulCommutative_closure`.

The cyclic subgroup of $g$ lies in the centralizer of $g$, by `Subgroup.zpowers_le_centralizer_singleton`. The centralizer of a normal subgroup is normal, by the instance `Subgroup.normal_centralizer`, and the centralizer of a characteristic subgroup is characteristic, by `Subgroup.characteristic_centralizer`. A homomorphism maps a centralizer into the centralizer of the image, by `Subgroup.map_centralizer_le_centralizer_image`.

#### Normalizers and the conjugation map

The normalizer $N_G(H)$ of a subgroup $H$ is the set of the $g$ with $g H g^{-1} = H$. It is `Subgroup.normalizer`, from Chapter 8. Each element of $C_G(H)$ normalizes $H$, so $C_G(S) \le N_G(S)$, by `Subgroup.centralizer_le_normalizer`. For one element the two agree: `Subgroup.normalizer_singleton` states $N_G(\{g\}) = C_G(\{g\})$.

Conjugation by an element of the normalizer is an automorphism of $H$. This gives a homomorphism
$$\varphi : N_G(H) \to \operatorname{Aut}(H), \qquad \varphi(x)(a) = x a x^{-1}.$$
It is `Subgroup.normalizerMonoidHom H`, with values in `MulAut ↥H`, and `Subgroup.normalizerMonoidHom_apply_apply_coe` is its formula. The kernel of $\varphi$ is the set of the $x$ with $x a x^{-1} = a$ for all $a \in H$, that is $C_G(H)$ seen inside $N_G(H)$. This is `Subgroup.normalizerMonoidHom_ker`. So $C_G(H)$ is normal in $N_G(H)$, which the instance `Subgroup.normal_subgroupOf_centralizer_normalizer` also records, and the first isomorphism theorem of Chapter 5 embeds $N_G(H)/C_G(H)$ into $\operatorname{Aut}(H)$. This "N/C theorem" is a standard tool: for example, if $H$ is cyclic of prime order $p$, then $N_G(H)/C_G(H)$ embeds in a group of order $p - 1$. The same conjugation is available as an action: the instance `Subgroup.instMulDistribMulActionSubtypeMemNormalizerCoe` lets $N_G(H)$ act on $H$, with the formula `Subgroup.smul_coe`.

#### Submonoids of inverses

The module `Mathlib.GroupTheory.Submonoid.Inverses` treats a question that only arises in a monoid. Let $S$ be a submonoid of $M$. The submonoid of left inverses is
$$S^{\mathrm{left}} = \{ x \in M : x y = 1 \text{ for some } y \in S \}.$$
It is `Submonoid.leftInv S`. It is a submonoid: $1 \cdot 1 = 1$, and if $x y = 1$ and $x' y' = 1$ with $y, y' \in S$, then $(x x')(y' y) = x (x' y') y = x y = 1$ with $y' y \in S$. Applying the construction twice gives a submonoid of $S$, by `Submonoid.leftInv_leftInv_le`. When $S$ consists of units, `Submonoid.leftInv_leftInv_eq` gives equality: each $s \in S$ has the left inverse $s^{-1}$, and $s$ is a left inverse of $s^{-1}$.

In a commutative monoid, inverses are unique, so each $x \in S^{\mathrm{left}}$ determines its partner in $S$. The map `Submonoid.fromLeftInv S` sends $x$ to that partner, and `Submonoid.fromCommLeftInv S` is the same map as a monoid homomorphism. Its basic equations are `Submonoid.mul_fromLeftInv` and `Submonoid.fromLeftInv_mul`. When $S \le$ `IsUnit.submonoid M`, the map is a bijection, and `Submonoid.leftInvEquiv S hS` is the resulting isomorphism $S^{\mathrm{left}} \cong S$. In a group, $S^{\mathrm{left}}$ is the pointwise inverse $S^{-1}$, by `Submonoid.leftInv_eq_inv`. The submonoid `IsUnit.submonoid M` of the units of $M$ is itself a group, by the instance `Submonoid.instGroupSubtypeMemSubmonoid`.

#### Common errors

1. `Subgroup.mem_centralizer_iff` gives `h * g = g * h` with the element $h$ of the set on the left. A proof that expects `g * h = h * g` must first rewrite with `eq_comm`. Use `Subgroup.mem_centralizer_singleton_iff` and `Commute` when only one element is involved.
2. The center of a semigroup is defined through `IsMulCentral`, not through the equation `g * z = z * g`. In a type with only a multiplication, the lemma `Subsemigroup.mem_center_iff` does not apply. Add the `Semigroup` assumption or use `Set.mem_center_iff`.
3. `Subgroup.centralizer` takes a set, not a subgroup. For a subgroup $H$, write `Subgroup.centralizer (H : Set G)`, with the coercion, as in the statement of `Subgroup.le_centralizer_iff`.

### Exercises

1. (A) Compute the center of $S_3$ and of the dihedral group $D_4$ of order $8$.
2. (A) Show that $C_G(\{g\}) = C_G(\{g^{-1}\})$ and that $C_G(\{g\}) = G$ if and only if $g \in Z(G)$.
3. (A) Show that $Z(G \times H) = Z(G) \times Z(H)$, and deduce that $Z(\mathbb{Z}/2 \times S_3)$ has order $2$.
4. (B) Show that if $G / Z(G)$ is cyclic, then $G$ is commutative. Hint: write each element as $a^k z$ with $z$ central.
5. (B) Let $H$ be a cyclic subgroup of order $5$ of a group $G$. Show that $N_G(H)/C_G(H)$ is cyclic of order dividing $4$.
6. (C) Let $M$ be the monoid of maps $\mathbb{N} \to \mathbb{N}$ under composition, and let $S$ be the submonoid generated by the shift $n \mapsto n + 1$. Describe `Submonoid.leftInv S`, and show that `Submonoid.leftInv_leftInv_eq` fails for this $S$.

### Reference

<?reference?>
