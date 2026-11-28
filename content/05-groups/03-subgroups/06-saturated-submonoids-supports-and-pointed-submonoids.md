---
title: Saturated submonoids, supports and pointed submonoids
kind: api
modules:
  - Mathlib.Algebra.Group.Submonoid.Saturation
  - Mathlib.Algebra.Group.Submonoid.Support
explains:
  E2: [Submonoid.MulSaturated.mul_mem_iff, Submonoid.mem_saturation_iff_exists_dvd, Submonoid.saturation_le_iff_le, SaturatedSubmonoid.mem_bot_iff, Subgroup.gc_toSubmonoid_mulSupport, isMulPointed_iff_mulSupport_eq_bot, Submonoid.IsMulSpanning.maximal_isMulPointed]
  E1: auto
families: []
requires: [V04, V05.C01, V05.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Saturated submonoids, supports and pointed submonoids

### Overview

A submonoid is closed under the product. Two modules of this section study submonoids with an extra closure property in the other direction. A submonoid $S$ of a monoid $M$ is saturated when a product $x y$ is in $S$ only if both factors $x$ and $y$ are in $S$. In a commutative monoid, the saturated submonoids are exactly the submonoids that are closed under divisors. They are the natural denominator sets of a localization: the elements that become units in a localization form a saturated submonoid. The complement of a prime ideal in a commutative ring is a standard example.

The second module studies a submonoid $M$ of a group $G$ through its support, the set of elements $x$ with $x \in M$ and $x^{-1} \in M$. The support is the largest subgroup inside $M$. A submonoid with a trivial support is pointed, and a submonoid that holds $a$ or $a^{-1}$ for each $a$ is spanning. These words come from the theory of ordered groups and convex cones: the set of elements $x \ge 1$ of an ordered group is a pointed submonoid, and it is spanning exactly when the order is total. Both modules use the lattice of submonoids from Chapter 3 and the Galois connections of Volume 4.

### The library around it

#### Saturated submonoids

The predicate `Submonoid.MulSaturated` on a submonoid $s$ of a monoid $M$ (with only `MulOneClass M`) states that $x y \in s$ implies $x \in s$ and $y \in s$, for all $x, y$. The additive form is `AddSubmonoid.AddSaturated`, made by the attribute to_additive as for all names of this section. Saturation is stable under meets: `Submonoid.MulSaturated.inf`, `Submonoid.MulSaturated.sInf` and `Submonoid.MulSaturated.iInf`, and `Submonoid.MulSaturated.top` states that $M$ itself is saturated. In a commutative monoid, one half of the condition is enough, by `Submonoid.MulSaturated.of_left` and `Submonoid.MulSaturated.of_right`.

**Theorem.** If $s$ is saturated, then $x y \in s$ if and only if $x \in s$ and $y \in s$.

*Proof.* The forward direction is the definition of saturation. The backward direction is the closure of $s$ under the product. $\square$

This is `Submonoid.MulSaturated.mul_mem_iff`, the form that a proof uses most often, because simp can rewrite with it once the saturation hypothesis is known.

The bundled form is the structure `SaturatedSubmonoid M`, with the field `SaturatedSubmonoid.toSubmonoid` and the proof `SaturatedSubmonoid.mulSaturated`. It has a `SetLike` instance and a `SubmonoidClass` instance, so an element of a saturated submonoid is a term of a subtype, as for a submonoid. Extensionality is `SaturatedSubmonoid.ext` (equal submonoids) and `SaturatedSubmonoid.ext'` (equal members), and `SaturatedSubmonoid.toSubmonoid_injective` states that the forgetful map is injective.

#### The saturation of a submonoid

The meet of saturated submonoids is saturated, so each submonoid $s$ has a smallest saturated submonoid that contains it. Mathlib calls it `Submonoid.saturation s`, of type `SaturatedSubmonoid M`. The inclusion is `Submonoid.le_toSubmonoid_saturation`, and the universal property is the following adjunction.

**Theorem.** For a submonoid $a$ and a saturated submonoid $b$, the saturation of $a$ is in $b$ if and only if $a \le b$.

*Proof.* If the saturation of $a$ is in $b$, then $a$ is in $b$, because $a$ is in its saturation. Conversely, if $a \le b$, then $b$ is a saturated submonoid that contains $a$, and the saturation is the smallest one. $\square$

The Lean name is `Submonoid.saturation_le_iff_le`, and `Submonoid.saturation_le_of_le` is the backward direction. In the language of order theory, the saturation and the forgetful map form a Galois connection, `Submonoid.gc_saturation`. The saturation of a saturated submonoid is itself, by `Submonoid.saturation_toSubmonoid`, so the connection is a Galois insertion, `Submonoid.giSaturation`. Volume 4 shows that a Galois insertion lifts a complete lattice to the subtype. So `SaturatedSubmonoid.instCompleteLattice` comes from `Submonoid.giSaturation`. The meet is the meet of the submonoids, by `SaturatedSubmonoid.mem_sInf`. The join is the saturation of the join of the submonoids, by `SaturatedSubmonoid.sup_def`, `SaturatedSubmonoid.sSup_def` and `SaturatedSubmonoid.iSup_def`. A left adjoint keeps joins, which gives `Submonoid.saturation_sup`, `Submonoid.saturation_sSup`, `Submonoid.saturation_iSup` and `Submonoid.saturation_bot`; `Submonoid.saturation_top` is the top.

For a proof about all elements of the saturation, `Submonoid.saturation_induction` is the induction principle. It has three cases: the elements of $s$, the products of two elements, and the factors $x$ and $y$ of a product $x y$ that is already known.

#### The commutative case

In a commutative monoid the saturation has an explicit description.

**Theorem.** Let $M$ be commutative and $s$ a submonoid. An element $x$ is in the saturation of $s$ if and only if $x$ divides some $m \in s$.

*Proof.* Let $t$ be the set of divisors of elements of $s$. It contains $s$, because each $m$ divides itself. It is a submonoid: $1$ divides $1$, and if $x \mid m$ and $y \mid m'$ then $x y \mid m m'$. It is saturated: if $x y \mid m$ then $x \mid m$ and $y \mid m$. A saturated submonoid $b$ that contains $s$ contains $t$: if $m = x c$ with $m \in s \subseteq b$, then $x \in b$ by saturation. So $t$ is the smallest saturated submonoid that contains $s$. $\square$

This is `Submonoid.mem_saturation_iff_exists_dvd`. The forms `Submonoid.mem_saturation_iff` and `Submonoid.mem_saturation_iff'` state the same condition as $\exists y, x y \in s$ and as $\exists y, y x \in s$. The special case $s = \{1\}$ is the bottom element.

**Theorem.** In a commutative monoid, the smallest saturated submonoid is the group of units: $x \in \bot$ if and only if $x$ is a unit.

*Proof.* The bottom is the saturation of the trivial submonoid, by `SaturatedSubmonoid.bot_def`. By the theorem above, $x$ is in it if and only if $x \mid 1$, and this holds if and only if $x$ is a unit, by `isUnit_iff_dvd_one`. $\square$

The Lean name is `SaturatedSubmonoid.mem_bot_iff`, with `IsUnit` on the right. So in a commutative monoid every saturated submonoid holds all units.

#### The support of a submonoid of a group

The module `Mathlib.Algebra.Group.Submonoid.Support` works in a group $G$. For a submonoid $M$ of $G$, the support `Submonoid.mulSupport M` is the subgroup $M \cap M^{-1}$. The membership lemma `Submonoid.mem_mulSupport` states $x \in \mathrm{supp}(M)$ if and only if $x \in M$ and $x^{-1} \in M$. The carrier is `Submonoid.coe_mulSupport`, and `Submonoid.mulSupport_toSubmonoid` gives the submonoid $M \sqcap M^{-1}$. In the additive form, `AddSubmonoid.support M` is $M \cap (-M)$ with `AddSubmonoid.mem_support`. This is the lineality space of a cone: the largest additive subgroup inside it.

**Theorem.** For a subgroup $H$ and a submonoid $M$ of $G$, $H \le M$ as submonoids if and only if $H \le \mathrm{supp}(M)$.

*Proof.* If $H \le \mathrm{supp}(M)$, then $H \le M$ because the support is in $M$. Conversely, let $H \le M$ and $h \in H$. Then $h \in M$, and $h^{-1} \in H \le M$, so $h$ is in the support. $\square$

This is the Galois connection `Subgroup.gc_toSubmonoid_mulSupport` between the forgetful map from subgroups and the support. The support of a subgroup is the subgroup itself, by `Subgroup.mulSupport_eq` (additive form `AddSubgroup.support_eq`), so the connection is a Galois coinsertion, `Subgroup.gciToSubmonoidMulSupport`. As a right adjoint, the support keeps meets: `Submonoid.mulSupport_inf`, `Submonoid.mulSupport_sInf`, `Submonoid.mulSupport_iInf`, `Submonoid.mulSupport_top` and `Submonoid.mulSupport_bot`. It is monotone by `Submonoid.mulSupport_mono`.

The support commutes with preimages, `Submonoid.mulSupport_comap`. For images there is only an inclusion in general, `Submonoid.map_mulSupport_le`. Equality `Submonoid.mulSupport_map` needs the hypothesis that the kernel of $f$ is in the support of $M$.

#### Pointed and spanning submonoids

A submonoid $M$ of a group is pointed when $x \in M$ and $x^{-1} \in M$ imply $x = 1$. The Lean predicate is `Submonoid.IsMulPointed`, and `AddSubmonoid.IsPointed` is the additive form. By the definition of the support, $M$ is pointed exactly when its support is trivial. This is `isMulPointed_iff_mulSupport_eq_bot`, with the two directions `Submonoid.IsMulPointed.mulSupport_eq_bot` and `Submonoid.IsMulPointed.of_mulSupport_eq_bot`. Note that this name is in the root namespace, as is `isPointed_iff_support_eq_bot`.

A submonoid $M$ is spanning when each $a \in G$ satisfies $a \in M$ or $a^{-1} \in M$. The Lean predicate is `Submonoid.IsMulSpanning`, with the accessor `Submonoid.IsMulSpanning.mem_or_inv_mem`. A spanning submonoid generates $G$ as a group, which explains the name. A larger submonoid is also spanning, `Submonoid.IsMulSpanning.of_le`. Spanning passes to preimages, `Submonoid.IsMulSpanning.comap`, and to images under a surjective homomorphism, `Submonoid.IsMulSpanning.map`.

For an ordered group, the set of elements $x \ge 1$ is pointed by antisymmetry. It is spanning exactly when the order is total. Conversely, a pointed submonoid $P$ defines a partial order by $x \le y$ when $x^{-1} y \in P$, and this order is total when $P$ is spanning. The next result says that the positive cone of a total order cannot grow.

**Theorem.** A pointed and spanning submonoid $M$ is a maximal pointed submonoid.

*Proof.* Let $N \ge M$ be pointed, and let $x \in N$. If $x \in M$, the proof is done. If not, then $x^{-1} \in M \le N$ because $M$ is spanning. So $x$ and $x^{-1}$ are both in $N$, and $x = 1$ because $N$ is pointed. Then $x \in M$ also in this case. So $N \le M$. $\square$

The Lean name is `Submonoid.IsMulSpanning.maximal_isMulPointed`, with the conclusion `Maximal Submonoid.IsMulPointed M`. The predicate `Maximal` comes from Volume 4.

#### Common errors

1. A learner proves that a submonoid of a group is saturated and expects an interesting subset. In a group every saturated submonoid is the whole group, because $x \cdot x^{-1} = 1$ is in every submonoid. Saturation is useful in a monoid that is not a group, for example the multiplicative monoid of a ring.
2. A learner uses `Submonoid.mem_saturation_iff` in a monoid that is not commutative. The lemma needs `CommMonoid M`; in the general case only `Submonoid.saturation_induction` and the adjunction are available.
3. A learner looks for the criterion of pointedness in the namespace `Submonoid` and does not find it. The name `isMulPointed_iff_mulSupport_eq_bot` is in the root namespace, without a prefix.

### Exercises

1. (A) Prove that every saturated submonoid of a group $G$ is equal to $G$.
2. (A) Let $M$ be the multiplicative monoid of $\mathbb{Z}$ and $s$ the submonoid of powers of $6$. Describe the saturation of $s$ with `Submonoid.mem_saturation_iff_exists_dvd`.
3. (B) Let $R$ be a commutative ring and $P$ a prime ideal. Prove that the complement of $P$ is a saturated submonoid of the multiplicative monoid of $R$.
4. (B) Prove `Submonoid.mulSupport_comap` from the definitions: for a homomorphism $f : G \to H$ and a submonoid $M'$ of $H$, the support of the preimage is the preimage of the support.
5. (B) Let $P$ be a pointed submonoid of $G$. Prove that $x \le y \iff x^{-1} y \in P$ is a partial order on $G$, and that it is total if and only if $P$ is spanning.
6. (C) Give a pointed submonoid of $\mathbb{Z}^2$ that is maximal among pointed submonoids, and prove that it is spanning. Is every maximal pointed submonoid of a group spanning?

### Reference

<?reference?>
