---
title: Special localizations and the Ore localization
kind: api
modules:
  - Mathlib.GroupTheory.MonoidLocalization.Away
  - Mathlib.GroupTheory.MonoidLocalization.Divisibility
  - Mathlib.GroupTheory.MonoidLocalization.MonoidWithZero
  - Mathlib.GroupTheory.MonoidLocalization.UniqueFactorization
  - Mathlib.GroupTheory.MonoidLocalization.Order
  - Mathlib.GroupTheory.MonoidLocalization.GrothendieckGroup
  - Mathlib.GroupTheory.MonoidLocalization.DivPairs
  - Mathlib.GroupTheory.OreLocalization.OreSet
  - Mathlib.GroupTheory.OreLocalization.Basic
  - Mathlib.GroupTheory.OreLocalization.Cardinality
explains:
  E2: [Submonoid.LocalizationMap.map_isUnit_iff, Submonoid.LocalizationMap.subsingleton_iff, Submonoid.LocalizationMap.map_eq_zero_iff, Localization.mk_le_mk, Algebra.GrothendieckGroup.lift, Algebra.GrothendieckGroup.of_injective, OreLocalization.OreSet, OreLocalization.oreDiv_mul_oreDiv, OreLocalization.universalMulHom, OreLocalization.numeratorHom_surjective_of_finite]
  E1: auto
families: []
requires: [V04, V05.C03, V05.C05, V05.C06, V05.C09]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Special localizations and the Ore localization

### Overview

The section before this one builds the localization $S^{-1}M$ of a commutative monoid and its universal property. This section describes the modules that apply it to special submonoids and special monoids. The localization away from one element $x$ inverts the powers of $x$. The localization at the whole monoid is the Grothendieck group, the universal commutative group of $M$. Further modules treat units and divisibility in a localization, localizations of monoids with zero, unique factorization, and the order on the localization of an ordered cancellative monoid.

The second half of the section is about a noncommutative monoid $R$. A submonoid $S$ of $R$ in general has no monoid of fractions with a simple description. The Ore condition on $S$ makes the fractions $s^{-1} r$ well behaved, and then the Ore localization $S^{-1}R$ exists. The library defines the type `Localization S` of a commutative monoid as this Ore localization, so the two halves of the section share their types.

### The library around it

#### Localization away from an element

For $x \in M$, `Localization.Away x` is the localization at the submonoid `Submonoid.powers x`. A localization map at this submonoid has the type `Submonoid.LocalizationMap.AwayMap x N`. The universal property needs only one unit: if $g(x)$ is a unit of $P$, then `Submonoid.LocalizationMap.AwayMap.lift x F hg` is the homomorphism $N \to P$ with `Submonoid.LocalizationMap.AwayMap.lift_eq`. The inverse of the image of $x$ is `Submonoid.LocalizationMap.AwayMap.invSelf`, the fraction $1/x$, and for the concrete type it is `Localization.Away.invSelf`. The map `Submonoid.LocalizationMap.awayToAwayRight` goes from the localization away from $x$ to the localization away from $x y$. It exists because $x$ divides $x y$, so $x$ becomes a unit when $x y$ does. The isomorphism `Localization.Away.mulEquivOfQuotient` identifies the concrete type with the target of each localization map away from $x$.

#### Units and divisibility

**Proposition (`Submonoid.LocalizationMap.map_isUnit_iff`).** For a localization map $f$ at $S$, the image $f(m)$ is a unit if and only if $m$ divides an element of $S$.

*Proof.* If $m t = s$ with $s \in S$, then $f(m) f(t) = f(s)$ is a unit, so $f(m)$ is a unit. Conversely, let $f(m)\,z = 1$, and write $z f(y) = f(x)$ with $y \in S$. Then $f(m x) = f(y)$, so $c m x = c y$ for some $c \in S$. So $m$ divides $c y \in S$. $\square$

The companion `Submonoid.LocalizationMap.map_dvd_map` says that $f(m_1)$ divides $f(m_2)$ if and only if $m_1$ divides $s m_2$ for some $s \in S$.

#### Monoids with zero

Let $M$ be a commutative monoid with zero. Then `Localization S` is a commutative monoid with zero (`Localization.instCommMonoidWithZero`), with `Localization.mk_zero`, and each localization map sends $0$ to $0$ (`Submonoid.LocalizationMap.map_zero`). The instance `Submonoid.instMonoidWithZeroHomClassLocalizationMap` makes a localization map a homomorphism of monoids with zero.

**Proposition (`Submonoid.LocalizationMap.map_eq_zero_iff`).** $f(m) = 0$ if and only if $s m = 0$ for some $s \in S$.

*Proof.* Apply condition 3 of a localization map to $f(m) = f(0)$: it gives $c m = c \cdot 0 = 0$ for some $c \in S$. The converse holds because $f(s)$ is a unit and $f(s) f(m) = 0$. $\square$

**Proposition (`Submonoid.LocalizationMap.subsingleton_iff`).** The target of a localization map at $S$ is the trivial monoid if and only if $0 \in S$.

*Proof.* If $0 \in S$, then $f(0)$ is a unit and is $0$, so $1 = 0$ in $N$. Conversely, if $N$ is trivial, then $f(1) = 0$, and the previous proposition gives $s \in S$ with $s = s \cdot 1 = 0$. $\square$

The lemmas `Submonoid.LocalizationMap.subsingleton` and `Submonoid.LocalizationMap.nontrivial` are the two directions. A localization map sends non-zero-divisors to non-zero-divisors (`Submonoid.LocalizationMap.map_nonZeroDivisors_le`), and the target has no zero divisors when $M$ has none (`Submonoid.LocalizationMap.noZeroDivisors`). The lift `Submonoid.LocalizationMap.lift₀` is the universal property for homomorphisms of monoids with zero.

Unique factorization passes to localizations. A prime $m$ with $f(m) \neq 0$ and $f(m)$ not a unit has a prime image (`Submonoid.LocalizationMap.map_prime`). So the target of a localization map of a unique factorization monoid is again one (`Submonoid.LocalizationMap.uniqueFactorizationMonoid`). The instance `instUniqueFactorizationMonoidLocalization` and the lemma `UniqueFactorizationMonoid.of_isLocalization` are the forms for commutative semirings.

#### Order

Let $\alpha$ be a commutative monoid with a partial order that makes it an ordered cancellative monoid (`IsOrderedCancelMonoid`). Then `Localization s` has a natural order.

**Proposition (`Localization.mk_le_mk`).** $\mathrm{mk}(a_1, a_2) \le \mathrm{mk}(b_1, b_2)$ if and only if $b_2 a_1 \le a_2 b_1$.

The relation does not depend on the representatives. If $(a_1, a_2) \sim (a_1', a_2')$, then $a_2' a_1 = a_2 a_1'$ by cancellation, and the order is compatible with multiplication in both directions in an ordered cancellative monoid. The instances `Localization.partialOrder` and `Localization.isOrderedCancelMonoid` give the structure, and `Localization.instLinearOrderOfIsOrderedCancelMonoid` gives a linear order from a linear order. For fixed $b \in s$, the map $a \mapsto \mathrm{mk}(a, b)$ is an order embedding (`Localization.mkOrderEmbedding`).

#### The Grothendieck group

The Grothendieck group of a commutative monoid $M$ is `Algebra.GrothendieckGroup M`, the localization of $M$ at the top submonoid. Each element of $M$ is invertible there, so it is a commutative group (`Algebra.GrothendieckGroup.instCommGroup`), with the inverse `Algebra.GrothendieckGroup.inv_mk`: $(m/s)^{-1} = s/m$. The map from $M$ is `Algebra.GrothendieckGroup.of`. The additive version `Algebra.GrothendieckAddGroup` gives $\mathbb{Z}$ from $\mathbb{N}$.

**Proposition (`Algebra.GrothendieckGroup.lift`).** For each commutative group $G$, composition with `Algebra.GrothendieckGroup.of` is a bijection from the homomorphisms of the Grothendieck group to $G$ to the monoid homomorphisms $M \to G$.

*Proof.* Each element of $G$ is a unit, so each $g : M \to G$ satisfies the hypothesis of the universal property of the localization at the top submonoid. The lift is unique by the epimorphism property of localization maps. $\square$

In Lean, the bijection is an `Equiv` from `M →* G` to `Algebra.GrothendieckGroup M →* G`, with `Algebra.GrothendieckGroup.lift_symm_apply`. The map `Algebra.GrothendieckGroup.of` is injective if and only if $M$ is cancellative, and `Algebra.GrothendieckGroup.of_injective` states the direction from `IsCancelMul`. It is the case $S = M$ of `Submonoid.LocalizationMap.injective_iff`.

The module `Mathlib.GroupTheory.MonoidLocalization.DivPairs` describes the submonoids of a Grothendieck group $G$ by pairs in $M$. For a localization map $f$ at the top submonoid and a submonoid $s$ of $G$, `Submonoid.divPairs f s` is the submonoid of pairs $(a, b) \in M \times M$ with $f(a)/f(b) \in s$ (`Submonoid.mem_divPairs`). The lemma `Submonoid.divPairs_comap` says that the result does not depend on the choice of the model of $G$.

#### Ore sets

Let $R$ be a monoid that need not be commutative, and let $S$ be a submonoid. The class `OreLocalization.OreSet S` holds two pieces of data and two properties:

1. Left Ore condition: for $r \in R$ and $s \in S$ there are $r' \in R$ and $s' \in S$ with $s' r = r' s$. The choices are `OreLocalization.oreNum r s` and `OreLocalization.oreDenom r s`, and the equation is `OreLocalization.ore_eq`.
2. Reversibility: if $r_1 s = r_2 s$ with $s \in S$, then $s' r_1 = s' r_2$ for some $s' \in S$ (`OreLocalization.ore_right_cancel`).

The Ore condition says that a right fraction $r s^{-1}$ can be rewritten as a left fraction $s'^{-1} r'$. In a commutative monoid each submonoid is an Ore set, by the instance `OreLocalization.oreSetComm` with $r' = r$ and $s' = s$ (`OreLocalization.oreSetComm_oreNum`). The trivial submonoid is an Ore set by `OreLocalization.oreSetBot`.

#### The Ore localization

For an Ore set $S$ and a type $X$ with an action of $R$, the type `OreLocalization S X` holds the fractions `x /ₒ s` with $x \in X$ and $s \in S$, read as $s^{-1} x$. The relation is `OreLocalization.oreEqv`, and `OreLocalization.oreDiv_eq_iff` says that $x_1 /ₒ s_1 = x_2 /ₒ s_2$ if and only if $u x_2 = v x_1$ and $u s_2 = v s_1$ for some $u \in S$ and $v \in R$. The lemma `OreLocalization.expand` multiplies the numerator and the denominator by the same element. Proofs about elements start with `OreLocalization.ind`, and functions out of the type come from `OreLocalization.liftExpand` and `OreLocalization.lift₂Expand`.

For $X = R$ the Ore localization is a monoid (`OreLocalization.instMonoid`), and it is commutative when $R$ is (`OreLocalization.instCommMonoid`). The product needs the Ore condition to move a numerator past a denominator.

**Proposition (`OreLocalization.oreDiv_mul_oreDiv`).** $(r_1 /ₒ s_1)(r_2 /ₒ s_2) = (r' r_2) /ₒ (s' s_1)$, where $r' = \mathrm{oreNum}(r_1, s_2)$ and $s' = \mathrm{oreDenom}(r_1, s_2)$.

*Proof sketch.* Read $r /ₒ s$ as $s^{-1} r$. The Ore equation $s' r_1 = r' s_2$ gives $r_1 s_2^{-1} = s'^{-1} r'$. So $s_1^{-1} r_1 s_2^{-1} r_2 = s_1^{-1} s'^{-1} r' r_2 = (s' s_1)^{-1} r' r_2$. The library takes this formula as the definition and proves that it respects the relation. $\square$

The lemma `OreLocalization.oreDiv_mul_char` gives the same product with any $r', s'$ that satisfy the Ore equation. The simpler rules are `OreLocalization.mul_div_one`, `OreLocalization.one_div_mul`, `OreLocalization.mul_cancel`, `OreLocalization.div_eq_one` and `OreLocalization.mul_inv`. The power rule `OreLocalization.oreDiv_pow` needs that $r$ and $s$ commute. In the commutative case the product is the usual one, `OreLocalization.oreDiv_mul_oreDiv_comm`.

The map $r \mapsto r /ₒ 1$ is `OreLocalization.numeratorHom`, a monoid homomorphism. It sends each element of $S$ to a unit (`OreLocalization.numerator_isUnit`), and `OreLocalization.numeratorUnit` gives this unit with inverse $1 /ₒ s$. The universal property is `OreLocalization.universalMulHom`: a homomorphism $f : R \to T$ with a compatible map from $S$ to the units of $T$ factors through the Ore localization, with `OreLocalization.universalMulHom_commutes` and the uniqueness `OreLocalization.universalMulHom_unique`. For an action of $R$ on $X$, the Ore localization of $R$ acts on that of $X$ (`OreLocalization.instMulActionOreLocalization`), with `OreLocalization.oreDiv_smul_oreDiv` and `OreLocalization.smul_cancel`.

#### Cardinality

**Proposition (`OreLocalization.numeratorHom_surjective_of_finite`).** If $S$ is finite, then each element of $S^{-1}R$ has the form $r /ₒ 1$.

*Proof.* Let $s \in S$. The powers of $s$ in the finite set $S$ repeat, so $s^m = s^{m+k}$ for some $m$ and some $k \ge 1$. The image of $s$ in $S^{-1}R$ is a unit, so its $k$-th power is $1$, and its inverse is the image of $s^{k-1}$. So $r /ₒ s = s^{k-1} r /ₒ 1$. $\square$

The general bounds are `OreLocalization.cardinalMk_le_max`, which bounds the cardinality of $S^{-1}X$ by the maximum of the cardinalities of $S$ and $X$, and `OreLocalization.cardinalMk_le`, which bounds $S^{-1}R$ by $R$. For a commuting $S$, `OreLocalization.cardinalMk_le_lift_cardinalMk_of_commute` bounds $S^{-1}X$ by $X$.

#### Common errors

1. The fraction `r /ₒ s` of the library is the left fraction $s^{-1} r$, not $r s^{-1}$. The Ore condition of `OreLocalization.OreSet` is the left condition $s' r = r' s$. A ring theory text with right fractions uses the mirror condition.
2. `Algebra.GrothendieckGroup.of` is not injective for a monoid that is not cancellative. In the monoid $\{0, 1\}$ under multiplication the Grothendieck group is trivial.
3. The order on `Localization s` needs `IsOrderedCancelMonoid`. The instances do not apply to an ordered monoid that is not cancellative, and they do not apply to a monoid with zero such as $(\mathbb{N}, \cdot)$.

### Exercises

1. (A) Show that the Grothendieck group of $(\mathbb{N}, +)$ is isomorphic to $(\mathbb{Z}, +)$ with `Algebra.GrothendieckAddGroup` and the universal property.
2. (A) In the localization of $(\mathbb{Z}, \cdot)$ away from $6$, find the units, and show that the image of $4$ is a unit with `Submonoid.LocalizationMap.map_isUnit_iff`.
3. (A) Let $M = \mathbb{Z}/6$ under multiplication and $S = \{1, 3\}$. Compute the elements $m$ with $f(m) = 0$ in the localization at $S$, using `Submonoid.LocalizationMap.map_eq_zero_iff`.
4. (B) Show that the Grothendieck group of a commutative monoid with an absorbing element $0$ is trivial.
5. (B) Let $R$ be a group and $S$ a submonoid. Show that $S$ is an Ore set, and that `OreLocalization.numeratorHom` is an isomorphism onto $S^{-1}R$.
6. (C) Let $R$ be the free monoid on two letters $a, b$ and let $S$ be the submonoid generated by $a$. Show that $S$ does not satisfy the left Ore condition.

### Reference

<?reference?>
