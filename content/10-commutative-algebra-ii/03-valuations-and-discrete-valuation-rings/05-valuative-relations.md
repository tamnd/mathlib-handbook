---
title: Valuative relations
kind: api
modules:
  - Mathlib.RingTheory.Valuation.ValuativeRel.Basic
  - Mathlib.RingTheory.Valuation.ValuativeRel.Trivial
explains:
  E2: [ValuativeRel, ValuativeRel.ValueGroupWithZero, ValuativeRel.valuation, Valuation.Compatible, ValuativeRel.ofValuation, ValuativeRel.isEquiv, ValuativeRel.IsDiscrete, ValuativeRel.uniformizer, ValuativeExtension, ValuativeRel.trivialRel]
  E1: auto
families: []
requires: [V10.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Valuative relations

### Overview

A valuation $v : R \to \Gamma$ carries more data than its use needs. Two valuations that are equivalent in the sense of Section 1 give the same ring of integers, the same topology and the same completion. In practice only the relation $v(x) \le v(y)$ matters. Mathlib makes this relation the primary object. A valuative relation on a ring $R$ is a relation $x \le_v y$ with the properties of $v(x) \le v(y)$. Each valuation gives one, equivalent valuations give the same one, and each valuative relation comes from a canonical valuation with values in a group built from the relation.

The class lets a type carry "a valuation up to equivalence" as an instance. The topological and uniform structures of Volume 14 use it, so that a valued field does not depend on the choice of a value group. This section describes the class, its value group, the compatibility of a valuation with a relation, and the classes for nontrivial, discrete and rank one relations.

### The library around it

#### The class

The class `ValuativeRel R` in `Mathlib.RingTheory.Valuation.ValuativeRel.Basic` has one field of data, the relation `ValuativeRel.vle`, written `x ≤ᵥ y`. Its axioms are the following.

| Lean name | Statement |
|---|---|
| `ValuativeRel.vle_total` | $x \le_v y$ or $y \le_v x$ |
| `ValuativeRel.vle_trans` | the relation is transitive |
| `ValuativeRel.vle_add` | $x \le_v z$ and $y \le_v z$ give $x + y \le_v z$ |
| `ValuativeRel.mul_vle_mul_left` | $x \le_v y$ gives $xz \le_v yz$ |
| `ValuativeRel.vle_mul_cancel` | if $z \not\le_v 0$, then $xz \le_v yz$ gives $x \le_v y$ |
| `ValuativeRel.not_vle_one_zero` | $1 \not\le_v 0$ |

The derived relations are `ValuativeRel.vlt`, written `x <ᵥ y`, the negation of $y \le_v x$, and `ValuativeRel.veq`, written `x =ᵥ y`. The module proves the usual order lemmas for them, such as `ValuativeRel.vle_add_cases` ($x + y \le_v x$ or $x + y \le_v y$), `ValuativeRel.zero_vle`, `ValuativeRel.mul_vlt_mul` and `ValuativeRel.pow_vle_pow`. On a field, `ValuativeRel.zero_vlt_iff` says that $0 <_v a$ if and only if $a \ne 0$. Two valuative relations are equal when their relations are equal, `ValuativeRel.ext_iff`.

The support `ValuativeRel.supp R` is the ideal of the $x$ with $x \le_v 0$. It is prime, by the instance `ValuativeRel.instIsPrimeSupp`. The submonoid `ValuativeRel.posSubmonoid R` is the set of the $x$ with $x \not\le_v 0$.

#### The value group

The type `ValuativeRel.ValueGroupWithZero R` is a quotient of $R \times$ `posSubmonoid R`. The class of a pair $(x, s)$ is `ValuativeRel.ValueGroupWithZero.mk x s`, and it stands for "$v(x)/v(s)$". Two pairs have the same class when $xt =_v ys$. The order is `ValuativeRel.ValueGroupWithZero.mk_le_mk`: the class of $(x, t)$ is at most the class of $(y, s)$ if and only if $xs \le_v yt$. The type is a linearly ordered commutative group with zero, by the instance `ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero`. The functions `ValuativeRel.ValueGroupWithZero.lift` and `ValuativeRel.ValueGroupWithZero.lift₂` define maps out of the quotient, and `ValuativeRel.ValueGroupWithZero.ind` is the induction principle.

The canonical valuation `ValuativeRel.valuation R` sends $x$ to the class of $(x, 1)$. On a division ring it is surjective, `ValuativeRel.valuation_surjective`, and `ValuativeRel.ValueGroupWithZero.mk_eq_valuation` says that the class of $(x, y)$ is $v(x/y)$. On a general ring each value is a quotient of two values, `ValuativeRel.exists_valuation_div_valuation_eq`. Its support is the support of the relation, `ValuativeRel.supp_eq_valuation_supp`.

#### Compatible valuations

A valuation $v : R \to \Gamma$ is compatible with the relation when $x \le_v y$ is the same as $v(x) \le v(y)$. This is the class `Valuation.Compatible v`, and `Valuation.Compatible.vle_iff_le` is its field. The lemmas `Valuation.vle_iff_le`, `Valuation.vlt_iff_lt` and `Valuation.veq_iff_eq` translate each relation, and `Valuation.one_vle_iff` and `Valuation.vle_one_iff` are the cases with $1$.

**Theorem.** Two valuations compatible with the same relation are equivalent. A valuation is compatible with the relation if and only if it is equivalent to the canonical valuation. These are `ValuativeRel.isEquiv` and `Valuation.compatible_iff_isEquiv`.

*Proof.* If $v_1$ and $v_2$ are compatible, then $v_1(x) \le v_1(y)$ if and only if $x \le_v y$ if and only if $v_2(x) \le v_2(y)$. This is the definition of equivalence. The canonical valuation is compatible by the instance `ValuativeRel.instCompatibleValueGroupWithZeroValuation`, because the order on the classes of $(x, 1)$ and $(y, 1)$ is $x \le_v y$. $\square$

Conversely, a valuation $v$ defines the relation `ValuativeRel.ofValuation v`, and $v$ is compatible with it by the instance `Valuation.Compatible.ofValuation`. The canonical valuation of this relation is equivalent to $v$, `ValuativeRel.isEquiv_ofValuation`. A valuation equivalent to a compatible one is compatible, `Valuation.IsEquiv.compatible`.

For a compatible $v$ with values in a group, `ValuativeRel.ValueGroupWithZero.embed v` is the strictly monotone map from the value group of the relation to the value group of $v$. The isomorphism `ValuativeRel.ValueGroupWithZero.orderMonoidIso v` identifies the two as ordered monoids with zero. So the value group of the relation is the value group of $v$ up to unique isomorphism.

#### Nontrivial, discrete and rank one relations

The properties of a valuation that are invariant under equivalence become classes on the relation.

1. `ValuativeRel.IsNontrivial R` says that some value is neither $0$ nor $1$. By `ValuativeRel.isNontrivial_iff_isNontrivial` it is the same as `Valuation.IsNontrivial v` for each compatible $v$, and `ValuativeRel.isNontrivial_iff_nontrivial_units` says that the units of the value group are not trivial. The lemma `ValuativeRel.IsNontrivial.exists_lt_one` gives a value $\gamma$ with $0 < \gamma < 1$.
2. `ValuativeRel.IsDiscrete R` says that there is a largest value below $1$, `ValuativeRel.IsDiscrete.has_maximal_element`. This largest value is `ValuativeRel.uniformizer R`, with `ValuativeRel.uniformizer_lt_one` and `ValuativeRel.le_uniformizer_iff`: a value is at most the uniformizer if and only if it is less than $1$. Here the uniformizer is a value, not an element of $R$.
3. `ValuativeRel.IsRankLeOne R` says that a structure `ValuativeRel.RankLeOneStruct R` exists, a strictly monotone map `ValuativeRel.RankLeOneStruct.emb` of the value group to $\mathbb{R}_{\ge 0}$. The value group is then archimedean, by the instance `ValuativeRel.instMulArchimedeanValueGroupWithZeroOfIsRankLeOne`.

Section 4 relates these classes to the classes `Valuation.IsRankOneDiscrete` and `Valuation.RankOne` of a single valuation.

#### Extensions and ordered rings

Let $B$ be an $A$-algebra, with a valuative relation on each ring. The class `ValuativeExtension A B` says that the map $A \to B$ preserves and reflects the relation, `ValuativeExtension.vle_iff_vle`, with the companions `ValuativeExtension.vlt_iff_vlt` and `ValuativeExtension.veq_iff_veq`. It gives the strictly monotone map `ValuativeExtension.mapValueGroupWithZero A B` of value groups, with `ValuativeExtension.mapValueGroupWithZero_valuation`. The class `ValuativePreorder R` says that the relation agrees with a given preorder on $R$, `ValuativePreorder.vle_iff_le`. The type synonym `ValuativeRel.WithPreorder R` puts the relation on $R$ as its preorder.

#### The trivial relation

The module `Mathlib.RingTheory.Valuation.ValuativeRel.Trivial` treats the relation of the trivial valuation on a domain, `ValuativeRel.trivialRel`. Here $x \le_v y$ holds if and only if $x = 0$ or $y \ne 0$. It is the relation of the valuation $1$, `ValuativeRel.trivialRel_eq_ofValuation_one`. When the trivial valuation is compatible, the value group has one unit, `ValuativeRel.subsingleton_units_valueGroupWithZero_of_trivialRel`, the relation is not nontrivial, `ValuativeRel.not_isNontrivial_of_trivialRel`, and it is discrete with uniformizer $0$, `ValuativeRel.isDiscrete_trivialRel`.

#### Common errors

1. `ValuativeRel R` is a class with data. A ring can have only one instance at a time. To study two valuations on one field, use `Valuation` terms, or the type synonym `WithVal` of Volume 14.
2. The relation `x <ᵥ y` is not $x \le_v y$ and $x \ne y$. It is the negation of $y \le_v x$, so $1 <_v 1 + \pi$ can fail even though $1 \ne 1 + \pi$.
3. `ValuativeRel.uniformizer R` is an element of the value group, not of $R$. A uniformizing element of $R$ needs a separate existence argument.

### Exercises

1. (A) Let $v$ be a valuation on $R$. Show from the axioms of a valuation that `ValuativeRel.ofValuation v` satisfies `ValuativeRel.vle_add`.
2. (A) Show from the axioms that $0 \le_v x$ for all $x$ and that $x \le_v 0$ gives $xy \le_v 0$.
3. (B) Show that the $p$-adic and the $q$-adic valuations of $\mathbb{Q}$ give different valuative relations for primes $p \ne q$.
4. (B) Let $K$ be a field with a valuative relation. Show that the set of $x$ with $x \le_v 1$ is a valuation subring of $K$, and that the relation is determined by this subring.
5. (B) Show that the trivial relation on a domain is discrete and that its uniformizer is $0$.
6. (C) Let $K$ be a field with a valuative relation, and let $v : K \to \Gamma$ be a compatible valuation. Show that the class of $(x, s)$ goes to $v(x)/v(s)$ under a well defined map, and that this map is strictly monotone. Compare with `ValuativeRel.ValueGroupWithZero.embed_strictMono`.

### Reference

<?reference?>
