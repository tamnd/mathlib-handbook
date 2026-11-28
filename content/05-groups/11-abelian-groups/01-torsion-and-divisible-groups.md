---
title: Torsion groups and divisible groups
kind: api
modules:
  - Mathlib.GroupTheory.Torsion
  - Mathlib.GroupTheory.Divisible
  - Mathlib.GroupTheory.DivisibleHull
explains:
  E2: [CommGroup.mem_torsion, IsMulTorsion.subgroup, IsMulTorsion.extension_closed, CommGroup.isMulTorsionFree_iff_torsion_eq_bot, DivisibleBy.surjective_smul, QuotientAddGroup.divisibleBy, DivisibleHull.mk_add_mk]
  E1: auto
families: []
requires: [V05.C04, V05.C05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Torsion groups and divisible groups

### Overview

An element of a group is a *torsion element* if it has finite order. A group is a *torsion group* if each element has finite order, and it is *torsion-free* if only $1$ has finite order. In a commutative group the torsion elements form a subgroup, the quotient by this subgroup is torsion-free, and the torsion subgroup splits into its primary components. The module `Mathlib.GroupTheory.Torsion` holds this theory. It uses the order of an element from Chapter 4 and the quotient groups of Chapter 5.

An additive group $A$ is *divisible* if each element $a$ has an $n$-th part, an element $b$ with $n b = a$, for each $n \ne 0$. The groups $\mathbb{Q}$, $\mathbb{R}$ and $\mathbb{Q}/\mathbb{Z}$ are divisible, and $\mathbb{Z}$ is not. The module `Mathlib.GroupTheory.Divisible` defines divisibility, and `Mathlib.GroupTheory.DivisibleHull` builds the smallest divisible group that contains a given torsion-free commutative monoid, by formal fractions $m / s$.

### The library around it

#### Torsion groups

The class of torsion monoids is `IsMulTorsion G`, with the additive form `IsAddTorsion G`. It says that `IsOfFinOrder g` holds for each $g$. Its negation is unfolded by `not_isMulTorsion_iff`. The closure properties of torsion groups are lemmas in the namespace `IsMulTorsion`.

| Lean name | Statement |
|---|---|
| `isMulTorsion_of_finite` | a finite group is a torsion group |
| `IsMulTorsion.subgroup` | a subgroup of a torsion group is a torsion group |
| `IsMulTorsion.of_surjective` | the image of a torsion group under a surjection is a torsion group |
| `IsMulTorsion.extension_closed` | if $N = \ker f$ and both $N$ and the target of $f$ are torsion, then $G$ is torsion |
| `IsMulTorsion.quotient_iff` | if $f$ is surjective with a torsion kernel, then the target is torsion if and only if $G$ is torsion |
| `ExponentExists.isMulTorsion` | a group with an exponent is a torsion group |
| `IsMulTorsion.exponentExists` | a torsion group with only finitely many orders of elements has an exponent |

The subgroup case is immediate: an element of $H$ has the same order in $H$ as in $G$, because the powers are computed in $G$. The extension case has a short proof. Let $g \in G$. The image $f(g)$ has finite order $n$, so $g^n \in \ker f = N$. Then $g^n$ has finite order $m$, so $g^{n m} = 1$ and $g$ has finite order. The class `Monoid.ExponentExists` comes from Chapter 4. The infinite group $\mathbb{Q}/\mathbb{Z}$ is a torsion group with no exponent, so the hypothesis of `IsMulTorsion.exponentExists` is needed.

#### The torsion subgroup

In a commutative group, the product of two elements of finite order has finite order: if $g^m = 1$ and $h^n = 1$, then $(g h)^{m n} = 1$. So the torsion elements form a subgroup, `CommGroup.torsion G`, and the commutative monoid version is the submonoid `CommMonoid.torsion G`. Membership is `CommGroup.mem_torsion`: $g$ is in the torsion subgroup if and only if `IsOfFinOrder g`. The additive forms are `AddCommGroup.torsion` and `AddCommMonoid.addTorsion`. The torsion subgroup of a non-commutative group need not be a subgroup, and the library defines it only for commutative groups.

The torsion subgroup is a functor. A homomorphism maps torsion elements to torsion elements, and this is `CommGroup.map_torsion_le`. The torsion subgroup of a product is the product of the torsion subgroups (`CommGroup.torsion_prod`), and an isomorphism maps the torsion subgroup onto the torsion subgroup (`MulEquiv.map_torsion`). The torsion subgroup is all of $G$ if and only if $G$ is a torsion group (`CommGroup.torsion_eq_top_iff`), and then `IsMulTorsion.torsionMulEquiv` is the isomorphism of the torsion submonoid with $G$.

A commutative group is torsion-free if and only if its torsion subgroup is trivial. This is `CommGroup.isMulTorsionFree_iff_torsion_eq_bot`, and the class `IsMulTorsionFree` is the library form of torsion-free. The quotient by the torsion subgroup is torsion-free. Proof: let $g^n \in T$ for an $n \ne 0$, where $T$ is the torsion subgroup. Then $g^{n m} = 1$ for some $m \ne 0$, so $g \in T$. The library states the conclusion as the instance `QuotientGroup.instHasUniqueRoots`: in $G / T$, the equation $x^n = y^n$ with $n \ne 0$ gives $x = y$. For modules, `instModuleQuotientAddSubgroupTorsion` puts the module structure on the quotient of a module by its torsion subgroup.

For a finitely generated commutative group $G$, the *free rank* is `CommGroup.freeRank G`. By `CommGroup.freeRank_def`, it is the rank of $G / T$ in the sense of `Group.rank`. The free rank is $0$ if and only if $G$ is a torsion group (`CommGroup.freeRank_eq_zero_iff`). The structure theorem of the next section shows that $G / T$ is free, so the free rank is the number of factors $\mathbb{Z}$ of $G$.

#### Primary components

Let $p$ be a prime. The *$p$-primary component* of a commutative group $G$ is the subgroup of the elements whose order is a power of $p$. It is `CommGroup.primaryComponent G p`, and `CommGroup.mem_primaryComponent` says that $g$ is in it if and only if $g^{p^k} = 1$ for some $k$. Each primary component is a $p$-group (`CommGroup.primaryComponent.isPGroup`). For two different primes, the components are disjoint (`CommMonoid.primaryComponent.disjoint`), because an element whose order is both a power of $p$ and a power of $p'$ has order $1$. The library does not state the decomposition of a torsion group as the direct sum of its primary components in this module.

#### Torsion and modules

The module also connects torsion with modules over a ring. If $R$ is a torsion additive group, then each $R$-module is a torsion group (`IsAddTorsion.module_of_torsion`): an element $n \cdot 1 = 0$ of $R$ gives $n \cdot m = (n \cdot 1) \cdot m = 0$. In particular each module over a finite ring is torsion (`IsAddTorsion.module_of_finite`), for example each module over `ZMod n` with $n \ne 0$.

#### Divisible groups

The library defines divisibility as data. The class `DivisibleBy A α` holds a function `DivisibleBy.div : A → α → A` with two laws: `DivisibleBy.div_zero` says that the division by $0$ gives $0$, and `DivisibleBy.div_cancel` says that $n \cdot \operatorname{div}(a, n) = a$ for $n \ne 0$. The usual case is $\alpha = \mathbb{N}$ or $\alpha = \mathbb{Z}$, with the scalar multiplication of an additive group. The multiplicative form is `RootableBy A α` with the function `RootableBy.root` and the law `RootableBy.root_cancel`: $\operatorname{root}(a, n)^n = a$. The class holds a choice of the $n$-th part, and the choice is not unique in general: in $\mathbb{Q}/\mathbb{Z}$, both $0$ and $1/2$ are halves of $0$.

The class and surjectivity are equivalent. `DivisibleBy.surjective_smul` says that $a \mapsto n \cdot a$ is surjective for $n \ne 0$. Proof: $\operatorname{div}(a, n)$ is a preimage of $a$. In the other direction, `divisibleByOfSMulRightSurj` builds the class from surjectivity with the axiom of choice, and `rootableByOfPowLeftSurj` is the multiplicative form. For a commutative group the condition $n A = A$ is enough, by `AddCommGroup.divisibleByIntOfSMulTopEqTop`.

| Lean name | Statement |
|---|---|
| `AddGroup.divisibleByIntOfDivisibleByNat` | divisible by $\mathbb{N}$ gives divisible by $\mathbb{Z}$ |
| `AddGroup.divisibleByNatOfDivisibleByInt` | divisible by $\mathbb{Z}$ gives divisible by $\mathbb{N}$ |
| `divisibleByIntOfCharZero` | a division ring of characteristic zero is divisible by $\mathbb{Z}$ |
| `Prod.divisibleBy` | a product of two divisible groups is divisible |
| `Pi.divisibleBy` | a product of a family of divisible groups is divisible |
| `Function.Surjective.divisibleBy` | the image of a divisible group under a surjection that respects scalars is divisible |
| `QuotientAddGroup.divisibleBy` | a quotient of a divisible group is divisible |

The passage from $\mathbb{N}$ to $\mathbb{Z}$ uses $\operatorname{div}(a, -n) = -\operatorname{div}(a, n)$. The quotient case follows from the surjection case. For $[a] \in A / B$ and $n \ne 0$, the class $[\operatorname{div}(a, n)]$ is an $n$-th part of $[a]$, because the quotient map respects the scalar multiplication. So $\mathbb{Q}/\mathbb{Z}$ is divisible because $\mathbb{Q}$ is divisible. The multiplicative forms are `Group.rootableByIntOfRootableByNat`, `Prod.rootableBy`, `Pi.rootableBy`, `Function.Surjective.rootableBy` and `QuotientGroup.rootableBy`.

#### The divisible hull

Let $M$ be a commutative additive monoid. The *divisible hull* `DivisibleHull M` is the set of formal fractions $m / s$ with $m \in M$ and $s$ a positive natural number. The type is an abbreviation for `LocalizedModule` of $M$ at the nonzero natural numbers, and a fraction is `DivisibleHull.mk m s` with `s : ℕ+`. Two fractions are equal when they become equal after multiplication by a positive integer: `DivisibleHull.mk_eq_mk` says that $m / s = m' / s'$ if and only if $u s' m = u s m'$ for some $u$. The addition is the rule of fractions, `DivisibleHull.mk_add_mk`:

$$\frac{m_1}{s_1} + \frac{m_2}{s_2} = \frac{s_2 m_1 + s_1 m_2}{s_1 s_2}.$$

Proof sketch: the addition of `LocalizedModule` is defined by this formula, and the lemma unfolds it. The simp lemmas `DivisibleHull.nsmul_mk`, `DivisibleHull.neg_mk` and `DivisibleHull.zsmul_mk` give the other operations on fractions. The principles `DivisibleHull.ind` and `DivisibleHull.liftOn` reduce a statement or a definition on the hull to one on fractions.

The hull is a module over the nonnegative rationals (`DivisibleHull.instModuleNNRat`), and for a group $M$ it is a vector space over $\mathbb{Q}$ (`DivisibleHull.instModuleRat`). The scalar action is $\frac{a}{b} \cdot \frac{m}{s} = \frac{a m}{b s}$ (`DivisibleHull.qsmul_mk`). The coercion `DivisibleHull.coe` sends $m$ to $m / 1$, and it is an additive monoid homomorphism (`DivisibleHull.coeAddMonoidHom`). This map is injective when $M$ has unique division, the class `HasUniqueDiv M`: then $n m = n m'$ with $n \ne 0$ gives $m = m'$. This is `DivisibleHull.coe_injective`. A torsion-free commutative group has unique division, so it embeds in a $\mathbb{Q}$-vector space.

For an ordered monoid $M$, the hull carries the order $m / s \le m' / s'$ if and only if $s' m \le s m'$ (`DivisibleHull.mk_le_mk`). It is a linear order (`DivisibleHull.instLinearOrder`), and for an ordered group the coercion is an ordered additive monoid homomorphism (`DivisibleHull.coeOrderAddMonoidHom`). The hull has the same Archimedean classes as $M$: `DivisibleHull.archimedeanClassOrderIso` is an order isomorphism between the two sets of classes. So the hull of an ordered group adds no new orders of magnitude.

#### Common errors

1. `CommGroup.torsion G` needs a commutative group. For a non-commutative group, state the property of each element with `IsOfFinOrder`, or the property of the whole group with `IsMulTorsion G`.
2. `DivisibleBy A ℕ` and `DivisibleBy A ℤ` are different classes. Lean does not convert one to the other by itself; use `AddGroup.divisibleByIntOfDivisibleByNat` or its inverse.
3. `DivisibleHull M` is not divisible by an instance of `DivisibleBy`. It is a module over $\mathbb{Q}$, so the $n$-th part of $x$ is the scalar product $\frac{1}{n} \cdot x$.

### Exercises

1. (A) Prove that $\mathbb{Z}$ is not divisible with `DivisibleBy.surjective_smul`.
2. (A) Prove with `CommGroup.mem_torsion` that the torsion subgroup of $\mathbb{Z} \times \mathbb{Z}/6$ is $\{0\} \times \mathbb{Z}/6$.
3. (B) Prove that a commutative group is a torsion group if and only if it is the union of its finite subgroups.
4. (B) Prove that a finite divisible group is trivial.
5. (B) Show that the divisible hull of $\mathbb{Z}$ is isomorphic to $\mathbb{Q}$ as a $\mathbb{Q}$-vector space, with `DivisibleHull.mk` and `DivisibleHull.mk_eq_mk`.
6. (C) Prove that in a commutative torsion group $G$, each element is a product of elements of the primary components, so $G$ is generated by the subgroups `CommGroup.primaryComponent G p`.

### Reference

<?reference?>
