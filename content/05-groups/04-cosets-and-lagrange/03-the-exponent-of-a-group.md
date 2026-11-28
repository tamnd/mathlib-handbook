---
title: The exponent of a group and the minimum order
kind: api
modules:
  - Mathlib.GroupTheory.Exponent
  - Mathlib.GroupTheory.Order.Min
  - Mathlib.GroupTheory.QuotientGroup.UnitsModPow
explains:
  E2: [Monoid.exponent, Monoid.pow_exponent_eq_one, Monoid.exponent_dvd_of_forall_pow_eq_one, Monoid.order_dvd_exponent, Group.exponent_dvd_card, Monoid.exists_orderOf_eq_exponent, mul_comm_of_exponent_two, Monoid.exponent_prod, Monoid.minOrder, Units.ModPow]
  E1: auto
families: []
requires: [V02, V05.C03]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The exponent of a group and the minimum order

### Overview

The order of an element $g$ is the least $n > 0$ with $g^n = 1$. The exponent of a group $G$ is the least $n > 0$ with $g^n = 1$ for all $g \in G$ at once. It is the least common multiple of the orders of the elements, when this is finite. The exponent divides the order of a finite group, by the theorem of Lagrange, and it can be smaller: the Klein group has order $4$ and exponent $2$. A finite commutative group is cyclic exactly when its exponent is its order, so the exponent detects cyclicity.

This section describes the library of the exponent in `Mathlib.GroupTheory.Exponent`. It also describes two smaller modules. The first, `Mathlib.GroupTheory.Order.Min`, defines the minimum order of a nontrivial element, a number that bounds the size of every nontrivial finite subgroup from below. The second, `Mathlib.GroupTheory.QuotientGroup.UnitsModPow`, defines the group of units of a commutative monoid modulo $n$-th powers. Its elements all satisfy $x^n = 1$, so it is a first example of a group of exponent dividing $n$.

The section uses the order of an element and the theorem of Lagrange from the two sections before it.

### The library around it

#### The definition

The definition is in two steps. The proposition `Monoid.ExponentExists G` says that some $n > 0$ satisfies $g^n = 1$ for all $g$. The number `Monoid.exponent G : ℕ` is the least such $n$ if one exists, and $0$ otherwise. So the exponent follows the same convention as `orderOf`: the value $0$ means "infinite". The lemma `Monoid.exponent_eq_sInf` states the definition as an infimum of a set of natural numbers, and `Monoid.exponent_eq_zero_iff` and `Monoid.exponent_ne_zero` relate the value $0$ to `Monoid.ExponentExists G`. A finite cancellative monoid has a nonzero exponent, by `Monoid.exponent_ne_zero_of_finite`, and the instance form `Monoid.neZero_exponent_of_finite` lets instance search find this fact. The additive version is `AddMonoid.exponent`, and `Monoid.exponent_multiplicative` passes between the two.

The first two facts are the defining properties. Each element satisfies $g^{\exp G} = 1$: this is `Monoid.pow_exponent_eq_one`. It holds also when the exponent is $0$, because $g^0 = 1$. And the exponent is minimal: for $0 < m < \exp G$ some element has $g^m \ne 1$, by `Monoid.exponent_min`.

**Proposition.** If $g^n = 1$ for all $g \in G$, then $\exp G$ divides $n$.

*Proof.* If $\exp G = 0$, then no positive $n$ works for all $g$, so $n = 0$ and $0 \mid 0$. Otherwise write $n = q \exp G + r$ with $0 \le r < \exp G$. For each $g$, $1 = g^n = (g^{\exp G})^q g^r = g^r$. By minimality, $r = 0$. $\square$

This is `Monoid.exponent_dvd_of_forall_pow_eq_one`, and `Monoid.exponent_dvd_iff_forall_pow_eq_one` is the equivalence. In a group, `Group.exponent_dvd_iff_forall_zpow_eq_one` states the same for integer powers. Applied to $n = \exp G$ and to one element at a time, the same argument gives $\operatorname{ord}(g) \mid \exp G$, which is `Monoid.order_dvd_exponent`. The equivalence `Monoid.exponent_dvd` reads: $\exp G \mid n$ if and only if $\operatorname{ord}(g) \mid n$ for all $g$. So the exponent is the least common multiple of the orders. For a finite monoid, `Monoid.lcm_orderOf_eq_exponent` states $\operatorname{lcm}_{g \in G} \operatorname{ord}(g) = \exp G$ with `Finset.lcm`.

A power can be reduced modulo the exponent: `Monoid.pow_eq_mod_exponent` states $g^n = g^{n \bmod \exp G}$.

#### The exponent and the order

**Proposition.** The exponent of a finite group divides its order.

*Proof.* By Lagrange, $\operatorname{ord}(g)$ divides $|G|$ for each $g$, so $g^{|G|} = 1$ for each $g$. The previous proposition gives $\exp G \mid |G|$. $\square$

This is `Group.exponent_dvd_card` for a `Fintype`, and `Group.exponent_dvd_nat_card` with `Nat.card`. For a nontrivial finite group the exponent is at least $2$, by `Monoid.one_lt_exponent`. The exponent is $1$ exactly for the trivial group, by `Monoid.exp_eq_one_iff`.

In a commutative monoid the exponent is attained by one element. This is the main theorem of the module.

**Theorem.** Let $G$ be a commutative monoid with $\exp G \ne 0$. Then some $g \in G$ has $\operatorname{ord}(g) = \exp G$.

*Proof sketch.* Write $\exp G = \prod_p p^{a_p}$. For each prime $p$ with $a_p > 0$, some element $g_p$ has order $p^{a_p}$: otherwise every order would divide $\exp G / p$, and then $\exp G \mid \exp G / p$. This step is `Nat.Prime.exists_orderOf_eq_pow_factorization_exponent`. The elements $g_p$ commute and their orders are coprime, so the product $\prod_p g_p$ has order $\prod_p p^{a_p}$. $\square$

The Lean statement is `Monoid.exists_orderOf_eq_exponent`. With it, the exponent of a commutative group is the supremum of the orders, by `Monoid.exponent_eq_iSup_orderOf`, and for a finite cancellative commutative monoid it is the largest order, by `Monoid.exponent_eq_max'_orderOf`. The commutativity matters. In $S_3$ the orders are $1$, $2$ and $3$, so $\exp S_3 = 6$, but $S_3$ has no element of order $6$. For two commuting elements, `Commute.exists_orderOf_eq_lcm` produces an element of the monoid they generate whose order is the least common multiple of their orders.

The theorem gives the cyclicity test. A finite commutative group $G$ with $\exp G = |G|$ has an element of order $|G|$, so it is cyclic. The library states this as `IsCyclic.of_exponent_eq_card`, in the module of cyclic groups, and the converse as `IsCyclic.exponent_eq_card`. For example, $\mathbb{Z}/2 \times \mathbb{Z}/4$ has exponent $4$ and order $8$, so it is not cyclic.

#### Constructions

The exponent behaves well under the usual constructions.

| Lean name | Statement |
|---|---|
| `Monoid.exponent_submonoid_dvd` | $\exp H \mid \exp G$ for a submonoid $H$ |
| `Group.exponent_quotient_dvd` | $\exp (G/N) \mid \exp G$ for a normal subgroup $N$ |
| `MonoidHom.exponent_dvd` | $\exp H \mid \exp G$ if $G \to H$ is surjective |
| `Monoid.exponent_dvd_of_monoidHom` | $\exp G \mid \exp H$ if $G \to H$ is injective |
| `Monoid.exponent_eq_of_mulEquiv` | isomorphic monoids have the same exponent |
| `Monoid.exponent_prod` | $\exp (G_1 \times G_2) = \operatorname{lcm}(\exp G_1, \exp G_2)$ |
| `Monoid.exponent_pi` | the exponent of a finite product is the lcm of the exponents |
| `MulOpposite.exponent` | $\exp G^{\mathrm{op}} = \exp G$ |

The proof of `Monoid.exponent_prod` is short. A pair $(g_1, g_2)$ satisfies $(g_1, g_2)^n = 1$ if and only if $g_1^n = 1$ and $g_2^n = 1$. So $\exp(G_1 \times G_2) \mid n$ if and only if $\exp G_1 \mid n$ and $\exp G_2 \mid n$, that is, if and only if $\operatorname{lcm}(\exp G_1, \exp G_2) \mid n$. Two natural numbers with the same multiples are equal.

The characteristic of a ring is the additive exponent of the ring, by `ringChar_eq_addMonoidExponent`. The additive exponent of $\mathbb{Z}/n$ is $n$, by `ZMod.exponent`.

#### Groups of exponent two

A group of exponent $2$ is commutative. The proof is one line: each element is its own inverse, so $a b = (a b)^{-1} = b^{-1} a^{-1} = b a$. The lemma `inv_eq_self_of_exponent_two` gives $x^{-1} = x$, and `mul_comm_of_exponent_two` gives $a b = b a$ in a cancellative monoid. The definition `commMonoidOfExponentTwo` builds the commutative structure. A related fact, `Commute.of_orderOf_dvd_two`, only asks that each order divide $2$. The lemma `mul_notMem_of_exponent_two` says that for distinct nontrivial $x$ and $y$ the product $x y$ is a fourth element, outside $\{x, y, 1\}$. This is the step that shows that the Klein group is the smallest group of exponent $2$ that is not cyclic.

For a prime $p$ and a nontrivial monoid, `Monoid.exponent_eq_prime_iff` says that $\exp G = p$ if and only if every nontrivial element has order $p$.

#### The minimum order

The module `Mathlib.GroupTheory.Order.Min` defines `Monoid.minOrder α : ℕ∞`, the infimum of the orders of the nontrivial elements of finite order. If there is no such element, the value is $\top$. So a torsion-free group has minimum order $\top$, by `Monoid.minOrder_eq_top`, and for a commutative group the converse holds, by `Monoid.minOrder_eq_top_iff` with the class `IsMulTorsionFree`. The basic bound is `Monoid.minOrder_le_orderOf`: each nontrivial element of finite order has order at least the minimum.

In a group, the minimum order also bounds subgroups. A nontrivial finite subgroup $H$ contains a nontrivial element $h$, and $\langle h \rangle \le H$, so $|H| \ge \operatorname{ord}(h) \ge \operatorname{minOrder}(G)$. This is `Monoid.minOrder_le_natCard`, and `Monoid.le_minOrder_iff_forall_subgroup` states that the minimum order is the infimum of the orders of the nontrivial finite subgroups. For the integers modulo $n$ with $n \ge 2$, `ZMod.minOrder` computes the minimum order as the smallest prime factor `Nat.minFac n`, and `ZMod.minOrder_of_prime` gives $p$ for a prime $p$.

#### Units modulo powers

Let $\alpha$ be a commutative monoid and $n \in \mathbb{N}$. The group `Units.ModPow α n` is the quotient $\alpha^\times / (\alpha^\times)^n$ of the units by the subgroup of $n$-th powers. It is an abbreviation for the quotient of `αˣ` by the range of `powMonoidHom n`, so the quotient group API of Chapter 5 applies to it. Each element satisfies $x^n = 1$, by `Units.ModPow.pow_eq_one`, so the exponent of this group divides $n$. Two units have the same class if and only if they differ by an $n$-th power, by `Units.ModPow.mk_eq_mk_iff`, and a class is trivial if and only if the unit is an $n$-th power, by `Units.ModPow.mk_eq_one_iff`. For $n = 2$, `Units.ModPow.mk_eq_one_iff_isSquare` states this with `IsSquare`. If every unit is an $n$-th power, the group is trivial, by `Units.ModPow.subsingleton_of_forall_exists_pow`.

The construction is functorial. A monoid homomorphism $\varphi : \alpha \to \beta$ induces `Units.ModPow.map φ n`, with `Units.ModPow.map_id` and `Units.ModPow.map_comp`, and an isomorphism induces the isomorphism `Units.ModPow.congr e n`. The units modulo $n$-th powers of a product are the product of the factors, by `Units.ModPow.piEquiv`. The additive version is `AddUnits.ModNSMul`. For a field $K$, the group $K^\times / (K^\times)^n$ is the group of Kummer theory.

#### Common errors

1. `Monoid.exponent G = 0` means that no common exponent exists, not that the group is trivial. The trivial group has exponent $1$. A lemma that needs a finite exponent asks for `Monoid.ExponentExists G` or for `Monoid.exponent G ≠ 0`.
2. `Monoid.exists_orderOf_eq_exponent` needs a `CommMonoid`. In a noncommutative group no element needs to have the exponent as its order, as $S_3$ shows.
3. `Monoid.minOrder` takes values in `ℕ∞`, not in `ℕ`. A comparison with a natural number needs a cast, and the value $\top$ stands for "no nontrivial element of finite order".

### Exercises

1. (A) Compute the exponents of $\mathbb{Z}/12$, $\mathbb{Z}/2 \times \mathbb{Z}/6$, $S_4$ and $D_4$.
2. (A) Show that the exponent of $\mathbb{Z}/m \times \mathbb{Z}/n$ is $\operatorname{lcm}(m, n)$, and deduce that this group is cyclic if and only if $\gcd(m, n) = 1$.
3. (A) Show that $\exp(G/N)$ divides $\exp G$ for each normal subgroup $N$.
4. (B) Let $G$ be a finite commutative group with $\exp G = |G|$. Show that $G$ is cyclic, using `Monoid.exists_orderOf_eq_exponent`.
5. (B) Show that `Monoid.minOrder` of $\mathbb{Z}/12$ is $2$ and that every nontrivial subgroup of $\mathbb{Z}/35$ has at least $5$ elements.
6. (C) Show that $(\mathbb{Z}/8)^\times$ has exponent $2$ and that $\mathbb{Q}^\times / (\mathbb{Q}^\times)^2$ is infinite. Hint: the classes of the primes are distinct.

### Reference

<?reference?>
