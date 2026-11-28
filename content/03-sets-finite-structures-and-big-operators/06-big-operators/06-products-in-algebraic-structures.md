---
title: Products in algebraic structures
kind: api
modules:
  - Mathlib.Algebra.BigOperators.Associated
  - Mathlib.Algebra.BigOperators.Field
  - Mathlib.Algebra.BigOperators.GroupWithZero.Action
  - Mathlib.Algebra.BigOperators.GroupWithZero.Finset
  - Mathlib.Algebra.BigOperators.ModEq
  - Mathlib.Algebra.BigOperators.Module
  - Mathlib.Algebra.BigOperators.RingEquiv
  - Mathlib.Algebra.BigOperators.WithTop
  - Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
  - Mathlib.Data.Finset.NoncommProd
explains:
  E2: [Finset.prod_eq_zero_iff, Finset.prod_boole, Prime.dvd_finsetProd_iff, Finset.prod_primes_dvd, Int.ModEq.prod, Finset.smul_sum, Finset.sum_range_by_parts, WithTop.sum_eq_top, Finset.prod_pos, Finset.noncommProd]
  E1: auto
families: []
requires: [V03.C03, V03.C04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Products in algebraic structures

### Overview

Sections 1 and 2 gave the rules for a finite product in a commutative monoid and for a finite sum in a semiring. Many proofs need more than these rules. They need to know when a product is zero, when a prime divides a product, how a product behaves under a congruence, how a scalar moves through a sum, or when a product is positive. They can also need a product in a monoid that is not commutative. This section gives the library for these questions.

Each module adds one structure to the base rules. The modules on monoids with zero give the rules for zero and for units. The modules on primes and on congruences give the rules of divisibility. The modules on actions and modules give the rules for scalars. The order module gives the rules for signs and bounds. The module `Mathlib.Data.Finset.NoncommProd` gives a product over a finset when only the factors commute in pairs.

### The library around it

#### Zero and units

In a commutative monoid with zero, a product with a zero factor is zero. This is `Finset.prod_eq_zero`: if $i \in s$ and $f(i) = 0$, then $\prod_{j \in s} f(j) = 0$. The proof splits $i$ off the product with the erase rule of Section 2, and $0 \cdot x = 0$.

The converse needs a ring with no zero divisors that is not the zero ring. Under these conditions `Finset.prod_eq_zero_iff` states

$$\prod_{x \in s} f(x) = 0 \iff \exists a \in s,\ f(a) = 0,$$

and `Finset.prod_ne_zero_iff` is its negation. The proof is induction on $s$. For the empty finset, the product is $1 \ne 0$. For the step, $f(a) \cdot P = 0$ holds exactly when $f(a) = 0$ or $P = 0$, because there are no zero divisors. In the ring $\mathbb{Z}/6$, the rule fails: $2 \cdot 3 = 0$ with two factors that are not zero.

The products of conditionals have closed forms. The rule `Finset.prod_ite_zero` says that the product of "$f(i)$ if $p(i)$, else $0$" is $\prod_{i \in s} f(i)$ when $p$ holds on all of $s$, and $0$ otherwise. The special case `Finset.prod_boole` has $f = 1$: the product of the indicator values of $p$ is $1$ exactly when $p$ holds on all of $s$. So a product of indicators is the indicator of the conjunction. The rule `Units.mk0_prod` says that in a group with zero, the unit of a nonzero product is the product of the units of the factors.

#### Primes and associated elements

A prime $p$ divides a product $ab$ only if it divides $a$ or $b$. The module `Mathlib.Algebra.BigOperators.Associated` extends this to finite products. The rule `Prime.dvd_finsetProd_iff` states

$$p \mid \prod_{a \in S} g(a) \iff \exists a \in S,\ p \mid g(a).$$

The proof is induction on $S$, with the two factor rule in the step. The prime $p$ does not divide the empty product $1$, because a prime is not a unit. The contrapositive `Prime.not_dvd_finsetProd` is the form for a proof that $p$ does not divide a product. The rule `Prime.exists_mem_finset_dvd` gives only the direction from left to right.

In the other direction, `Finset.prod_primes_dvd` says that if each element of a finset $s$ of primes divides $n$, then $\prod_{p \in s} p$ divides $n$. The ring must cancel nonzero factors and have only the unit $1$, as $\mathbb{N}$ does. The condition on units makes two associated primes in $s$ equal, so the primes in $s$ are coprime in pairs. The form for multisets, `Multiset.prod_primes_dvd`, also counts the multiplicities.

For a unique factorization, `exists_associated_mem_of_dvd_prod` says that a prime $p$ that divides a product of primes is associated with one of the factors. The rule `Associated.prod` says that a product of associated factors is associated with the product. The rule `Associates.prod_mk` says that the map `Associates.mk` to the monoid of classes of associated elements commutes with the product of a multiset.

#### Congruences

The module `Mathlib.Algebra.BigOperators.ModEq` lifts the rules of Section 2 to congruences in $\mathbb{N}$ and $\mathbb{Z}$. The rule `Int.ModEq.prod` says that if $f(x) \equiv g(x) \pmod n$ for each $x \in s$, then

$$\prod_{x \in s} f(x) \equiv \prod_{x \in s} g(x) \pmod n.$$

The proof is induction on $s$ with the product rule for one congruence. The rules `Nat.ModEq.prod` and the sum forms are the same for $\mathbb{N}$, and the module has forms for lists and multisets. The rule `Int.sum_modEq_single` says that if all terms other than $f(a)$ are $0$ modulo $n$, then the sum is $f(a)$ modulo $n$. The rule `Int.prod_modEq_single` is its product form, with $1$ in place of $0$. The rule `Int.sum_modEq_ite` gives the value when $a$ can be outside $s$.

For example, $\sum_{k=1}^{6} k! \equiv 1! + 2! + 3! + 4! \pmod{5}$, because $5 \mid k!$ for $k \ge 5$. The value is $33 \equiv 3$.

#### Scalars and modules

A scalar moves through a sum. The rule `Finset.smul_sum` states $r \cdot \sum_{x \in s} f(x) = \sum_{x \in s} r \cdot f(x)$ for a scalar action that distributes over addition. It is the module form of `Finset.mul_sum`. The module `Mathlib.Algebra.BigOperators.GroupWithZero.Action` has the forms for products too. The rule `Finset.smul_prod` says $b^{|s|} \cdot \prod_{x \in s} f(x) = \prod_{x \in s} b \cdot f(x)$, because each factor brings one copy of $b$. The rule `Finset.prod_smul` says $\prod_i b_i \cdot f_i = (\prod_i b_i) \cdot \prod_i f_i$. The rule `Finset.smul_prod_perm` says that a group element $g$ fixes the product of the orbit values $\prod_{h} h \cdot b$, because $h \mapsto gh$ is a bijection of the group. The module also has the forms for lists, multisets and `finprod`.

The module `Mathlib.Algebra.BigOperators.Module` has the summation by parts. With $G(n) = \sum_{i < n} g(i)$, the rule `Finset.sum_range_by_parts` states

$$\sum_{i < n} f(i) \cdot g(i) = f(n - 1) \cdot G(n) - \sum_{i < n - 1} \bigl(f(i + 1) - f(i)\bigr) \cdot G(i + 1).$$

This is the discrete form of the integration by parts. The rules `Finset.sum_Ico_by_parts` and `Finset.sum_Ioc_by_parts` are the forms for other intervals. A use is the Abel test: if $f$ decreases to $0$ and the partial sums $G$ are bounded, then the right side converges.

The module `Mathlib.Algebra.BigOperators.Field` has the division rules. The rule `Finset.sum_div` states $(\sum_{i \in s} f(i)) / a = \sum_{i \in s} f(i) / a$, and `Multiset.sum_map_div` is the multiset form. It also has rules for the density of Chapter 3: `Finset.dens_biUnion` says that the density of a disjoint union is the sum of the densities, and `Finset.dens_eq_sum_dens_fiberwise` splits a density into the densities of the fibers of a map.

The module `Mathlib.Algebra.BigOperators.RingEquiv` says that a ring isomorphism commutes with finite sums and products: `RingEquiv.map_sum` and `RingEquiv.map_prod`. The rule `RingEquiv.unop_map_list_prod` is the form for an isomorphism to the opposite ring, which reverses the order of the factors.

#### Extended values

The types `WithTop M` and `WithBot M` add a top or bottom element to $M$. The module `Mathlib.Algebra.BigOperators.WithTop` gives the rules for sums with these values. The rule `WithTop.sum_eq_top` says that a sum is $\top$ exactly when one term is $\top$. The rule `WithTop.sum_lt_top` says that a sum is finite exactly when each term is finite. The rule `WithTop.coe_sum` says that the cast from $M$ commutes with sums. For products, the rules `WithTop.prod_lt_top` and `WithTop.prod_eq_top` need a monoid with zero with no zero divisors, because $0 \cdot \top = 0$ in `WithTop`. The rule `WithBot.bot_lt_sum_iff` is the dual form.

#### Signs and bounds

The module `Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset` gives the order rules for products in an ordered semiring, such as $\mathbb{R}$. These rules need nonnegative factors, and the names end in the subscript zero when there is also a rule for ordered groups.

| Lean name | Statement |
|---|---|
| `Finset.prod_nonneg` | $0 \le f(i)$ for all $i \in s$ gives $0 \le \prod_{i \in s} f(i)$ |
| `Finset.prod_pos` | $0 < f(i)$ for all $i \in s$ gives $0 < \prod_{i \in s} f(i)$ |
| `Finset.prod_le_prod₀` | $0 \le f \le g$ on $s$ gives $\prod f \le \prod g$ |
| `Finset.prod_le_one₀` | $0 \le f \le 1$ on $s$ gives $\prod f \le 1$ |
| `Finset.one_le_prod₀` | $1 \le f$ on $s$ gives $1 \le \prod f$ |
| `Finset.prod_lt_prod_of_nonempty₀` | $0 < f < g$ on a nonempty $s$ gives $\prod f < \prod g$ |
| `Finset.le_prod_max_one` | $f(i) \le \prod_{j \in s} \max(f(j), 1)$ for $i \in s$ |

The proof of `Finset.prod_le_prod₀` is induction on $s$. In the step, $f(a) P_f \le g(a) P_f \le g(a) P_g$, and the two steps use $0 \le P_f$ and $0 \le g(a)$. So the condition $0 \le f$ is necessary: for $f = (-2, -2)$ and $g = (1, 1)$, $f \le g$ but $\prod f = 4 > 1 = \prod g$. The rule `Monotone.finsetProd` says that a product of monotone nonnegative functions is monotone.

#### Products that do not commute

The product `Finset.prod` needs a commutative monoid, because a finset has no order. In a monoid such as a group of matrices, a product over a finset has a value when the factors commute in pairs. The definition `Finset.noncommProd` takes a finset $s$, a function $f$ and a proof that $f(x)$ and $f(y)$ commute for $x, y \in s$. The definition `Multiset.noncommProd` is the form for a multiset of elements. The proof of commutation is the condition `Commute` in pairs. With it, the product of the elements of the multiset in any order has the same value, so the product does not depend on a choice of list.

The rules copy the rules of Section 1, with a proof of commutation as one more argument.

1. `Finset.noncommProd_empty` and `Finset.noncommProd_singleton` give the values $1$ and $f(a)$.
2. `Finset.noncommProd_insert_of_notMem` splits off one factor at the left.
3. `Finset.noncommProd_union_of_disjoint` splits a product over a disjoint union.
4. `Finset.noncommProd_mul_distrib` gives $\prod (f g) = \prod f \cdot \prod g$, when $f$ and $g$ also commute with each other.
5. `Finset.noncommProd_eq_pow_card` gives $m^{|s|}$ for a constant function.
6. `Finset.noncommProd_eq_prod` says that in a commutative monoid, the new product is the old one.
7. `Finset.noncommProd_commute` says that an element that commutes with each factor commutes with the product.

The rule `Finset.noncommProd_mulSingle` writes an element $x$ of a product of monoids as the product of the elements `Pi.mulSingle i (x i)`. These elements commute, because each one is $1$ at all indices but one, and the indices differ. The rule `MonoidHom.pi_ext` follows: two monoid homomorphisms out of a finite product of monoids are equal when they are equal on each `Pi.mulSingle i x`.

#### Common errors

1. The rule `Finset.prod_eq_zero_iff` needs no zero divisors and a nontrivial ring. In $\mathbb{Z}/n$ for $n$ that is not prime, only the direction from right to left holds, and it is `Finset.prod_eq_zero`.
2. The order rules for products need $0 \le f$. Without this condition, a proof with `Finset.prod_le_prod₀` leaves a goal that is false for negative factors.
3. A term of `Finset.noncommProd` contains the proof of commutation. A rewrite that changes $s$ or $f$ must change the proof too. Use `Finset.noncommProd_congr` for this, not a plain rewrite, which can fail with a motive error.

### Exercises

1. (A) Use `Finset.prod_eq_zero_iff` to prove that $\prod_{k=1}^{n} (k - 3) = 0$ in $\mathbb{Z}$ for $n \ge 3$.
2. (A) Compute $\sum_{k=1}^{10} k! \bmod 9$ with `Nat.sum_modEq_single` or by the rules of this section.
3. (B) Prove that if a prime $p$ divides $n!$, then $p \le n$. Use `Prime.dvd_finsetProd_iff` with the product over $[1, n]$.
4. (B) Use `Finset.sum_range_by_parts` with $f(i) = i$ and $g(i) = 1$ to compute $\sum_{i < n} i$.
5. (B) Prove $\prod_{i \in s} (1 - x_i) \ge 1 - \sum_{i \in s} x_i$ for $0 \le x_i \le 1$, by induction on $s$ with `Finset.prod_nonneg` and `Finset.prod_le_one₀`.
6. (C) Let $g_1, \ldots, g_n$ be elements of a group that commute in pairs and have orders $m_1, \ldots, m_n$. Prove with `Finset.noncommProd_mul_distrib` that $(\prod_i g_i)^{m}= 1$ for $m = \operatorname{lcm}(m_1, \ldots, m_n)$.

### Reference

<?reference?>
