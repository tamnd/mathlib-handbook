---
title: The order of an element
kind: theory
modules:
  - Mathlib.GroupTheory.OrderOfElement
explains:
  E3: [orderOf_dvd_card]
  E2: [orderOf, pow_orderOf_eq_one, orderOf_dvd_iff_pow_eq_one, orderOf_pos, Fintype.card_zpowers, pow_card_eq_one, orderOf_pow', orderOf_eq_prime, isCyclic_of_prime_card, Commute.orderOf_mul_eq_mul_orderOf_of_coprime]
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

## The order of an element

### Overview

The order of an element $a$ is the least $n \ge 1$ with $a^n = 1$. It is the number of elements of the cyclic subgroup $\langle a \rangle$. With Lagrange's theorem this gives the main fact of the section: in a finite group, the order of each element divides the order of the group. Two classical theorems of number theory follow at once, the little theorem of Fermat and its generalization by Euler. A second consequence is that a group of prime order is cyclic.

The section also computes the order of a power, and the order of a product of two commuting elements with coprime orders. It ends with the proof that the converse of Lagrange's theorem is false: the group $A_4$ of order $12$ has no subgroup of order $6$. Chapter 8 proves a partial converse, the theorems of Cauchy and Sylow.

### Definitions

**Definition (Order of an element).** Let $G$ be a monoid and $a \in G$. If $a^n = 1$ for some $n \ge 1$, the order of $a$ is the least such $n$, written $\operatorname{ord}(a)$. Otherwise $a$ has infinite order.

::: mathlib
`orderOf` · `Mathlib.GroupTheory.OrderOfElement`

The order as a natural number, defined for each monoid. The convention is that `orderOf a = 0` when $a$ has infinite order. So `orderOf a = 0 ↔ ∀ n, 0 < n → a ^ n ≠ 1`, which is `orderOf_eq_zero_iff'`. The additive form is `addOrderOf`, so `addOrderOf (1 : ZMod n) = n`.

<?decl orderOf?>
:::

::: mathlib
`pow_orderOf_eq_one` · `Mathlib.GroupTheory.OrderOfElement`

The basic property `a ^ orderOf a = 1`. It holds for the convention `0` too, because `a ^ 0 = 1`.

<?decl pow_orderOf_eq_one?>
:::

### Theorems and proofs

**Theorem (Powers equal to $1$).** Let $a$ have finite order $n$. Then $a^m = 1$ if and only if $n \mid m$, for each $m \in \mathbb{Z}$.

*Proof.* If $m = q n$, then $a^m = (a^n)^q = 1$. Conversely, let $a^m = 1$. Divide with remainder: $m = q n + r$ with $0 \le r < n$. Then $a^r = a^m (a^n)^{-q} = 1$. Since $n$ is the least positive exponent with this property, $r$ is not positive, so $r = 0$ and $n \mid m$. $\square$

::: mathlib
`orderOf_dvd_iff_pow_eq_one` · `Mathlib.GroupTheory.OrderOfElement`

The theorem for natural exponents: `orderOf a ∣ n ↔ a ^ n = 1`. With the convention `orderOf a = 0` it is still true, since `0 ∣ n` means `n = 0`. One direction is `orderOf_dvd_of_pow_eq_one`.

<?decl orderOf_dvd_iff_pow_eq_one?>
:::

**Theorem (Order of a cyclic subgroup).** If $a$ has finite order $n$, then $\langle a \rangle = \{1, a, \ldots, a^{n - 1}\}$ has exactly $n$ elements. In a finite group, each element has finite order.

*Proof.* The first claim is the theorem on the structure of cyclic groups of the previous chapter, applied to $\langle a \rangle$. For the second claim, the powers $a, a^2, a^3, \ldots$ of an element of a finite group cannot all be distinct. So $a^i = a^j$ with $1 \le i < j$, and then $a^{j - i} = 1$ by cancellation, with $j - i \ge 1$. $\square$

::: mathlib
`orderOf_pos` · `Mathlib.GroupTheory.OrderOfElement`

In a finite left cancellative monoid each element has positive order. The proof is the argument above with the pigeonhole principle.

<?decl orderOf_pos?>
:::

::: mathlib
`Fintype.card_zpowers` · `Mathlib.GroupTheory.OrderOfElement`

The equation `Fintype.card (zpowers a) = orderOf a` in a finite group. The version with `Nat.card`, which needs no `Fintype` instance, is `Nat.card_zpowers`.

<?decl Fintype.card_zpowers?>
:::

**Theorem (The order of an element divides the order of the group).** Let $G$ be a finite group and $a \in G$. Then $\operatorname{ord}(a)$ divides $|G|$, and $a^{|G|} = 1$.

*Proof.* The order of $a$ is $|\langle a \rangle|$, by the theorem above. This number divides $|G|$, by Lagrange's theorem. So $|G| = k \operatorname{ord}(a)$ for some $k$, and $a^{|G|} = (a^{\operatorname{ord}(a)})^k = 1$. $\square$

::: mathlib
`orderOf_dvd_card` · `Mathlib.GroupTheory.OrderOfElement`

The theorem for a group with a `Fintype` instance: `orderOf a ∣ Fintype.card G`. The form with `Nat.card` and no finiteness hypothesis is `orderOf_dvd_natCard`; for an infinite group the right side is `0`.

<?decl orderOf_dvd_card?>
:::

::: mathlib
`pow_card_eq_one` · `Mathlib.GroupTheory.OrderOfElement`

The consequence `a ^ Fintype.card G = 1`. The `Nat.card` form is `pow_card_eq_one'`.

<?decl pow_card_eq_one?>
:::

**Corollary (Fermat and Euler).** Let $n \ge 1$ and let $a$ be an integer coprime to $n$. Then $a^{\varphi(n)} \equiv 1 \pmod n$, where $\varphi(n)$ is the number of units of $\mathbb{Z}/n$. In particular, for a prime $p$ that does not divide $a$, $a^{p - 1} \equiv 1 \pmod p$.

*Proof.* The class of $a$ is a unit of $\mathbb{Z}/n$, by Chapter 1. The group $(\mathbb{Z}/n)^\times$ has $\varphi(n)$ elements, so $\bar a^{\varphi(n)} = 1$ by the theorem. For a prime $p$, the units of $\mathbb{Z}/p$ are the $p - 1$ nonzero classes. $\square$

In Mathlib these are `ZMod.pow_totient` and `ZMod.pow_card_sub_one_eq_one`, in the volume on fields.

**Corollary (Groups of prime order).** Let $|G| = p$ be prime. Then $G$ is cyclic, and each element $a \neq 1$ generates $G$.

*Proof.* Let $a \neq 1$. Then $\operatorname{ord}(a)$ divides $p$ and is not $1$, so it is $p$. So $\langle a \rangle$ has $p$ elements, and $\langle a \rangle = G$. $\square$

::: mathlib
`isCyclic_of_prime_card` · `Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup`

The corollary: `Nat.card G = p → IsCyclic G`, for a prime `p` given as an instance `Fact p.Prime`. Such an instance is made with `haveI := Fact.mk hp`.

<?decl isCyclic_of_prime_card?>
:::

::: mathlib
`orderOf_eq_prime` · `Mathlib.GroupTheory.OrderOfElement`

A test for prime order: if `a ^ p = 1` and `a ≠ 1`, then `orderOf a = p`. The proof is the first part of the proof above.

<?decl orderOf_eq_prime?>
:::

**Theorem (Order of a power).** Let $a$ have finite order $n$ and let $k \ge 1$. Then $\operatorname{ord}(a^k) = n / \gcd(n, k)$.

*Proof.* Let $d = \gcd(n, k)$, and write $n = d n'$ and $k = d k'$ with $\gcd(n', k') = 1$. For $m \ge 1$, the power $(a^k)^m = a^{k m}$ is $1$ if and only if $n \mid k m$, by the first theorem. That is $d n' \mid d k' m$, or $n' \mid k' m$. Since $n'$ and $k'$ are coprime, this holds if and only if $n' \mid m$. So the least such $m$ is $n'$. $\square$

::: mathlib
`orderOf_pow'` · `Mathlib.GroupTheory.OrderOfElement`

The theorem in a monoid, for `n ≠ 0`: `orderOf (a ^ n) = orderOf a / (orderOf a).gcd n`. The hypothesis excludes `a ^ 0 = 1`. In a finite group the version `orderOf_pow` needs no hypothesis.

<?decl orderOf_pow'?>
:::

**Theorem (Order of a product).** Let $a$ and $b$ commute, with finite orders $m$ and $n$ that are coprime. Then $\operatorname{ord}(a b) = m n$.

*Proof.* Since $a b = b a$, the power $(a b)^k$ is $a^k b^k$ for each $k$. So $(a b)^{m n} = (a^m)^n (b^n)^m = 1$, and $\operatorname{ord}(a b)$ divides $m n$. Let $k = \operatorname{ord}(a b)$. Then $a^k = b^{-k}$. This element is in $\langle a \rangle \cap \langle b \rangle$, a subgroup whose order divides $m$ and $n$, by Lagrange's theorem. So the intersection is $\{1\}$, and $a^k = 1$ and $b^k = 1$. So $m \mid k$ and $n \mid k$, and $m n \mid k$ because $m$ and $n$ are coprime. So $k = m n$. $\square$

::: mathlib
`Commute.orderOf_mul_eq_mul_orderOf_of_coprime` · `Mathlib.GroupTheory.OrderOfElement`

The theorem for two commuting elements of a monoid. The hypothesis `Commute a b` is needed, as the counterexample below shows.

<?decl Commute.orderOf_mul_eq_mul_orderOf_of_coprime?>
:::

**Theorem ($A_4$ has no subgroup of order $6$).** The alternating group $A_4$, of order $12$, has no subgroup of order $6$.

*Proof.* The group $A_4$ has the identity, the three products of two disjoint transpositions, and the eight $3$-cycles: four choices of three points from four, and two cyclic orders on each choice. Assume that $H \le A_4$ has $6$ elements. Then $[A_4 : H] = 2$, so the left cosets are $H$ and its complement.

Step 1: for each $g \in A_4$, $g \in H$ or $g^2 \in H$. Let $g \notin H$. Then the cosets $H$ and $g H$ are the two cosets, and $g^2$ is in one of them. If $g^2 \in g H$, then $g \in H$ by cancellation, which is false. So $g^2 \in H$.

Step 2: each $3$-cycle $c$ is in $H$. Apply Step 1 to $g = c^2$. If $c^2 \in H$ then $c = c^4 = (c^2)^2 \in H$, since $c^3 = 1$. If $c^2 \notin H$, then $(c^2)^2 = c \in H$ by Step 1.

So $H$ contains the identity and the eight $3$-cycles, which are $9 > 6$ elements. This is a contradiction. $\square$

### Examples

**Example (Orders in $\mathbb{Z}/12$).** The additive order of $k$ in $\mathbb{Z}/12$ is $12 / \gcd(12, k)$, by the theorem on powers with $a = 1$. So $0$ has order $1$, $6$ has order $2$, $4$ and $8$ have order $3$, $3$ and $9$ have order $4$, $2$ and $10$ have order $6$, and $1, 5, 7, 11$ have order $12$. Each order divides $12$.

**Example (Fermat and Euler).** Modulo $7$: $3^1 = 3$, $3^2 = 2$, $3^3 = 6$, $3^4 = 4$, $3^5 = 5$, $3^6 = 1$. So $3$ has order $6$ in $(\mathbb{Z}/7)^\times$, and it generates the group. The element $2$ has $2^3 = 8 = 1$, so it has order $3$, which divides $6$. Modulo $10$, $\varphi(10) = 4$, and $3^4 = 81 \equiv 1$. So the last digit of $3^{2026}$ is the last digit of $3^{2026 \bmod 4} = 3^2 = 9$.

**Counterexample (The order of a product).** In $S_3$ the transpositions $(1\,2)$ and $(1\,3)$ have order $2$. Their product $(1\,2)(1\,3) = (1\,3\,2)$ has order $3$, not $4$ and not a divisor of $2$. In $D_n$ two reflections of order $2$ can have a product of order $n$. The theorem on products needs commuting elements. In the infinite group of the bijections of $\mathbb{Z}$, the reflections $x \mapsto -x$ and $x \mapsto 1 - x$ have order $2$, and their product is the shift $x \mapsto x + 1$ or $x \mapsto x - 1$, of infinite order.

**Example (Elements of finite order in an infinite group).** In $\mathbb{Q}/\mathbb{Z}$, the class of $1/n$ has order $n$. So the group is infinite while each element has finite order. In $(\mathbb{Z}, +)$ each element except $0$ has infinite order, and Mathlib gives `addOrderOf (1 : ℤ) = 0`.

**Example (The order in Lean).**

<?lean MathlibHandbook/V05/C04/Examples.lean#order_dvd?>

**Example (The power of the order of the group).**

<?lean MathlibHandbook/V05/C04/Examples.lean#pow_card?>

**Example (Positive order).**

<?lean MathlibHandbook/V05/C04/Examples.lean#order_pos?>

### The library around it

The file `Mathlib.GroupTheory.OrderOfElement` has the theory of the order in a monoid, in a cancellative monoid and in a group, with additive copies for `addOrderOf`. The lemma `orderOf_injective` says that an injective homomorphism keeps the order, and `orderOf_eq_one_iff` says that only $1$ has order $1$. The exponent of a group, the least common multiple of the orders, is `Monoid.exponent`. The number of elements of each order in a cyclic group is `IsCyclic.card_orderOf_eq_totient`.

Common errors of a learner:

- `orderOf a = 0` does not mean that $a = 1$. It means that $a$ has infinite order. The unit has `orderOf 1 = 1`.
- `orderOf` for an element of a subgroup `↥H` is the same number as for its value in `G`, but the two terms differ. The lemma `Subgroup.orderOf_coe` relates them.
- `orderOf_pow'` needs `n ≠ 0`, and the division in it is the division of natural numbers.

### Exercises

1. (A) Find the orders of all the elements of $D_4$.
2. (A) Show that $\operatorname{ord}(a) = \operatorname{ord}(a^{-1})$ and $\operatorname{ord}(g a g^{-1}) = \operatorname{ord}(a)$.
3. (B) Show that a group of even order has an element of order $2$. Hint: pair each element with its inverse.
4. (B) Show that a finite group whose elements all satisfy $x^2 = 1$ has order a power of $2$. Hint: the group is commutative by Chapter 1, so it is a vector space over $\mathbb{Z}/2$.
5. (B) Compute the last two digits of $7^{2026}$ with Euler's theorem.
6. (L) Prove that $x^{\operatorname{ord}(x)} = 1$. The solution is `pow_order_example`.
7. (L) Prove that $x^n = 1$ gives $\operatorname{ord}(x) \mid n$. The solution is `order_dvd_example`.
8. (L) Prove that $\operatorname{ord}(x) = 1$ if and only if $x = 1$. The solution is `order_one_example`.
9. (C) Show that a group of order $p^2$, with $p$ prime, has a subgroup of order $p$. Hint: take an element $a \neq 1$ and consider its order.

### Notes and history

Fermat stated his little theorem in a letter of 1640, without proof. Euler proved it in 1736 and gave the general form with $\varphi(n)$ in 1763. The proof by the order of the unit group is the one that group theory makes standard, and it is a direct consequence of Lagrange's theorem.

In Mathlib, `orderOf` is defined with `Function.minimalPeriod` of the map $x \mapsto a x$, the least period of an orbit of a dynamical system. This makes the definition work in each monoid and gives the convention `0` for infinite order at no cost.

### Reference

<?reference?>
