---
title: Tropical semirings
kind: api
modules:
  - Mathlib.Algebra.Tropical.Basic
  - Mathlib.Algebra.Tropical.BigOperators
  - Mathlib.Algebra.Tropical.Lattice
explains:
  E2: [MinTropical, MinTropical.untrop_add, MinTropical.trop_add, MinTropical.add_self, MinTropical.add_pow, MinTropical.instCommSemiring, MinTropical.mul_eq_zero_iff, MinTropical.trop_sum, MinTropical.Finset.untrop_sum']
  E1: auto
families: []
requires: [V03.C06, V04.C08]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Tropical semirings

### Overview

Let $R$ be a linearly ordered additive monoid, such as $\mathbb{Z}$ or $\mathbb{R}$. Define two new operations on $R$:

$$x \oplus y = \min(x, y), \qquad x \otimes y = x + y.$$

The tropical product $\otimes$ is the old sum, and the tropical sum $\oplus$ is the minimum. Both are associative and commutative, and $\otimes$ distributes over $\oplus$, because $x + \min(y, z) = \min(x + y, x + z)$. The neutral element of $\otimes$ is $0$. A neutral element for $\oplus$ must be at least each element, so it is a top element $\top$. With a top, the structure is a commutative semiring: the min-tropical semiring.

This semiring is a monoid of a new kind. Its addition is idempotent, $x \oplus x = x$, so no element except the zero has an additive inverse. Tropical algebra turns problems about polynomials into problems about piecewise linear functions: a tropical polynomial $\bigoplus_i a_i \otimes x^{\otimes i}$ is the function $x \mapsto \min_i (a_i + i x)$. Shortest paths in a graph are matrix powers over this semiring. The modules of this section build the semiring in Mathlib, with its order and its finite sums.

### The library around it

#### The type and the two maps

The type `MinTropical` of $R$ is a type synonym: it has the same elements as $R$. The map `MinTropical.trop` sends $x$ in $R$ to the same element in the new type, and `MinTropical.untrop` goes back. The type `MaxTropical` is the dual construction, with $\max$ for the sum. The declarations about `MaxTropical` come from the declarations about `MinTropical` by the attribute `to_dual`, which swaps $\min$ and $\max$, $\top$ and $\bot$, and the names.

The two maps are inverse bijections, and the library gives them in each useful form.

| Lean name | Statement |
|---|---|
| `MinTropical.untrop_trop` | $\mathrm{untrop}(\mathrm{trop}\ x) = x$ |
| `MinTropical.trop_untrop` | $\mathrm{trop}(\mathrm{untrop}\ x) = x$ |
| `MinTropical.trop_inj_iff` | $\mathrm{trop}\ x = \mathrm{trop}\ y \iff x = y$ |
| `MinTropical.untrop_inj_iff` | $\mathrm{untrop}\ x = \mathrm{untrop}\ y \iff x = y$ |
| `MinTropical.tropEquiv` | the bijection as an equivalence |
| `MinTropical.tropOrderIso` | the bijection as an order isomorphism |
| `MinTropical.tropRec` | a recursor: to prove a statement for each element, prove it for $\mathrm{trop}\ x$ |

The order on the new type is the order of $R$: `MinTropical.untrop_le_iff` says that $\mathrm{untrop}\ x \le \mathrm{untrop}\ y \iff x \le y$, and `MinTropical.trop_monotone` says that the map is monotone. The instance `MinTropical.instLinearOrder` carries a linear order.

#### Tropical addition

The sum of the new type is the minimum. The instance needs only a linear order on $R$.

| Lean name | Statement |
|---|---|
| `MinTropical.untrop_add` | $\mathrm{untrop}(x + y) = \min(\mathrm{untrop}\ x, \mathrm{untrop}\ y)$ |
| `MinTropical.trop_min` | $\mathrm{trop}(\min(x, y)) = \mathrm{trop}\ x + \mathrm{trop}\ y$ |
| `MinTropical.trop_add_def` | $x + y = \mathrm{trop}(\min(\mathrm{untrop}\ x, \mathrm{untrop}\ y))$ |
| `MinTropical.min_eq_add` | on the new type, $\min$ is the sum |
| `MinTropical.add_eq_left` | if $x \le y$, then $x + y = x$ |
| `MinTropical.add_eq_iff` | $x + y = z$ if and only if $x = z$ and $x \le y$, or $y = z$ and $y \le x$ |
| `MinTropical.add_self` | $x + x = x$ |
| `MinTropical.succ_nsmul` | $(n + 1) \cdot x = x$ for each natural number $n$ |

The proof of `MinTropical.add_self` is $\min(x, x) = x$. Then `MinTropical.succ_nsmul` follows by induction on $n$: $(n + 2) \cdot x = (n + 1) \cdot x + x = x + x = x$. So the additive monoid is far from a group. If $x + y = \top$ in a tropical semiring, then $\min(x, y) = \top$, so $x = y = \top$. This is `MinTropical.add_eq_zero_iff` for the type `WithTop`.

The zero of the new type is $\mathrm{trop}\ \top$, by the instance `MinTropical.instZeroOfTop`, with `MinTropical.untrop_zero` and `MinTropical.trop_top`. With a top element on $R$, the instance `MinTropical.instAddCommMonoidOfOrderTop` gives a commutative additive monoid. In the order, the zero is the largest element: `MinTropical.le_zero` says $x \le 0$ for each $x$. This is the reverse of the usual picture, and it is a frequent source of confusion.

#### Tropical multiplication

The product of the new type is the sum of $R$, and the one is the zero of $R$.

| Lean name | Statement |
|---|---|
| `MinTropical.trop_add` | $\mathrm{trop}(x + y) = \mathrm{trop}\ x \cdot \mathrm{trop}\ y$ |
| `MinTropical.untrop_mul` | $\mathrm{untrop}(x y) = \mathrm{untrop}\ x + \mathrm{untrop}\ y$ |
| `MinTropical.trop_mul_def` | $x y = \mathrm{trop}(\mathrm{untrop}\ x + \mathrm{untrop}\ y)$ |
| `MinTropical.trop_zero` | $\mathrm{trop}\ 0 = 1$ |
| `MinTropical.untrop_one` | $\mathrm{untrop}\ 1 = 0$ |
| `MinTropical.untrop_inv` | $\mathrm{untrop}(x^{-1}) = -\mathrm{untrop}\ x$ |
| `MinTropical.untrop_div` | $\mathrm{untrop}(x / y) = \mathrm{untrop}\ x - \mathrm{untrop}\ y$ |
| `MinTropical.untrop_pow` | $\mathrm{untrop}(x^n) = n \cdot \mathrm{untrop}\ x$ |
| `MinTropical.trop_nsmul` | $\mathrm{trop}(n \cdot x) = (\mathrm{trop}\ x)^n$ |
| `MinTropical.trop_zsmul` | the same for an integer $n$ in an additive group |

The multiplicative structure copies the additive structure of $R$, one class at a time. An additive monoid gives a monoid (`MinTropical.instMonoidOfAddMonoid`), an additive commutative monoid a commutative monoid (`MinTropical.instCommMonoidOfAddCommMonoid`), and an additive group a group (`MinTropical.instGroupOfAddGroup`). The instance `MinTropical.instPowOfSMul` turns the scalar multiple $n \cdot x$ into the power $x^n$. So, on the multiplicative side, `MinTropical.trop` does what the type synonym `Multiplicative` does: it writes the sum of $R$ as a product. The ordered classes go along too: `MinTropical.mulLeftMono` says that the product is monotone when the sum of $R$ is monotone.

#### The semiring

The distributive law needs a linear order and a monotone sum on $R$. The instance `MinTropical.instDistribOfAddLeftMonoOfAddRightMono` states

$$x \otimes (y \oplus z) = (x \otimes y) \oplus (x \otimes z),$$

which is $x + \min(y, z) = \min(x + y, x + z)$ in $R$. Its proof: if $y \le z$, then $x + y \le x + z$, and both sides are $x + y$. The other case is the same.

The class `LinearOrderedAddCommMonoidWithTop` collects the hypotheses for the full semiring: a linearly ordered commutative additive monoid with a top element $\top$ such that $\top + x = \top$. The instance `MinTropical.instCommSemiring` makes the new type a commutative semiring. The zero laws $0 \otimes x = 0$ hold because $\top + x = \top$. The type `WithTop` of an ordered cancellative additive monoid, such as the integers or the reals with a top added, satisfies the hypotheses by the instance `WithTop.linearOrderedAddCommMonoidWithTop`.

On this type the semiring has no zero divisors. The lemma `MinTropical.mul_eq_zero_iff` says that $a b = 0$ if and only if $a = 0$ or $b = 0$. Its proof: $a b = 0$ means $\mathrm{untrop}\ a + \mathrm{untrop}\ b = \top$ in the type `WithTop`, and a sum there is $\top$ only if one of its terms is $\top$. The instance `MinTropical.instNoZeroDivisorsWithTop` records this.

The binomial theorem has a simple form, the freshman's dream. The lemma `MinTropical.add_pow` says

$$(x \oplus y)^{\otimes n} = x^{\otimes n} \oplus y^{\otimes n}.$$

The proof uses the order. Suppose $x \le y$. Then $x \oplus y = x$, and $x^n \le y^n$ because the product is monotone, so the right side is $x^n$ too. The other case is the same. In usual notation, $n \min(x, y) = \min(n x, n y)$.

The isomorphism `MinTropical.equivMaxTropical` exchanges the two constructions: the min-tropical structure on $R$ is the max-tropical structure on the order dual of $R$. It is an isomorphism for both operations. The inverse direction is `MaxTropical.equivMinTropical`. For `MaxTropical`, the zero is $\bot$, by `MaxTropical.trop_bot`, and the sum is the maximum, by `MaxTropical.untrop_add`.

#### Finite sums and products

The module `Mathlib.Algebra.Tropical.BigOperators` converts the finite sums and products of Volume 3 into minima and sums of $R$.

| Lean name | Statement |
|---|---|
| `MinTropical.trop_sum` | $\mathrm{trop}(\sum_{i \in s} f(i)) = \prod_{i \in s} \mathrm{trop}(f(i))$ |
| `MinTropical.untrop_prod` | $\mathrm{untrop}(\prod_{i \in s} f(i)) = \sum_{i \in s} \mathrm{untrop}(f(i))$ |
| `MinTropical.Finset.trop_inf` | $\mathrm{trop}(\inf_{i \in s} f(i)) = \sum_{i \in s} \mathrm{trop}(f(i))$ |
| `MinTropical.Finset.untrop_sum'` | $\mathrm{untrop}(\sum_{i \in s} f(i)) = \inf_{i \in s} \mathrm{untrop}(f(i))$ |
| `MinTropical.untrop_sum_eq_sInf_image` | the same, as the infimum of the image set, for values in `WithTop` |
| `MinTropical.trop_iInf` | $\mathrm{trop}(\inf_i f(i)) = \sum_i \mathrm{trop}(f(i))$ over a finite type |
| `MinTropical.List.trop_minimum` | the minimum of a list is the tropical sum of its entries |
| `MinTropical.Multiset.trop_inf` | the same for a multiset |

The first two lemmas are the statement that `MinTropical.trop` is a monoid homomorphism, applied to a finite product. The proofs are inductions on the finite set: the empty sum goes to the empty product, and one step uses `MinTropical.trop_add`. The second pair is the same induction with `MinTropical.untrop_add` and the infimum of a finite set. With these lemmas, the value of a tropical polynomial at a point is the minimum of the linear functions $a_i + i x$, which is the reason for the theory.

#### The order structures

The module `Mathlib.Algebra.Tropical.Lattice` copies the order structures of $R$ to the new type, with the same order. The instances are `MinTropical.instLattice`, `MinTropical.instSemilatticeInf`, `MinTropical.instSemilatticeSup`, `MinTropical.instSupSet`, `MinTropical.instInfSet`, `MinTropical.instConditionallyCompleteLattice` and `MinTropical.instConditionallyCompleteLinearOrder`. The supremum of a set of tropical elements is the image of the supremum of their images in $R$. The lemma `MinTropical.untrop_sup` states this for two elements: the maximum in the new type is the maximum in $R$. The proofs use the order isomorphism `MinTropical.tropOrderIso`.

#### Common errors

1. The sum of `MinTropical` is the minimum, and the zero is the top element. So `MinTropical.le_zero` holds: each element is at most the zero. A proof that uses $0 \le x$ from the base type is wrong in the new type.
2. Do not unfold the type synonym. Move between $R$ and the new type with `MinTropical.trop` and `MinTropical.untrop` and their simp lemmas. A proof by definition can work, but then simp does not see the structure.
3. The semiring instance needs a top on $R$. For $R = \mathbb{Z}$, use the type `WithTop` of the integers. The type `MinTropical` of the integers has no zero and is not a semiring.

### Exercises

1. (A) Compute in the min-tropical semiring of the integers with a top: $3 \oplus 5$, $3 \otimes 5$, $(2 \oplus 7) \otimes 4$ and $2^{\otimes 3}$.
2. (A) Use `MinTropical.add_self` to show that a nonzero element of a tropical semiring has no additive inverse.
3. (B) Show that the tropical polynomial $x^{\otimes 2} \oplus (1 \otimes x) \oplus 3$ over the reals is the function $x \mapsto \min(2x, x + 1, 3)$. Find the points where the minimum is attained twice.
4. (B) Prove the identity of `MinTropical.add_pow` for $n = 2$ directly from the distributive law, without the order argument.
5. (B) Let $A$ be the matrix of edge lengths of a weighted graph, with $\top$ when there is no edge and $0$ on the diagonal. Prove that the tropical square of $A$ gives the length of the shortest path with at most two edges.
6. (C) Prove that the min-tropical and the max-tropical structures on $\mathbb{Z}$ are isomorphic, with the map $x \mapsto -x$, and compare with `MinTropical.equivMaxTropical`.

### Reference

<?reference?>
