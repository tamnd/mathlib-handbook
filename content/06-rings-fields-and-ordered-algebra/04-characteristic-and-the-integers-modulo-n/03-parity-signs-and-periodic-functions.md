---
title: Parity, signs and periodic functions
kind: api
modules:
  - Mathlib.Algebra.Ring.Parity
  - Mathlib.Algebra.Ring.Int.Parity
  - Mathlib.Algebra.Ring.NegOnePow
  - Mathlib.Algebra.Ring.Periodic
explains:
  E2: [Odd, neg_one_pow_eq_ite, Odd.neg_pow, isUnit_two_iff_forall_even, Int.negOnePow, Int.negOnePow_add, Function.Periodic, Function.Antiperiodic, Function.Antiperiodic.periodic_two_mul, Function.Periodic.lift]
  E1: auto
families: []
requires: [V05.C01, V06.C01, V06.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Parity, signs and periodic functions

### Overview

An element $a$ of a semiring is even if $a = r + r$ for some $r$, and odd if $a = 2 r + 1$ for some $r$. Volume 5 defines `Even` for any additive structure, as the additive form of a square. The odd elements need both addition and the unit, so `Odd` lives in the ring part of the library. For the integers and the natural numbers each element is even or odd and not both, and parity is the residue modulo $2$, so this section sits next to the characteristic and $\mathbb{Z}/n$.

Parity controls the sign $(-1)^n$, and the section treats this sign as a function from $\mathbb{Z}$ to the units $\{\pm 1\}$. The last part treats periodic and antiperiodic functions on a ring, $f(x + c) = f(x)$ and $f(x + c) = -f(x)$. These are the functions on the circle $\mathbb{R}/c\mathbb{Z}$, and parity enters through the fact that an antiperiodic function is periodic with period $2c$.

### The library around it

#### Even and odd elements of a semiring

The predicate `Odd a` holds when $a = 2 k + 1$ for some $k$, and `odd_iff_exists_bit1` restates this. For even elements, `even_iff_two_dvd` gives $\mathrm{Even}\, a \iff 2 \mid a$ in a semiring, and `even_iff_exists_two_mul` gives the form $a = 2 r$. The module `Mathlib.Algebra.Ring.Parity` collects the arithmetic: `Even.add_odd`, `Odd.add_even` and `Odd.add_odd` for sums, `Even.mul_left`, `Even.mul_right` and `Odd.mul` for products, and `Odd.pow` for powers. The constants have their own lemmas, such as `even_two`, `odd_one`, `odd_neg_one` and `even_neg_two`.

A ring homomorphism preserves parity, by `Odd.map`, since it sends $2k + 1$ to $2 f(k) + 1$. In a ring of characteristic $2$, where $2 = 0$, each natural number cast is $0$ or $1$: `natCast_eq_zero_or_one_of_two_eq_zero`, with `natCast_eq_zero_of_even_of_two_eq_zero` and `natCast_eq_one_of_odd_of_two_eq_zero` for the two cases.

Parity is not exclusive in a general ring. In $\mathbb{Q}$ each element is even, since $a = a/2 + a/2$, and so each element is also odd. The lemma `isUnit_two_iff_forall_even` makes this precise: each element of a semiring is even if and only if $2$ is a unit.

*Proof.* If $2$ is a unit, then $a = 2 \cdot (2^{-1} a)$ for each $a$, so $a$ is even. Conversely, if $1$ is even, then $1 = r + r$ for some $r$. This gives $r \cdot 2 = r + r = 1$ and $2 \cdot r = r + r = 1$, so $r$ is a two-sided inverse of $2$. $\square$

#### Parity in the natural numbers and the integers

For $\mathbb{N}$ the module `Mathlib.Algebra.Ring.Parity` has the basic dichotomy: `Nat.even_or_odd`, `Nat.even_xor_odd`, `Nat.not_even_iff_odd` and `Nat.not_odd_iff_even`. The link to the residue is `Nat.odd_iff`, which says $n$ is odd if and only if $n \% 2 = 1$. Parity of a sum or product follows truth tables: `Nat.even_add'` and `Nat.odd_add` for sums, and `Nat.odd_mul` says that $m n$ is odd if and only if both factors are odd. The predicates are decidable, so `decide` proves a parity statement about a numeral.

The module `Mathlib.Algebra.Ring.Int.Parity` gives the same API for $\mathbb{Z}$, with names such as `Int.even_or_odd`, `Int.odd_iff`, `Int.odd_mul` and `Int.natAbs_even`, which says that $n$ and $|n|$ have the same parity. It also has a few number theoretic facts. A product of consecutive integers is even, by `Int.even_mul_succ_self`. A square is $0$ or $1$ modulo $4$, by `Int.sq_emod_four`. The square of an odd number is $1$ modulo $8$.

**Proposition.** If $k$ is odd, then $8 \mid k^2 - 1$.

*Proof.* Write $k = 2 m + 1$. Then $k^2 - 1 = 4 m^2 + 4 m = 4 m (m + 1)$. One of $m$ and $m + 1$ is even, so $m(m+1) = 2 j$ and $k^2 - 1 = 8 j$. $\square$

The lemmas are `Nat.eight_dvd_sq_sub_one_of_odd` and `Int.eight_dvd_sq_sub_one_of_odd`. A related fact, `Int.four_dvd_add_or_sub_of_odd`, says that for odd $a$ and $b$ one of $a + b$ and $a - b$ is divisible by $4$.

#### Signs: the powers of minus one

For $n \in \mathbb{N}$ the power $(-1)^n$ depends only on the parity of $n$. In any monoid with a distributive negation, `neg_one_pow_eq_ite` states $(-1)^n = 1$ if $n$ is even and $-1$ otherwise. The two cases are `Even.neg_one_pow` and `Odd.neg_one_pow`. More generally, `Even.neg_pow` gives $(-a)^n = a^n$ for even $n$, and `Odd.neg_pow` gives $(-a)^n = -a^n$ for odd $n$. The lemma `neg_one_pow_eq_one_iff_even` needs $-1 \ne 1$, so it fails in characteristic $2$.

A consequence of `Odd.neg_pow` is the factor theorem for odd powers. If $a + b = 0$ and $n$ is odd, then $a^n + b^n = 0$, by `Odd.pow_add_pow_eq_zero`: $b = -a$ gives $b^n = -a^n$. Parity also controls iterates of an involution: `Function.Involutive.iterate_even` and `Function.Involutive.iterate_odd` say that $f^{[n]}$ is the identity for even $n$ and $f$ for odd $n$.

For an integer exponent the module `Mathlib.Algebra.Ring.NegOnePow` defines `Int.negOnePow n`, the sign $(-1)^n$ as a unit of $\mathbb{Z}$. The value is a unit, not an integer, so it lives in a group, and `Int.negOnePow_def` unfolds it to the power of $-1$ in $\mathbb{Z}^\times$. It turns sums into products, by `Int.negOnePow_add`, so $n \mapsto (-1)^n$ is a homomorphism from the additive group $\mathbb{Z}$ to $\mathbb{Z}^\times$. Its kernel is the even integers: `Int.negOnePow_even`, `Int.negOnePow_odd` and `Int.negOnePow_eq_iff`, which says $(-1)^{n_1} = (-1)^{n_2}$ if and only if $n_1 - n_2$ is even. To use the sign in another ring, cast it: `Int.coe_negOnePow` gives the image $(-1)^{|n|}$ in a ring $R$.

#### Periodic and antiperiodic functions

A function $f : \alpha \to \beta$ is periodic with period $c$ if $f(x + c) = f(x)$ for all $x$. The predicate is `Function.Periodic f c`. It is antiperiodic with antiperiod $c$ if $f(x + c) = -f(x)$, which is `Function.Antiperiodic f c`. The sine function is antiperiodic with antiperiod $\pi$, and the exponential $t \mapsto e^{2\pi i t}$ is periodic with period $1$.

The module `Mathlib.Algebra.Ring.Periodic` proves that periods add, negate and scale by integers: `Function.Periodic.add_period`, `Function.Periodic.neg`, `Function.Periodic.nsmul` and `Function.Periodic.int_mul`. The functions with a given period are closed under the pointwise operations, by `Function.Periodic.add`, `Function.Periodic.mul` and `Function.Periodic.div`, and under composition with any function on the left, by `Function.Periodic.comp`. Finite sums and products of periodic functions are periodic, with `Finset.periodic_sum` and `Finset.periodic_prod`.

An antiperiodic function is periodic with twice the period: $f(x + 2c) = -f(x + c) = f(x)$. The lemma is `Function.Antiperiodic.periodic_two_mul`, and `Function.Antiperiodic.periodic` gives the same result with the period written $c + c$. Parity enters through the multiples of $c$: an odd multiple of an antiperiod is an antiperiod, by `Function.Antiperiodic.nat_odd_mul_antiperiodic`, and an even multiple is a period, by `Function.Antiperiodic.nat_even_mul_periodic`. The product of two antiperiodic functions is periodic, by `Function.Antiperiodic.mul`.

A periodic function on an additive group factors through the quotient by the multiples of the period. `Function.Periodic.lift` is this function on $\alpha / \mathbb{Z} c$, and `Function.Periodic.lift_coe` says that it agrees with $f$ on cosets. This is how a periodic function on $\mathbb{R}$ becomes a function on the circle $\mathbb{R}/c\mathbb{Z}$. A function with a nonzero period is not injective, by `Function.Periodic.not_injective`.

#### Common errors

1. In a general ring, `Even a` and `Odd a` are not exclusive. The lemmas `Nat.not_even_iff_odd` and `Int.not_even_iff_odd` hold only in $\mathbb{N}$ and $\mathbb{Z}$, and in $\mathbb{Q}$ each element is both even and odd.
2. `Int.negOnePow n` is a unit of $\mathbb{Z}$, not an integer. To compare it with $(-1)^n$ in a ring, first apply the coercion from units and then the cast, with `Int.coe_negOnePow`.
3. `Function.Periodic f c` with $c = 0$ is always true, by `Function.periodic_with_period_zero`. A hypothesis that $c \ne 0$ is needed for results such as `Function.Periodic.not_injective`.

### Exercises

1. (A) Prove that the sum of two odd integers is even, with `Odd.add_odd`.
2. (A) Show that $(-1)^n (-1)^n = 1$ for each $n \in \mathbb{N}$, by a case split on the parity of $n$.
3. (A) Show that $x \mapsto \cos x$ has period $2\pi$ and antiperiod $\pi$, given $\cos(x + \pi) = -\cos x$.
4. (B) Show that for each integer $n$, $n^2 \% 4$ is $0$ or $1$, and deduce that no integer $n$ with $n \% 4 = 3$ is a sum of two squares.
5. (B) Prove that $n \mapsto (-1)^n$ is a group homomorphism $\mathbb{Z} \to \mathbb{Z}^\times$ with kernel $2\mathbb{Z}$.
6. (C) Let $f : \mathbb{R} \to \mathbb{R}$ be continuous, periodic with periods $1$ and $\sqrt 2$. Prove that $f$ is constant.

### Reference

<?reference?>
