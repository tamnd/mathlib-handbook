---
title: The binary numerals PosNum, Num and ZNum
kind: api
modules:
  - Mathlib.Data.Num.Basic
  - Mathlib.Data.Num.Lemmas
  - Mathlib.Data.Num.ZNum
  - Mathlib.Data.Num.Bitwise
  - Mathlib.Data.Num.Prime
explains:
  E2: [Num.to_of_nat, Num.of_to_nat, Num.add_to_nat, Num.cmp_to_nat, Num.cast_le, Num.castNum_and, ZNum.to_of_int, ZNum.cast_add, PosNum.minFac_to_nat]
  E1: auto
families: []
requires: [V02.C01, V02.C02, V02.C03]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The binary numerals PosNum, Num and ZNum

### Overview

The type `ℕ` stores a number $n$ as $n$ applications of the successor to $0$. This form is good for induction, but a computation on it takes a number of steps that grows with the value of $n$, not with the number of its digits. The types of this section store a number by its bits. A computation on them takes a number of steps that grows with $\log_2 n$, and the kernel can evaluate it by reduction.

There are three types. The type `PosNum` holds the positive numbers. The type `Num` holds the natural numbers, as zero or a positive number. The type `ZNum` holds the integers, as zero, a positive number or the negative of a positive number. Each type has a cast to a general type $\alpha$, and the main lemmas say that the casts to `ℕ` and `ℤ` are bijections that respect the operations. With these lemmas, a statement about `Num` changes into a statement about `ℕ`, where the library of Chapter 1 applies, and the converse.

The modules are `Mathlib.Data.Num.Basic` (the types and the operations), `Mathlib.Data.Num.Lemmas` (the cast lemmas for `PosNum` and `Num`), `Mathlib.Data.Num.ZNum` (the cast lemmas for `ZNum`), `Mathlib.Data.Num.Bitwise` (the bitwise operations and the signed type `SNum`) and `Mathlib.Data.Num.Prime` (primality). The previous section gives the bits of a natural number, and this section uses the same words.

### The library around it

#### The three types

The type `PosNum` has three constructors: `PosNum.one` is the number $1$, and for a positive number $p$, `PosNum.bit0 p` is $2p$ and `PosNum.bit1 p` is $2p + 1$. So the number $6$ is `bit0 (bit1 one)`, read from the low bit to the high bit. Each positive number has exactly one such term, because the leading bit of a positive number is always $1$ and the constructor `PosNum.one` supplies it.

The type `Num` has the constructors `Num.zero` and `Num.pos`, so a term of `Num` is $0$ or a term of `PosNum`. The type `ZNum` has the constructors `ZNum.zero`, `ZNum.pos` and `ZNum.neg`, where `ZNum.neg p` is the number $-p$. The functions `PosNum.bit0`, `Num.bit0`, `Num.bit1`, `ZNum.bit0`, `ZNum.bit1` and `ZNum.bitm1` (the map $n \mapsto 2n - 1$) extend the constructors to all of the type. The functions `PosNum.bit` and `Num.bit` take a Boolean bit as the first argument, as `Nat.bit` does.

The definitions in `Mathlib.Data.Num.Basic` are structural recursions on the bits. For example, the sum of `bit1 p` and `bit1 q` is `bit0 (succ (p + q))`, which is the rule of school addition with a carry. The module defines the successor (`PosNum.succ`, `Num.succ`), the predecessor (`PosNum.pred'`, which takes values in `Num`), addition, multiplication, comparison (`PosNum.cmp`, `Num.cmp`, `ZNum.cmp`), subtraction (`PosNum.sub'` and `Num.sub'` with values in `ZNum`, and `Num.psub`, which gives none when the result is negative), division with remainder (`PosNum.divMod`, with `Num.div` and `Num.mod` as the instances of $/$ and $\%$), the greatest common divisor (`Num.gcd`, `ZNum.gcd`), the absolute value `ZNum.abs : ZNum → Num` and the length in bits (`Num.size : Num → Num` and `Num.natSize : Num → ℕ`).

#### The casts and the conversions from `ℕ` and `ℤ`

The function `castPosNum` sends a positive number to any type $\alpha$ with $1$ and $+$. It reads the bits from the top: one goes to $1$, `bit0 p` goes to $x + x$ and `bit1 p` goes to $x + x + 1$, where $x$ is the image of $p$. The functions `castNum` (for a type with $0$, $1$ and $+$) and `castZNum` (for a type with $0$, $1$, $+$ and negation) extend it. The coercion instances `posNumCoe`, `numNatCoe` and `znumCoe` connect these functions to the arrow $\uparrow$, so `(n : ℕ)` for `n : Num` is `castNum n`.

The other direction is from `ℕ` to `Num`. The coercion `(n : Num)` for `n : ℕ` uses the natural number cast structure of `Num`, which goes through the successor $n$ times. The function `Num.ofNat'` builds the same value bit by bit, by binary recursion on $n$ (`Num.ofNat'_bit`), and `Num.ofNat'_eq` says that the two are equal. For `PosNum` there is `PosNum.ofNat`, which sends $0$ to $1$ and is the identity on positive numbers. For `ZNum` the conversion from `ℤ` uses the integer cast, and `ZNum.ofInt'` is the fast form.

The two main lemmas for `Num` are

$$\mathrm{(to\_of\_nat)}\quad \uparrow(\uparrow n : \mathrm{Num}) = n \text{ for } n \in \mathbb{N}, \qquad \mathrm{(of\_to\_nat)}\quad \uparrow(\uparrow m : \mathbb{N}) = m \text{ for } m \in \mathrm{Num}.$$

These are `Num.to_of_nat` and `Num.of_to_nat`. Together they say that the cast `Num → ℕ` is a bijection with inverse the cast `ℕ → Num`. The lemma `Num.to_nat_inj` states the injectivity as an equivalence $\uparrow m = \uparrow n \leftrightarrow m = n$, and `Num.toNat_injective` states it as `Function.Injective castNum`. For `PosNum` the analogues are `PosNum.to_nat_inj`, `PosNum.of_to_nat` (the cast of $p$ to `ℕ` and back to `Num` is `Num.pos p`) and `PosNum.to_nat_pos`, which says that $0 < \uparrow p$. For `ZNum` the bijection with `ℤ` is `ZNum.to_of_int` and `ZNum.of_to_int`.

The cast to a general type $\alpha$ factors through `ℕ` or `ℤ`. The lemma `Num.cast_to_nat` says that the cast of $n$ to $\alpha$ is the cast of $\uparrow n : \mathbb{N}$ to $\alpha$ when $\alpha$ is an additive monoid with one. The lemmas `Num.cast_to_int` and `PosNum.cast_to_int` go through `ℤ`, and `Num.of_natCast` and `ZNum.of_intCast` go in the other direction. Each `Num` also gives a `ZNum` by `Num.toZNum`, and `Num.cast_toZNum` says that the two casts agree. The map `Num.toZNumNeg` gives the negative, and `Num.zneg_toZNum` says that $-\mathrm{toZNum}(n) = \mathrm{toZNumNeg}(n)$.

#### The operations commute with the casts

For each operation there is a lemma that says that the cast to `ℕ` (or to `ℤ`) carries it to the same operation in `ℕ` (or in `ℤ`). These lemmas have names that end in *to_nat* or *to_int*.

| Operation in `Num` | Lemma | Statement in `ℕ` |
|---|---|---|
| $m + n$ | `Num.add_to_nat` | $\uparrow(m + n) = \uparrow m + \uparrow n$ |
| $m \cdot n$ | `Num.mul_to_nat` | $\uparrow(m n) = \uparrow m \cdot \uparrow n$ |
| successor | `Num.succ_to_nat` | $\uparrow(\mathrm{succ}\, n) = \uparrow n + 1$ |
| $m - n$ (truncated) | `Num.sub_to_nat` | $\uparrow(m - n) = \uparrow m - \uparrow n$ |
| $m / n$ | `Num.div_to_nat` | $\uparrow(m / n) = \uparrow m / \uparrow n$ |
| $m \bmod n$ | `Num.mod_to_nat` | $\uparrow(m \% n) = \uparrow m \% \uparrow n$ |
| $\gcd(m, n)$ | `Num.gcd_to_nat` | $\uparrow \gcd(m, n) = \gcd(\uparrow m, \uparrow n)$ |
| $m \mid n$ | `Num.dvd_to_nat` | $\uparrow m \mid \uparrow n \leftrightarrow m \mid n$ |
| length in bits | `Num.size_to_nat`, `Num.natSize_to_nat` | the size of $\uparrow n$ in the sense of `Nat.size` |
| `Num.bit` | `Num.bit_to_nat` | $\uparrow(\mathrm{bit}\, b\, n) = \mathrm{bit}\, b\, (\uparrow n)$ |

The same lemmas exist for `PosNum`, for example `PosNum.add_to_nat`, `PosNum.mul_to_nat` and `PosNum.bit_to_nat`. For `ZNum` the statements are about `ℤ`: `ZNum.div_to_int`, `ZNum.mod_to_int`, `ZNum.abs_to_nat` (the absolute value goes to the natural absolute value of the integer) and `ZNum.gcd_to_nat`. The lemmas with general targets are `Num.cast_add`, `Num.cast_mul`, `Num.cast_succ`, `ZNum.cast_add`, `ZNum.cast_mul`, `ZNum.cast_zneg` and `ZNum.cast_succ`. They need a semiring or a ring structure on $\alpha$, because the statement $\uparrow(m + n) = \uparrow m + \uparrow n$ is false for a general type with $1$ and $+$.

The comparison `Num.cmp` gives a value of the core type *Ordering*. The lemma `Num.cmp_to_nat` says that the value of `Num.cmp m n` agrees with the order of $\uparrow m$ and $\uparrow n$ in `ℕ`: if it is *lt*, then $\uparrow m < \uparrow n$, if it is *eq*, then $m = n$, and if it is *gt*, then $\uparrow n < \uparrow m$. The order on `Num` is defined by the comparison (`Num.lt_iff_cmp`, `Num.le_iff_cmp`), and `Num.lt_to_nat` and `Num.le_to_nat` give the transfer to `ℕ`. For an ordered semiring $\alpha$, `Num.cast_le`, `Num.cast_lt` and `Num.cast_inj` say that the cast to $\alpha$ is an order embedding. For `ZNum` the lemmas are `ZNum.le_to_int`, `ZNum.cast_le`, `ZNum.cast_lt` and `ZNum.cast_inj`, with an ordered ring as the target.

#### The algebraic structures and the transfer method

The algebraic instances on these types are not proved directly from the definitions. Each axiom is a statement such as $m + n = n + m$. The proof applies `Num.to_nat_inj`, rewrites with the lemmas of the table to change the statement into the same statement in `ℕ`, and then uses the lemma for `ℕ`. The tactics `Num.transfer` and `PosNum.transfer` do these steps. This gives the instances `Num.commSemiring`, `Num.linearOrder` and `Num.isStrictOrderedRing` on `Num`, `PosNum.commMonoid`, `PosNum.addCommSemigroup`, `PosNum.distrib` and `PosNum.linearOrder` on `PosNum`, and `ZNum.commRing` and `ZNum.linearOrder` on `ZNum`. With these instances the general lemmas of Chapter 3 apply to `Num` and `ZNum` without new proofs.

The same method is the normal method for new results. To prove a statement about `Num`, rewrite it with the cast lemmas into a statement about `ℕ`, prove that statement, and change it back with `Num.to_nat_inj`. Do not do induction on the constructors of `Num` unless the statement is about the binary structure itself. The proof of `PosNum.succ'_pred'` (the predecessor and the successor are inverse) is one of the few statements where a proof by cases on the bits is natural.

The decidability instances work in the same way. The instance `Num.decidableDvd` decides $m \mid n$ by the test $n \bmod m = 0$, which is `Num.dvd_iff_mod_eq_zero`. The order and the equality are decidable through `Num.cmp`, so the decision takes a number of steps that grows with the number of bits.

#### Bitwise operations and the signed type `SNum`

The module `Mathlib.Data.Num.Bitwise` defines the bitwise operations on `PosNum` and `Num`. The functions `Num.land`, `Num.lor`, `Num.lxor` and `Num.ldiff` are the bitwise and, or, exclusive or and difference, and `Num.shiftl` and `Num.shiftr` are the shifts. They are also the instances of the notations `&&&`, `|||` and `^^^` and of the shift notations, as the lemmas `Num.land_eq_and` and `Num.lor_eq_or` state. The function `Num.testBit` gives the bit at a position, and `Num.oneBits` gives the list of the positions of the bits that are $1$.

The cast lemmas connect these operations with the bitwise operations on `ℕ` of the previous section. They are `Num.castNum_and`, `Num.castNum_or`, `Num.castNum_xor`, `Num.castNum_ldiff`, `Num.castNum_shiftLeft`, `Num.castNum_shiftRight` and `Num.castNum_testBit`. The first four have one common proof, from the general lemma `Num.castNum_eq_bitwise`, which applies to each operation that comes from a function $g$ on the bits with $g(\mathrm{false}, \mathrm{false}) = \mathrm{false}$.

The same module defines a type `SNum` of signed numbers in two's complement form, with the type `NzsNum` of the nonzero ones. A term of `SNum` is a finite list of bits followed by an infinite repetition of a sign bit: `SNum.zero false` is $0$ and `SNum.zero true` is $-1$, and `SNum.bit b p` puts the bit $b$ below $p$. The module defines `SNum.add`, `SNum.neg`, `SNum.testBit` and the cast `Int.ofSnum` to `ℤ`. The library has no cast lemmas for `SNum` like the ones for `ZNum`, so for proofs `ZNum` is the better choice.

#### Primality

The module `Mathlib.Data.Num.Prime` defines `Num.Prime` and `PosNum.Prime` as the primality of the cast to `ℕ` in the sense of `Nat.Prime` (Chapter 2 of this volume). The function `PosNum.minFac` computes the smallest prime factor by trial division on the binary form, and `Num.minFac` extends it to `Num`. The lemmas `PosNum.minFac_to_nat` and `Num.minFac_to_nat` say that these values are the casts of `Nat.minFac`. With them, the instances `PosNum.decidablePrime` and `Num.decidablePrime` decide primality with the test "$n > 1$ and the smallest prime factor of $n$ is $n$".

#### Common errors

1. Two different coercions. For `n : ℕ`, the term `((n : Num) : ℕ)` is a cast to `Num` followed by a cast back. It is equal to $n$ only after the rewrite `Num.to_of_nat`. This lemma is not a simp lemma, but the simp tactic closes the goal with `Num.of_natCast` at the target `ℕ`. A statement where the casts go in the other order needs `Num.of_to_nat`. If a goal shows a cast that does not simplify, find which of the two directions it is.
2. The general cast needs structure. The lemma `Num.cast_add` needs a semiring as the target. For a type that has only $0$, $1$ and $+$, the cast is defined but it does not respect addition, and the rewrite does not apply. Examine the instances of the target before the rewrite, or prove the statement in `ℕ` and use `Num.cast_to_nat` for an additive monoid with one.
3. Truncated and signed subtraction. The subtraction $m - n$ on `Num` is truncated at $0$, as in `ℕ`, and `Num.sub_to_nat` is a statement about truncated subtraction in `ℕ`. The function `Num.sub'` gives the true difference as a `ZNum`, and its cast lemma `Num.cast_sub'` is a statement in a ring.

### Exercises

1. (A) Write the numbers $5$, $8$ and $13$ as terms of `PosNum` with the constructors `PosNum.one`, `PosNum.bit0` and `PosNum.bit1`. Then write $-13$ as a term of `ZNum`.
2. (A) Use `Num.add_to_nat`, `Num.mul_to_nat` and `Num.to_nat_inj` to prove that $m \cdot (n + k) = m n + m k$ for `m n k : Num`, without the instance `Num.commSemiring`.
3. (B) Prove that the cast `Num → ℕ` is a bijection, and give its inverse. Use `Num.to_of_nat` and `Num.of_to_nat`. Then state the same result for `ZNum` and `ℤ`.
4. (B) The sum of `bit1 p` and `bit1 q` in `PosNum` is `bit0 (succ (p + q))`. Prove the equation $(2p + 1) + (2q + 1) = 2((p + q) + 1)$ in `ℕ`, and explain why this proves the rule after the cast with `PosNum.add_to_nat`.
5. (B) Use `Num.castNum_and` and `Num.castNum_testBit` to show that for `m n : Num` the bit at position $i$ of $m$ `&&&` $n$ is the conjunction of the bits at position $i$ of $m$ and $n$. Use the lemma for `ℕ` of the previous section.
6. (C) Explain why `Num.dvd_to_nat` and `Num.dvd_iff_mod_eq_zero` give a decision procedure for $m \mid n$ whose number of steps grows with the number of bits of $m$ and $n$, while the same test on `ℕ` with the unary form grows with the values. Then explain why `Num.decidablePrime` needs `Num.minFac_to_nat` to be correct.

### Reference

<?reference?>
