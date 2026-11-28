---
title: Intervals, logarithms, square roots, bits and Fibonacci numbers in ℤ
kind: api
modules:
  - Mathlib.Data.Int.Interval
  - Mathlib.Data.Int.CardIntervalMod
  - Mathlib.Data.Int.Range
  - Mathlib.Data.Int.Log
  - Mathlib.Data.Int.Sqrt
  - Mathlib.Data.Int.Bitwise
  - Mathlib.Data.Int.Fib.Basic
  - Mathlib.Data.Int.Fib.Lemmas
explains:
  E2: [Int.card_Icc, Int.Ico_filter_dvd_card, Int.zpow_log_le_self, Int.neg_log_inv_eq_clog, Int.exists_mul_self, Int.testBit_bitwise, Int.fib_neg_natCast, Int.fib_add]
  E1: auto
families: []
requires: [V02.C01, V02.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Intervals, logarithms, square roots, bits and Fibonacci numbers in ℤ

### Overview

The first two sections of this chapter build `ℤ` and its congruences. This section collects the functions on `ℤ` that a proof uses after that. Each module of the section takes a construction on `ℕ` and extends it to all integers. The finite intervals $[a, b]$ of $\mathbb{Z}$ are images of the ranges $\{0, \dots, n - 1\}$ of $\mathbb{N}$. The logarithm with an integer value extends the logarithm `Nat.log` to the positive elements of an ordered field. The integer square root, the binary operations and the Fibonacci numbers extend their versions on `ℕ` to the negative integers.

The extensions follow one pattern. The definition on `ℤ` reduces to the definition on `ℕ`, through a case split on the sign or through the truncation to `ℕ`. A lemma with a name such as `Int.fib_natCast` or `Int.log_natCast` states that the new function agrees with the old one on the casts of natural numbers. The other lemmas give the behaviour on the negative side and the junk values.

### The library around it

#### Finite intervals

The instance `Int.instLocallyFiniteOrder` makes `ℤ` a locally finite order. So the finite sets `Finset.Icc a b`, `Finset.Ico a b`, `Finset.Ioc a b`, `Finset.Ioo a b` and `Finset.uIcc a b` exist for all integers $a$ and $b$. The module `Mathlib.Data.Int.Interval` defines each of them as the image of a range of `ℕ` under a translation. For example, `Int.Icc_eq_finset_map` states

$$[a, b] = \{a + k : k \in \mathbb{N},\ k < \max(b + 1 - a, 0)\},$$

and `Int.Ico_eq_finset_map`, `Int.Ioc_eq_finset_map`, `Int.Ioo_eq_finset_map` and `Int.uIcc_eq_finset_map` are the same for the other intervals. The embedding is `Nat.castEmbedding` composed with `addLeftEmbedding`.

The cardinalities follow from these descriptions. The cardinality of a finite set is a natural number, but $b + 1 - a$ is an integer that can be negative. The library gives two forms for each interval.

| Lean name | Statement |
|---|---|
| `Int.card_Icc` | $\#[a, b] = \operatorname{toNat}(b + 1 - a)$ |
| `Int.card_Ico` | $\#[a, b) = \operatorname{toNat}(b - a)$ |
| `Int.card_Ioc` | $\#(a, b] = \operatorname{toNat}(b - a)$ |
| `Int.card_Ioo` | $\#(a, b) = \operatorname{toNat}(b - a - 1)$ |
| `Int.card_uIcc` | $\#[\min(a, b), \max(a, b)] = \lvert b - a \rvert + 1$ |
| `Int.card_Icc_of_le` | $a \leq b + 1 \Rightarrow \#[a, b] = b + 1 - a$ in `ℤ` |
| `Int.card_Ico_of_le` | $a \leq b \Rightarrow \#[a, b) = b - a$ in `ℤ` |
| `Int.card_Ioo_of_lt` | $a < b \Rightarrow \#(a, b) = b - a - 1$ in `ℤ` |

Here $\operatorname{toNat}(z) = \max(z, 0)$ is the truncation of `ℤ` to `ℕ`. The forms with `_of_le` cast the cardinality to `ℤ` and state an equation in `ℤ`, so `ring` and `omega` can use them. The lemmas `Int.card_fintype_Icc_of_le` and its variants state the same for the cardinality of the subtype `Set.Icc a b` as a `Fintype`.

*Proof of `Int.card_Icc`.* By `Int.Icc_eq_finset_map`, $[a, b]$ is the image of $\{0, \dots, n - 1\}$ with $n = \operatorname{toNat}(b + 1 - a)$ under $k \mapsto a + k$. This map is injective. An injective image of a finite set has the same cardinality, and the range has $n$ elements. $\square$

`Int.Icc_eq_pair` states $[a, a + 1] = \{a, a + 1\}$. `Int.image_Ico_emod` states that the remainders modulo $a > 0$ of the $a$ consecutive integers $n, \dots, n + a - 1$ are exactly $0, \dots, a - 1$.

The module `Mathlib.Data.Int.Range` gives an older form of the same idea: the list `Int.range m n` of the integers $r$ with $m \leq r < n$, with the lemma `Int.mem_range_iff`. Its main use is decidability. The instances `Int.decidableLELT`, `Int.decidableLELE`, `Int.decidableLTLT` and `Int.decidableLTLE` decide a statement of the form $\forall r,\ m \leq r < n \Rightarrow P(r)$ for a decidable predicate $P$, so `decide` proves such a statement for numerals.

#### Counting in residue classes

The module `Mathlib.Data.Int.CardIntervalMod` counts the elements of an interval in one residue class. The answer uses the floor and the ceiling of rational numbers.

**Theorem.** For $r > 0$, the number of multiples of $r$ in $[a, b)$ is $\max(\lceil b/r \rceil - \lceil a/r \rceil, 0)$.

*Proof.* A multiple $x = r m$ is in $[a, b)$ if and only if $a/r \leq m < b/r$, that is, $\lceil a/r \rceil \leq m < \lceil b/r \rceil$. So $m \mapsto r m$ is a bijection from $[\lceil a/r \rceil, \lceil b/r \rceil)$ to the multiples in $[a, b)$. The card lemma for `Finset.Ico` gives the count. $\square$

This is `Int.Ico_filter_dvd_card`, and `Int.Ico_filter_dvd_eq` is the bijection of the proof. For a half open interval $(a, b]$ the floors replace the ceilings: `Int.Ioc_filter_dvd_card` and `Int.Ioc_filter_dvd_eq`. A translation by $v$ moves the class of $v$ to the class of $0$, so `Int.Ico_filter_modEq_eq` and `Int.Ico_filter_modEq_card` count the $x \in [a, b)$ with $x \equiv v \pmod r$:

$$\#\{x \in [a, b) : x \equiv v \ (r)\} = \max\left(\left\lceil \frac{b - v}{r} \right\rceil - \left\lceil \frac{a - v}{r} \right\rceil, 0\right).$$

The versions for `ℕ` are `Nat.Ico_filter_modEq_card` and `Nat.Ioc_filter_modEq_card`. The lemmas `Nat.Ico_filter_modEq_cast` and `Nat.Ioc_filter_modEq_cast` transport the sets from `ℕ` to `ℤ`. The function `Nat.count` counts the $x < b$ with a property, and `Nat.count_modEq_card` gives $\#\{x < b : x \equiv v \ (r)\} = \lfloor b / r \rfloor + [v \bmod r < b \bmod r]$, where the bracket is $1$ if the condition holds and $0$ if not. The form `Nat.count_modEq_card_eq_ceil` gives the same number as one ceiling.

#### Logarithms with an integer value

Let $R$ be an ordered field with a floor function (a `FloorSemiring`), for example `ℚ` or `ℝ`, and let $b \geq 2$ be a natural number. The module `Mathlib.Data.Int.Log` defines two functions $R \to \mathbb{Z}$.

1. `Int.log b r` is the greatest $k \in \mathbb{Z}$ with $b^k \leq r$.
2. `Int.clog b r` is the least $k \in \mathbb{Z}$ with $r \leq b^k$.

The definition reduces to `ℕ`. If $r \geq 1$, `Int.log b r` is `Nat.log b ⌊r⌋₊`. If $r < 1$, it is $-$`Nat.clog b ⌈r⁻¹⌉₊`. The function `Int.clog` has the dual definition. The junk value is $0$: `Int.log_of_right_le_zero` for $r \leq 0$, and `Int.log_of_left_le_one` for $b \leq 1$. The equations `Int.log_of_one_le_right` and `Int.log_of_right_le_one` unfold the definition, and `Int.log_natCast` and `Int.log_ofNat` state that `Int.log` agrees with `Nat.log` on natural numbers.

**Theorem.** For $b > 1$ and $r > 0$, $b^{\log_b r} \leq r < b^{\log_b r + 1}$.

*Proof of the first inequality.* Let $r \geq 1$ and $k = \operatorname{Nat.log}_b \lfloor r \rfloor$. Then $b^k \leq \lfloor r \rfloor \leq r$. Let $0 < r < 1$ and $k = \operatorname{Nat.clog}_b \lceil r^{-1} \rceil$. Then $r^{-1} \leq \lceil r^{-1} \rceil \leq b^k$, so $b^{-k} \leq r$. $\square$

The two halves are `Int.zpow_log_le_self` and `Int.lt_zpow_succ_log_self`. For `Int.clog` they are `Int.zpow_pred_clog_lt_self` and `Int.self_le_zpow_clog`. The lemma `Int.zpow_le_iff_le_log` is the form that a proof uses most: for $r > 0$, $b^x \leq r$ if and only if $x \leq \log_b r$. The dual is `Int.le_zpow_iff_clog_le`. These equivalences say that `Int.log` is a right adjoint of $k \mapsto b^k$ and `Int.clog` a left adjoint. The library packs them as a Galois coinsertion `Int.zpowLogGi` and a Galois insertion `Int.clogZPowGi`. Consequences are `Int.log_zpow` and `Int.clog_zpow`, which state $\log_b b^z = z$, and the monotonicity lemmas `Int.log_mono_right` and `Int.clog_mono_right`.

**Theorem.** For each $r$, $-\log_b(r^{-1}) = \operatorname{clog}_b(r)$.

*Proof for $r > 0$.* The integer $k$ satisfies $b^k \leq r^{-1}$ if and only if $r \leq b^{-k}$. So the greatest $k$ of the first kind is the negative of the least $-k$ of the second kind. For $r \leq 0$, both sides are $0$. $\square$

This is `Int.neg_log_inv_eq_clog`, with the twin `Int.neg_clog_inv_eq_log` and the forms `Int.log_inv` and `Int.clog_inv`. The value `Int.log 10 r` is the position of the first digit of $r$ that is not zero. For example, the logarithm of $0.09$ in base $10$ is $-2$ and the logarithm of $11$ is $1$.

#### The integer square root

The function `Int.sqrt` is the square root `Nat.sqrt` of the truncation of $z$ to `ℕ`. So it is $\lfloor \sqrt{z} \rfloor$ for $z \geq 0$, and the junk value $0$ for $z < 0$. The module has five lemmas. `Int.sqrt_nonneg` states that the value is not negative. `Int.sqrt_natCast` and `Int.sqrt_ofNat` reduce to `Nat.sqrt`. `Int.sqrt_eq` states $\operatorname{sqrt}(n \cdot n) = \lvert n \rvert$. The main lemma is the test for squares.

**Theorem.** An integer $x$ is a square if and only if $\operatorname{sqrt}(x)^2 = x$.

*Proof.* If $\operatorname{sqrt}(x)^2 = x$, then $x$ is a square. If $x = n \cdot n$, then `Int.sqrt_eq` gives $\operatorname{sqrt}(x) = \lvert n \rvert$, and $\lvert n \rvert^2 = n^2 = x$. $\square$

This is `Int.exists_mul_self`. The function `Int.sqrt` computes, so `#eval` gives its values. The rational square root `Rat.sqrt` of Chapter 4 uses `Int.sqrt` on the numerator.

#### Bits of an integer

Lean stores an integer with two constructors, one for $n \geq 0$ and one for $-(n + 1)$, but a bitwise operation needs the binary form. The module `Mathlib.Data.Int.Bitwise` treats an integer as an infinite sequence of bits in two's complement. A number $n \geq 0$ has finitely many bits $1$. A number $n < 0$ has finitely many bits $0$, because $-1$ has all its bits equal to $1$.

The basic functions are the following.

1. `Int.bodd n` is the last bit, `true` if $n$ is odd. The lemmas `Int.bodd_add` and `Int.bodd_mul` state that it sends a sum to the `xor` of the bits and a product to their `&&`.
2. `Int.div2 n` is $\lfloor n/2 \rfloor$, by `Int.div2_val`.
3. `Int.bit b n` is $2 n + b$, by `Int.bit_val`. The lemma `Int.bit_decomp` states `Int.bit n.bodd n.div2 = n`.
4. `Int.bitCasesOn` is a recursor: to prove $P(n)$ for each $n$, it is enough to prove $P(2m + b)$ for each $m$ and each bit $b$.

The operations `Int.lnot`, `Int.land`, `Int.lor`, `Int.xor` and `Int.ldiff` are the complement, the bitwise and, or, xor and the difference $m \wedge \neg n$. The complement of $n$ is $-n - 1$. The general form is `Int.bitwise f m n` for a function $f$ of two bits, and `Int.bitwise_and`, `Int.bitwise_or`, `Int.bitwise_xor` and `Int.bitwise_diff` identify the four cases. The definition splits on the signs. On two numbers $m, n \geq 0$, it computes the bitwise operation of `ℕ` and gives a negative result exactly when $f$ sends two bits $0$ to $1$, because then all the high bits of the result are $1$.

**Theorem.** For each $f$ and each position $k$, the bit $k$ of `Int.bitwise f m n` is $f$ applied to the bits $k$ of $m$ and $n$.

*Proof sketch.* The four cases of signs reduce to the same statement for `ℕ`, with the complement on the negative arguments. In two's complement, the bit $k$ of $-n - 1$ is the negation of the bit $k$ of $n$, and the definition applies $f$ to the negated bits. $\square$

This is `Int.testBit_bitwise`. Its corollaries `Int.testBit_land`, `Int.testBit_lor`, `Int.testBit_lxor`, `Int.testBit_ldiff` and `Int.testBit_lnot` give the bits of each operation. The lemmas `Int.land_bit`, `Int.lor_bit` and `Int.bitwise_bit` give the same facts in the recursive form `Int.bit`. The shifts are the instances `Int.instShiftLeft_mathlib` and `Int.instShiftRight_mathlib`, with a shift by an integer. A shift by a negative number goes the other way: `Int.shiftLeft_neg` and `Int.shiftRight_neg`. A left shift is a multiplication, `Int.shiftLeft_eq_mul_pow`, and `Int.one_shiftLeft` gives $1 \ll n = 2^n$.

#### Fibonacci numbers on ℤ

The recurrence $F_{n+2} = F_{n+1} + F_n$ runs backwards as $F_n = F_{n+2} - F_{n+1}$. So it has a unique extension to $\mathbb{Z}$. The values are $F_{-1} = 1$, $F_{-2} = -1$, $F_{-3} = 2$, $F_{-4} = -3$. The function `Int.fib` defines it from `Nat.fib`: for $n \geq 0$ it is `Nat.fib` of $n$, and for $n < 0$ it is $\pm F_{\lvert n \rvert}$ with a sign that depends on the parity of $n$.

**Theorem.** For $n \in \mathbb{N}$, $F_{-n} = (-1)^{n+1} F_n$.

*Proof.* For $n = 0$ both sides are $0$. For $n > 0$ the definition gives $-F_n$ if $n$ is even and $F_n$ if $n$ is odd, and this is $(-1)^{n+1} F_n$. $\square$

This is `Int.fib_neg_natCast`. The other forms are `Int.fib_neg`, with an `if` on `Even n`, and `Int.coe_fib_neg`. The recurrence holds on all of $\mathbb{Z}$: `Int.fib_add_two`, and its rearrangements `Int.fib_add_one` and `Int.fib_eq_fib_add_two_sub_fib_add_one`. With these lemmas, the identities of `Nat.fib` extend to $\mathbb{Z}$.

| Lean name | Statement |
|---|---|
| `Int.fib_add` | $F_{m+n} = F_{m-1} F_n + F_m F_{n+1}$ |
| `Int.fib_two_mul` | $F_{2n} = F_n (2 F_{n+1} - F_n)$ |
| `Int.fib_two_mul_add_one` | $F_{2n+1} = F_{n+1}^2 + F_n^2$ |
| `Int.fib_two_mul_add_two` | $F_{2n+2} = F_{n+1} (2 F_n + F_{n+1})$ |
| `Int.fib_dvd` | $m \mid n \Rightarrow F_m \mid F_n$ |
| `Int.gcd_fib` | $\gcd(F_m, F_n) = F_{\gcd(m, n)}$ |
| `Int.fib_eq_zero` | $F_n = 0 \iff n = 0$ |
| `Int.fib_succ_mul_fib_pred_sub_fib_sq` | $F_{n+1} F_{n-1} - F_n^2 = (-1)^{\lvert n \rvert}$ |
| `Int.fib_add_sq_sub_fib_mul_fib_add_two_mul` | $F_{x+a}^2 - F_x F_{x+2a} = (-1)^{\lvert x \rvert} F_a^2$ |

*Proof sketch of `Int.fib_add`.* Fix $m$. Both sides satisfy the Fibonacci recurrence in $n$, in both directions. So they agree for all $n$ as soon as they agree for $n = 0$ and $n = 1$. For $n = 0$ the right side is $F_m$. For $n = 1$ it is $F_{m-1} + F_m = F_{m+1}$. $\square$

The last two rows of the table are Cassini's identity and Catalan's identity, in `Mathlib.Data.Int.Fib.Lemmas`. On the odd integers $F_n$ is positive: `Int.fib_two_mul_add_one_pos`, and `Int.fib_of_odd` writes it with `Nat.fib`.

#### Common errors

1. `Int.card_Icc` gives a natural number with a truncation, not $b + 1 - a$. To compute in `ℤ`, use `Int.card_Icc_of_le` and prove $a \leq b + 1$ first.
2. `Int.log b r` and `Int.sqrt z` have the junk value $0$ for $r \leq 0$ and $z < 0$, and `Int.log` has it for $b \leq 1$. The bounds `Int.zpow_log_le_self` and `Int.lt_zpow_succ_log_self` need $1 < b$, and the first also needs $0 < r$.
3. The lemmas about bits refer to two's complement. The complement `Int.lnot n` is $-n - 1$, not $-n$, and a negative integer has infinitely many bits $1$.

### Exercises

1. (A) Use `Int.card_Ioo` to compute the cardinality of $(-3, 4)$ and of $(4, -3)$ in `ℤ`.
2. (A) Compute `Int.log 2 (3/16 : ℚ)` and `Int.clog 2 (3/16 : ℚ)` from the definitions, and check the bounds of `Int.zpow_log_le_self` and `Int.self_le_zpow_clog`.
3. (A) Compute $F_{-5}$ and $F_{-6}$ with the recurrence run backwards, and compare with `Int.fib_neg_natCast`.
4. (B) Show with `Int.Ico_filter_modEq_card` that each interval of $r$ consecutive integers has exactly one element in each class modulo $r$.
5. (B) Prove that `Int.land n (Int.lnot n) = 0` and `Int.lor n (Int.lnot n) = -1` for each integer $n$, with the lemmas on bits.
6. (C) Prove Cassini's identity $F_{n+1} F_{n-1} - F_n^2 = (-1)^{\lvert n \rvert}$ for all $n \in \mathbb{Z}$ from the case $n \geq 1$ and `Int.fib_neg_natCast`.

### Reference

<?reference?>
