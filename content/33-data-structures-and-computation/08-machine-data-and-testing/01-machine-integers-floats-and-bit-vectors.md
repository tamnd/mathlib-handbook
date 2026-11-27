---
title: Machine integers, floats and bit vectors
kind: theory
modules:
  - Mathlib.Data.UInt
  - Mathlib.Data.BitVec
  - Mathlib.Data.FP.Basic
  - Mathlib.Data.LawfulXor.Basic
  - Mathlib.Data.LawfulXor.Equiv
  - Mathlib.Data.Char
  - Mathlib.Data.String.Basic
  - Mathlib.Data.String.Defs
  - Mathlib.Data.String.Lemmas
explains:
  E3: [UInt8.instCommRing, UInt8.toBitVec_injective, BitVec.instCommRing, BitVec.toFin_injective, BitVec.equivFin, LawfulXor, xor_cancel_left, xor_eq_zero_iff, Equiv.xor, Equiv.xor_trans_xor, instLinearOrderChar, String.lt_iff_toList_lt, String.instLinearOrder, String.length_leftpad]
  E2: [UInt8.instCommMonoid, UInt8.instNonUnitalCommRing, UInt8.toFin_injective, UInt8.toBitVec_natCast, UInt8.toBitVec_intCast, UInt8.toBitVec_nsmul, UInt8.isASCIIDigit, UInt8.toChar, UInt64.instCommRing, BitVec.toNat_injective, BitVec.toFin_intCast, BitVec.toFin_pow, BitVec.instCommSemiring, zero_xor, xor_cancel_right, xor_left_involutive, xor_eq_iff_left_eq, xor_left_eq_self_iff, isFixedPt_xor_left_iff, instLawfulXorNat, instLawfulXorBitVec, instLawfulXorUInt8, Equiv.xor_symm, Equiv.xor_zero, Equiv.xor_eq_one_iff, Equiv.isFixedPt_xor, String.le_iff_toList_le, String.lt_iff_ltb, String.ltb, String.ofList_eq, String.leftpad, String.replicate, String.rightpad, String.IsPrefix, String.IsSuffix, String.length_replicate, String.leftpad_prefix, String.leftpad_suffix, String.congr_append]
  E1: auto
families: []
requires: [V01.C04, V05.C07, V06.C01, V06.C04, V33.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Machine integers, floats and bit vectors

### Overview

A computer computes with words of a fixed number of bits, and an addition that leaves the range wraps around. In `UInt8`, the type of bytes, $255 + 1 = 0$. This is the arithmetic of the ring $\mathbb{Z}/256\mathbb{Z}$, and this section proves it. The core of Lean defines `UInt8` to `UInt64`, `USize` and the bit vectors `BitVec w`. Mathlib adds a commutative ring on `BitVec w`, a ring isomorphism `BitVec w ≃+* Fin (2 ^ w)`, and rings on the machine integers.

The section then treats exclusive or (`^^^`) and its four laws, the orders on characters and strings, and an old model of floating point numbers. The model is deprecated in this edition, but a small instance of it shows why floating point addition is not associative.

### Definitions

**Definition (Bit vector).** For $w \in \mathbb{N}$, a bit vector of width $w$ is an element of `BitVec w`, a structure with one field `toFin : Fin (2 ^ w)`. So a bit vector is a number $0 \le x < 2^w$, read as $w$ bits. The value as a natural number is `toNat`. The core of Lean defines the ring operations by those of `Fin (2 ^ w)`, that is, modulo $2^w$.

**Definition (Machine integer).** `UInt8` is a structure with one field `toBitVec : BitVec 8`. The operations of `UInt8` are the operations of `BitVec 8`, so $a + b$ has the value $(a + b) \bmod 256$ and $a \cdot b$ has the value $ab \bmod 256$. The types `UInt16`, `UInt32`, `UInt64` and `USize` are the same with widths $16$, $32$, $64$ and the word size of the platform.

**Definition (Transported structure).** Let $f \colon A \to B$ be injective, let $B$ be a commutative ring, and let $A$ have the operations of a ring (zero, one, $+$, $\cdot$, negation, subtraction, scalars, powers and casts). The map $f$ preserves the structure if $f(0) = 0$, $f(1) = 1$, $f(a + b) = f(a) + f(b)$, $f(ab) = f(a) f(b)$, and the same for each other operation. The construction of the ring on $A$ is `Function.Injective.commRing`.

**Definition (Lawful exclusive or).** Let $\alpha$ have a zero and an operation $a \oplus b$ (written `a ^^^ b`). The class `LawfulXor α` asks for four laws: $(a \oplus b) \oplus c = a \oplus (b \oplus c)$, $a \oplus a = 0$, $a \oplus 0 = a$ and $a \oplus b = b \oplus a$. So $(\alpha, \oplus, 0)$ is a commutative group in which each element is its own inverse. Mathlib gives instances for `Nat`, `Fin (2 ^ w)`, `BitVec w` and the machine integers, signed and unsigned. For $a \in \alpha$, `Equiv.xor a : Equiv.Perm α` is the map $x \mapsto a \oplus x$.

**Definition (Character and string).** A `Char` is a Unicode scalar value: a 32 bit number $n$ with $n < \mathtt{0xD800}$ or $\mathtt{0xDFFF} < n < \mathtt{0x110000}$, ordered as a number. A `String` is a sequence of characters; `s.toList` is its list of characters, `String.ofList` is the inverse, and `s.length` is the length of `s.toList`.

**Definition (Lexicographic order).** For lists over a linear order, $[\,] < b :: t$, no list is below $[\,]$, and $a :: s < b :: t$ if $a < b$, or $a = b$ and $s < t$.

**Definition (Padding).** `String.leftpad n c s` is the string `replicate (n - s.length) c ++ s`, where `String.replicate k c` has $k$ copies of $c$ and `-` is truncated subtraction; `String.rightpad` pads on the right.

### Theorems and proofs

**Theorem (Transport of a ring structure).** If $f \colon A \to B$ is injective, $B$ is a commutative ring and $f$ preserves the structure, then the operations of $A$ make $A$ a commutative ring, and $f$ is a ring homomorphism.

*Proof.* Each axiom of a commutative ring is an equation between two terms built from variables and operations. Take associativity of addition. For $a, b, c \in A$, $$f((a + b) + c) = (f(a) + f(b)) + f(c) = f(a) + (f(b) + f(c)) = f(a + (b + c)),$$ by preservation of $+$ (twice on each side) and associativity in $B$. As $f$ is injective, $(a + b) + c = a + (b + c)$. Each other axiom, the laws of scalars, powers and casts included, follows in the same way: move $f$ inside both sides, apply the axiom in $B$, and cancel $f$. Preservation of the operations says that $f$ is a homomorphism. $\square$

**Theorem (Bit vectors form the ring of integers modulo $2^w$).** `BitVec w` is a commutative ring, and `toFin` is a ring isomorphism `BitVec w ≃+* Fin (2 ^ w)`.

*Proof.* `toFin` is injective: two structures with one field are equal when the fields are equal (this is `BitVec.toFin_injective`). It preserves zero, one, addition, multiplication, negation and subtraction by the definitions of the operations. It preserves powers by induction on $n$: $x^0 = 1$, and $\operatorname{toFin}(x^{n+1}) = \operatorname{toFin}(x^n \cdot x) = \operatorname{toFin}(x)^n \operatorname{toFin}(x)$ (`BitVec.toFin_pow`). Scalar multiplication by $n \in \mathbb{N}$ is multiplication by the cast of $n$, and the casts agree (`BitVec.toFin_intCast` for $\mathbb{Z}$). The transport theorem gives the ring. The inverse of `toFin` is `BitVec.ofFin`, so `toFin` is a bijection, and a bijective ring homomorphism is a ring isomorphism. $\square$

**Corollary (Machine integers).** `UInt8` with the operations of the core is a commutative ring, and $x \mapsto \operatorname{toFin}(\operatorname{toBitVec}(x))$ is a ring isomorphism onto $\mathbb{Z}/256\mathbb{Z}$ (the ring `Fin 256`). The same holds for the other widths.

*Proof.* `toBitVec` is injective (`UInt8.toBitVec_injective`), and it preserves the operations by their definitions, with `UInt8.toBitVec_natCast`, `UInt8.toBitVec_intCast` and `UInt8.toBitVec_nsmul` for casts and scalars. The transport theorem gives the ring. Each bit vector of width $8$ comes from a byte, so `toBitVec` is bijective. Compose with the isomorphism above. $\square$

**Proposition (Units modulo $2^n$).** Let $n \ge 1$. In $\mathbb{Z}/2^n\mathbb{Z}$, the class of $a$ is a unit if and only if $a$ is odd. Each even class $a$ is a zero divisor.

*Proof.* If $a$ is odd, then $\gcd(a, 2^n) = 1$, so by Bézout there are integers $u, v$ with $ua + v 2^n = 1$, and $ua \equiv 1 \pmod{2^n}$. If $a = 2k$, then $a \cdot 2^{n-1} = k 2^n \equiv 0$, and $2^{n-1} \not\equiv 0$, so $a$ is a zero divisor. A zero divisor is not a unit: $ua = 1$ and $ab = 0$ give $b = uab = 0$. $\square$

**Theorem (Cancellation for exclusive or).** In a lawful exclusive or structure, $a \oplus (a \oplus b) = b$ (`xor_cancel_left`), and $a \oplus b = 0$ if and only if $a = b$ (`xor_eq_zero_iff`).

*Proof.* $a \oplus (a \oplus b) = (a \oplus a) \oplus b = 0 \oplus b = b \oplus 0 = b$, by associativity, self inverse, commutativity and the zero law. For the equivalence, if $a = b$ then $a \oplus b = a \oplus a = 0$. If $a \oplus b = 0$, then $b = a \oplus (a \oplus b) = a \oplus 0 = a$. $\square$

**Theorem (Exclusive or as a group of permutations).** Each `Equiv.xor a` is its own inverse. The map $a \mapsto \operatorname{xor} a$ is an injective group homomorphism from $(\alpha, \oplus, 0)$ to $\operatorname{Perm}(\alpha)$: $\operatorname{xor} a \circ \operatorname{xor} b = \operatorname{xor}(a \oplus b)$ (`Equiv.xor_trans_xor`), and $\operatorname{xor} a = \mathrm{id}$ only for $a = 0$. For $a \ne 0$, $\operatorname{xor} a$ has no fixed point.

*Proof.* By cancellation, $x \mapsto a \oplus x$ composed with itself is the identity, so it is a bijection and its own inverse. For all $x$, $a \oplus (b \oplus x) = (a \oplus b) \oplus x$ by associativity, which is the homomorphism law. If $\operatorname{xor} a = \mathrm{id}$, apply it to $0$: $a = a \oplus 0 = 0$. A fixed point $x$ of $\operatorname{xor} a$ satisfies $a \oplus x = x = 0 \oplus x$, and cancellation of $x$ on the right (`xor_cancel_right`) gives $a = 0$. $\square$

**Theorem (Order on strings).** `String` is a linear order, and $s < t$ if and only if `s.toList < t.toList` in the lexicographic order (`String.lt_iff_toList_lt`).

*Proof.* The equivalence comes from the core. As `toList` is injective, it suffices to prove that the lexicographic order on lists over the linear order `Char` is a strict linear order. Irreflexivity: by induction on $s$, as $a :: s < a :: s$ needs $a < a$ or $s < s$. Transitivity: let $s < t$ and $t < u$, and argue by induction on $s$ for all $t, u$. As no list is below $[\,]$, $t$ and $u$ are not empty. If $s = [\,]$, then $s < u$. Else write $s = a :: s'$, $t = b :: t'$, $u = c :: u'$. If $a < b$ or $b < c$, then $a < c$ (with $a = b$ or $b = c$ in the mixed cases), so $s < u$. Else $a = b = c$, $s' < t'$ and $t' < u'$, and the hypothesis of induction gives $s' < u'$. Trichotomy: by induction on $s$ for all $t$. If one of the lists is empty, the claim is direct. Else compare the heads $a, b$ in `Char`: if $a < b$ or $b < a$, the lists compare in the same way, and if $a = b$, apply the hypothesis to the tails. $\square$

**Proposition (Length of a padded string).** The length of `leftpad n c s` is $\max(n, \operatorname{length} s)$ (`String.length_leftpad`), and $s$ is a suffix of it.

*Proof.* Write $\ell = \operatorname{length} s$. The padded string is $c^{\,n \dot- \ell}$ followed by $s$, so its length is $(n \dot- \ell) + \ell$. If $n \ge \ell$ this is $n$, and if $n < \ell$ it is $0 + \ell = \ell$; in both cases it is $\max(n, \ell)$. The list $s$ is a suffix of $l' \mathbin{+\!\!+} s$ for each list $l'$. $\square$

### Examples

**Example (Byte arithmetic).** In `UInt8`: $255 + 1 = 0$; $200 + 100 = 300 - 256 = 44$; $20 \cdot 13 = 260 - 256 = 4$; $0 - 1 = 255$; $16 \cdot 16 = 0$, so $16$ is a zero divisor. The unit $3$ has the inverse $171$, as $3 \cdot 171 = 513 = 2 \cdot 256 + 1$. The unit $255 = -1$ is its own inverse: $255^2 = 65025 = 254 \cdot 256 + 1$. In Lean the ring on `UInt8` is scoped:

```lean
open scoped UInt8.CommRing in
example (a b : UInt8) : (a + b) * (a - b) = a * a - b * b := by
  ring
```

**Counterexample (No ordered ring).** The order of `UInt8` compares values, and it does not respect addition: $1 \le 255$, while $1 + 1 = 2$ and $255 + 1 = 0$, and $2 > 0$. So `UInt8` is not an ordered ring, and the statement $x < x + 1$ fails at $x = 255$.

**Example (Exclusive or on small words).** On `Nat`, $5 \oplus 3 = 101_2 \oplus 011_2 = 110_2 = 6$, and $6 \oplus 3 = 5$, as cancellation predicts. The swap of two variables without a third one is $x \leftarrow x \oplus y$, $y \leftarrow x \oplus y$, $x \leftarrow x \oplus y$. From $(x, y) = (5, 3)$ it gives $(6, 3)$, then $(6, 6 \oplus 3) = (6, 5)$, then $(6 \oplus 5, 5) = (3, 5)$. In general the steps give $(x \oplus y) \oplus y = x$ and $(x \oplus y) \oplus x = y$ by cancellation. On `Fin 4`, the permutation $\operatorname{xor} 3$ is $(0\ 3)(1\ 2)$, $\operatorname{xor} 1$ is $(0\ 1)(2\ 3)$, and their composite is $(0\ 2)(1\ 3) = \operatorname{xor} 2$, as $3 \oplus 1 = 2$.

**Example (Strings in order).** The codes are `'A'` $= 65$, `'Z'` $= 90$, `'a'` $= 97$, `'e'` $= 101$, `'y'` $= 121$. So `"Zebra" < "apple"`, as $90 < 97$: capital letters come first. `"app" < "apple"`, as a proper prefix is smaller. `"apple" < "apply"`, as the first difference is $101 < 121$. For padding, `leftpad 5 '0' "42"` is `"00042"` of length $\max(5, 2) = 5$, and `leftpad 1 '0' "42"` is `"42"` of length $\max(1, 2) = 2$.

**Example (A small floating point system).** The deprecated model of `Mathlib.Data.FP.Basic` fixes a precision $p$ and a maximal exponent $e_{\max} \ge p$, with $e_{\min} = 1 - e_{\max}$. A finite float has a sign, an exponent $e$ and a mantissa $m \in \mathbb{N}$, with value $\pm m \cdot 2^{e}$. The validity condition asks $e_{\min} \le e + p - 1 \le e_{\max}$ and $e = \max(e + \operatorname{size}(m) - p, e_{\min})$, where $\operatorname{size}(m)$ is the number of bits of $m$. So $m$ has exactly $p$ bits (a normal float), or $e = e_{\min}$ and $m$ has fewer bits (a subnormal float). Take $p = 3$ and $e_{\max} = 3$, so $e_{\min} = -2$ and $-2 \le e \le 1$. The $20$ nonnegative finite floats are $0, 0.25, \dots, 1.75$ ($e = -2$, $m = 0, \dots, 7$), then $2, 2.5, 3, 3.5$ ($e = -1$), $4, 5, 6, 7$ ($e = 0$) and $8, 10, 12, 14$ ($e = 1$), with $m = 4, \dots, 7$. Addition computes the exact rational sum and rounds it to the nearest float, and a tie goes to the float with an even mantissa. Then $9$ lies halfway between $8 = 4 \cdot 2$ and $10 = 5 \cdot 2$, so $8 + 1$ rounds to $8$. So $(8 + 1) + 1 = 8 + 1 = 8$, while $8 + (1 + 1) = 8 + 2 = 10$. So addition is not associative.

### The library around it

::: mathlib
`BitVec.equivFin` · `Mathlib.Data.BitVec`

`equivFin : BitVec m ≃+* Fin (2 ^ m)` sends `a` to `a.toFin`, with inverse `ofFin`. The rings come from `toFin_injective.commSemiring` and `toFin_injective.commRing`, with `toFin_nsmul`, `toFin_zsmul`, `toFin_pow` and `toFin_intCast`. The ring on `Fin (2 ^ m)` is the scoped instance of `Fin.CommRing`.

<?decl BitVec.equivFin?>
:::

::: mathlib
`UInt8.instCommRing` · `Mathlib.Data.UInt`

The file builds, for each of `UInt8`, `UInt16`, `UInt32`, `UInt64` and `USize`, the instances `instCommMonoid` and `instNonUnitalCommRing`, which are global, and `instCommRing`, which is scoped: write `open scoped UInt8.CommRing` before `ring` on bytes. The header explains that global casts from `ℕ` and `ℤ` would form a cycle of coercions. The file also defines the ASCII tests such as `isASCIIDigit` and `UInt8.toChar`.

<?decl UInt8.instCommRing?>
:::

::: mathlib
`LawfulXor` · `Mathlib.Data.LawfulXor.Basic`

`LawfulXor α` needs `[XorOp α] [Zero α]` and has the fields `xor_assoc`, `xor_self`, `xor_zero` and `xor_comm`. The derived lemmas are `zero_xor`, `xor_cancel_left`, `xor_cancel_right`, `xor_left_involutive`, `xor_eq_iff_left_eq`, `xor_eq_zero_iff`, `xor_left_eq_self_iff` and `isFixedPt_xor_left_iff`.

<?decl LawfulXor?>
:::

::: mathlib
`Equiv.xor` · `Mathlib.Data.LawfulXor.Equiv`

`Equiv.xor a : Perm α` with `xor_apply`, `xor_symm`, `xor_involutive`, `xor_zero : Equiv.xor 0 = 1`, `xor_eq_one_iff`, `isFixedPt_xor` and `xor_trans_xor : (Equiv.xor b).trans (Equiv.xor a) = Equiv.xor (a ^^^ b)`. In `Perm α` the product `σ * τ` is `τ.trans σ`, so the last lemma reads `xor a * xor b = xor (a ^^^ b)`.

<?decl Equiv.xor?>
:::

::: mathlib
`String.instLinearOrder` · `Mathlib.Data.String.Basic`

The linear order on strings, with `lt_iff_toList_lt`, `le_iff_toList_le` and `ofList_eq`. `String.ltb` compares iterators, and `lt_iff_ltb` proves that it decides `<`. The order on `Char` is `instLinearOrderChar`.

<?decl String.instLinearOrder?>
:::

::: mathlib
`String.length_leftpad` · `Mathlib.Data.String.Lemmas`

With `length_replicate`, `leftpad_prefix` (the padding is a prefix), `leftpad_suffix` (the string is a suffix) and `congr_append`. The definitions `leftpad`, `rightpad`, `replicate`, `IsPrefix`, `IsSuffix` and `mapTokens` are in `Mathlib.Data.String.Defs`.

<?decl String.length_leftpad?>
:::

The model `FP.Float` is deprecated in this edition, with `Float` of the core as the replacement. Its rounding functions are marked `unsafe` and carry no proof, and the index of this edition has no declaration for a bound on the error of floating point rounding.

Common errors of a learner: The first error is to call `ring` on `UInt8` and see it fail; the commutative ring is scoped, and `open scoped UInt8.CommRing` makes it available. The second error is to expect `a ≤ b → a + c ≤ b + c` on machine integers; it fails by wrap around, as the counterexample above shows. The third error is to state a lemma about `String` with the order of `List Char` in mind and forget the cast; pass through `String.lt_iff_toList_lt` first.

### Exercises

1. (A) Compute in `UInt8` the values of $128 + 128$, $3 \cdot 86$, $7 - 10$ and $2^8$. Hint: reduce modulo $256$; the last value is $0$.
2. (A) Find the inverse of $5$ in `UInt8`. Hint: $5 \cdot 205 = 1025$.
3. (A) Compute `leftpad 4 ' ' "abc"` and `rightpad 2 '*' "abc"`, with their lengths. Hint: $4 \dot- 3 = 1$ and $2 \dot- 3 = 0$.
4. (B) Prove from the four laws of `LawfulXor` that $a \oplus b = c$ if and only if $a = c \oplus b$. Hint: apply $x \mapsto x \oplus b$ to both sides and use cancellation.
5. (B) Let $\alpha$ be a finite type with a lawful exclusive or and an element $a \ne 0$. Prove that the number of elements of $\alpha$ is even. Hint: the permutation $\operatorname{xor} a$ is an involution without fixed points, so its orbits have two elements.
6. (B) Prove that the units of `UInt8` form a group of $128$ elements, and that $x^2 = 1$ has the four solutions $1, 127, 129, 255$. Hint: $x^2 - 1 = (x - 1)(x + 1)$, and of the two even factors one is divisible by $2$ only once.
7. (C) In the floating point system with $p = 3$ and $e_{\max} = 3$, find three floats $x, y, z$ with $(x \cdot y) \cdot z \ne x \cdot (y \cdot z)$ after rounding. Hint: try $x = 1.25$ and $y = z = 1.75$; $1.25 \cdot 1.75 = 2.1875$ rounds to $2$, and $1.75 \cdot 1.75 = 3.0625$ rounds to $3$.

### Notes and history

Knuth treats arithmetic modulo $2^n$ in TAOCP. The IEEE 754 standard of 1985 fixed the formats of binary floating point numbers, the rounding to nearest with ties to even, the infinities and the values that are not a number. The model in `Mathlib.Data.FP.Basic` follows this design with one rounding mode.

The Mathlib files are by these authors, read from their headers: `Mathlib.Data.UInt`, `Mathlib.Data.FP.Basic`, `Mathlib.Data.Char` and `Mathlib.Data.String.Basic` by Mario Carneiro, `Mathlib.Data.BitVec` by Simon Hudon, Harun Khan and Alex Keizer, `Mathlib.Data.LawfulXor.Basic` by Eric Wieser, `Mathlib.Data.LawfulXor.Equiv` by Wrenna Robson, `Mathlib.Data.String.Defs` by Simon Hudon, Keeley Hoek, Floris van Doorn and Chris Bailey, and `Mathlib.Data.String.Lemmas` by Chris Bailey.

### Reference

<?reference?>
