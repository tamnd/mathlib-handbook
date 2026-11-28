---
title: The bits of a natural number
kind: api
modules:
  - Mathlib.Data.Nat.BinaryRec
  - Mathlib.Data.Nat.Bits
  - Mathlib.Data.Nat.Bitwise
  - Mathlib.Data.Nat.BitIndices
  - Mathlib.Data.Nat.Size
explains:
  E2: [Nat.bit_val, Nat.binaryRec, Nat.bit_bodd_div2, Nat.testBit_land, Nat.lt_of_testBit, Nat.sum_map_two_pow_bitIndices, Nat.lt_size]
  E1: auto
families: []
requires: [V01.C05, V02.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The bits of a natural number

### Overview

The type `ℕ` is built from $0$ and the successor, and the induction of Chapter 1 follows this unary structure. Each natural number also has a binary form: $n = 2m + b$ with a last bit $b \in \{0, 1\}$ and a number $m = \lfloor n/2 \rfloor$ that is smaller when $n \ne 0$. This gives a second structure on `ℕ`, with $0$ and the two maps $m \mapsto 2m$ and $m \mapsto 2m + 1$. Proofs about the bitwise operations, about the size of a number in bits and about fast algorithms follow this binary structure.

The modules of this section build the binary structure. The constructor `Nat.bit` and the recursor `Nat.binaryRec` are in `Mathlib.Data.Nat.BinaryRec`, the parity bit, the halving map and the list of bits are in `Mathlib.Data.Nat.Bits`, the bitwise operations are in `Mathlib.Data.Nat.Bitwise`, the set of the positions of the bits is in `Mathlib.Data.Nat.BitIndices`, and the length in bits is in `Mathlib.Data.Nat.Size`. The next section uses the same ideas for the binary types `PosNum` and `Num`.

### The library around it

#### The constructor `Nat.bit` and binary recursion

The function `Nat.bit : Bool → ℕ → ℕ` appends a bit at the low end: `Nat.bit b n` is $2n + b$, where the Boolean value $b$ counts as $0$ or $1$ through the core map *Bool.toNat*. This is `Nat.bit_val`. The two special cases are `Nat.bit_false_apply`, $\mathrm{bit}(\mathrm{false}, n) = 2n$, and `Nat.bit_true_apply`, $\mathrm{bit}(\mathrm{true}, n) = 2n + 1$. The inverse direction is given by `Nat.bit_div_two`, $\mathrm{bit}(b, n) / 2 = n$, and `Nat.bit_mod_two`, $\mathrm{bit}(b, n) \bmod 2 = b$. So `Nat.bit` is injective, and its only value that is not a "new" number is $\mathrm{bit}(\mathrm{false}, 0) = 0$ (`Nat.bit_false_zero`, `Nat.bit_eq_zero_iff`).

Each number is a value of `Nat.bit`: `Nat.bit_testBit_zero_shiftRight_one` says that $n = \mathrm{bit}(b, n \gg 1)$, where $b$ is the bit at position $0$ and $n \gg 1 = \lfloor n/2 \rfloor$ is the shift to the right (`Nat.shiftRight_one`). This gives the case analysis `Nat.bitCasesOn` and the recursor `Nat.binaryRec`.

**The principle of binary recursion.** Let $C(n)$ be a family of types (or of propositions). Given a value $z \in C(0)$ and a step $f(b, n) : C(n) \to C(\mathrm{bit}(b, n))$, there is a function $F$ with $F(n) \in C(n)$ for each $n$, with $F(0) = z$ and $F(\mathrm{bit}(b, n)) = f(b, n, F(n))$ whenever $\mathrm{bit}(b, n) \ne 0$.

*Proof sketch.* Define $F(n)$ by strong recursion on $n$. For $n = 0$ take $z$. For $n \ne 0$ write $n = \mathrm{bit}(b, m)$ with $m = \lfloor n/2 \rfloor < n$ (`Nat.binaryRec_decreasing`), and take $f(b, m, F(m))$. The equation for $\mathrm{bit}(b, n)$ holds by the definition, except in the case $\mathrm{bit}(\mathrm{false}, 0) = 0$, where the definition returns $z$. $\square$

The recursor is `Nat.binaryRec`, with the equations `Nat.binaryRec_zero` and `Nat.binaryRec_eq`. The second equation has a side condition: either the step at $(\mathrm{false}, 0)$ returns $z$, or the argument is not $\mathrm{bit}(\mathrm{false}, 0)$. Two variants avoid the side condition. In `Nat.binaryRec'` the step is only asked for $(b, n)$ with $n = 0 \to b = \mathrm{true}$, so each argument of the step is a nonzero number. In `Nat.binaryRecFromOne` the cases are $0$, $1$, and the step for $n \ne 0$. The lemmas `Nat.binaryRec_one`, `Nat.binaryRec'_eq` and `Nat.binaryRecFromOne_eq` give their equations. When the motive is a proposition, the recursor is an induction principle: to prove $P(n)$ for each $n$, prove $P(0)$ and prove $P(2n + b)$ from $P(n)$.

#### Parity, halving and the list of bits

The module `Mathlib.Data.Nat.Bits` defines the last bit `Nat.bodd`, a Boolean value that is $\mathrm{true}$ for an odd number, and the halving map `Nat.div2`. The basic facts are `Nat.mod_two_of_bodd`, $n \bmod 2 = \mathrm{bodd}(n)$, `Nat.div2_val`, $\mathrm{div2}(n) = n / 2$, and the reconstruction `Nat.bit_bodd_div2`:
$$\mathrm{bit}(\mathrm{bodd}(n), \mathrm{div2}(n)) = n.$$
*Proof.* By `Nat.bit_val`, the left side is $2 \lfloor n/2 \rfloor + (n \bmod 2)$, and this is $n$ by the division algorithm of Chapter 2. $\square$

The parity bit is a homomorphism to the Booleans: `Nat.bodd_add` says that $\mathrm{bodd}(m + n)$ is the exclusive or of $\mathrm{bodd}(m)$ and $\mathrm{bodd}(n)$, and `Nat.bodd_mul` says that $\mathrm{bodd}(m n)$ is their conjunction. These are the rules "odd plus odd is even" and "odd times odd is odd". The lemmas `Nat.bodd_bit` and `Nat.div2_bit` evaluate the two maps on `Nat.bit`.

The list `Nat.bits n : List Bool` is the binary expansion of $n$, with the lowest bit first. So `Nat.bits 6` is the list false, true, true, since $6 = 0 \cdot 1 + 1 \cdot 2 + 1 \cdot 4$. The list of $0$ is empty (`Nat.zero_bits`), and there are no leading zeros: `Nat.bit1_bits` says that the list of $2n + 1$ is true followed by the list of $n$, and `Nat.bit0_bits` gives the same with false for $2n$ when $n \ne 0$. The head of the list is the parity bit (`Nat.bodd_eq_bits_head`), and the tail is the list of $n/2$ (`Nat.div2_bits_eq_tail`).

The module also defines `Nat.shiftLeft'`, which shifts to the left and fills with a given bit, and `Nat.ldiff`, the bitwise difference "$m$ and not $n$". The lemmas `Nat.shiftLeft'_false` and `Nat.shiftLeft'_add` relate the first one to the shift `m <<< n` of core Lean, and `Nat.shiftLeft_eq_mul_pow` in `Mathlib.Data.Nat.Size` gives $m \ll n = m \cdot 2^n$.

#### Bitwise operations

Core Lean defines the bit at position $i$ of $n$ (the function *testBit*) and a general bitwise operation (the function *bitwise*) that applies a Boolean function $f$ to the two bits at each position. The operations `&&&`, `|||` and `^^^` on `ℕ` are the conjunction, the disjunction and the exclusive or. The module `Mathlib.Data.Nat.Bitwise` proves their laws by binary recursion. The general rule is `Nat.bitwise_bit`: if $f(\mathrm{false}, \mathrm{false}) = \mathrm{false}$, then the operation for $f$ applied to $\mathrm{bit}(a, m)$ and $\mathrm{bit}(b, n)$ is $\mathrm{bit}(f(a, b), \cdot)$ of the operation applied to $m$ and $n$. The special cases are `Nat.land_bit`, `Nat.lor_bit`, `Nat.xor_bit` and `Nat.ldiff_bit`.

The most useful form is the extensional one. Two numbers with the same bits are equal, and the bits of the result are computed position by position:

| Lean name | Statement |
|---|---|
| `Nat.testBit_land` | bit $k$ of $m \mathbin{\&} n$ is the conjunction of the bits $k$ of $m$ and $n$ |
| `Nat.testBit_lor` | bit $k$ of the bitwise or $m \vee n$ is the disjunction of the bits |
| `Nat.testBit_ldiff` | bit $k$ of $\mathrm{ldiff}(m, n)$ is "bit of $m$ and not bit of $n$" |
| `Nat.zero_of_testBit_eq_false` | a number with no bit equal to true is $0$ |
| `Nat.testBit_eq_false_of_lt` | if $n < 2^i$, then the bit $i$ of $n$ is false |
| `Nat.exists_most_significant_bit` | each $n \ne 0$ has a highest bit equal to true |
| `Nat.lt_of_testBit` | comparison of $m$ and $n$ at the highest position where they differ |
| `Nat.two_pow_and` | $2^i \mathbin{\&} n = 2^i \cdot (\text{bit } i \text{ of } n)$ |

**Proof sketch of `Nat.testBit_land`.** Binary induction on $m$ and $n$ together. For position $0$, the bit of $\mathrm{bit}(a, m') \mathbin{\&} \mathrm{bit}(b, n') = \mathrm{bit}(a \wedge b, m' \mathbin{\&} n')$ is $a \wedge b$ by `Nat.testBit_bit_zero`. For position $k + 1$, the bit is the bit $k$ of $m' \mathbin{\&} n'$ by `Nat.testBit_bit_succ`, and the hypothesis applies. $\square$

With these lemmas, the laws of the operations follow from the laws of the Booleans: `Nat.land_comm`, `Nat.land_assoc`, `Nat.lor_comm`, `Nat.lor_assoc`, and in general `Nat.bitwise_comm` for a symmetric $f$. The lemma `Nat.lt_of_testBit` says: if $m$ and $n$ agree at each position above $i$, and the bit $i$ is false in $m$ and true in $n$, then $m < n$. Indeed the higher bits contribute the same amount to both numbers, the bit $i$ gives $2^i$ more to $n$, and the lower bits of $m$ sum to less than $2^i$.

The module ends with facts on the exclusive or. Here $(m \oplus n) \bmod 2 = (m + n) \bmod 2$ (`Nat.xor_mod_two_eq`), $n \oplus 1 = n + 1$ for even $n$ (`Nat.xor_one_of_even`), and `Nat.xor_trichotomy` says that if $a \oplus b \oplus c \ne 0$ then one of $b \oplus c < a$, $c \oplus a < b$, $a \oplus b < c$ holds. This last fact is the key step of the theory of the game of Nim, which is in the combinatorial game theory of Mathlib.

#### Bit indices and the size

The module `Mathlib.Data.Nat.BitIndices` gives the positions of the bits equal to true. The list `Nat.bitIndices n` is sorted and has no repetition (`Nat.bitIndices_sorted`, `Nat.bitIndices_nodup`), and $i$ is in it if and only if the bit $i$ of $n$ is true (`Nat.mem_bitIndices`). The two directions of the binary expansion are
$$\sum_{i \in \mathrm{bitIndices}(n)} 2^i = n \qquad\text{and}\qquad \mathrm{bitIndices}\Big(\sum_{i \in L} 2^i\Big) = L$$
for a strictly increasing list $L$. These are `Nat.sum_map_two_pow_bitIndices` and `Nat.bitIndices_sum_map_two_pow`. So each number is a sum of distinct powers of $2$ in exactly one way. The first statement is a binary induction with `Nat.bitIndices_two_mul` and `Nat.bitIndices_two_mul_add_one`: the indices of $2n$ are those of $n$ moved up by one, and the indices of $2n + 1$ get $0$ in addition. The examples are `Nat.bitIndices_two_pow`, the list with only $k$ for $2^k$, and `Nat.bitIndices_zero`.

The module `Mathlib.Data.Nat.Size` defines `Nat.size n`, the number of binary digits of $n$, with `Nat.size_zero` and `Nat.size_one` and `Nat.size_eq_bits_len`, which says that it is the length of `Nat.bits n`. Its characterization is `Nat.lt_size`:
$$m < \mathrm{size}(n) \iff 2^m \leq n,$$
and its dual form `Nat.size_le`, $\mathrm{size}(m) \leq n \iff m < 2^n$. So $\mathrm{size}(n) = \lfloor \log_2 n \rfloor + 1$ for $n \geq 1$, and $2^{\mathrm{size}(n) - 1} \leq n < 2^{\mathrm{size}(n)}$. *Proof sketch.* Binary induction on $n$: by `Nat.size_bit`, $\mathrm{size}(\mathrm{bit}(b, n)) = \mathrm{size}(n) + 1$ for a nonzero argument, and $2^{m + 1} \leq 2n + b \iff 2^m \leq n$. $\square$ Other lemmas are `Nat.size_pow`, $\mathrm{size}(2^n) = n + 1$, the monotonicity `Nat.size_le_size`, and `Nat.size_shiftLeft`, which adds the shift to the size.

#### Common errors

1. The Boolean argument of `Nat.bit` comes first: `Nat.bit b n` is $2n + b$, not $2b + n$. The list `Nat.bits n` has the lowest bit first, the opposite of the usual way to write a number.
2. The equation `Nat.binaryRec_eq` has a side condition for the case $\mathrm{bit}(\mathrm{false}, 0) = 0$. If the step does not return the start value there, use `Nat.binaryRec'` or `Nat.binaryRecFromOne`.
3. The rule `Nat.bitwise_bit` needs $f(\mathrm{false}, \mathrm{false}) = \mathrm{false}$. For a function such as "not equal" this holds, but for "equal" it fails, because the result would have infinitely many bits equal to true.

### Exercises

1. (A) Compute `Nat.bits 13`, `Nat.bitIndices 13` and `Nat.size 13`, and check `Nat.sum_map_two_pow_bitIndices` for $n = 13$.
2. (A) Prove $\mathrm{bodd}(n^2) = \mathrm{bodd}(n)$ with `Nat.bodd_mul`.
3. (B) Prove by binary recursion that $m \mathbin{\&} n \leq m$ for all $m, n$.
4. (B) Prove that $m \oplus n = 0$ if and only if $m = n$, with the bits of the two numbers.
5. (B) Prove `Nat.size_le` from `Nat.lt_size`.
6. (C) Use `Nat.xor_trichotomy` to prove: in a position of Nim with three heaps $a, b, c$ and $a \oplus b \oplus c \ne 0$, there is a move to a position with $a' \oplus b' \oplus c' = 0$.

### Reference

<?reference?>
