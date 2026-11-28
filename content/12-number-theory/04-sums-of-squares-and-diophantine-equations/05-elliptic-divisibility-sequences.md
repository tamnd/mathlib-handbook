---
title: Elliptic divisibility sequences
kind: api
modules:
  - Mathlib.NumberTheory.EllipticDivisibilitySequence
explains:
  E2: [IsEllipticNet, IsEllipticSequence, IsEllipticDvdSequence, IsEllipticNet.rel_eq, normEDS, IsEllipticDvdSequence.normEDS, normEDS_mul_complEDS, normEDS_two_three_two]
  E1: auto
families: []
requires: [V06, V02.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Elliptic divisibility sequences

### Overview

A *divisibility sequence* is a sequence $W : \mathbb{Z} \to R$ with $W(k) \mid W(nk)$ for all $k$ and $n$. The identity sequence and the Fibonacci numbers are examples. An *elliptic divisibility sequence* is a divisibility sequence that also satisfies a quartic recurrence, the elliptic relation. The main examples come from elliptic curves: the denominators of the multiples $nP$ of a rational point $P$, and the division polynomials $\psi_n$, form such sequences. The recurrence then encodes the group law of the curve.

The module `Mathlib.NumberTheory.EllipticDivisibilitySequence` works over an arbitrary commutative ring $R$. It defines elliptic nets, elliptic sequences and elliptic divisibility sequences as predicates on functions `ℤ → R`, and it constructs the canonical normalised example `normEDS b c d` from three parameters. It proves that this example is an elliptic divisibility sequence, with an explicit witness of the divisibility. The division polynomials of elliptic curves in Volume 28 are built from the auxiliary sequence of this module. The section uses only rings and divisibility from Volume 6.

### The library around it

#### The elliptic relation

Let $W : \mathbb{Z} \to R$. For $p, q, r, s \in \mathbb{Z}$ the *elliptic relator* is
$$ER(p, q, r, s) = W(p+q+s)W(p-q)W(r+s)W(r) - W(p+r+s)W(p-r)W(q+s)W(q) + W(q+r+s)W(q-r)W(p+s)W(p).$$
It is `IsEllipticNet.rel W p q r s`. The library defines three predicates.

| Lean name | Statement |
|---|---|
| `IsEllipticNet W` | $ER(p, q, r, s) = 0$ for all $p, q, r, s$ |
| `IsEllipticSequence W` | $ER(p, q, r, 0) = 0$ for all $p, q, r$ |
| `IsEllipticDvdSequence W` | $W$ is an elliptic sequence and `IsDvdSequence W` |

Here `IsDvdSequence W` means $k \mid l \Rightarrow W(k) \mid W(l)$. An elliptic net is an elliptic sequence, by `IsEllipticNet.isEllipticSequence`. The converse holds when $W(1)$ and $W(2)$ are not zero divisors, by `IsEllipticSequence.isEllipticNet`. The relator here differs from the elliptic net recurrence of Stange by the sign of the last term. With this sign, the definition covers both the elliptic nets and the elliptic sequences of Ward without the assumption that $W$ is odd.

#### The symmetric form

A change of variables makes the relator symmetric. The *elliptic atom* is $W_a(a, b) = W\big(\tfrac{a+b}{2}\big)W\big(\tfrac{a-b}{2}\big)$, `IsEllipticNet.atom W a b`, with integer division. The symmetric relator is
$$ER_a(a, b, c, d) = W_a(a, b)W_a(c, d) - W_a(a, c)W_a(b, d) + W_a(a, d)W_a(b, c),$$
`IsEllipticNet.atomRel W a b c d`.

**Lemma.** `IsEllipticNet.rel_eq`: $ER(p, q, r, s) = ER_a(2p + s, 2q + s, 2r + s, s)$.

*Proof.* With $a = 2p + s$ and $b = 2q + s$, the two halves are $\tfrac{a + b}{2} = p + q + s$ and $\tfrac{a - b}{2} = p - q$. So $W_a(a, b) = W(p + q + s)W(p - q)$. In the same way $W_a(c, d) = W(r + s)W(r)$ for $c = 2r + s$ and $d = s$. So the first terms agree, and the other two terms agree in the same way. $\square$

The inverse change, for four integers of the same parity, is `IsEllipticNet.atomRel_eq`. The symmetric form has many symmetries, and the module proves them as a family of lemmas. The names say which arguments change: `IsEllipticNet.atomRel_perm` for permutations, `IsEllipticNet.atomRel_neg₁` to `IsEllipticNet.atomRel_neg₄` for a change of sign of one argument, `IsEllipticNet.atomRel_abs₁` to `IsEllipticNet.atomRel_abs₄` for the absolute value, and `IsEllipticNet.atomRel_same₁₂` and its relatives for two equal arguments. The atoms have `IsEllipticNet.atom_neg_left`, `IsEllipticNet.atom_neg_right` and `IsEllipticNet.atom_same`.

#### Operations on elliptic sequences

The three predicates are stable under the natural operations.

1. Scalar multiples: if $W$ is an elliptic net, sequence or divisibility sequence, so is $x \cdot W$ for $x \in R$. The relator is homogeneous of degree $4$ in $W$. The lemmas are `IsEllipticNet.smul`, `IsEllipticSequence.smul` and `IsEllipticDvdSequence.smul`.
2. Ring homomorphisms: if $f : R \to S$ is a ring homomorphism, then $f \circ W$ keeps each property. The relator commutes with $f$, by `IsEllipticNet.map_rel`, and the lemmas are `IsEllipticNet.comp`, `IsEllipticSequence.comp` and `IsEllipticDvdSequence.comp`.
3. Negation of the index: `IsEllipticSequence.neg`.
4. The identity sequence $W(n) = n$ in `ℤ` is an elliptic divisibility sequence: `IsEllipticNet.id`, `IsEllipticSequence.id` and `IsEllipticDvdSequence.id`.

An odd sequence is an elliptic sequence if it satisfies two families of relations. These are the *even relations* $ER(m + 1, m - 1, 1, 0) = 0$, which say
$$W(2m)W(2) = W(m - 1)^2W(m)W(m + 2) - W(m - 2)W(m)W(m + 1)^2,$$
and the *odd relations* $ER(m + 1, m, 1, 0) = 0$, which say
$$W(2m + 1) = W(m + 2)W(m)^3 - W(m - 1)W(m + 1)^3$$
when $W(1) = 1$. The criterion `IsEllipticSequence.of_even_odd` needs `Function.Odd W` and asks that $W(1)$ and $W(2)$ lie in `nonZeroDivisors R`. The version for nets is `IsEllipticNet.of_even_odd`.

#### The normalised sequence

Let $b, c, d \in R$. The even and odd relations determine a sequence from its first values $W(0) = 0$, $W(1) = 1$, $W(2) = b$, $W(3) = c$, $W(4) = db$. The term $W(2m)$ comes from the even relation, which needs a division by $W(2) = b$. To avoid the division, the library first defines an auxiliary sequence `preNormEDS (b ^ 4) c d`, with the recurrences `preNormEDS_even` and `preNormEDS_odd`, in which the factor $b$ appears only in the odd step. Then `normEDS b c d n` is this auxiliary sequence at odd $n$ and $b$ times it at even $n$. The version on `ℕ` is `preNormEDS'`, and `normEDS` extends it to `ℤ` as an odd function.

| Lean name | Statement |
|---|---|
| `normEDS_zero`, `normEDS_one` | $W(0) = 0$, $W(1) = 1$ |
| `normEDS_two`, `normEDS_three`, `normEDS_four` | $W(2) = b$, $W(3) = c$, $W(4) = db$ |
| `normEDS_neg` | $W(-n) = -W(n)$ |
| `normEDS_odd` | $W(2m + 1) = W(m + 2)W(m)^3 - W(m - 1)W(m + 1)^3$ |
| `normEDS_even` | $W(2m)\,b = W(m - 1)^2W(m)W(m + 2) - W(m - 2)W(m)W(m + 1)^2$ |
| `map_normEDS` | $f(W_{b,c,d}(n)) = W_{f(b), f(c), f(d)}(n)$ for a ring homomorphism $f$ |

The relations in the form of the relator are `normEDS_rel_even` and `normEDS_rel_odd`. The recursion principles `normEDSRec` and `normEDSRec'` prove a statement for all indices by the same induction as the definition: from five consecutive values to the next even and odd values.

**Example.** For $b = 2$, $c = 3$, $d = 2$ the first values are $0, 1, 2, 3, 4$, and the recurrences give $W(n) = n$ for all $n$. This is `normEDS_two_three_two`. For $b = 1$, $c = -1$, $d = 1$ the recurrences give
$$0, 1, 1, -1, 1, 2, -1, -3, -5, 7, -4, -23, \ldots,$$
the sequence of the point $(0, 0)$ on the curve $y^2 + y = x^3 - x$. For instance $W(5) = W(4)W(2)^3 - W(1)W(3)^3 = 1 + 1 = 2$.

#### The main theorem

**Theorem.** For all $b, c, d$, `normEDS b c d` is an elliptic net, and it is an elliptic divisibility sequence: `IsEllipticNet.normEDS`, `IsEllipticSequence.normEDS`, `IsDvdSequence.normEDS` and `IsEllipticDvdSequence.normEDS`.

The proof of the elliptic relation is a long induction with `normEDSRec`. The proof of divisibility is constructive. The module defines a *complement sequence* `complEDS b c d k n` with
$$W(k) \cdot W^c(k, n) = W(nk),$$
which is `normEDS_mul_complEDS`. So $W(k) \mid W(nk)$ with an explicit quotient, and this gives `IsDvdSequence.normEDS`. The complement is built by its own recursion, `complEDSRec`, from the case $n = 2$, the *2-complement* `complEDS₂`, with $W(k)W^c_2(k) = W(2k)$ by `normEDS_mul_complEDS₂`. For the identity sequence the complement is $W^c(k, n) = n$, by `complEDS_two_three_two`. The divisibility $W(k) \mid W(2k)$ alone is `normEDS_dvd_normEDS_two_mul`.

#### Common errors

1. `normEDS b c d 4` is $db$, not $d$. The parameter $d$ is $W(4)/W(2)$, which keeps the definition free of division.
2. `IsEllipticSequence W` fixes $s = 0$ in the relator, while `IsEllipticNet W` asks the relation for all $s$. The two predicates agree only under the hypothesis on $W(1)$ and $W(2)$ of `IsEllipticSequence.isEllipticNet`.
3. `preNormEDS` takes $b^4$, not $b$, as its first argument in the definition of `normEDS`. A lemma about `preNormEDS b c d` applies to `normEDS b c d` only after this substitution and the factor $b$ at even indices.

### Exercises

1. (A) Compute $W(6)$, $W(7)$ and $W(8)$ for `normEDS 1 (-1) 1` with the recurrences, and check that $W(2) \mid W(6)$ and $W(4) \mid W(8)$.
2. (A) Show that the identity sequence satisfies the odd relation $2m + 1 = (m + 2)m^3 - (m - 1)(m + 1)^3$.
3. (B) Show that if $W$ is an elliptic sequence, then so is $n \mapsto W(-n)$, from the definition of the relator.
4. (B) Show that the sequence $W(n) = n$ in `ℤ` satisfies $ER(p, q, r, s) = 0$ for all $p, q, r, s$, by expanding the relator as a polynomial.
5. (C) Let $K$ be a field and let $W : \mathbb{Z} \to K$ satisfy the even and odd relations, with $W(0) = 0$, $W(1) = 1$ and $W(2) \neq 0$. Show by strong induction that $W(n) = $ `normEDS` $W(2)\ W(3)\ (W(4)/W(2))\ n$ for all $n \geq 0$.

### Reference

<?reference?>
