---
title: Floor, ceiling, fractional part and rounding
kind: api
modules:
  - Mathlib.Algebra.Order.Floor.Ring
  - Mathlib.Algebra.Order.Floor.Semiring
  - Mathlib.Algebra.Order.Floor.Semifield
  - Mathlib.Algebra.Order.Floor.BigOperators
  - Mathlib.Algebra.Order.Floor.Div
  - Mathlib.Algebra.Order.Floor.Extended
  - Mathlib.Algebra.Order.Round
  - Mathlib.Algebra.Order.Nonneg.Floor
explains:
  E2: [Int.floor_add_eq_or, Int.ceil_neg, Int.fract_neg, Int.fract_eq_fract, Int.map_floor, Nat.floor_div_eq_div, Int.sum_floor_add_div, le_floorDiv_iff_smul_le, round_eq, abs_sub_round]
  E1: auto
families: []
requires: [V06.C03, V04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Floor, ceiling, fractional part and rounding

### Overview

Section 3 defines the class `FloorRing R` and the floor $\lfloor a \rfloor$, the greatest integer at most $a$, through the Galois connection $z \le \lfloor a \rfloor \iff z \le a$. This section gives the rest of the API: the ceiling $\lceil a \rceil$, the fractional part $\{a\} = a - \lfloor a \rfloor$, the natural floor $\lfloor a \rfloor_{\mathbb{N}}$ for semirings, the rules for sums, negatives and quotients, rounding to the nearest integer, and the floor and ceiling division of a module by a scalar. It also gives the floor on the extended nonnegative reals.

The section needs the ordered rings and fields of Sections 1 and 2 and the floor function of Section 3. The proofs in the library are almost always the same two steps: a characterization such as $\lfloor a \rfloor = z \iff z \le a < z + 1$, and a computation in $\mathbb{Z}$.

### The library around it

#### Ceiling and floor of sums and negatives

The ceiling `Int.ceil a`, written `⌈a⌉`, is the least integer at least $a$. It satisfies `Int.ceil_eq_iff`: $\lceil a \rceil = z \iff z - 1 < a \le z$. The floor and the ceiling are related by negation: `Int.ceil_neg` says $\lceil -a \rceil = -\lfloor a \rfloor$ and `Int.floor_neg` says $\lfloor -a \rfloor = -\lceil a \rceil$. Proof: $z \le -a \iff -z \ge a$, so the greatest $z$ with $z \le -a$ is minus the least $w$ with $w \ge a$. The lemma `Int.ceil_le_floor_add_one` says $\lceil a \rceil \le \lfloor a \rfloor + 1$.

The floor commutes with the addition of an integer, by `Int.floor_add_intCast`, `Int.floor_add_natCast` and `Int.floor_add_one`. For two arbitrary elements there is a carry: `Int.floor_add_eq_or` says $\lfloor a + b \rfloor$ is $\lfloor a \rfloor + \lfloor b \rfloor$ or $\lfloor a \rfloor + \lfloor b \rfloor + 1$. Proof: write $a = \lfloor a \rfloor + \{a\}$ and $b = \lfloor b \rfloor + \{b\}$. Then $\lfloor a + b \rfloor = \lfloor a \rfloor + \lfloor b \rfloor + \lfloor \{a\} + \{b\} \rfloor$, and $0 \le \{a\} + \{b\} < 2$. The lemma `Int.le_floor_add_floor` gives the lower bound in one inequality, and `Int.floor_add_eq_add_iff` and `Int.floor_add_eq_add_add_one_iff` say which case holds through the fractional parts.

The preimages of intervals under the floor are intervals: `Int.preimage_floor_singleton` says $\lfloor \cdot \rfloor^{-1}(m) = [m, m + 1)$, and `Int.preimage_Icc`, `Int.preimage_Ioo` and the others give the preimages of the intervals of $\mathbb{Z}$. Two elements with the same floor are close: `Int.abs_sub_lt_one_of_floor_eq_floor` says $|a - b| < 1$.

#### The fractional part

The fractional part `Int.fract a` is $a - \lfloor a \rfloor$. It lies in $[0, 1)$, by `Int.fract_nonneg` and `Int.fract_lt_one`, and `Int.floor_add_fract` says $\lfloor a \rfloor + \{a\} = a$. The main rules are these.

| Lean name | Statement |
| --- | --- |
| `Int.fract_add_intCast` | $\{a + m\} = \{a\}$ for $m \in \mathbb{Z}$ |
| `Int.fract_eq_fract` | $\{a\} = \{b\} \iff a - b \in \mathbb{Z}$ |
| `Int.fract_add` | $\{a + b\} - \{a\} - \{b\} \in \mathbb{Z}$ |
| `Int.fract_add_le` | $\{a + b\} \le \{a\} + \{b\}$ |
| `Int.fract_neg` | $\{-a\} = 1 - \{a\}$ when $\{a\} \neq 0$ |
| `Int.fract_eq_zero_iff` | $\{a\} = 0 \iff a \in \mathbb{Z}$ |
| `Int.fract_div_natCast_eq_div_natCast_mod` | $\{m / n\} = (m \bmod n)/n$ |

The theorem `Int.fract_eq_fract` says that the fractional part is the quotient map $R \to R/\mathbb{Z}$ with the representatives in $[0, 1)$. Proof: if $a - b = z$, then $\lfloor a \rfloor = \lfloor b \rfloor + z$ and the fractional parts agree. Conversely $a - b = \lfloor a \rfloor - \lfloor b \rfloor$ when $\{a\} = \{b\}$. The `Int.fract_neg` rule shows why $\{a\} \neq 0$ is needed: for $a = 1$, $\{-1\} = 0$ and not $1 - 0$.

#### Maps and uniqueness

A floor function is unique: `subsingleton_floorRing` says that a linearly ordered ring has at most one `FloorRing` structure. So any two proofs that $R$ has a floor give the same floor, and the floor is preserved by each strictly monotone ring map. The theorem `Int.map_floor` says $\lfloor f(a) \rfloor = \lfloor a \rfloor$ for a strictly monotone ring map $f : R \to S$ between floor rings, and `Int.map_ceil` and `Int.map_fract` are the forms for the ceiling and the fractional part. Proof: $f$ keeps the integers and the order, so it keeps the condition $z \le a < z + 1$.

#### The natural floor and quotients

For a semiring, the class `FloorSemiring R` gives the natural floor `Nat.floor a`, written `⌊a⌋₊`, and the natural ceiling `Nat.ceil a`. The natural floor is $0$ for negative $a$, by `Nat.floor_of_nonpos`. The lemma `Nat.floor_eq_iff` says $\lfloor a \rfloor_{\mathbb{N}} = n \iff n \le a < n + 1$ for $a \ge 0$, and the module `Mathlib.Algebra.Order.Floor.Semiring` repeats the integer API for it, such as `Nat.floor_add_natCast` and `Nat.ceil_add_natCast`. The instance `Nonneg.floorSemiring` gives the nonnegative part of a floor semiring the same floor.

The floor of a quotient by a natural number is the quotient of the floor. In a field, `Int.floor_div_natCast` says $\lfloor a / n \rfloor = \lfloor a \rfloor / n$, with integer division on the right, and `Nat.floor_div_natCast` is the natural form. The case $a = m$ gives `Nat.floor_div_eq_div`: $\lfloor m / n \rfloor_{\mathbb{N}} = m / n$, the floor of the rational quotient is the natural quotient. Proof of the general rule: $\lfloor a \rfloor = qn + r$ with $0 \le r < n$, so $q \le a/n < q + 1$, since $a < \lfloor a \rfloor + 1 \le (q + 1) n$.

The norm_num extension `Mathlib.Meta.NormNum.evalNatFloor` computes $\lfloor q \rfloor_{\mathbb{N}}$ for a numeral $q$, and the positivity extensions such as `Mathlib.Meta.Positivity.evalIntCeil` prove the positivity of a ceiling.

#### Hermite's identity

The module `Mathlib.Algebra.Order.Floor.BigOperators` proves Hermite's identity, `Int.sum_floor_add_div`:
$$\sum_{i=0}^{n-1} \left\lfloor x + \frac{i}{n} \right\rfloor = \lfloor n x \rfloor.$$
Proof sketch: both sides increase by $n$ when $x$ increases by $1$, so it is enough to prove the identity for $x \in [0, 1)$. Write $x \in [k/n, (k+1)/n)$. Then $\lfloor x + i/n \rfloor$ is $1$ for $i \ge n - k$ and $0$ otherwise, so the sum is $k$, and $\lfloor nx \rfloor = k$. The integer version `Int.sum_range_add_ediv` says $\sum_{i < n} \lfloor (m + i)/n \rfloor = m$.

#### Rounding

The function `round x` is the nearest integer to $x$, with halves rounded up. In a field, `round_eq` says $\operatorname{round}(x) = \lfloor x + 1/2 \rfloor$. So `round_two_inv` says $\operatorname{round}(1/2) = 1$ and `round_neg_two_inv` says $\operatorname{round}(-1/2) = 0$. Rounding does not commute with negation at the halves. The error is at most one half, by `abs_sub_round`, and `round_le` says that no integer is nearer: $|x - \operatorname{round} x| \le |x - z|$. The exact error is `abs_sub_round_eq_min`: $|x - \operatorname{round} x| = \min(\{x\}, 1 - \{x\})$. Like the floor, rounding commutes with integer translation, by `round_add_intCast`, and with strictly monotone ring maps, by `Int.map_round`.

#### Floor and ceiling division

The module `Mathlib.Algebra.Order.Floor.Div` defines a floor division of an ordered module $\beta$ by a positive scalar $a \in \alpha$. The class `FloorDiv α β` has the operation `b ⌊/⌋ a` with the Galois connection `le_floorDiv_iff_smul_le`: $c \le b \lfloor/\rfloor a \iff a \cdot c \le b$. The class `CeilDiv α β` has `b ⌈/⌉ a` with `ceilDiv_le_iff_le_smul`: $b \lceil/\rceil a \le c \iff b \le a \cdot c$. For $\mathbb{N}$, `Nat.floorDiv_eq_div` says that floor division is the usual division, and `Nat.ceilDiv_eq_add_pred_div` says $a \lceil/\rceil b = (a + b - 1)/b$. The instances `Pi.instFloorDiv` and `Finsupp.instFloorDiv` divide functions pointwise, by `Pi.floorDiv_apply` and `Finsupp.floorDiv_apply`. The use of the general form is the division of a multiset or a monomial exponent vector by a natural number, coordinate by coordinate.

#### The extended floor

The module `Mathlib.Algebra.Order.Floor.Extended` defines `ENat.floor` and `ENat.ceil`, maps from the extended nonnegative reals to $\mathbb{N} \cup \{\infty\}$. They satisfy `ENat.floor_eq_top`: $\lfloor r \rfloor_e = \top \iff r = \top$. The Galois connections `ENat.gc_toENNReal_floor` and `ENat.gc_ceil_toENNReal` characterize them as the adjoints of the inclusion, so the API is the same as for the integer floor.

#### Common errors

1. `Nat.floor` of a negative element is $0$. A lemma such as `Nat.floor_eq_iff` needs the hypothesis $0 \le a$, and the identity $\lfloor a \rfloor_{\mathbb{N}} = \lfloor a \rfloor$ holds only for $a \ge 0$.
2. `Int.fract (-a)` is not $-\{a\}$. The fractional part is always in $[0, 1)$, and `Int.fract_neg` gives $1 - \{a\}$ when $a \notin \mathbb{Z}$.
3. `round` rounds halves up, so $\operatorname{round}(-x) = -\operatorname{round}(x)$ fails for $x = 1/2$. Use `round_neg_two_inv` and `round_two_inv` to check the convention.

### Exercises

1. (A) Compute $\lfloor -7/2 \rfloor$, $\lceil -7/2 \rceil$ and $\{-7/2\}$ in $\mathbb{Q}$, and check `Int.ceil_neg`.
2. (A) Find $a, b \in \mathbb{Q}$ with $\lfloor a + b \rfloor = \lfloor a \rfloor + \lfloor b \rfloor + 1$.
3. (B) Prove `Int.fract_add_le` from `Int.floor_add_eq_or`.
4. (B) Verify Hermite's identity for $n = 3$ and $x = 5/4$.
5. (B) Prove $\lfloor a/n \rfloor = \lfloor \lfloor a \rfloor / n \rfloor$ for $a \in \mathbb{Q}$ and an integer $n \ge 1$, where both quotients are rational.
6. (C) Prove `subsingleton_floorRing`: two floor functions on a linearly ordered ring are equal.

### Reference

<?reference?>
