---
title: Ordered semirings and fields, the lemma library
kind: api
modules:
  - Mathlib.Algebra.Order.Ring.Unbundled.Basic
  - Mathlib.Algebra.Order.Ring.Unbundled.Rat
  - Mathlib.Algebra.Order.Ring.Basic
  - Mathlib.Algebra.Order.Ring.Canonical
  - Mathlib.Algebra.Order.Ring.Cast
  - Mathlib.Algebra.Order.Ring.Pow
  - Mathlib.Algebra.Order.Ring.GeomSum
  - Mathlib.Algebra.Order.Ring.Finset
  - Mathlib.Algebra.Order.Ring.Idempotent
  - Mathlib.Algebra.Order.Ring.InjSurj
  - Mathlib.Algebra.Order.Ring.Int
  - Mathlib.Algebra.Order.Ring.Nat
  - Mathlib.Algebra.Order.Ring.NNRat
  - Mathlib.Algebra.Order.Ring.Interval
  - Mathlib.Algebra.Order.Ring.Units
  - Mathlib.Algebra.Order.Invertible
  - Mathlib.Algebra.Order.Chebyshev
  - Mathlib.Algebra.Order.Algebra
  - Mathlib.Algebra.Order.Field.Canonical
  - Mathlib.Algebra.Order.Field.GeomSum
  - Mathlib.Algebra.Order.Field.Pi
  - Mathlib.Algebra.Order.Field.Pointwise
  - Mathlib.Algebra.Order.Field.Power
  - Mathlib.Algebra.Order.Field.Rat
  - Mathlib.Algebra.Order.Field.Subfield
explains:
  E2: [mul_nonneg_iff, mul_le_mul_of_nonpos_left, two_mul_le_add_sq, one_add_mul_le_pow, Odd.strictMono_pow, geom_sum_pos_iff, geom_sum_eq_zero_iff_neg_one, sq_sum_le_card_mul_sum_sq, Monovary.sum_mul_sum_le_card_mul_sum, isOrderedModule_iff_algebraMap_mono]
  E1: auto
families: []
requires: [V06.C01, V06.C03, V04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Ordered semirings and fields, the lemma library

### Overview

Sections 1 and 2 define ordered semirings and ordered fields and prove the basic rules. This section is a guide to the rest of the lemma library: the rules for signs of products, the inequalities for powers and geometric sums, the inequalities of Chebyshev and of Cauchy and Schwarz for finite sums, casts from $\mathbb{Z}$, and ordered algebras. Most of these lemmas are short, but there are many of them, and their names follow fixed patterns. A reader who knows the patterns can guess the name of a lemma before the search.

The modules `Mathlib.Algebra.Order.Ring.Unbundled.Basic` and `Mathlib.Algebra.Order.Ring.Unbundled.Rat` state the lemmas with the weakest hypotheses. A lemma there assumes only the order classes that its proof uses, such as `PosMulMono R` or `ExistsAddOfLE R`, and not `IsOrderedRing R`. So the same lemma applies to $\mathbb{N}$, to $\mathbb{Z}$, to ordered fields and to some structures that are not ordered rings.

### The library around it

#### Signs of products

The central sign rules have the forms below. The names put the condition on the factors in the order of the factors: `mul_nonneg_iff_of_pos_left` has its condition on the left factor.

| Lean name | Statement |
| --- | --- |
| `mul_nonneg_iff` | $0 \le ab \iff (0 \le a \wedge 0 \le b) \vee (a \le 0 \wedge b \le 0)$ |
| `mul_pos_iff` | $0 < ab \iff (0 < a \wedge 0 < b) \vee (a < 0 \wedge b < 0)$ |
| `mul_nonpos_iff` | $ab \le 0 \iff (0 \le a \wedge b \le 0) \vee (a \le 0 \wedge 0 \le b)$ |
| `mul_pos_of_neg_of_neg` | $a < 0 \to b < 0 \to 0 < ab$ |
| `mul_le_mul_of_nonpos_left` | $b \le a \to c \le 0 \to ca \le cb$ |
| `mul_lt_mul_left_of_neg` | $c < 0 \to (ca < cb \iff b < a)$ |
| `mul_self_pos` | $0 < a a \iff a \neq 0$ |

The lemmas `mul_nonneg_iff` and `mul_pos_iff` need a linear order. In a partial order, two elements can both be incomparable with $0$. The proof of `mul_le_mul_of_nonpos_left` shows the role of `ExistsAddOfLE R`. Write $a = b + d$ and $0 = c + e$ with $0 \le d$ and $0 \le e$. Then $ea \ge eb$, and adding $ca + cb$ gives $ca \le cb$ after cancellation. In a ring this is the usual argument with $-c$, but the lemma applies also to semirings without negation.

The monotone forms follow the same rules: `Monotone.const_mul_of_nonpos` says that $x \mapsto c f(x)$ is antitone for $c \le 0$ and a monotone $f$, and `StrictMono.const_mul_of_neg` is the strict form. The comparison forms `cmp_mul_pos_left` and `cmp_mul_neg_left` say how multiplication by a positive or negative element changes `cmp`.

#### Squares, the AM-GM inequality and the rearrangement rule

The inequality of the arithmetic and geometric means for two terms is `two_mul_le_add_sq`: $2ab \le a^2 + b^2$. Proof: $a^2 + b^2 - 2ab = (a - b)^2 \ge 0$. The form `four_mul_le_sq_add` is $4ab \le (a + b)^2$. The lemma `mul_self_le_mul_self_iff` says $a^2 \le b^2 \iff a \le b$ for nonnegative $a$ and $b$, and `nonneg_le_nonneg_of_sq_le_sq` gives one direction with weaker hypotheses. In the module `Mathlib.Algebra.Order.Ring.Basic`, `IsSquare.nonneg` says that a square is nonnegative, and so `not_isSquare_of_neg` says that a negative element is not a square.

The rearrangement rule for two pairs is `mul_add_mul_le_mul_add_mul`: if $a \le b$ and $c \le d$, then $ad + bc \le ac + bd$. Proof: $(ac + bd) - (ad + bc) = (b - a)(d - c) \ge 0$. The sum is larger when the large factors are paired.

#### Powers and Bernoulli's inequality

Bernoulli's inequality is `one_add_mul_le_pow`: for $a \ge -2$ and each $n$, $1 + na \le (1 + a)^n$. Proof by induction: $(1 + a)^{n+2} = (1+a)^n (1+a)^2$, so the step from $n$ to $n + 2$ multiplies the claim for $n$ by $(1 + a)^2 \ge 0$. Then $(1 + na)(1 + a)^2 = 1 + (n+2)a + a^2(n(2 + a) + 1)$, and the last term is nonnegative because $a \ge -2$. The cases $n = 0$ and $n = 1$ start the induction. The bound $-2$ is the place where the step needs $2 + a \ge 0$, and `one_add_mul_le_pow_of_sq_nonneg` states the lemma with these conditions for a semiring.

The parity of the exponent fixes the sign of a power. `Even.pow_nonneg` says $0 \le a^n$ for even $n$. For odd $n$, `Odd.pow_neg_iff` says $a^n < 0 \iff a < 0$, and `Odd.strictMono_pow` says that $a \mapsto a^n$ is strictly monotone on the whole ring. Proof of the second: on $[0, \infty)$ the power is strictly monotone, and $(-a)^n = -a^n$ extends this to negative elements. So `Odd.pow_injective` says that an odd power is injective. Over a field, the module `Mathlib.Algebra.Order.Field.Power` proves the same rules for integer powers, such as `Even.zpow_nonneg`, `Odd.zpow_neg_iff`, `abs_zpow` and `zpow_eq_one_iff_of_ne_zero₀`. The estimate `pow_add_pow_le` says $x^n + y^n \le (x + y)^n$ for nonnegative $x, y$ and $n \neq 0$, and `add_pow_le` is the converse with a factor: $(a + b)^n \le 2^{n-1}(a^n + b^n)$.

#### Geometric sums

The sum $\sum_{i < n} x^i$ has the following sign rules in an ordered ring. The theorem `geom_sum_pos` says that it is positive for $x \ge 0$ and $n \neq 0$. For any $x$, `geom_sum_pos_iff` says that it is positive exactly when $n$ is odd or $x > -1$, and `geom_sum_eq_zero_iff_neg_one` says that it is $0$ exactly when $x = -1$ and $n$ is even. Proof sketch of the second: for $x \neq 1$ the sum is $(1 - x^n)/(1 - x)$ in the field of fractions, and $x^n = 1$ with $x \neq 1$ in an ordered ring forces $x = -1$ and $n$ even. The lemmas `geom_sum_alternating_of_le_neg_one` and `geom_sum_alternating_of_lt_neg_one` describe the signs for $x \le -1$, which alternate with $n$.

In a canonically ordered semifield such as $\mathbb{Q}_{\ge 0}$, the module `Mathlib.Algebra.Order.Field.GeomSum` gives the closed form `geom_sum_of_lt_one` for $x < 1$ and the bound `geom_sum_lt`: $\sum_{i < n} x^i < (1 - x)^{-1}$ for $0 < x < 1$. For natural numbers, `Nat.geomSum_lt` bounds a sum of digits in base $b$ by the next power, which is the key step in the uniqueness of base-$b$ expansions.

#### Finite sums: Chebyshev and Cauchy-Schwarz

Two functions $f, g : \iota \to \alpha$ are monovarying, `Monovary f g`, when $g(i) < g(j)$ implies $f(i) \le f(j)$. The module `Mathlib.Algebra.Order.Chebyshev` proves the sum inequality of Chebyshev, `Monovary.sum_mul_sum_le_card_mul_sum`:
$$\Big(\sum_i f(i)\Big)\Big(\sum_i g(i)\Big) \le |\iota| \sum_i f(i) g(i).$$
Proof: $\sum_{i,j} (f(i) - f(j))(g(i) - g(j)) \ge 0$, since each term is nonnegative for monovarying functions, and the left side expands to $2|\iota| \sum f g - 2 \sum f \sum g$. For antivarying functions the inequality reverses, by `Antivary.card_mul_sum_le_sum_mul_sum`.

With $g = f$ the inequality becomes `sq_sum_le_card_mul_sum_sq`: $(\sum_{i \in s} f(i))^2 \le |s| \sum_{i \in s} f(i)^2$. This is the Cauchy-Schwarz inequality for the vectors $f$ and $(1, \dots, 1)$. The form `sum_div_card_sq_le_sum_sq_div_card` says that the square of the mean is at most the mean of the squares. The power version `pow_sum_le_card_mul_sum_pow` is $(\sum f)^{n+1} \le |s|^n \sum f^{n+1}$ for nonnegative $f$.

#### Casts and the number systems

The cast $\mathbb{Z} \to R$ into an ordered ring keeps the order. The module `Mathlib.Algebra.Order.Ring.Cast` has `Int.cast_le`, `Int.cast_lt`, `Int.cast_nonneg`, `Int.cast_pos`, `Int.cast_abs`, `Int.cast_max` and `Int.cast_min`. The instances for the number systems are `Nat.instIsStrictOrderedRing`, `Int.instIsStrictOrderedRing` of Section 1 and `NNRat.instIsStrictOrderedRing`. The order on $\mathbb{Q}$ is defined in `Mathlib.Algebra.Order.Ring.Unbundled.Rat` through the numerator: `Rat.num_pos` says $0 < q \iff 0 < q_{\mathrm{num}}$, and `Rat.divInt_le_divInt` says $a/b \le c/d \iff ad \le cb$ for positive $b$ and $d$.

A structure that embeds in an ordered ring is an ordered ring. `Function.Injective.isOrderedRing` takes a map that keeps $0$, $1$, addition, multiplication and the order, and `Function.Injective.isStrictOrderedRing` is the strict form. So `Subfield.toIsStrictOrderedRing` orders each subfield of an ordered field. The canonically ordered semirings, where $a \le b$ means $b = a + c$, are ordered by `CanonicallyOrderedAdd.toIsOrderedRing`, and the truncated subtraction satisfies `tsub_mul` and `mul_self_tsub_mul_self`: $a^2 - b^2 = (a + b)(a - b)$ in $\mathbb{N}$.

#### Ordered algebras and the remaining modules

An algebra $\beta$ over an ordered semiring $\alpha$ is an ordered module exactly when the structure map is monotone: `isOrderedModule_iff_algebraMap_mono`. Proof: $a \cdot b = \operatorname{algebraMap}(a) \, b$, so monotone scalar multiplication is monotone multiplication by $\operatorname{algebraMap}(a)$. The lemmas `algebraMap_mono`, `algebraMap_nonneg` and `algebraMap_pos` give the consequences, and the extension `Mathlib.Meta.Positivity.evalAlgebraMap` lets the tactic `positivity` prove $0 \le \operatorname{algebraMap}(a)$.

The other modules are small:

- `Mathlib.Algebra.Order.Invertible` gives the order of `⅟a`, such as `invOf_pos`: $0 < ⅟a \iff 0 < a$.
- `Mathlib.Algebra.Order.Ring.Units` says by `Units.index_posSubgroup` that the positive units have index $2$ in the units of an ordered ring.
- `Mathlib.Algebra.Order.Ring.Idempotent` orders the idempotents of a commutative ring as a Boolean algebra, with $e \le f$ when $ef = e$, and `OrderIso.isIdempotentElemMulZeroAddOne` matches them with the pairs $(e, 1 - e)$.
- `Mathlib.Algebra.Order.Ring.Interval` gives `IsStrictOrderedRing.int_eq_of_mul_mem_Ioo`: if $rk$ is strictly between $r(m-1)$ and $r(m+1)$ for $r > 0$, then $k = m$.
- `Mathlib.Algebra.Order.Ring.Finset` moves casts and constant factors through `Finset.sup`, such as `Finset.mul_sup₀`.
- `Mathlib.Algebra.Order.Field.Pointwise` scales intervals: `LinearOrderedField.smul_Icc` says $r [a, b] = [ra, rb]$ for $r > 0$.
- `Mathlib.Algebra.Order.Field.Pi` gives `Pi.exists_forall_pos_add_lt`, one $\varepsilon$ for finitely many strict inequalities.
- `Mathlib.Algebra.Order.Field.Canonical` and `Mathlib.Algebra.Order.Field.Rat` make a canonically ordered semifield, such as $\mathbb{Q}_{\ge 0}$, into a linearly ordered group with zero, and give `tsub_div`.

#### Common errors

1. `mul_nonneg_iff` and `mul_pos_iff` need a linear order. For a partial order, use the one-way lemmas such as `mul_nonneg` and `mul_pos_of_neg_of_neg`.
2. Bernoulli's inequality `one_add_mul_le_pow` needs $a \ge -2$. The statement is false below this bound: for $a = -4$ and $n = 3$ it says $-11 \le -27$.
3. In $\mathbb{N}$ subtraction is truncated, so `tsub_mul` and `mul_tsub` are the forms to use. The ring lemmas `sub_mul` and `mul_sub` do not apply.

### Exercises

1. (A) Prove $0 \le a b$ for $a, b \le 0$ in an ordered ring with `mul_nonneg_iff`.
2. (A) Use `one_add_mul_le_pow` to prove $1.01^{100} \ge 2$ in $\mathbb{Q}$.
3. (B) Prove `two_mul_le_add_sq` from the nonnegativity of $(a - b)^2$.
4. (B) Show that $\sum_{i < 5} (-2)^i > 0$ with `geom_sum_pos_iff`, and compute the sum.
5. (B) Derive $(a + b + c)^2 \le 3(a^2 + b^2 + c^2)$ from `sq_sum_le_card_mul_sum_sq`.
6. (C) Prove Chebyshev's inequality for two increasing sequences of length $n$ from the double sum $\sum_{i,j} (f(i) - f(j))(g(i) - g(j))$.

### Reference

<?reference?>
