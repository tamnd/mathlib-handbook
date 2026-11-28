---
title: The cast from ℚ and the cast lemmas in special settings
kind: api
modules:
  - Mathlib.Data.Rat.Cast.CharZero
  - Mathlib.Data.Rat.Cast.Lemmas
  - Mathlib.Data.Rat.Cast.OfScientific
  - Mathlib.Data.Rat.Cast.Order
  - Mathlib.Data.Rat.BigOperators
  - Mathlib.Data.Nat.Cast.Commute
  - Mathlib.Data.Nat.Cast.NeZero
  - Mathlib.Data.Nat.Cast.Order.Ring
  - Mathlib.Data.Nat.Cast.Pi
  - Mathlib.Data.Nat.Cast.Prod
  - Mathlib.Data.Nat.Cast.SetInterval
  - Mathlib.Data.Nat.Cast.WithTop
  - Mathlib.Data.Nat.Cast.Synonym
explains:
  E2: [Rat.cast_add, Rat.cast_injective, Rat.cast_le, Nat.cast_comm, Nat.cast_tsub, Rat.cast_pow]
  E1: auto
families: []
requires: [V02.C04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The cast from ℚ and the cast lemmas in special settings

### Overview

The first section of this chapter defines the casts from `ℕ`, `ℤ` and `ℚ` and proves their rules for the operations of a ring. The cast from `ℚ` needs more care than the other two. A rational number $p = a/b$ goes to $a \cdot b^{-1}$ in a division ring $\alpha$, and this is a ring homomorphism only when $b$ is not zero in $\alpha$, that is, when $\alpha$ has characteristic zero. The modules of this section hold the rules for the cast from `ℚ` and from `ℚ≥0`: first the algebraic rules under `CharZero`, then the rules for the order in a linearly ordered field.

The other modules of the section are small. They give the cast lemmas for special targets: commutation in a noncommutative semiring, the order in an ordered ring, functions and pairs, intervals of integers, and `WithTop ℕ`. Each lemma is short, but the tactics `push_cast` and `norm_cast` need all of them, so the reader meets their names in the goals.

### The library around it

#### The algebraic rules for the cast from ℚ

The cast `Rat.cast : ℚ → α` is defined in each division ring by $q \mapsto \mathrm{num}(q) / \mathrm{den}(q)$, the content of `Rat.cast_def`. Some rules hold in each division ring. The module `Mathlib.Data.Rat.Cast.Lemmas` has `Rat.cast_pow`, $\uparrow(p^n) = (\uparrow p)^n$, and the inverses of integers and of natural numbers, `Rat.cast_inv_int` and `Rat.cast_inv_nat`. The power rule holds without a hypothesis on $\alpha$, because $(p^n)$ has numerator $\mathrm{num}(p)^n$ and denominator $\mathrm{den}(p)^n$, with no cancellation, and the casts of two integers commute.

The rules for the sum and the product need `CharZero α`. In `ZMod 2` the cast of $\frac12$ is $1 \cdot 2^{-1} = 1 \cdot 0^{-1} = 0$, by the junk value $0^{-1} = 0$. Then $\uparrow(\frac12 + \frac12) = \uparrow 1 = 1$, but $\uparrow\frac12 + \uparrow\frac12 = 0$. The module `Mathlib.Data.Rat.Cast.CharZero` gives the rules under the hypothesis:

| Lean name | Statement |
|---|---|
| `Rat.cast_add` | $\uparrow(p + q) = \uparrow p + \uparrow q$ |
| `Rat.cast_sub` | $\uparrow(p - q) = \uparrow p - \uparrow q$ |
| `Rat.cast_mul` | $\uparrow(p q) = \uparrow p \cdot \uparrow q$ |
| `Rat.cast_inv` | $\uparrow(p^{-1}) = (\uparrow p)^{-1}$ |
| `Rat.cast_div` | $\uparrow(p / q) = \uparrow p / \uparrow q$ |
| `Rat.cast_zpow` | $\uparrow(p^n) = (\uparrow p)^n$ for $n \in \mathbb{Z}$ |
| `Rat.cast_divInt` | $\uparrow(a / b) = \uparrow a / \uparrow b$ for $a, b \in \mathbb{Z}$ |
| `Rat.cast_inj` | $\uparrow p = \uparrow q \iff p = q$ |
| `Rat.cast_eq_zero` | $\uparrow p = 0 \iff p = 0$ |

**Proof sketch of `Rat.cast_add`.** Write $p = a/b$ and $q = c/d$ in lowest terms, with $b, d > 0$. In characteristic zero, the casts of $b$ and $d$ are not zero. First prove that each fraction $m/k$ with $k \ne 0$ has the cast $\uparrow m / \uparrow k$, also when the fraction is not in lowest terms: if $m/k = a/b$, then $m b = a k$ in $\mathbb{Z}$, so $\uparrow m \uparrow b = \uparrow a \uparrow k$ in $\alpha$, and division by $\uparrow b \uparrow k \ne 0$ gives the claim. Then $p + q = (a d + b c)/(b d)$ gives $\uparrow(p + q) = (\uparrow a \uparrow d + \uparrow b \uparrow c) / (\uparrow b \uparrow d) = \uparrow a / \uparrow b + \uparrow c / \uparrow d$. $\square$

The rules together make the bundled ring homomorphism `Rat.castHom α : ℚ →+* α`, with `Rat.coe_castHom` as its simp lemma. Each ring homomorphism from a field of characteristic zero is injective, so `Rat.cast_injective` holds. For the nonnegative rationals, the same file has the family `NNRat.cast_add`, `NNRat.cast_mul`, `NNRat.cast_inv`, `NNRat.cast_div`, `NNRat.cast_zpow`, `NNRat.cast_inj` and `NNRat.cast_divNat` in a division semiring of characteristic zero, with the bundled `NNRat.castHom`. The cast from `ℚ≥0` through `ℚ` is the direct cast, by `Rat.cast_nnratCast`.

The module `Mathlib.Data.Rat.BigOperators` extends the rules to finite sums and products: `Rat.cast_sum`, `Rat.cast_prod`, `Rat.cast_list_sum`, `Rat.cast_list_prod`, `Rat.cast_multiset_sum` and `Rat.cast_multiset_prod`. The rules for products need a field, since a product over a `Finset` uses commutativity. The module `Mathlib.Data.Rat.Cast.OfScientific` gives the instance `instLawfulOfScientificOfCharZero`, which tells the tactic `grind` that a decimal literal such as `1.5` in a field of characteristic zero is the cast of the rational number with the same value. The lemma `Rat.cast_ofScientific` states the same fact for the cast.

#### The order rules for the cast from ℚ

In a linearly ordered field $K$, the cast from `ℚ` is a strict order embedding. The module `Mathlib.Data.Rat.Cast.Order` states this as `Rat.cast_strictMono` and bundles it as `Rat.castOrderEmbedding : ℚ ↪o K`.

**Proof sketch of `Rat.cast_le`.** First, $\uparrow q \geq 0$ if and only if $q \geq 0$. Indeed $\uparrow q = \uparrow\mathrm{num}(q) / \uparrow\mathrm{den}(q)$ with a positive denominator, so its sign is the sign of $\mathrm{num}(q)$, which is the sign of $q$. Then $\uparrow p \leq \uparrow q$ if and only if $0 \leq \uparrow q - \uparrow p = \uparrow(q - p)$, if and only if $0 \leq q - p$. $\square$

The names follow the pattern of the casts from `ℕ` and `ℤ`:

| Lean name | Statement |
|---|---|
| `Rat.cast_le`, `Rat.cast_lt` | $\uparrow p \leq \uparrow q \iff p \leq q$, and the same for $<$ |
| `Rat.cast_nonneg`, `Rat.cast_pos` | $0 \leq \uparrow q \iff 0 \leq q$, and the same for $<$ |
| `Rat.cast_nonpos`, `Rat.cast_lt_zero` | the signs on the other side |
| `Rat.cast_min`, `Rat.cast_max`, `Rat.cast_abs` | the cast commutes with $\min$, $\max$ and $\lvert \cdot \rvert$ |
| `Rat.cast_le_natCast`, `Rat.natCast_le_cast` | comparison of $\uparrow q$ with the cast of a natural number |
| `Rat.cast_le_intCast`, `Rat.intCast_lt_cast` | comparison of $\uparrow q$ with the cast of an integer |
| `Rat.preimage_cast_Icc`, `Rat.preimage_cast_Ioi` | the preimage of an interval with rational ends is the interval in `ℚ` |

The preimage lemmas exist for each kind of interval, from `Rat.preimage_cast_Ioo` to `Rat.preimage_cast_uIoc`. The family for `ℚ≥0` in a linearly ordered semifield has the same names with the prefix `NNRat.`: `NNRat.cast_le`, `NNRat.cast_lt`, `NNRat.cast_pos`, `NNRat.one_le_cast`, `NNRat.cast_le_ofNat` and `NNRat.preimage_cast_Icc`. The module also extends the tactic `positivity` with `Mathlib.Meta.Positivity.evalRatCast`, so `positivity` proves $0 < \uparrow q$ from $0 < q$.

#### Casts from ℕ in special settings

The module `Mathlib.Data.Nat.Cast.Commute` treats a semiring that need not be commutative. The cast of a natural number commutes with each element.

**Proof of `Nat.cast_comm`.** Induction on $n$. For $n = 0$, both sides of $\uparrow 0 \cdot x = x \cdot \uparrow 0$ are $0$. For the step, $\uparrow(n + 1) \cdot x = \uparrow n \cdot x + x = x \cdot \uparrow n + x = x \cdot \uparrow(n + 1)$, by the distributive laws and the hypothesis. $\square$

The module states the fact in the forms that the API of `Commute` needs: `Nat.cast_commute`, `Nat.commute_cast`, `Commute.ofNat_left` and `Commute.ofNat_right` for literals, and `Commute.natCast_mul_left`, `Commute.natCast_mul_right` and `Commute.natCast_mul_natCast_mul`, which say that $\uparrow m \cdot a$ and $\uparrow n \cdot b$ commute when $a$ and $b$ commute. The lemmas `SemiconjBy.natCast_mul_left` and `SemiconjBy.natCast_mul_right` are the forms for `SemiconjBy`. The additive forms are `Nat.cast_add_comm` and `Nat.addCommute_cast`.

The module `Mathlib.Data.Nat.Cast.Order.Ring` gives the order rules in an ordered semiring: `Nat.cast_nonneg`, `Nat.cast_pos`, `Nat.cast_min`, `Nat.cast_max`, and in an ordered ring `Nat.abs_cast`, which says $\lvert \uparrow n \rvert = \uparrow n$. The literal forms are `Nat.ofNat_nonneg`, `Nat.ofNat_pos` and `Nat.abs_ofNat`. The lemma `Nat.cast_eq_neg_cast` says that $\uparrow m = -\uparrow n$ only for $m = n = 0$. The lemma `Nat.cast_tsub` says $\uparrow(m - n) = \uparrow m - \uparrow n$ for the truncated subtraction, in a canonically ordered semiring with an ordered subtraction such as `ℝ≥0` or `ℕ` itself.

**Proof sketch of `Nat.cast_tsub`.** If $n \leq m$, write $m = n + k$; then $\uparrow m = \uparrow n + \uparrow k$, so $\uparrow m - \uparrow n = \uparrow k = \uparrow(m - n)$ by the law of the ordered subtraction. If $m < n$, then $m - n = 0$, and $\uparrow m \leq \uparrow n$ gives $\uparrow m - \uparrow n = 0$. $\square$

The module `Mathlib.Data.Nat.Cast.NeZero` connects the class `NeZero` on a cast with the class on the number. If `NeZero (n : R)` holds in some `R`, then `n ≠ 0` in `ℕ`, by `NeZero.of_neZero_natCast`, and `NeZero.pos_of_neZero_natCast` gives `0 < n`. The lemma `NeZero.one_le` gives `1 ≤ n` from `NeZero n`, and `NeZero.natCast_ne` gives `(n : R) ≠ 0` from the instance.

#### Functions, pairs, intervals and WithTop

The cast into a type of functions is pointwise: the module `Mathlib.Data.Nat.Cast.Pi` gives the instance `Pi.instNatCast`, with `Pi.natCast_apply`, the statement $(\uparrow n)(i) = \uparrow n$, and `Pi.natCast_def`. For pairs, `Mathlib.Data.Nat.Cast.Prod` gives `Prod.instAddMonoidWithOne` and the simp lemmas `Prod.fst_natCast`, `Prod.snd_natCast`, `Prod.fst_ofNat` and `Prod.snd_ofNat`.

The module `Mathlib.Data.Nat.Cast.SetInterval` computes the image of intervals of `ℕ` in `ℤ`. The image of $[a, b]$ is $[a, b]$ in `ℤ` by `Nat.image_cast_int_Icc`, and the same holds for each kind of interval. Intervals with no lower end become intervals from $0$: `Nat.image_cast_int_Iic` gives $[0, a]$, and `Nat.range_cast_int` says that the range of the cast is $[0, \infty)$.

The module `Mathlib.Data.Nat.Cast.WithTop` has two lemmas, `Nat.cast_withTop` and `Nat.cast_withBot`. Each says that two casts from `ℕ` into `WithTop ℕ` or `WithBot ℕ` agree: the coercion of the option type and the cast of an `AddMonoidWithOne`. The module also gives the well founded relation `instWellFoundedRelationWithTopNat`. The module `Mathlib.Data.Nat.Cast.Synonym` is deprecated, and its content is now in `Mathlib.Algebra.Order.Ring.Synonym`.

#### Common errors

1. The rule `Rat.cast_add` needs `CharZero α`. In `ZMod p` the cast from `ℚ` is not additive, and a proof that uses `push_cast` there fails with no clear message. Check the instance first.
2. The lemma `Rat.cast_le` needs a linearly ordered field. In `ℝ≥0` the right lemmas are the `NNRat.` forms for the cast from `ℚ≥0`.
3. For a literal such as `2`, the simp normal form is `OfNat.ofNat 2`, not the cast of the natural number $2$. So `Nat.cast_pos` does not match $0 < 2$; use `Nat.ofNat_pos` or `zero_lt_two`.

### Exercises

1. (A) Prove that $\uparrow(\frac{3}{4}) + \uparrow(\frac{1}{4}) = 1$ in `ℝ`, with `Rat.cast_add` and then with `push_cast`.
2. (A) Use `Rat.cast_lt` to show that $\uparrow p < \uparrow q$ in `ℝ` for rational $p < q$, and that `Rat.castOrderEmbedding` is injective.
3. (B) Show that in `ZMod 3` the cast from `ℚ` is not multiplicative, by a direct computation of $\uparrow(\frac13 \cdot 3)$ and $\uparrow\frac13 \cdot \uparrow 3$.
4. (B) Prove `Commute.natCast_mul_natCast_mul` from `Nat.cast_comm` and the laws of a semiring.
5. (B) Show that the image of the interval $(a, b)$ of `ℕ` under the cast to `ℤ` is the interval $(a, b)$ of `ℤ`, from the definitions.
6. (C) Prove that each ring homomorphism $f : \mathbb{Q} \to K$ into a field of characteristic zero is equal to `Rat.castHom K`, and deduce that it is injective.

### Reference

<?reference?>
