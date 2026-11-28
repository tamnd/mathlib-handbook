---
title: Bool, Ordering, signs and two-pointings
kind: api
modules:
  - Mathlib.Data.Bool.AllAny
  - Mathlib.Data.Bool.Count
  - Mathlib.Data.Bool.Set
  - Mathlib.Logic.Equiv.Bool
  - Mathlib.Data.Ordering.Basic
  - Mathlib.Data.Ordering.Lemmas
  - Mathlib.Basic.Sign.Defs
  - Mathlib.Basic.Sign.Basic
  - Mathlib.Data.Sign.Defs
  - Mathlib.Data.Sign.Basic
  - Mathlib.Basic.TwoPointing
  - Mathlib.Data.TwoPointing
explains:
  E2: [TwoPointing.nonempty_two_pointing_iff, List.IsChain.two_mul_count_bool_of_even, cmpUsing_eq_gt, sign_mul, self_mul_sign]
  E1: auto
families: []
requires: [V01.C01, V01.C03]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Bool, Ordering, signs and two-pointings

### Overview

The first section of this chapter sorted types by their size: empty, nonempty, with at most one element, with exactly one element, and nontrivial. This section treats some small types with a fixed number of elements. The type `Bool` has two elements, `false` and `true`. The type `Ordering` has three elements, `lt`, `eq` and `gt`, and it records the result of a comparison. The type `SignType` has three elements, $-1$, $0$ and $1$, and it records the sign of a number. Each of these types is small, but each has its own API, and a reader meets all three often.

The section ends with *two-pointings*. A two-pointing of $\alpha$ is a pair of two different elements of $\alpha$. A type has a two-pointing exactly when it is nontrivial, so `TwoPointing α` is the data that `Nontrivial α` asserts. The Boolean decisions of Chapter 1 and the equivalences of Chapter 3 are used throughout.

### The library around it

#### Booleans

The type `Bool` and its operations are in the core library. Chapter 1 explained the passage between a decidable proposition $p$ and the Boolean `decide p`. The module `Mathlib.Data.Bool.Set` describes `Bool` as a set: `Bool.univ_eq` states $\mathrm{univ} = \{\mathrm{false}, \mathrm{true}\}$, `Bool.compl_singleton` states $\{b\}^c = \{\lnot b\}$, and `Bool.range_eq` states that the range of $f : \mathrm{Bool} \to \alpha$ is $\{f\ \mathrm{false}, f\ \mathrm{true}\}$. The module `Mathlib.Logic.Equiv.Bool` states that negation is a bijection: `Bool.not_injective`, `Bool.not_surjective`, `Bool.not_bijective`, and `Bool.not_leftInverse` for $\lnot \lnot b = b$. The permutation `Equiv.boolNot : Equiv.Perm Bool` is negation as an equivalence, and it is its own inverse (`Equiv.boolNot_symm_apply`).

The module `Mathlib.Data.Bool.AllAny` connects the Boolean tests on lists with quantifiers. For a decidable predicate $p$, `List.all_iff_forall_prop` states that `l.all (fun a ↦ decide (p a)) = true` holds if and only if $\forall a \in l,\ p\,a$. The lemma `List.any_iff_exists_prop` is the form with $\exists$, and `List.any_of_mem` gives `l.any p = true` from one witness.

The module `Mathlib.Data.Bool.Count` counts the two values in a list of Booleans. The first lemma is `List.count_true_add_count_false`: the number of `true` plus the number of `false` is the length. The forms `List.count_false_add_count_true`, `List.count_add_count_not` and `List.count_not_add_count` state the same fact in other orders. The rest of the module treats *alternating* lists: lists $l$ with `List.IsChain (· ≠ ·) l`, where two neighbours always differ. Such a list is $b, \lnot b, b, \lnot b, \ldots$, so its counts are almost equal.

**Theorem.** Let $l$ be an alternating list of Booleans of even length. Then $2 \cdot \mathrm{count}(b, l) = \mathrm{length}(l)$ for each $b$.

*Proof.* By induction on the length, in steps of 2. The empty list has both sides $0$. A list of even length $n + 2$ has the form $a :: c :: l'$, with $c \neq a$ because the list alternates. The two Booleans $a$ and $c$ are different, so exactly one of them is $b$. The tail $l'$ is again alternating, of even length $n$. So $2 \cdot \mathrm{count}(b, l) = 2 + 2 \cdot \mathrm{count}(b, l') = 2 + n$. $\square$

This is `List.IsChain.two_mul_count_bool_of_even`. The lemma `List.IsChain.count_false_eq_count_true` is the same fact for the two values. For a list of odd length, the counts differ by one, and the head of the list decides which count is larger: see `List.IsChain.two_mul_count_bool_eq_ite`. The bounds `List.IsChain.count_not_le_count_add_one`, `List.IsChain.length_div_two_le_count_bool` and `List.IsChain.two_mul_count_bool_le_length_add_one` hold for every alternating list.

#### Comparisons

The type `Ordering` is in the core library. It is the result type of the comparison function `compare`. The module `Mathlib.Data.Ordering.Basic` defines the predicate `Ordering.Compares o a b`, which states that the ordering $o$ describes $a$ and $b$. It is $a < b$ for `lt`, $a = b$ for `eq` and $a > b$ for `gt`: these are `Ordering.compares_lt`, `Ordering.compares_eq` and `Ordering.compares_gt`. The module also defines `cmpUsing lt a b` for a decidable relation `lt`. It is `lt` when $\mathrm{lt}(a, b)$, `gt` when $\mathrm{lt}(b, a)$ and not $\mathrm{lt}(a, b)$, and `eq` in the other case. The function `cmp` is `cmpUsing` for the relation $<$ of the type. Two incomparable elements get the result `eq`, so `cmp` is honest only for a linear order.

**Theorem.** Let `lt` be a strict order. Then `cmpUsing lt a b = gt` if and only if $\mathrm{lt}(b, a)$.

*Proof.* By the definition, `cmpUsing lt a b = gt` holds if and only if $\lnot \mathrm{lt}(a, b)$ and $\mathrm{lt}(b, a)$. A strict order is asymmetric: $\mathrm{lt}(b, a)$ implies $\lnot \mathrm{lt}(a, b)$. So the first condition follows from the second. $\square$

This is `cmpUsing_eq_gt`, and it needs `IsStrictOrder`. The other two lemmas need no hypothesis: `cmpUsing_eq_lt` states that the result is `lt` exactly when $\mathrm{lt}(a, b)$, and `cmpUsing_eq_eq` states that it is `eq` exactly when neither $\mathrm{lt}(a, b)$ nor $\mathrm{lt}(b, a)$. The module `Mathlib.Data.Ordering.Lemmas` also has `Ordering.ite_eq_lt_distrib`, `Ordering.ite_eq_eq_distrib` and `Ordering.ite_eq_gt_distrib`, which push an equation with a constructor into the branches of an `if`.

#### Signs

The module `Mathlib.Basic.Sign.Defs` defines the inductive type `SignType` with the three constructors `SignType.zero`, `SignType.neg` and `SignType.pos`. The simp normal form writes them as $0$, $-1$ and $1$ (`SignType.zero_eq_zero`, `SignType.neg_eq_neg_one`, `SignType.pos_eq_one`). Every sign is one of the three (`SignType.trichotomy`). The type carries this structure:

| Lean name | Statement |
|---|---|
| `SignType.instLinearOrder` | the linear order $-1 < 0 < 1$ |
| `SignType.instCommGroupWithZero` | multiplication of signs, with $0$ absorbing |
| `SignType.instHasDistribNeg` | negation, with $-(a b) = (-a) b$ |
| `SignType.fin3Equiv` | `SignType ≃* Fin 3`, a multiplicative equivalence |
| `instFintypeSignType` | the three elements form a finite type |

The order lemmas have the usual names: `SignType.neg_one_le`, `SignType.le_one`, `SignType.nonneg_iff`, `SignType.pos_iff` and `SignType.neg_iff`. The coercion `SignType.cast` sends a sign to any type with $0$, $1$ and negation, with the lemmas `SignType.coe_zero`, `SignType.coe_one` and `SignType.coe_neg_one`. The lemma `SignType.map_cast'` states that a function that preserves $0$, $1$ and $-1$ commutes with the cast.

The sign of an element is `SignType.sign a`, for a preorder with zero and a decidable $<$. It is a monotone map, a term of `α →o SignType`. By `sign_apply`, it is $1$ when $0 < a$, $-1$ when $a < 0$, and $0$ otherwise. The basic computations are `sign_zero`, `sign_pos`, `sign_neg`, `sign_eq_one_iff`, `sign_eq_neg_one_iff` and, for a linear order, `sign_eq_zero_iff` and `sign_nonneg_iff`. The lemma `Int.sign_eq_sign` links the integer sign of the core library with this one.

The module `Mathlib.Basic.Sign.Basic` proves the algebraic laws in a linearly ordered ring.

**Theorem.** In a strictly ordered ring with a linear order, $\mathrm{sign}(xy) = \mathrm{sign}(x)\,\mathrm{sign}(y)$.

*Proof.* If $x = 0$ or $y = 0$, both sides are $0$. Otherwise each of $x$ and $y$ is positive or negative. The product of two positive or two negative elements is positive, and the product of a positive and a negative element is negative, by the order axioms of the ring. In each of the four cases, the sign of $xy$ is the product of the signs. $\square$

This is `sign_mul`, and `signHom` packages it as a map `α →*₀ SignType` that preserves $0$, $1$ and products. The lemma `sign_pow` follows. In the other direction, `SignType.castHom` is the cast as a map of monoids with zero.

**Theorem.** In the same rings, $x \cdot \mathrm{sign}(x) = |x|$.

*Proof.* If $x > 0$, then $\mathrm{sign}(x) = 1$ and $|x| = x$. If $x = 0$, both sides are $0$. If $x < 0$, then $\mathrm{sign}(x) = -1$ and $|x| = -x$. $\square$

This is `self_mul_sign`. The variants `sign_mul_self`, `abs_mul_sign` and `sign_mul_abs` change the order of the factors. Other lemmas of the module: `SignType.pow_odd` and `SignType.pow_even` for powers of a sign, `SignType.univ_eq` for the finset of all signs, `sign_sum` for a sum of terms of one sign, and `exists_signed_sum`, which writes an integer function on a finset as a sum of $\sum_a |f(a)|$ signs. The modules `Mathlib.Data.Sign.Defs` and `Mathlib.Data.Sign.Basic` have no live declarations.

#### Two-pointings

The structure `TwoPointing α` extends `α × α` with the field `TwoPointing.fst_ne_snd`, which states that the two components differ. The projection `TwoPointing.toProd` gives the pair. Extensionality is `TwoPointing.ext`. The standard two-pointings are `TwoPointing.bool` (with $\mathrm{false}$ first), `TwoPointing.prop` (with `False` first), `TwoPointing.prod` and `TwoPointing.sum` for products and sums, and `TwoPointing.pi` for a function type with a nonempty domain, by constant functions. The function `TwoPointing.swap` exchanges the two points, and `TwoPointing.swap_swap` states that it is an involution.

**Theorem.** A type $\alpha$ has a two-pointing if and only if $\alpha$ is nontrivial.

*Proof.* A two-pointing gives two elements $x \neq y$, which is the definition of `Nontrivial α`. Conversely, `exists_pair_ne` gives $x \neq y$ in a nontrivial type, and the pair $(x, y)$ with this proof is a two-pointing. $\square$

This is `TwoPointing.nonempty_two_pointing_iff`, and its halves are `TwoPointing.to_nontrivial` and `TwoPointing.instNonemptyOfNontrivial`. So `Nontrivial α` is a proposition, and `TwoPointing α` is the data behind it: a definition can use the two points, which a proof of `Nontrivial α` does not provide. The module `Mathlib.Data.TwoPointing` has no live declarations.

#### Common errors

1. A learner writes `cmp a b` for two elements of a partial order and expects `lt` or `gt` for every pair of different elements. Incomparable elements give `eq`.
2. A learner writes `SignType.sign x = -1` and expects a lemma in the form `SignType.neg`. The simp normal form uses $-1$, $0$ and $1$.
3. A learner applies `sign_mul` in a ring with a partial order. The lemma needs a linear order: the four cases of the proof need that each element is positive, negative or zero.

### Exercises

1. (A) Prove that a function $f : \mathrm{Bool} \to \alpha$ is surjective if and only if every element of $\alpha$ is $f\ \mathrm{false}$ or $f\ \mathrm{true}$. Use `Bool.range_eq`.
2. (A) Prove that $\mathrm{sign}(-x) = -\mathrm{sign}(x)$ in a linearly ordered ring.
3. (B) Compute the image of $-1$ under `SignType.fin3Equiv`, and check that $(-1)(-1) = 1$ holds on both sides.
4. (B) Let $l$ be an alternating list of Booleans of odd length that starts with `true`. Prove that $\mathrm{count}(\mathrm{true}, l) = \mathrm{count}(\mathrm{false}, l) + 1$.
5. (B) Prove that `cmpUsing (· < ·) a b = cmpUsing (· < ·) b a` implies $a = b$ in a linear order.
6. (B) Construct an equivalence between `TwoPointing Bool` and `Bool`.

### Reference

<?reference?>
