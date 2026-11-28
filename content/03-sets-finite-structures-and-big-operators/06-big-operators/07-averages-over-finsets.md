---
title: Averages over finsets
kind: api
modules:
  - Mathlib.Algebra.BigOperators.Expect
  - Mathlib.Algebra.Order.BigOperators.Expect
  - Mathlib.Algebra.BigOperators.Balance
explains:
  E2: [Finset.expect, Finset.expect_eq_sum_div_card, Finset.card_smul_expect, Finset.expect_const, Finset.expect_le_expect, Finset.exists_le_of_expect_le, Finset.expect_mul_sq_le_sq_mul_sq, Fintype.balance_apply, Fintype.sum_balance]
  E1: auto
families: []
requires: [V03.C03, V03.C04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Averages over finsets

### Overview

The average of a function $f$ over a nonempty finite set $s$ is the sum of its values divided by the card of $s$. In additive combinatorics and in probability on a finite set, the average is often more natural than the sum. A density is an average of an indicator, and the expectation of a random variable on a uniform finite space is an average. Mathlib has a separate operator for this, `Finset.expect`, with the notation `𝔼 i ∈ s, f i` from `BigOperators.bigexpect`. The notation `𝔼 i, f i` is the average over `Finset.univ`.

The definition divides by the card through a scalar action of the nonnegative rationals `NNRat`, written $\mathbb{Q}_{\ge 0}$. So `Finset.expect` works in each additive commutative monoid $M$ with an instance `Module ℚ≥0 M`. This class contains the fields of characteristic zero, such as $\mathbb{Q}$, $\mathbb{R}$ and $\mathbb{C}$, and the vector spaces over them. It also contains $\mathbb{Q}_{\ge 0}$ and $\mathbb{R}_{\ge 0}$, which are not groups. The value is

$$\mathbb{E}_{i \in s} f(i) = |s|^{-1} \cdot \sum_{i \in s} f(i),$$

where $|s|^{-1}$ is the inverse in $\mathbb{Q}_{\ge 0}$. For the empty finset, the card is $0$, its inverse in $\mathbb{Q}_{\ge 0}$ is $0$, and the average is $0$. This is `Finset.expect_empty`.

The three modules have three parts of the theory. `Mathlib.Algebra.BigOperators.Expect` has the algebra: linearity, the change of index, and the link with the sum. `Mathlib.Algebra.Order.BigOperators.Expect` has the inequalities. `Mathlib.Algebra.BigOperators.Balance` has the balance of a function, which is the function minus its average.

### The library around it

#### The link with the sum

Most proofs about an average start with a rewrite to a sum. There are two rules for this.

| Lean name | Statement |
|---|---|
| `Finset.card_smul_expect` | $\lvert s \rvert \cdot \mathbb{E}_{i \in s} f(i) = \sum_{i \in s} f(i)$ |
| `Finset.expect_eq_sum_div_card` | $\mathbb{E}_{i \in s} f(i) = \bigl(\sum_{i \in s} f(i)\bigr) / \lvert s \rvert$ in a semifield of characteristic zero |
| `Finset.expect_univ` | $\mathbb{E}_i f(i) = \lvert \iota \rvert^{-1} \cdot \sum_i f(i)$ for a finite type $\iota$ |
| `Fintype.expect_eq_sum_div_card` | the form of `Finset.expect_eq_sum_div_card` over `Finset.univ` |
| `Fintype.card_mul_expect` | $\lvert \iota \rvert \cdot \mathbb{E}_i f(i) = \sum_i f(i)$ in a semiring |

The first rule holds for all $s$, also for the empty one. The proof has two cases. If $s$ is empty, the two sides are $0$. If $s$ has $n > 0$ elements, then $n \cdot (n^{-1} \cdot S) = (n \cdot n^{-1}) \cdot S = S$, because $n$ is not zero in $\mathbb{Q}_{\ge 0}$. The second rule needs division, so it needs a semifield $K$, and the characteristic zero makes the cast of $|s|$ to $K$ agree with the cast through $\mathbb{Q}_{\ge 0}$.

The rule `Finset.expect_eq_sum_div_card` is the best start for a computation with numbers. For example, the average of $i^2$ over $\{1, 2, 3\}$ is $(1 + 4 + 9) / 3 = 14 / 3$.

#### Algebra of averages

The average is a linear map in $f$, so the rules of Section 2 for sums carry over.

1. `Finset.expect_add_distrib`, `Finset.expect_sub_distrib` and `Finset.expect_neg_distrib` are the rules for $f + g$, $f - g$ and $-f$.
2. `Finset.mul_expect` and `Finset.expect_mul` move a constant factor out on the left or on the right. `Finset.smul_expect` moves a scalar.
3. `map_expect` says that a $\mathbb{Q}_{\ge 0}$-linear map commutes with the average. The cast `algebraMap.coe_expect` is a special case.
4. `Finset.expect_comm` exchanges two averages, and `Finset.expect_sum_comm` exchanges an average and a sum.
5. `Finset.expect_product` writes an average over $s \times t$ as an average of averages.
6. `Finset.expect_apply` evaluates an average of functions at a point.

The rules for the index differ from the rules for sums in one way. The card is part of the value, so a change of index must keep the card. The rules `Finset.expect_bij`, `Finset.expect_nbij` and `Finset.expect_equiv` ask for a bijection, as `Finset.sum_bij` does. But there is no rule for a union: the average over $s \cup t$ is a weighted mean of the two averages, not their sum. The rule `Finset.expect_image` needs a map that is injective on the index finset.

The constants behave differently too. `Finset.expect_const` says that the average of the constant $a$ over a nonempty $s$ is $a$, not $|s| \cdot a$. The hypothesis is necessary: over the empty finset, the average is $0$. The rule `Finset.expect_singleton` gives $\mathbb{E}_{j \in \{i\}} f(j) = f(i)$. The rule `Finset.expect_indicator_one` says that the average over the whole type of the indicator of $s$ is the density `Finset.dens` of $s$, from Chapter 3. The power rule `Finset.expect_pow` expands $(\mathbb{E}_{i \in s} f(i))^n$ into an average over the tuples in $s^n$ of the products of the values.

#### Inequalities

The file `Mathlib.Algebra.Order.BigOperators.Expect` gives the order rules. The values lie in an ordered additive monoid with an instance `PosSMulMono ℚ≥0 α`, which says that a scalar $q \ge 0$ keeps the order.

| Lean name | Statement |
|---|---|
| `Finset.expect_le_expect` | if $f \le g$ on $s$, then $\mathbb{E}_s f \le \mathbb{E}_s g$ |
| `Finset.expect_nonneg` | if $f \ge 0$ on $s$, then $\mathbb{E}_s f \ge 0$ |
| `Finset.expect_le` | if $s$ is nonempty and $f \le a$ on $s$, then $\mathbb{E}_s f \le a$ |
| `Finset.le_expect` | if $s$ is nonempty and $a \le f$ on $s$, then $a \le \mathbb{E}_s f$ |
| `Finset.exists_le_of_expect_le` | if $s$ is nonempty and $\mathbb{E}_s f \le a$, then $f(x) \le a$ for some $x \in s$ |
| `Finset.abs_expect_le` | $\lvert \mathbb{E}_s f \rvert \le \mathbb{E}_s \lvert f \rvert$ |
| `Finset.expect_mul_sq_le_sq_mul_sq` | $(\mathbb{E}_s f g)^2 \le \mathbb{E}_s f^2 \cdot \mathbb{E}_s g^2$ |

The rule `Finset.exists_le_of_expect_le` is the averaging principle: some value is at most the average. It is the pigeonhole principle in the form of an average. The proof is by contradiction. If $f(x) > a$ for all $x \in s$, then `Finset.expect_lt_expect`, or the strict form of `Finset.le_expect`, gives $\mathbb{E}_s f > a$. The order is linear here, so the negation of $f(x) \le a$ is $f(x) > a$. The rules `Finset.exists_lt_of_expect_lt`, `Finset.exists_le_of_le_expect` and `Finset.exists_lt_of_lt_expect` are the other forms.

The rule `Finset.expect_mul_sq_le_sq_mul_sq` is the Cauchy Schwarz inequality for averages. It follows from the form for sums of Section 2: both sides have the factor $|s|^{-2}$. The rule `Finset.le_expect_of_subadditive` is the triangle inequality for a general subadditive map $m$ with $m(0) = 0$ that commutes with the division by a natural number. A norm is the main example.

The positivity extension `Mathlib.Meta.Positivity.evalFinsetExpect` lets the positivity tactic prove $0 \le \mathbb{E}_{i \in s} f(i)$ when it can prove $0 \le f(i)$, and $0 < \mathbb{E}_{i \in s} f(i)$ when it also knows that $s$ is nonempty.

#### Balance

For a function $f$ on a finite type $\iota$ with values in an additive commutative group, the balance `Fintype.balance f` is $f$ minus its average. By `Fintype.balance_apply`,

$$\mathrm{balance}(f)(x) = f(x) - \mathbb{E}_y f(y).$$

The balance has average $0$, by `Fintype.expect_balance`, and sum $0$, by `Fintype.sum_balance`. The proof of the first is linearity: $\mathbb{E}_x (f(x) - c) = \mathbb{E}_x f(x) - c$ for the constant $c = \mathbb{E}_y f(y)$, when $\iota$ is nonempty, and the sum rule is the first rule times $|\iota|$. For an empty $\iota$, both sides are sums over the empty finset. The map $f \mapsto \mathrm{balance}(f)$ is additive, by `Fintype.balance_add`, `Fintype.balance_neg` and `Fintype.balance_sub`. It is idempotent, by `Fintype.balance_idem`, because the balance of a function with average $0$ is the function itself. It commutes with linear maps, by `Fintype.map_balance`. In Fourier analysis on a finite group, the balance removes the constant term.

#### Common errors

1. The average over the empty finset is $0$, so many rules need the hypothesis that $s$ is nonempty, in the form of `Finset.Nonempty`. For example, `Finset.expect_const` and `Finset.expect_le` fail without it. If a rewrite does not apply, look for a side goal of this kind.
2. The rules for sums do not transfer by name. There is no rule for the average over $s \cup t$ as a sum, and the average of a constant is the constant. Rewrite with `Finset.expect_eq_sum_div_card` first if you need a rule for sums.
3. `Finset.expect` needs `Module ℚ≥0 M`. The integers $\mathbb{Z}$ and the naturals $\mathbb{N}$ have no such instance, so an average of integers must be cast first, for example to $\mathbb{Q}$.

### Exercises

1. (A) Compute $\mathbb{E}_{i \in \{1, 2, 3, 4\}} i$ in $\mathbb{Q}$ with `Finset.expect_eq_sum_div_card`.
2. (A) Show that the average of $f$ over a singleton $\{i\}$ is $f(i)$, from the definition and `Finset.card_smul_expect`.
3. (B) Let $s$ be nonempty and let $\mathbb{E}_{i \in s} f(i) = 0$ for a real function $f$. Prove that $f(x) \ge 0$ for some $x \in s$.
4. (B) Prove $\mathbb{E}_{i \in s} (f(i) - \mathbb{E}_{j \in s} f(j))^2 = \mathbb{E}_{i \in s} f(i)^2 - (\mathbb{E}_{i \in s} f(i))^2$ for a nonempty $s$ and a real function $f$. Conclude that the square of the average is at most the average of the square.
5. (B) Prove that the balance of a constant function is $0$.
6. (C) Let $t$ and $u$ be disjoint nonempty finsets. Write the average over $t \cup u$ as a weighted mean of the averages over $t$ and over $u$, with the weights $|t| / |t \cup u|$ and $|u| / |t \cup u|$.

### Reference

<?reference?>
