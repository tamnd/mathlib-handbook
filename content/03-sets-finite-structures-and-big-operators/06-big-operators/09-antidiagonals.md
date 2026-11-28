---
title: Antidiagonals and the sums over them
kind: api
modules:
  - Mathlib.Data.Finset.NatAntidiagonal
  - Mathlib.Data.Finset.MulAntidiagonal
  - Mathlib.Data.Finset.SMulAntidiagonal
  - Mathlib.Data.Finset.NatDivisors
  - Mathlib.Algebra.BigOperators.NatAntidiagonal
  - Mathlib.Algebra.Order.Antidiag.Finsupp
  - Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
  - Mathlib.Algebra.Order.Antidiag.Nat
  - Mathlib.Algebra.Order.Antidiag.Pi
  - Mathlib.Algebra.Order.Antidiag.Prod
  - Mathlib.Algebra.Order.Antidiag.Tendsto
explains:
  E2: [Finset.HasAntidiagonal.mem_antidiagonal, Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd, Finset.Nat.card_antidiagonal, Finset.Nat.sum_antidiagonal_eq_sum_range_succ, Finset.card_finsuppAntidiag_nat_eq_choose, Nat.card_finMulAntidiag_of_squarefree, Nat.divisors_mul, Finset.mulAntidiagonal_min_mul_min]
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

## Antidiagonals and the sums over them

### Overview

The product of two power series $\sum a_i X^i$ and $\sum b_j X^j$ has the coefficient $\sum_{i + j = n} a_i b_j$ at $X^n$. The index set of this sum is the *antidiagonal* $\{(i, j) : i + j = n\}$. It is finite, and the sum over it is a sum over a finset in the sense of this chapter. The same index set appears for polynomials, for the convolution of sequences and for many identities of binomial coefficients. Mathlib does not define it once for each type. The class `Finset.HasAntidiagonal` states that each $n$ has a finset of the pairs that add up to $n$, and the instances give this finset for $\mathbb{N}$, for products, for finitely supported functions and for the positive integers.

The modules of this section also give the antidiagonals in several variables, the finsets of tuples $(f_1, \ldots, f_d)$ with a fixed sum or a fixed product, and the divisors of a product. The last group of modules treats sets that are not finite but are partially well ordered. There, the pairs $(a, b) \in s \times t$ with $a b = x$ form a finset, and this finset is the index set for the multiplication of Hahn series.

### The library around it

#### The class HasAntidiagonal

The module `Mathlib.Algebra.Order.Antidiag.Prod` defines the class `Finset.HasAntidiagonal A` for an additive monoid $A$. It has a function `antidiagonal : A → Finset (A × A)` and the rule `Finset.HasAntidiagonal.mem_antidiagonal`: $$p \in \mathrm{antidiagonal}(n) \iff p_1 + p_2 = n.$$ The function is exported, so a user writes `antidiagonal n`. Its full name is `Finset.HasAntidiagonal.antidiagonal`.

The rule fixes the finset completely. Two instances have the same members by the rule, so they are equal by extensionality. This is the instance `Finset.HasAntidiagonal.instSubsingleton`, and it means that two paths to an instance never give two different antidiagonals.

| Lean name | Statement |
|---|---|
| `Finset.HasAntidiagonal.swap_mem_antidiagonal` | $(p_2, p_1) \in \mathrm{antidiagonal}(n) \iff p \in \mathrm{antidiagonal}(n)$, for commutative $A$ |
| `Finset.HasAntidiagonal.map_swap_antidiagonal` | the swap maps $\mathrm{antidiagonal}(n)$ to itself |
| `Finset.HasAntidiagonal.antidiagonal_congr` | in a cancellative monoid, two members are equal when their first parts are equal |
| `Finset.HasAntidiagonal.antidiagonal_zero` | $\mathrm{antidiagonal}(0) = \{(0, 0)\}$ in a canonically ordered monoid |
| `Finset.HasAntidiagonal.antidiagonal.fst_le` | $p \in \mathrm{antidiagonal}(n) \Rightarrow p_1 \le n$ in a canonically ordered monoid |
| `Finset.HasAntidiagonal.filter_fst_eq_antidiagonal` | the members with $p_1 = m$ are $\{(m, n - m)\}$ if $m \le n$, and none otherwise |

**Theorem (The antidiagonals partition the square).** The pairs $(n, p)$ with $p \in \mathrm{antidiagonal}(n)$ are in bijection with $A \times A$.

*Proof.* Send $(n, p)$ to $p$. The inverse sends $(a, b)$ to $(a + b, (a, b))$, which is valid by the membership rule. The two maps are inverse, because $p \in \mathrm{antidiagonal}(n)$ forces $n = p_1 + p_2$. $\square$

This is `Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd`. It is the tool to change a double sum $\sum_n \sum_{i + j = n}$ into a sum over pairs. The instance `Finset.HasAntidiagonal.instSum` gives an antidiagonal for $A \times B$ from the antidiagonals of $A$ and $B$, and `Finset.HasAntidiagonal.antidiagonal_sum` describes it. A locally finite canonically ordered monoid has an antidiagonal by `Finset.HasAntidiagonal.antidiagonalOfLocallyFinite`. The multiplicative mirror is the class `Finset.HasMulAntidiagonal` with `Finset.HasMulAntidiagonal.mem_mulAntidiagonal`, and the instance `PNat.instHasAntidiagonal` gives the additive form on `Additive ℕ+`. The module `Mathlib.Algebra.Order.Antidiag.Tendsto` adds one limit result, `Finset.HasAntidiagonal.tendsto_sup'_antidiagonal_cofinite`, which moves a limit along the cofinite filter to the maximum over the antidiagonal.

#### The antidiagonal of the natural numbers

The instance `Finset.Nat.instHasAntidiagonal` in `Mathlib.Data.Finset.NatAntidiagonal` gives $\mathrm{antidiagonal}(n) = \{(0, n), (1, n - 1), \ldots, (n, 0)\}$.

**Theorem (Size of the antidiagonal).** The antidiagonal of $n \in \mathbb{N}$ has $n + 1$ elements.

*Proof.* The map $i \mapsto (i, n - i)$ sends $\{0, 1, \ldots, n\}$ to the antidiagonal. It is injective, because the first part recovers $i$. It is onto: if $i + j = n$, then $i \le n$ and $j = n - i$. So the two finsets have the same size, $n + 1$. $\square$

The Lean forms are `Finset.Nat.card_antidiagonal`, the image form `Finset.Nat.antidiagonal_eq_image`, and the equivalence `Finset.Nat.antidiagonalEquivFin` with `Fin (n + 1)`. The recursion `Finset.Nat.antidiagonal_succ` builds the antidiagonal of $n + 1$ from $(0, n + 1)$ and the shift of the antidiagonal of $n$.

The module `Mathlib.Algebra.BigOperators.NatAntidiagonal` turns these forms into rules for sums. Each rule has a twin for products with the prefix `prod_`, such as `Finset.Nat.prod_antidiagonal_eq_prod_range_succ`.

| Lean name | Statement |
|---|---|
| `Finset.Nat.sum_antidiagonal_eq_sum_range_succ` | $\sum_{i + j = n} f(i, j) = \sum_{k = 0}^{n} f(k, n - k)$ |
| `Finset.Nat.sum_antidiagonal_succ` | $\sum_{i + j = n + 1} f(i, j) = f(0, n + 1) + \sum_{i + j = n} f(i + 1, j)$ |
| `Finset.Nat.sum_antidiagonal_succ'` | the same with the last term $f(n + 1, 0)$ split off |
| `Finset.Nat.sum_antidiagonal_swap` | $\sum_{i + j = n} f(j, i) = \sum_{i + j = n} f(i, j)$ |
| `Finset.Nat.sum_antidiagonal_subst` | the value $n$ in $f$ can be replaced by $i + j$ inside the sum |

The swap gives a short proof of a known sum. Let $S = \sum_{i + j = n} i$. By the swap, $S = \sum_{i + j = n} j$, so $2S = \sum_{i + j = n} (i + j) = (n + 1) n$ by the size of the antidiagonal. Thus $S = n(n + 1)/2$, the sum $0 + 1 + \cdots + n$.

#### Tuples and finitely supported functions

The module `Mathlib.Algebra.Order.Antidiag.Pi` gives the antidiagonal in several variables. For a finset $s$ of indices, `Finset.piAntidiag s n` is the finset of functions $f$ with $\sum_{i \in s} f(i) = n$ and $f(i) = 0$ outside $s$. This is `Finset.mem_piAntidiag`. The recursion `Finset.piAntidiag_cons` splits on the value at one new index, as a disjoint union over $\mathrm{antidiagonal}(n)$, and `Finset.piAntidiag_empty` gives $\{0\}$ if $n = 0$ and $\emptyset$ otherwise. The form for tuples on `Fin d` is `Finset.finAntidiagonal` with `Finset.mem_finAntidiagonal`. The lemma `Finset.map_sym_eq_piAntidiag` links the antidiagonal to the multisets of Section 8 of Chapter 3: the count function maps the multisets of size $n$ over $s$ onto `s.piAntidiag n`.

The module `Mathlib.Algebra.Order.Antidiag.Finsupp` gives the same finset for finitely supported functions, which a later chapter treats. Its member `Finset.finsuppAntidiag s n` has the rule `Finset.mem_finsuppAntidiag`: the sum over $s$ is $n$ and the support is a subset of $s$. The recursion is `Finset.finsuppAntidiag_insert`. Over $\mathbb{N}$, the count is the stars and bars formula.

**Theorem (Stars and bars).** The functions $f : s \to \mathbb{N}$ with $\sum_{i \in s} f(i) = n$ are $\binom{|s| + n - 1}{n}$ in number.

*Proof.* Send $f$ to the multiset that contains each $i \in s$ exactly $f(i)$ times. It has size $n$, and the map is a bijection onto the multisets of size $n$ with elements in $s$. By the count of Section 8 of Chapter 3, there are $\binom{|s| + n - 1}{n}$ such multisets. $\square$

The bijection is `Finset.finsuppAntidiagEquiv`, and the count is `Finset.card_finsuppAntidiag_nat_eq_choose`. The form `Finset.card_finsuppAntidiag_nat_eq_multichoose` uses `Nat.multichoose` instead, and `Nat.multichoose_eq` links the two.

#### Multiplicative antidiagonals of the natural numbers

The module `Mathlib.Algebra.Order.Antidiag.Nat` defines `Nat.finMulAntidiag d n`, the finset of tuples $f : \mathrm{Fin}\ d \to \mathbb{N}$ with $\prod_i f(i) = n$. By `Nat.mem_finMulAntidiag`, membership also needs $n \ne 0$, and `Nat.finMulAntidiag_zero_right` states that the finset for $n = 0$ is empty. For $d = 2$, the pairs are the divisor pairs: `Nat.image_piFinTwoEquiv_finMulAntidiag` sends the finset to `Nat.divisorsAntidiagonal n`.

**Theorem (Factorizations of a squarefree number).** If $n$ is squarefree with $\omega$ distinct prime factors, then $n$ has $d^{\omega}$ ordered factorizations $n = f_1 \cdots f_d$.

*Proof.* Each prime $p \mid n$ divides exactly one factor $f_i$, because $p^2 \nmid n$. A factorization is thus a choice of a coordinate $i$ for each prime $p \mid n$. Conversely, each such choice gives a factorization: let $f_i$ be the product of the primes that go to $i$. The $\omega$ primes each have $d$ choices, so there are $d^{\omega}$ factorizations. $\square$

This is `Nat.card_finMulAntidiag_of_squarefree`, with the count of distinct prime factors `ArithmeticFunction.cardDistinctFactors`. The key step of the proof is `Nat.finMulAntidiag_existsUnique_prime_dvd`. A related count, `Nat.card_pair_lcm_eq`, states that a squarefree $n$ is the least common multiple of $3^{\omega}$ ordered pairs: each prime divides the first number, the second number or both.

The module `Mathlib.Data.Finset.NatDivisors` gives the divisors of a product. By `Nat.divisors_mul`, $$\mathrm{divisors}(m n) = \mathrm{divisors}(m) \cdot \mathrm{divisors}(n),$$ where the right side is the pointwise product of finsets. So `Nat.divisors` is a monoid hom from $\mathbb{N}$ to `Finset ℕ`, named `Nat.divisorsHom`. For coprime $m$ and $n$, `Nat.Coprime.mul_injOn_divisors` states that the products $a b$ with $a \mid m$ and $b \mid n$ are distinct.

#### Antidiagonals of well ordered sets

The module `Mathlib.Data.Finset.MulAntidiagonal` works with sets $s$ and $t$ in an ordered cancellative monoid that are partially well ordered (`Set.IsPWO`). For such sets, the pairs $(a, b) \in s \times t$ with $a b = x$ form a finite set. The finset is `Finset.mulAntidiagonal hs ht x`, with the rule `Finset.mem_mulAntidiagonal`. The additive form is `Finset.antidiagonal hs ht x`, and it has the same short name as the class function above, in the namespace `Finset`. Hahn series multiply by sums over these finsets.

**Theorem (The minimal pair).** Let $s$ and $t$ be well founded sets in a linearly ordered cancellative monoid. Then $\min s \cdot \min t$ has exactly one factorization $a b$ with $a \in s$ and $b \in t$, namely $(\min s, \min t)$.

*Proof.* Let $a b = \min s \cdot \min t$ with $a \in s$ and $b \in t$. Then $a \ge \min s$ and $b \ge \min t$. If one of the two inequalities is strict, then $a b > \min s \cdot \min t$, by the strict monotonicity of multiplication. So both are equalities. $\square$

This is `Finset.mulAntidiagonal_min_mul_min`, with the additive twin `Finset.antidiagonal_min_add_min`. It gives the leading coefficient of a product of Hahn series. The module `Mathlib.Data.Finset.SMulAntidiagonal` extends these finsets to an action of one ordered set on another: `Finset.SMulAntidiagonal` with `Finset.mem_smulAntidiagonal`, and `Finset.VAddAntidiagonal` in the additive case.

#### Common errors

1. The name `Finset.antidiagonal` is the well ordered form, with the arguments `hs ht a`. The class function is `Finset.HasAntidiagonal.antidiagonal`, and it is written `antidiagonal n` after `open Finset`. A search for lemmas about `antidiagonal n` must look in the namespace `Finset.HasAntidiagonal` and in `Finset.Nat`.
2. In `Finset.Nat.sum_antidiagonal_eq_sum_range_succ`, the term $n - k$ is the truncated subtraction of $\mathbb{N}$. It is correct for $k \le n$, which the range gives. A rewrite of $n - k$ later in the proof needs the hypothesis $k \le n$ from `Finset.mem_range`.
3. `Nat.finMulAntidiag d 0` is empty, not the infinite set of tuples with a zero entry. A statement for all $n$ must treat $n = 0$ apart.

### Exercises

1. (A) List `antidiagonal 4` in $\mathbb{N}$ and `antidiagonal (1, 1)` in $\mathbb{N} \times \mathbb{N}$, and check `Finset.Nat.card_antidiagonal`.
2. (A) Use `Finset.Nat.sum_antidiagonal_eq_sum_range_succ` to prove $\sum_{i + j = n} \binom{n}{i} = 2^n$.
3. (B) Prove the Vandermonde identity $\sum_{i + j = k} \binom{m}{i} \binom{n}{j} = \binom{m + n}{k}$ by a count of the $k$-subsets of a disjoint union of an $m$-set and an $n$-set.
4. (B) Count the solutions of $x_1 + x_2 + x_3 = 10$ in $\mathbb{N}$ with `Finset.card_finsuppAntidiag_nat_eq_choose`, and check the count for $x_1 + x_2 = 10$ against `Finset.Nat.card_antidiagonal`.
5. (B) For $n = 30$, count the ordered factorizations $n = a b c$ with `Nat.card_finMulAntidiag_of_squarefree`, and count the pairs with least common multiple $30$.
6. (C) Prove that a nonempty antidiagonal of a cancellative monoid has as many members as the set of first parts $\{p_1 : p \in \mathrm{antidiagonal}(n)\}$. Hint: use `Finset.HasAntidiagonal.antidiagonal_congr`.

### Reference

<?reference?>
