---
title: Factorials, binomial coefficients and the binomial theorem
kind: theory
modules:
  - Mathlib.Data.Nat.Factorial.Basic
  - Mathlib.Data.Nat.Choose.Basic
  - Mathlib.Data.Nat.Choose.Sum
explains:
  E3: [Nat.factorial, Nat.choose, add_pow]
  E2: [Nat.factorial_succ, Nat.factorial_pos, Nat.dvd_factorial, Nat.choose_succ_succ, Nat.choose_eq_zero_of_lt, Nat.choose_mul_factorial_mul_factorial, Nat.choose_eq_factorial_div_factorial, Nat.choose_symm, Nat.sum_range_choose]
  E1: auto
families: []
requires: [V01.C05]
reads_with: ["MIL"]
lean:
  - MathlibHandbook/V02/C01/Examples.lean
  - MathlibHandbook/V02/C01/Exercises.lean
  - MathlibHandbook/V02/C01/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Factorials, binomial coefficients and the binomial theorem

### Overview

The recursion theorem of the first section defines functions on $\mathbb{N}$ by a value at $0$ and a step. This section uses it for the factorial $n!$ and the binomial coefficient $\binom{n}{k}$. Mathlib defines $\binom{n}{k}$ by the recursion of Pascal's triangle, and the section proves the formula $n! / (k! (n - k)!)$ from it. The main theorem is the binomial theorem: in each commutative ring, $(x + y)^n$ is the sum of the terms $\binom{n}{m} x^m y^{n - m}$.

### Definitions

**Definition (Factorial).** The factorial is the function $\mathbb{N} \to \mathbb{N}$ with $0! = 1$ and $(n + 1)! = (n + 1) \cdot n!$.

So $n! = 1 \cdot 2 \cdots n$ for $n \geq 1$. The value $0! = 1$ is not a junk value: it is the empty product, and it makes the formulas below hold for $k = 0$ and $k = n$.

::: mathlib
`Nat.factorial` · `Mathlib.Data.Nat.Factorial.Basic`

The two equations are `Nat.factorial_zero` and `Nat.factorial_succ`. The notation `n !` is available after `open Nat`. Write `(n + 1)!` with the parentheses: `n + 1 !` parses as `n + (1 !)`.

<?decl Nat.factorial?>
:::

**Definition (Binomial coefficient).** The binomial coefficient $\binom{n}{k}$, for $n, k \in \mathbb{N}$, is defined by recursion:
$$\binom{n}{0} = 1, \qquad \binom{0}{k + 1} = 0, \qquad \binom{n + 1}{k + 1} = \binom{n}{k} + \binom{n}{k + 1}.$$

The third equation is the rule of Pascal's triangle. The value for $k > n$ is $0$, the correct count of subsets. The formula with factorials is a theorem, not the definition, because division in $\mathbb{N}$ is not exact in general.

::: mathlib
`Nat.choose` · `Mathlib.Data.Nat.Choose.Basic`

The definition `Nat.choose` has exactly the three equations above, as `Nat.choose_zero_right`, `Nat.choose_zero_succ` and `Nat.choose_succ_succ`. The value for $k > n$ is $0$ by `Nat.choose_eq_zero_of_lt`. With dot notation, `n.choose k` is $\binom{n}{k}$. The count of subsets is `Finset.card_powersetCard` in the files on finite sets.

<?decl Nat.choose?>
:::

### Theorems and proofs

**Theorem (Factorials).** For each $n$: $n! > 0$, $n \leq n!$, and $m \mid n!$ for each $m$ with $1 \leq m \leq n$.

*Proof.* Each part is an induction on $n$. First, $0! = 1 > 0$, and $(n + 1)! = (n + 1) \cdot n!$ is a product of two positive numbers. Second, $0 \leq 1$, and $n + 1 \leq (n + 1) \cdot n!$ because $n! \geq 1$. Third, for $n = 0$ there is no $m$. Suppose the claim for $n$, and let $1 \leq m \leq n + 1$. If $m = n + 1$, then $m$ divides $(n + 1) \cdot n!$. If $m \leq n$, then $m \mid n!$ by the hypothesis, so $m$ divides $(n + 1) \cdot n!$. $\square$

::: mathlib
`Nat.dvd_factorial` · `Mathlib.Data.Nat.Factorial.Basic`

The hypotheses are `0 < m` and `m ≤ n`. The first is necessary: $0 \nmid n!$, because $0$ divides only $0$. The lemma `Nat.factorial_pos` is the first part of the theorem, and `Nat.self_le_factorial` is the second.

<?decl Nat.dvd_factorial?>
:::

**Theorem (Coefficients above the diagonal).** $\binom{n}{k} = 0$ for $k > n$, and $\binom{n}{n} = 1$.

*Proof.* Induction on $n$, for all $k$ at once. For $n = 0$ and $k > 0$, write $k = j + 1$; then $\binom{0}{j + 1} = 0$ by the definition. For $n + 1$ and $k > n + 1$, write $k = j + 1$ with $j > n$. Then $\binom{n + 1}{j + 1} = \binom{n}{j} + \binom{n}{j + 1}$, and both terms are $0$ by the hypothesis, since $j > n$ and $j + 1 > n$. For the diagonal, $\binom{0}{0} = 1$, and $\binom{n + 1}{n + 1} = \binom{n}{n} + \binom{n}{n + 1} = 1 + 0$. $\square$

**Theorem (Factorial formula).** For $k \leq n$,
$$\binom{n}{k} \cdot k! \cdot (n - k)! = n!.$$

*Proof.* Induction on $n$, for all $k \leq n$. For $n = 0$, $k = 0$ and both sides are $1$. Suppose the formula for $n$ and each $k \leq n$, and let $k \leq n + 1$. If $k = 0$, both sides are $(n + 1)!$. Otherwise write $k = j + 1$ with $j \leq n$. By the definition,
$$\binom{n + 1}{j + 1} (j + 1)! \, (n - j)! = \binom{n}{j} (j + 1)! \, (n - j)! + \binom{n}{j + 1} (j + 1)! \, (n - j)!.$$
In the first term, $(j + 1)! = (j + 1) \cdot j!$, so the hypothesis for $j$ gives the value $(j + 1) \cdot n!$. For the second term there are two cases. If $j = n$, then $\binom{n}{n + 1} = 0$, so the term is $0$, and the sum is $(n + 1) \cdot n! = (n + 1)!$. If $j < n$, then $n - j = (n - j - 1) + 1$, so $(n - j)! = (n - j) \cdot (n - j - 1)!$, and the hypothesis for $j + 1 \leq n$ gives the value $(n - j) \cdot n!$. The sum is $(j + 1) n! + (n - j) n! = (n + 1) \cdot n! = (n + 1)!$. $\square$

::: mathlib
`Nat.choose_mul_factorial_mul_factorial` · `Mathlib.Data.Nat.Choose.Basic`

The hypothesis `k ≤ n` is necessary. For $k > n$, the left side is $0$ and the right side is $n! > 0$. The form with division is `Nat.choose_eq_factorial_div_factorial`, and it has the same hypothesis.

<?decl Nat.choose_mul_factorial_mul_factorial?>
:::

**Corollary (Symmetry).** For $k \leq n$, $\binom{n}{n - k} = \binom{n}{k}$.

*Proof.* Let $j = n - k$. Then $j \leq n$ and $n - j = k$. The factorial formula for $j$ gives $\binom{n}{j} \cdot j! \cdot k! = n!$, and for $k$ it gives $\binom{n}{k} \cdot k! \cdot j! = n!$. The factor $j! \, k!$ is positive, so the two coefficients are equal. $\square$

::: mathlib
`Nat.choose_symm` · `Mathlib.Data.Nat.Choose.Basic`

Without the hypothesis `k ≤ n` the statement is false, because $n - k = 0$ for $k > n$; see the counterexample below.

<?decl Nat.choose_symm?>
:::

**Theorem (Counting subsets).** A finite set $X$ with $n$ elements has exactly $\binom{n}{k}$ subsets with $k$ elements.

*Proof.* Let $c(n, k)$ be the number of such subsets; a bijection of sets shows that it depends only on $n$ and $k$. Then $c(n, 0) = 1$ and $c(0, k + 1) = 0$. Let $X$ have $n + 1$ elements, and choose $x \in X$. A subset with $k + 1$ elements either contains $x$, and removing $x$ gives a subset of $X \setminus \{x\}$ with $k$ elements, or it is a subset of $X \setminus \{x\}$ with $k + 1$ elements. So $c(n + 1, k + 1) = c(n, k) + c(n, k + 1)$. The function $c$ satisfies the three equations of the definition, so $c(n, k) = \binom{n}{k}$ by induction on $n$. $\square$

**Theorem (Binomial theorem).** Let $R$ be a commutative semiring, $x, y \in R$ and $n \in \mathbb{N}$. Then
$$(x + y)^n = \sum_{m = 0}^{n} \binom{n}{m} x^m y^{n - m}.$$

*Proof.* Induction on $n$. For $n = 0$ both sides are $1$. Suppose the formula for $n$. Then
$$(x + y)^{n + 1} = (x + y) \sum_{m = 0}^{n} \binom{n}{m} x^m y^{n - m} = \sum_{m = 0}^{n} \binom{n}{m} x^{m + 1} y^{n - m} + \sum_{m = 0}^{n} \binom{n}{m} x^m y^{n + 1 - m}.$$
In the first sum, put $j = m + 1$. It becomes $\sum_{j = 1}^{n + 1} \binom{n}{j - 1} x^j y^{n + 1 - j}$. The second sum is $\sum_{j = 0}^{n} \binom{n}{j} x^j y^{n + 1 - j}$. Now collect the coefficient of $x^j y^{n + 1 - j}$ for each $j$ from $0$ to $n + 1$:

- for $j = 0$ only the second sum has a term, with coefficient $\binom{n}{0} = 1 = \binom{n + 1}{0}$;
- for $1 \leq j \leq n$ both sums have a term, and the coefficient is $\binom{n}{j - 1} + \binom{n}{j} = \binom{n + 1}{j}$ by Pascal's rule;
- for $j = n + 1$ only the first sum has a term, with coefficient $\binom{n}{n} = 1 = \binom{n + 1}{n + 1}$.

So the sum is $\sum_{j = 0}^{n + 1} \binom{n + 1}{j} x^j y^{n + 1 - j}$, which is the formula for $n + 1$. The proof uses the commutativity of $R$ when it moves $x$ past the powers of $y$. $\square$

::: mathlib
`add_pow` · `Mathlib.Data.Nat.Choose.Sum`

The sum is over `Finset.range (n + 1)`, which is $\{0, \dots, n\}$, and the term is `x ^ m * y ^ (n - m) * ↑(n.choose m)`, with the cast of the coefficient into `R` (Chapter 5). The lemma `Nat.sum_range_choose` is the case $x = y = 1$.

<?decl add_pow?>
:::

**Corollary (Sum of a row).** $\sum_{m = 0}^{n} \binom{n}{m} = 2^n$, and $\sum_{m = 0}^{n} (-1)^m \binom{n}{m} = 0$ for $n \geq 1$.

*Proof.* Take $x = y = 1$ in the binomial theorem for $R = \mathbb{N}$: $(1 + 1)^n = 2^n$. Take $x = -1$ and $y = 1$ in $R = \mathbb{Z}$: $(-1 + 1)^n = 0^n = 0$ for $n \geq 1$. $\square$

### Examples

**Example (Values).** $5! = 120$ and $10! = 3628800$. The rows $0$ to $5$ of Pascal's triangle are
$$1; \quad 1, 1; \quad 1, 2, 1; \quad 1, 3, 3, 1; \quad 1, 4, 6, 4, 1; \quad 1, 5, 10, 10, 5, 1.$$
Check one entry with the formula: $\binom{5}{2} \cdot 2! \cdot 3! = 10 \cdot 2 \cdot 6 = 120 = 5!$. In Lean, `Nat.factorial_pos` gives the positivity of each factorial.

<?lean MathlibHandbook/V02/C01/Examples.lean#factorial?>

**Example (The binomial theorem).** $(a + b)^4 = a^4 + 4a^3 b + 6a^2 b^2 + 4a b^3 + b^4$, from row $4$. With $a = 10$ and $b = 1$: $11^4 = 10000 + 4000 + 600 + 40 + 1 = 14641$, so the digits of $11^4$ are the entries of row $4$. At row $5$ the entries $10$ carry.

**Counterexample (Symmetry needs its hypothesis).** Take $n = 3$ and $k = 5$. Then $\binom{3}{5} = 0$. But $3 - 5 = 0$ in $\mathbb{N}$, so $\binom{3}{3 - 5} = \binom{3}{0} = 1$. The identity $\binom{n}{n - k} = \binom{n}{k}$ fails, and this is why `Nat.choose_symm` asks for `k ≤ n`.

### The library around it

The file `Mathlib.Data.Nat.Factorial.Basic` also has the order lemmas `Nat.factorial_le` and `Nat.factorial_lt`, and `Mathlib.Data.Nat.Choose.Basic` has `Nat.choose_self`, `Nat.choose_one_right` and `Nat.choose_pos`. The divisibility of the coefficients by a prime is `Nat.Prime.dvd_choose_self` in `Mathlib.Data.Nat.Choose.Dvd`.

### Exercises

1. (A) Prove that $\binom{n}{1} = n$ and $\binom{n}{2} = n(n - 1)/2$. *Hint.* Induction on $n$ with Pascal's rule, or the factorial formula.
2. (B) Prove the identity $k \binom{n}{k} = n \binom{n - 1}{k - 1}$ for $1 \leq k \leq n$. *Hint.* Use the factorial formula on both sides, or count pairs of a subset and a marked element.
3. (B) Prove that $\sum_{k = 0}^{n} \binom{n}{k}^2 = \binom{2n}{n}$. *Hint.* Count the subsets of size $n$ of a set of $2n$ elements, split into two halves.
4. (B) Prove that the product of $k$ consecutive natural numbers is divisible by $k!$. *Hint.* $(m + 1)(m + 2) \cdots (m + k) = k! \binom{m + k}{k}$.
5. (C) Prove the formula $\sum_{m = k}^{n} \binom{m}{k} = \binom{n + 1}{k + 1}$, and use it with $k = 1$ to get the sum $1 + 2 + \dots + n$. *Hint.* Induction on $n$ with Pascal's rule.
6. (L) Prove that $2 \leq n!$ for each $n \geq 2$. The solution is `two_le_factorial`.

### Notes and history

Pascal's *Traité du triangle arithmétique* (1654) studied the triangle, which is much older: it is in the work of al-Karaji and of Jia Xian in the eleventh century. The notation $n!$ is due to Kramp (1808). Mathlib states `add_pow` for commutative semirings, so that it serves `ℕ`, `ℤ` and the polynomials at once.

### Reference

<?reference?>
