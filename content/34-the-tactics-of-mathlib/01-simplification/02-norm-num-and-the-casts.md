---
title: norm_num and the casts
kind: tactic
modules: [Mathlib.Tactic.NormNum.Prime]
explains:
  E2: [Mathlib.Meta.NormNum.evalNatPrime]
  E1: [Nat.cast_add, Nat.cast_lt]
families: [F-simp-cast]
requires: [V00]
reads_with: ["MIL"]
lean: [MathlibHandbook/V34/C01/Examples.lean, MathlibHandbook/V34/C01/Solutions.lean]
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## norm_num and the casts

### Overview

The tactic `norm_num` computes with numerals. It proves goals such as `(2 : ℚ) / 3 + 1 / 6 = 5 / 6`, `(3 : ℝ) ^ 4 - 2 ^ 6 = 17` and `Nat.Prime 97`. A written proof does such a computation in the head or on scrap paper, and does not write it down. In Lean each step needs a proof, and `norm_num` makes these proofs.

The tactics `push_cast` and `norm_cast` move and remove the casts between the number types `ℕ`, `ℤ`, `ℚ` and `ℝ`. A mathematician writes $n \in \mathbb{N}$ and then uses $n$ as a real number with no comment. In Lean the natural number `n` and the real number `(n : ℝ)` are different terms, and a proof must move between them. This section explains the two kinds of tactics, the facts about the casts that they use, and the failures that come from the subtraction and the division of `ℕ`.

### What it does

#### norm_num: simp with evaluation

The tactic `norm_num` is `simp` with a set of extensions. Each extension evaluates one kind of term on numerals: a sum, a product, a power, a quotient, a comparison, a divisibility, a remainder, a greatest common divisor, a primality and others. The result of an extension is a numeral and a proof that the term is equal to it.

A numeral in a ring $R$ is the image of a natural number under the map $\mathbb{N} \to R$. A rational numeral in a division ring is a quotient $p / q$ of numerals with $q \neq 0$ in $R$. The extension for a sum uses the fact that the map is additive. For example, on `(2 : ℚ) / 3 + 1 / 6`, the extension computes $2 \cdot 6 + 1 \cdot 3 = 15$ and $3 \cdot 6 = 18$ in $\mathbb{N}$, reduces $15/18$ to $5/6$ by the greatest common divisor $3$, and proves the equation in $\mathbb{Q}$ from these facts. The work in $\mathbb{N}$ uses the binary form of the numbers, so it is fast even for large numerals.

So `norm_num` decides each equation and each inequality between closed terms of numerals in an ordered field with characteristic zero. It also uses the simp set, so it can simplify a goal with variables, but it does not do the algebra of a ring.

#### How norm_num proves that a number is prime

The extension `Mathlib.Meta.NormNum.evalNatPrime` proves `Nat.Prime n` for a numeral `n`. It does not try all the divisors from $2$ to $n - 1$. It uses the following fact.

**Theorem (Trial division).** Let $n \geq 2$ be a natural number. If no natural number $k$ with $2 \leq k$ and $k^2 \leq n$ divides $n$, then $n$ is prime.

*Proof.* Assume that $n$ is not prime. Since $n \geq 2$, there is a divisor $d$ of $n$ with $1 < d < n$. Write $n = d e$. Then $e > 1$, because $e = 1$ gives $d = n$. Also $e < n$, because $d > 1$. Let $k = \min(d, e)$. Then $k \geq 2$ and $k$ divides $n$. From $k \leq d$ and $k \leq e$ follows $k^2 \leq d e = n$. This contradicts the hypothesis. So $n$ is prime. $\square$

For $n = 97$, the numbers $k$ with $k^2 \leq 97$ are $2, 3, \ldots, 9$. None of them divides $97$: the remainders are $1, 1, 1, 2, 1, 6, 1, 7$. So $97$ is prime. The extension makes this proof. It finds the smallest factor of $n$ by a search over the candidates, and it proves the fact about each remainder with the arithmetic of numerals. For a number that is not prime, such as $91$, it is shorter: the extension finds the factor $7$ and proves $91 = 7 \cdot 13$.

#### The casts

**Definition (Cast).** For a ring $R$, the cast of a natural number is the map $c : \mathbb{N} \to R$ defined by recursion: $c(0) = 0$ and $c(n + 1) = c(n) + 1$. The casts $\mathbb{Z} \to R$ and $\mathbb{Q} \to R$ for a field $R$ of characteristic zero are defined from it. Lean writes the cast of `n` as `↑n` or `(n : R)`.

The tactics of casts use a set of lemmas with the attribute `norm_cast`. There are three kinds.

1. A lemma that moves a cast through an operation, such as `Nat.cast_add : ((m + n : ℕ) : R) = (m : R) + (n : R)`.
2. A lemma that removes a cast from a relation, such as `Nat.cast_lt : (m : R) < (n : R) ↔ m < n` in an ordered semiring that is not trivial.
3. A lemma that removes a cast of a numeral, such as `Nat.cast_ofNat : ((5 : ℕ) : R) = 5`.

**Theorem (The cast is additive).** For each ring $R$ and all $m, n \in \mathbb{N}$, the image of $m + n$ is the sum of the images of $m$ and $n$.

*Proof.* Write $c(n)$ for the image of $n$ in $R$. Fix $m$, and use induction on $n$. For $n = 0$: $c(m + 0) = c(m) = c(m) + 0 = c(m) + c(0)$. For the step, assume $c(m + n) = c(m) + c(n)$. Then $c(m + (n + 1)) = c((m + n) + 1) = c(m + n) + 1 = c(m) + c(n) + 1 = c(m) + c(n + 1)$. The second and the last equations are the definition of $c$, and the third is the hypothesis of induction. $\square$

The same kind of induction proves that $c(mn) = c(m) c(n)$. In an ordered field, $c$ is strictly increasing, since $c(n + 1) = c(n) + 1 > c(n)$. So $c$ is injective, and $c(m) < c(n)$ if and only if $m < n$. These are the facts that let `norm_cast` remove the casts from a relation.

The tactic `push_cast` rewrites with the lemmas of the first and the third kind. It moves each cast from the outside of a term to its leaves. The tactic `norm_cast` does the opposite on a statement. It moves the casts up, and then it removes them with the lemmas of the second kind when the two sides of a relation are casts from the same type. The tactic `exact_mod_cast h` closes the goal with `h` after `norm_cast` on both of them. The tactic `assumption_mod_cast` does the same with each hypothesis.

#### The subtraction and the division of ℕ

The subtraction of `ℕ` is truncated: `a - b = 0` when `a ≤ b`. So the cast of `a - b` is not always the difference of the casts: `((2 - 3 : ℕ) : ℤ)` is `0`, but `(2 : ℤ) - 3` is `-1`. The lemma `Nat.cast_sub` has the hypothesis `b ≤ a`. In the same way, the division of `ℕ` rounds down: `7 / 2 = 3`, while `(7 : ℝ) / 2 = 3.5`. The lemma `Nat.cast_div` needs the hypothesis that the divisor divides the dividend. These are the places where the casts need work by the user.

::: mathlib
`Nat.cast_add` · `Mathlib.Data.Nat.Cast.Defs`

The cast of a sum is the sum of the casts. The lemma has the attributes `simp` and `norm_cast`. The attribute `norm_cast` gives it to `push_cast`, because the lemma moves a cast. The statement holds in each additive monoid with one, `AddMonoidWithOne`, which is the most general setting in which the cast of a natural number makes sense.

<?decl Nat.cast_add?>
:::

::: mathlib
`Nat.cast_lt` · `Mathlib.Data.Nat.Cast.Order.Basic`

The cast is strictly increasing, so it reflects and preserves `<`. The lemma needs an ordered semiring in which $0 \neq 1$: in the zero ring, all the casts are equal. This lemma is a lemma of the second kind for `norm_cast`: with it, `exact_mod_cast` turns `(a : ℤ) < b` into `a < b`.

<?decl Nat.cast_lt?>
:::

::: mathlib
`Mathlib.Meta.NormNum.evalNatPrime` · `Mathlib.Tactic.NormNum.Prime`

The extension of `norm_num` for `Nat.Prime n`. It is in a separate module, so a file that proves a fact about primes must import `Mathlib.Tactic.NormNum.Prime`. For a composite number it gives a factor, and for a prime it gives a proof by the search for the smallest factor.

<?decl Mathlib.Meta.NormNum.evalNatPrime?>
:::

### How to use it

Write `norm_num` on a goal of numerals. Write `norm_num at h` on a hypothesis. Write `norm_num [foo]` to add the lemma `foo`, as with `simp`. A hypothesis that `norm_num at h` turns into `False` closes the goal.

The cast tactics have a common pattern of use. A goal about natural numbers often needs a step in a field, because the field has the division and the subtraction that the proof uses. The pattern is:

1. Cast the statement to `ℚ` or `ℝ`, or start from a goal that is already there.
2. Write `push_cast` to move the casts to the variables. Then the goal is a statement about the real numbers `(n : ℝ)`, with no cast of a compound term.
3. Close it with `ring`, `linarith` or `field_simp`.

In the other direction, when a hypothesis `h : (a : ℝ) ≤ b` holds in a field and the goal `a ≤ b` is in `ℕ`, write `exact_mod_cast h`. For a hypothesis that needs work, write `norm_cast at h` and look at the result.

Give `push_cast` the hypotheses that a lemma of casts needs. For a subtraction, write `push_cast [h]` with `h : b ≤ a`. Then `push_cast` uses `Nat.cast_sub` with this hypothesis.

### What it cannot do

The tactic `norm_num` does not do the algebra of a ring. On the goal `x + x = 2 * x` for `x : ℚ`, `norm_num` leaves the goal open. Use `ring`. It does not prove an inequality with a variable, such as `a ≤ a ^ 2` for `a : ℕ`. On a hypothesis `h : 2 * x + 3 = 7` over `ℝ`, `norm_num at h` does not change `h`: the hypothesis is already in normal form, and `norm_num` does not solve equations. Use `linarith`.

The tactic `norm_num` decides primality, but the cost grows with the square root of the number. For a number of twenty digits, the search is too long. A certificate of primality, such as a Pratt certificate, is then the better route.

The tactic `push_cast` does not move a cast through a subtraction of `ℕ` without the hypothesis. On `((n - 2 : ℕ) : ℤ) = (n : ℤ) - 2`, `push_cast` leaves the goal as it is, and the linter says that the tactic does not change the goal. The goal is false for $n = 0$. With `h : 2 ≤ n`, the call `push_cast [h]` turns the left side into `(n : ℤ) - 2`.

In the same way, `push_cast` does not move a cast through the division of `ℕ`. On `(n : ℝ) / 2 = ((n / 2 : ℕ) : ℝ)` it changes nothing, and the goal is false for odd $n$.

The tactic `norm_cast` needs the casts to come from the same type on the two sides. On a statement with a cast from `ℕ` on one side and a cast from `ℤ` on the other side, it first moves the casts to a common type. When it cannot find one, it leaves the casts.

### Examples

**Example (Fractions).** The goal is $\frac{2}{3} + \frac{1}{6} = \frac{5}{6}$ in $\mathbb{Q}$. By hand: $\frac{2}{3} = \frac{4}{6}$, and $\frac{4}{6} + \frac{1}{6} = \frac{5}{6}$. The tactic `norm_num` makes the same computation with a common denominator and a reduction by the greatest common divisor.

<?lean MathlibHandbook/V34/C01/Examples.lean#norm_num_rat?>

**Example (Primes).** The extension for primality proves `Nat.Prime 97` by trial division, and `¬ Nat.Prime 91` from $91 = 7 \cdot 13$.

<?lean MathlibHandbook/V34/C01/Examples.lean#norm_num_prime?>

**Example (Powers and other functions of numerals).** Each of these goals is closed by `norm_num`. The values are $81 - 64 = 17$, $\gcd(84, 120) = 12$, the remainder $17 \bmod 5 = 2$ and $91 = 7 \cdot 13$.

```lean
example : (3 : ℝ) ^ 4 - 2 ^ 6 = 17 := by norm_num
example : Nat.gcd 84 120 = 12 := by norm_num
example : (17 : ℕ) % 5 = 2 := by norm_num
example : (7 : ℤ) ∣ 91 := by norm_num
example : (1 : ℝ) / 3 ≠ 0.33 := by norm_num
```

The last goal uses the decimal `0.33`, which Lean reads as the rational number $33/100$. Then `norm_num` compares $1/3$ and $33/100$ by the cross products $100$ and $99$.

**Example (Moving the casts).** The goal is $((n + 1)^2 : \mathbb{N})$ cast to $\mathbb{Z}$ equals $(n + 1)^2$ with $n$ cast to $\mathbb{Z}$. The call `push_cast` moves the cast through the power and the sum, with `Nat.cast_pow`, `Nat.cast_add` and `Nat.cast_one`. The goal becomes

```text
n : ℕ
⊢ (↑n + 1) ^ 2 = (↑n + 1) ^ 2
```

and `ring` closes it. Here `rfl` would also work.

<?lean MathlibHandbook/V34/C01/Examples.lean#push_cast?>

**Example (Removing the casts).** The tactic `exact_mod_cast` turns `(a : ℤ) < b` into `a < b` with `Nat.cast_lt`. The tactic `norm_cast at h` turns `(a : ℤ) + 1 = b` into `a + 1 = b`, with `Nat.cast_add`, `Nat.cast_one` and the injectivity of the cast. Then `h` is the goal.

<?lean MathlibHandbook/V34/C01/Examples.lean#norm_cast?>

**Example (A subtraction of ℕ).** For $n \geq 2$, the cast of $n - 2$ is $n - 2$ in $\mathbb{Z}$. The hypothesis `h` goes to `push_cast`.

```lean
example (n : ℕ) (h : 2 ≤ n) : ((n - 2 : ℕ) : ℤ) = (n : ℤ) - 2 := by
  push_cast [h]
  ring
```

Without `[h]`, the goal stays `↑(n - 2) = ↑n - 2`, and no tactic of casts can prove it. The statement is false for $n = 0$ and $n = 1$.

**Example (A step through ℝ).** Let $n \in \mathbb{N}$ with $n^2 = 9$ in $\mathbb{R}$. Then $n = 3$. The proof moves the hypothesis to $\mathbb{N}$, and then `nlinarith` solves the equation of degree two with $n \geq 0$.

```lean
example (n : ℕ) (hn : (n : ℝ) ^ 2 = 9) : n = 3 := by
  have : n ^ 2 = 9 := by exact_mod_cast hn
  nlinarith
```

### Exercises

1. (L) Prove `(3 : ℚ) ^ 2 - 1 / 2 = 17 / 2` with `norm_num` (`numeral_sum` in `Exercises.lean`).
2. (A) Tell why `norm_num` proves `¬ Nat.Prime 91`. Give the two factors.
3. (A) List the numbers $k$ that the trial division tests for $n = 101$. Prove by hand that $101$ is prime.
4. (A) Compute `((2 - 5 : ℕ) : ℤ)` and `(2 : ℤ) - 5`. Tell which lemma relates them and which hypothesis it needs.
5. (B) Give a goal with a cast of a subtraction of `ℕ` that `push_cast` cannot change. Then give the hypothesis that makes it work.
6. (B) Prove that the cast $\mathbb{N} \to R$ is multiplicative for each ring $R$. Hint: use induction on the second factor and the theorem on sums.
7. (B) Prove that $(n : \mathbb{R}) / 2 = ((n / 2 : \mathbb{N}) : \mathbb{R})$ holds if and only if $n$ is even.
8. (C) The trial division tests all $k$ with $k^2 \leq n$. Prove that it is enough to test the primes $k$ with $k^2 \leq n$. Estimate the number of tests for $n$ of $2d$ digits.
9. (L) Prove that the cast of `2 * n + 1` from `ℕ` to `ℤ` is `2 * (n : ℤ) + 1` (`cast_two_mul_add_one` in `Exercises.lean`).

### Reference

<?reference?>
