---
title: A proof read line by line
kind: guide
modules: []
explains: {}
families: []
requires: [V00.C03, V00.C04]
reads_with: ["MIL Ch. 2"]
lean:
  - MathlibHandbook/V00/C05/Examples.lean
  - MathlibHandbook/V00/C05/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## A proof read line by line

### Overview

The number $\sqrt 2$ is irrational. The classical proof shows that no square of a natural number is twice the square of a positive natural number. This section gives that proof in Lean and reads it line by line. It then shows the result as Mathlib states it.

### The proof on paper

**Theorem.** Let $m$ and $n$ be natural numbers with $n > 0$. Then $m^2 \ne 2n^2$.

*Proof.* Use strong induction on $n$. Suppose that $m^2 = 2n^2$. Then $2$ divides $m^2$, and $2$ is prime, so $2$ divides $m$. Write $m = 2k$. Then $4k^2 = 2n^2$, so $n^2 = 2k^2$. Since $n > 0$, also $k > 0$. If $n \le k$, then $n^2 \le k^2 < 2k^2 = n^2$, which is false. So $k < n$, and the hypothesis of the induction for $k$ gives $n^2 \ne 2k^2$. This is a contradiction. $\square$

### The proof in Lean

**Example (No square is twice a square).** The proof in the companion follows the proof on paper.

<?lean MathlibHandbook/V00/C05/Examples.lean#sq_ne_two_mul_sq?>

Read it line by line.

1. The statement has the arguments `m` and `n` and the hypothesis `hn : 0 < n`. The conclusion `m ^ 2 ≠ 2 * n ^ 2` is the statement `m ^ 2 = 2 * n ^ 2 → False`, by the definition of `≠` and of `¬`.
2. The line `induction n using Nat.strong_induction_on generalizing m` starts the strong induction on `n`, with the principle of Section 3.1. The word `generalizing` makes the hypothesis of the induction true for each `m`, and not only for the `m` of the statement. The paper proof needs this: it applies the hypothesis to $k$ with a new left side $n$.
3. The case `| _ n ih` names the number `n` and the hypothesis of the induction `ih`. The hypothesis says: for each `k < n` and each `m`, if `0 < k` then `m ^ 2 ≠ 2 * k ^ 2`.
4. The line `intro h` takes the hypothesis `h : m ^ 2 = 2 * n ^ 2`. The goal is now `False`.
5. The line `have hm : 2 ∣ m` uses `Nat.Prime.dvd_of_dvd_pow`. The term `⟨n ^ 2, h⟩` is the proof that `2` divides `m ^ 2`, because `h` writes `m ^ 2` as `2` times `n ^ 2`, and `a ∣ b` is defined as `∃ c, b = a * c`.
6. The line `obtain ⟨k, rfl⟩ := hm` writes `m` as `2 * k` in each hypothesis and in the goal. The pattern `rfl` replaces the variable `m` by `2 * k` everywhere, so `m` is gone.
7. The line `have hk : n ^ 2 = 2 * k ^ 2 := by linarith` divides the equation `(2 * k) ^ 2 = 2 * n ^ 2` by two. The tactic `linarith` runs `ring_nf` on the hypotheses first, so it sees `4 * k ^ 2 = 2 * n ^ 2`, a linear equation in the atoms `k ^ 2` and `n ^ 2`.
8. The lines of `hk0` show `0 < k`. The core lemma `Nat.eq_zero_or_pos` splits into the cases `k = 0` and `0 < k`. In the case `k = 0`, the tactic `simp` turns `hk : n ^ 2 = 2 * 0 ^ 2` into `n = 0`, and `omega` finds the contradiction with `hn : 0 < n`.
9. The lines of `hlt` show `k < n` by contradiction, as in the proof on paper. From `¬ k < n`, the lemma `not_lt` gives `n ≤ k`, and then `n ^ 2 ≤ k ^ 2`. With `0 < k ^ 2` and `hk`, the hypotheses give $n^2 \le k^2 < 2k^2 = n^2$, and `linarith` finds the contradiction.
10. The last line applies the hypothesis of the induction: `ih k hlt n hk0 hk`. The arguments are, in order, the smaller number `k`, the proof `k < n`, the new left side `n` in place of `m`, the proof `0 < k`, and the equation `n ^ 2 = 2 * k ^ 2`. The result has type `False` and closes the goal.

### The goals at three points

The goal after step 6 is the following.

```text
n : ℕ
ih : ∀ m < n, ∀ (m_1 : ℕ), 0 < m → m_1 ^ 2 ≠ 2 * m ^ 2
hn : 0 < n
k : ℕ
h : (2 * k) ^ 2 = 2 * n ^ 2
⊢ False
```

The names in `ih` are the names Lean chooses: the first bound variable `m` is the smaller number, and `m_1` is the left side. They are the `k` and the `m` of step 3. After step 7 the goal has the new hypothesis `hk : n ^ 2 = 2 * k ^ 2`. Before the last line it has also `hk0 : 0 < k` and `hlt : k < n`, and the term `ih k hlt n hk0 hk` uses all of them.

### The result in Mathlib

**Theorem (The square root of two is irrational).** There are no integers $p, q$ with $q \ne 0$ and $\sqrt 2 = p / q$.

*Proof.* Suppose $\sqrt 2 = p/q$. Since $\sqrt 2 > 0$, $p$ and $q$ have the same sign, so replace them by $|p|$ and $|q|$, and let $m = |p|$ and $n = |q| > 0$ as natural numbers. Then $m = \sqrt 2 \, n$, and $m^2 = 2n^2$. This contradicts the theorem above. $\square$

**Example (The irrationality of the square root of two).** Mathlib states the result for the real number `√2`.

<?lean MathlibHandbook/V00/C05/Examples.lean#irrational_sqrt_two?>

::: mathlib
`irrational_sqrt_two` · `Mathlib.NumberTheory.Real.Irrational`

A real number is irrational when it is not in the range of the map from `ℚ` to `ℝ`. So the statement is `√2 ∉ Set.range ((↑) : ℚ → ℝ)`. The proof in Mathlib is one line, `simpa using Nat.prime_two.irrational_sqrt`: it takes the general result for the square root of a prime, at the prime `2`, and `simpa` turns the cast `((2 : ℕ) : ℝ)` into the numeral `(2 : ℝ)`.

<?decl irrational_sqrt_two?>
:::

::: mathlib
`Nat.Prime.irrational_sqrt` · `Mathlib.NumberTheory.Real.Irrational`

The general result: for each prime $p$, $\sqrt p$ is irrational. The square root is of the cast `↑p : ℝ`. The hypothesis is explicit, so the dot form `hp.irrational_sqrt` applies to `hp : Nat.Prime p`. This is the form of Section 4.1.

<?decl Nat.Prime.irrational_sqrt?>
:::

::: mathlib
`Nat.Prime.dvd_of_dvd_pow` · `Mathlib.Data.Nat.Prime.Basic`

A prime that divides a power divides the base. Step 5 of the proof uses it. The power `m` and the base `n` are implicit, and Lean finds them from the proof `p ∣ m ^ n`.

<?decl Nat.Prime.dvd_of_dvd_pow?>
:::

### Common errors

1. Writing `2 ∣ m` as `m / 2`. The sign `∣` is typed `\mid`, and it is a proposition. The term `m / 2` is a natural number.
2. Forgetting `generalizing m`. The hypothesis `ih` is then for the fixed `m` of the statement, and the last line fails with a type mismatch.
3. Reading `obtain ⟨k, rfl⟩` as a new hypothesis `m = 2 * k`. The pattern `rfl` substitutes, and `m` is no longer in the goal.
4. Writing `Irrational (Real.sqrt 2)` and `Irrational √2` as two different statements. The sign `√` is notation for `Real.sqrt`.

### Exercises

1. (A) In step 2, explain what fails if the proof does not use `generalizing m`.
2. (A) Write the type of `ih k hlt` after step 9.
3. (B) Change the proof on paper to show that $m^2 \ne 3n^2$ for $n > 0$. Which step changes?
4. (B) Explain why the theorem of this section gives that $\sqrt 2$ is not a rational number, with the definition of `Irrational` in Mathlib.
5. (B) Prove on paper that $\sqrt 6$ is irrational, from the irrationality of $\sqrt 2$ or from a descent. Hint: $m^2 = 6n^2$ gives $2 \mid m$.
6. (C) Prove on paper that $\sqrt n$ is irrational for each natural number $n$ that is not a square. Hint: write $n = a^2 b$ with $b > 1$ squarefree, and use a prime factor of $b$.
7. (L) Prove `MathlibHandbook.V00.C05.Exercises.irrational_sqrt_two_mul` with `irrational_sqrt_two` and a lemma of the namespace `Irrational`.

### Notes and history

The proof that $\sqrt 2$ is irrational is in the tenth book of Euclid's *Elements*. The form by descent, with a smaller solution from each solution, is the form of this section. Freek Wiedijk lists this theorem as the first of his list of 100 theorems for provers.
