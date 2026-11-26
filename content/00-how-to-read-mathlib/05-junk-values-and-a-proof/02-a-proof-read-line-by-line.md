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

1. The statement has the arguments `m` and `n` and the hypothesis `hn : 0 < n`. The conclusion `m ^ 2 ≠ 2 * n ^ 2` is the statement `m ^ 2 = 2 * n ^ 2 → False`.
2. The line `induction n using Nat.strong_induction_on generalizing m` starts the strong induction on `n`. The word `generalizing` makes the hypothesis of the induction true for each `m`, and not only for the `m` of the statement.
3. The case `| _ n ih` names the number `n` and the hypothesis of the induction `ih`. The hypothesis says: for each `k < n` and each `m`, if `0 < k` then `m ^ 2 ≠ 2 * k ^ 2`.
4. The line `intro h` takes the hypothesis `h : m ^ 2 = 2 * n ^ 2`. The goal is now `False`.
5. The line `have hm : 2 ∣ m` uses `Nat.Prime.dvd_of_dvd_pow`. The term `⟨n ^ 2, h⟩` is the proof that `2` divides `m ^ 2`, because `h` writes `m ^ 2` as `2` times `n ^ 2`.
6. The line `obtain ⟨k, rfl⟩ := hm` writes `m` as `2 * k` in each hypothesis and in the goal.
7. The line `have hk : n ^ 2 = 2 * k ^ 2 := by linarith` divides the equation `(2 * k) ^ 2 = 2 * n ^ 2` by two. The tactic `linarith` sees the squares as atoms after it expands the left side.
8. The lines of `hk0` show `0 < k`. In the case `k = 0`, the tactic `simp` makes `hk` simpler, and `omega` finds the contradiction with `0 < n`.
9. The lines of `hlt` show `k < n` by contradiction, as in the proof on paper.
10. The last line applies the hypothesis of the induction to `k`, with the pair `n` and `k`.

### The result in Mathlib

**Example (The irrationality of the square root of two).** Mathlib states the result for the real number `√2`.

<?lean MathlibHandbook/V00/C05/Examples.lean#irrational_sqrt_two?>

::: mathlib
`irrational_sqrt_two` · `Mathlib.NumberTheory.Real.Irrational`

A real number is irrational when it is not in the range of the map from `ℚ` to `ℝ`. The proof in Mathlib uses the general result for the square root of a prime.

<?decl irrational_sqrt_two?>
:::

::: mathlib
`Nat.Prime.dvd_of_dvd_pow` · `Mathlib.Data.Nat.Prime.Basic`

A prime that divides a power divides the base. Step 5 of the proof uses it.

<?decl Nat.Prime.dvd_of_dvd_pow?>
:::

### Exercises

1. (A) In step 2, explain what fails if the proof does not use `generalizing m`.
2. (B) Change the proof on paper to show that $m^2 \ne 3n^2$ for $n > 0$. Which step changes?
3. (B) Explain why the theorem of this section gives that $\sqrt 2$ is not a rational number.
4. (L) Prove `MathlibHandbook.V00.C05.Exercises.irrational_sqrt_two_mul` with `irrational_sqrt_two` and a lemma of the namespace `Irrational`.

### Notes and history

The proof that $\sqrt 2$ is irrational is in the tenth book of Euclid's *Elements*. The form by descent, with a smaller solution from each solution, is the form of this section. Freek Wiedijk lists this theorem as the first of his list of 100 theorems for provers.
