---
title: Reading a proof term
kind: guide
modules: []
explains: {}
families: []
requires: [V00.C03, V00.C04]
reads_with: ["TPIL", "MIL Ch. 5"]
lean:
  - MathlibHandbook/V00/C05/Examples.lean
  - MathlibHandbook/V00/C05/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Reading a proof term

### Overview

Many short proofs in Mathlib are terms, not tactic proofs. A term has no goal view between its steps, and it uses the forms `let`, `have`, `fun`, the anonymous constructor `⟨_, _⟩` and the operator `<|`. This section reads two proofs of Mathlib from the source: Euclid's proof that there are infinitely many primes, written as a term, and the proof of the formula of Gauss for $0 + 1 + \dots + (n-1)$, written as a `calc` chain. For each proof the section gives the paper proof first, then the source, then the reading of each line.

### The forms of a term

**Definition (Forms of a proof term).** The following forms appear in the proofs of this section.

1. `let x := t` names the term `t`, and the rest of the proof can use `x` and its value.
2. `have h : P := t` proves `P` by `t`, and the rest can use `h`, but not the term `t`.
3. `f <| x` is `f x`. The operator saves parentheses: `f <| g <| x` is `f (g x)`.
4. `fun h => t` is a function. As a proof of `¬ P` or of `P → Q`, it starts with the hypothesis `h`.
5. `⟨a, b, c⟩` is the anonymous constructor: here a proof of `∃ p, A p ∧ B p` from a witness `a` and proofs `b : A a` and `c : B a`.
6. `(h).2 x` uses the second direction of an equivalence `h`.

A term proof is read from the end: the last line is the conclusion, and the lines above it prove its parts.

### Euclid's theorem as a term

**Theorem (Euclid).** For each $n \in \mathbb{N}$ there is a prime $p$ with $n \le p$.

*Proof.* Let $p$ be the smallest factor greater than $1$ of $N = n! + 1$. Since $n! \ge 1$, $N \ge 2$, so $N \ne 1$, and $p$ is a prime. Suppose that $p \le n$. Then $p$ is a positive number at most $n$, so $p \mid n!$. Also $p \mid n! + 1$. So $p$ divides the difference $1$, which is false for a prime. So $p \le n$ is false, and $n < p$, so $n \le p$. $\square$

The source in `Mathlib/Data/Nat/Prime/Infinite.lean` is the following term.

```lean
theorem exists_infinite_primes (n : ℕ) : ∃ p, n ≤ p ∧ Prime p :=
  let p := minFac (n ! + 1)
  have f1 : n ! + 1 ≠ 1 := ne_of_gt <| succ_lt_succ <| factorial_pos _
  have pp : Prime p := minFac_prime f1
  have np : n ≤ p :=
    le_of_not_ge fun h =>
      have h₁ : p ∣ n ! := dvd_factorial (minFac_pos _) h
      have h₂ : p ∣ 1 := (Nat.dvd_add_iff_right h₁).2 (minFac_dvd _)
      pp.not_dvd_one h₂
  ⟨p, np, pp⟩
```

The file is in the namespace `Nat` with `open Nat`, so `Prime` is `Nat.Prime`, `minFac` is `Nat.minFac`, and `n !` is the factorial. Read from the end.

1. The last line `⟨p, np, pp⟩` is the conclusion: the witness `p`, a proof `np : n ≤ p` and a proof `pp : Prime p`. The lines above give the three parts.
2. `let p := minFac (n ! + 1)` names the witness: the smallest factor of $n! + 1$ that is not $1$. The term `Nat.minFac m` is defined for all `m`, with the junk value `minFac 1 = 1`, and `Nat.minFac_prime` says that it is prime when `m ≠ 1`.
3. `f1` proves $n! + 1 \ne 1$. Read the chain from the right: `factorial_pos _ : 0 < n !`, then `succ_lt_succ` gives `0 + 1 < n ! + 1`, which Lean reads as `1 < n ! + 1`, and `ne_of_gt` gives `n ! + 1 ≠ 1`. The `_` is `n`, and Lean finds it.
4. `pp` proves that `p` is prime, by `minFac_prime` with the hypothesis `f1`.
5. `np` proves $n \le p$ with `le_of_not_ge : ¬ a ≤ b → b ≤ a`, at `a = p` and `b = n`. So its argument is a proof of `¬ (p ≤ n)`, and `le_of_not_ge` turns it into `n ≤ p`. That argument is `fun h => ...`, a proof of a negation: it takes `h : p ≤ n` and gives `False`.
6. Inside, `h₁` proves $p \mid n!$, with `Nat.dvd_factorial`: a positive number at most $n$ divides $n!$. The positivity is `minFac_pos _`.
7. `h₂` proves $p \mid 1$. The core lemma `Nat.dvd_add_iff_right h₁` says that, as `p ∣ n !`, `p ∣ 1 ↔ p ∣ n ! + 1`. Its second direction `.2` takes `minFac_dvd _ : p ∣ n ! + 1` and gives `p ∣ 1`.
8. `pp.not_dvd_one h₂` is the contradiction: a prime does not divide $1$. Its type is `False`, so the function `fun h => ...` is a proof of `¬ (p ≤ n)`, and `le_of_not_ge` turns it into `n ≤ p`.

Each line of the term is a sentence of the paper proof. The term has no tactic, and Lean checks it in a few milliseconds.

::: mathlib
`Nat.exists_infinite_primes` · `Mathlib.Data.Nat.Prime.Infinite`

The statement is `∀ n, ∃ p, n ≤ p ∧ Nat.Prime p`. The existential quantifier with a conjunction is the form of Section 2.4, and the proof gives it as a triple.

<?decl Nat.exists_infinite_primes?>
:::

::: mathlib
`Nat.minFac_prime` · `Mathlib.Data.Nat.Prime.Defs`

The smallest factor of $m$ other than $1$ is prime, when $m \ne 1$. The hypothesis is explicit, and `m` is implicit. For $m = 1$ the value is the junk value $1$, which is not prime, and the hypothesis rules this case out.

<?decl Nat.minFac_prime?>
:::

::: mathlib
`Nat.dvd_factorial` · `Mathlib.Data.Nat.Factorial.Basic`

If $0 < m \le n$, then $m \mid n!$. Both hypotheses are explicit, in the order of the paper proof: first the positivity, then the bound. On paper, $n! = 1 \cdot 2 \cdots n$ has the factor $m$.

<?decl Nat.dvd_factorial?>
:::

### The formula of Gauss as a chain

**Theorem (Gauss).** For each $n \in \mathbb{N}$, $2 \sum_{i=0}^{n-1} i = n(n-1)$.

*Proof.* Write $S = \sum_{i=0}^{n-1} i$. The map $i \mapsto n - 1 - i$ is a bijection of $\{0, \dots, n-1\}$, so $S = \sum_{i=0}^{n-1} (n-1-i)$. Adding the two forms term by term, $2S = \sum_{i=0}^{n-1} \bigl(i + (n-1-i)\bigr) = \sum_{i=0}^{n-1} (n - 1) = n(n-1)$. $\square$

The source in `Mathlib/Algebra/BigOperators/Intervals.lean` is a `calc` chain with the same four steps.

```lean
theorem sum_range_id_mul_two (n : ℕ) : (∑ i ∈ range n, i) * 2 = n * (n - 1) :=
  calc
    (∑ i ∈ range n, i) * 2 = (∑ i ∈ range n, i) + ∑ i ∈ range n, (n - 1 - i) := by
      rw [sum_range_reflect (fun i => i) n, mul_two]
    _ = ∑ i ∈ range n, (i + (n - 1 - i)) := sum_add_distrib.symm
    _ = ∑ _ ∈ range n, (n - 1) :=
      sum_congr rfl fun _ hi => add_tsub_cancel_of_le <| Nat.le_sub_one_of_lt <| mem_range.1 hi
    _ = n * (n - 1) := by rw [sum_const, card_range, Nat.nsmul_eq_mul]
```

1. The first step writes $2S$ as $S + \sum (n-1-i)$. The rewrite with `Finset.sum_range_reflect` turns the reflected sum back into $S$, and `mul_two` turns $S \cdot 2$ into $S + S$. Both sides are then $S + S$.
2. The second step is `Finset.sum_add_distrib` read from right to left: `.symm` reverses an equation. It joins the two sums into one sum of $i + (n-1-i)$.
3. The third step uses `Finset.sum_congr`: two sums over the same set, `rfl`, are equal if their terms are equal at each point of the set. For $i$ in the range, `mem_range.1 hi : i < n`, so $i \le n - 1$, and `add_tsub_cancel_of_le` gives $i + (n - 1 - i) = n - 1$. This is the place where truncated subtraction needs its hypothesis, as in Section 5.1.
4. The last step computes the sum of a constant: `sum_const` gives `card (range n) • (n - 1)`, `card_range` gives `n • (n - 1)`, and `Nat.nsmul_eq_mul` turns the multiple into a product.

::: mathlib
`Finset.sum_congr` · `Mathlib.Algebra.BigOperators.Group.Finset.Basic`

The lemma of congruence for sums. The first explicit hypothesis is an equality of the index sets, the second is an equality of the terms on the set. The second is a bounded universal statement, so its proof is a function `fun x hx => ...`, as in step 3.

<?decl Finset.sum_congr?>
:::

::: mathlib
`Finset.sum_range_reflect` · `Mathlib.Algebra.BigOperators.Intervals`

The sum of $f(n - 1 - j)$ over $j < n$ is the sum of $f(j)$. It is the bijection of the paper proof, with the truncated subtraction of `ℕ`, which is the true subtraction for $j < n$.

<?decl Finset.sum_range_reflect?>
:::

### Common errors

1. Reading a term from the top as a list of steps that change a goal. A term has no goal. Read it from the last line, which shows the shape of the conclusion.
2. Reading `f <| g <| x` as `(f g) x`. The operator groups to the right.
3. Confusing `let` and `have`. After `have`, the value is hidden. The proof above uses `let` for `p`, because the later lines need `p = minFac (n ! + 1)` to apply `minFac_dvd`.
4. Missing the junk values inside a short proof. The value `minFac 1 = 1` is the reason the proof needs `f1`.

### Exercises

1. (A) For $n = 3$, compute $n! + 1$ and $p = \operatorname{minFac}(n! + 1)$, and check $n \le p$.
2. (A) Write the types of `factorial_pos _`, of `succ_lt_succ (factorial_pos _)` and of `f1`.
3. (B) For $n = 4$, $n! + 1 = 25$. Compute $p$ and check each line of the term for this $n$.
4. (B) Rewrite the proof of `exists_infinite_primes` as a tactic proof, with one tactic for each line of the term.
5. (B) Explain why the third step of the Gauss chain fails for the sum over `range (n + 1)` of `i + (n - 1 - i)`. Give the term with $i = n$.
6. (C) Prove on paper that for each $n$ there is a prime $p \equiv 3 \pmod 4$ with $p > n$. Hint: take a prime factor of $4 \cdot n! - 1$ that is $3 \bmod 4$, and explain why one exists.

### Notes and history

Euclid's proof is Proposition 20 of Book IX of the *Elements*. The proof by $n! + 1$ is a common modern form of it. The proof term in Mathlib dates from the first library for Lean 3, and it kept its form through the move to Lean 4. The pairing of $i$ with $n - 1 - i$ is the argument of the story told about Gauss as a child.
