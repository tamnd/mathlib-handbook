---
title: induction and cases
kind: tactic
modules: []
explains:
  E1: [Nat.le_induction, Nat.strong_induction_on, Nat.even_or_odd]
families: []
requires: [V00]
reads_with: ["MIL"]
lean: [MathlibHandbook/V34/C05/Examples.lean, MathlibHandbook/V34/C05/Solutions.lean]
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## induction and cases

### Overview

The tactic `induction n` makes a proof by induction on a natural number $n$: it gives one goal for $n = 0$ and one goal for $n = k + 1$, with the hypothesis of induction for $k$. With the option `using`, it makes an induction from a base other than $0$, or a strong induction, where the hypothesis holds for all smaller numbers. The tactic `cases n` makes the split into $n = 0$ and $n = k + 1$ with no hypothesis of induction. The tactic `rcases` on a lemma such as `Nat.even_or_odd n` splits on the parity, and `interval_cases n` splits a bounded variable into its values.

The section proves the principle of induction and its two variants from the well-ordering of $\mathbb{N}$, and it shows each tactic on a goal of number theory or of sums, with the goal state after each step.

### What it does

#### The principle of induction

**Theorem (Well-ordering).** Each nonempty set $S \subseteq \mathbb{N}$ has a least element.

*Proof.* Assume that $S$ has no least element. Let $T = \{n : \forall m \leq n,\ m \notin S\}$. Then $0 \in T$: if $0 \in S$, then $0$ is the least element of $S$, since $0 \leq m$ for each $m$. Let $n \in T$. If $n + 1 \in S$, then $n + 1$ is the least element of $S$, since each $m < n + 1$ satisfies $m \leq n$ and so $m \notin S$. This is false, so $n + 1 \notin S$, and $n + 1 \in T$. So $T$ contains $0$ and is closed under $n \mapsto n + 1$. In Lean, the type `ℕ` is the inductive type with the constructors `0` and `succ`, and its recursor gives the conclusion that $T = \mathbb{N}$. Then no $n$ is in $S$, so $S$ is empty, a contradiction. $\square$

In Lean, the principle of induction is the recursor of the inductive type `ℕ`, so it is a rule of the logic and not a theorem. The proof above shows that the principle and the well-ordering give each other. The next theorem is the converse direction, with the well-ordering as the hypothesis.

**Theorem (Induction).** Let $P$ be a predicate on $\mathbb{N}$. If $P(0)$, and $P(k) \to P(k + 1)$ for each $k$, then $P(n)$ for each $n$.

*Proof.* Let $S = \{n : \neg P(n)\}$, and assume that $S$ is not empty. By the well-ordering, $S$ has a least element $m$. Then $m \neq 0$, since $P(0)$. So $m = k + 1$ for some $k$. Since $k < m$ and $m$ is least, $k \notin S$, so $P(k)$. By the hypothesis, $P(k + 1)$, that is, $P(m)$. This contradicts $m \in S$. So $S$ is empty, and $P(n)$ for each $n$. $\square$

**Theorem (Induction from a base).** Let $b \in \mathbb{N}$ and let $P$ be a predicate on $\mathbb{N}$. If $P(b)$, and $P(k) \to P(k + 1)$ for each $k \geq b$, then $P(n)$ for each $n \geq b$.

*Proof.* Let $Q(j) = P(b + j)$. Then $Q(0) = P(b)$ holds. If $Q(j)$, then $P(b + j)$ with $b + j \geq b$, so $P(b + j + 1)$, that is, $Q(j + 1)$. By induction, $Q(j)$ for each $j$. For $n \geq b$, write $n = b + (n - b)$: then $P(n) = Q(n - b)$ holds. $\square$

**Theorem (Strong induction).** Let $P$ be a predicate on $\mathbb{N}$. If, for each $n$, the hypothesis $\forall m < n,\ P(m)$ implies $P(n)$, then $P(n)$ for each $n$.

*Proof.* Let $S = \{n : \neg P(n)\}$, and assume that $S$ is not empty. Let $n$ be its least element. Then each $m < n$ is not in $S$, so $P(m)$ for each $m < n$. By the hypothesis, $P(n)$. This contradicts $n \in S$. $\square$

Strong induction has no separate base case: for $n = 0$, the hypothesis $\forall m < 0,\ P(m)$ is empty, and the step must prove $P(0)$ with no help.

#### The tactics

The tactic `induction n with | zero => tac₀ | succ k ih => tac₁` applies the principle of induction to the target. It gives the goal $P(0)$ with the name `zero`, and the goal $P(k + 1)$ with `ih : P(k)` and the name `succ`. The hypotheses of the context that mention $n$ must be in the target too. The tactic moves them into the target before the step and back after it, so that the hypothesis of induction includes them.

The form `induction n, h using Nat.le_induction with | base => … | succ k hk ih => …` uses the theorem of induction from a base, with `h : b ≤ n`. The goal `succ` has `hk : b ≤ k` and `ih : P(k)`. The form `induction n using Nat.strong_induction_on with | _ n ih => …` uses strong induction, with `ih : ∀ m < n, P m`.

The tactic `cases n with | zero => … | succ m => …` splits $n$ into $0$ and $m + 1$, with no hypothesis of induction. It is the right step when the proof uses only the form of $n$. The step `rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩` splits $n$ into $k + k$ and $2k + 1$. The tactic `interval_cases n` finds the bounds of $n$ in the context, such as $n < 2$, and makes one goal for each value.

::: mathlib
`Nat.le_induction` · `Mathlib.Data.Nat.Init`

The theorem of induction from a base $m$: from $P(m)$ and the step for each $k \geq m$, $P(n)$ for each $n \geq m$. The predicate takes the proof of $m \leq n$ as an argument, so the call names both `n` and `h` in `induction n, h using Nat.le_induction`.

<?decl Nat.le_induction?>
:::

::: mathlib
`Nat.strong_induction_on` · `Mathlib.Data.Nat.Init`

The theorem of strong induction. With `using`, the tactic `induction` takes the step `∀ n, (∀ m < n, P m) → P n` as its one goal, with the name `ind`.

<?decl Nat.strong_induction_on?>
:::

::: mathlib
`Nat.even_or_odd` · `Mathlib.Algebra.Ring.Parity`

Each natural number is even or odd. With `rcases` and the patterns `⟨k, rfl⟩`, it gives the two cases $n = k + k$ and $n = 2k + 1$. It replaces an induction when the claim depends only on the parity.

<?decl Nat.even_or_odd?>
:::

### How to use it

Write `induction n with` and the two cases `zero` and `succ k ih`, with names for each new variable. In the case `succ`, rewrite the target so that the expression of the hypothesis of induction appears: for a sum, `rw [Finset.sum_range_succ, ih]`. Then close the goal with `ring`, `linarith`, `omega` or `nlinarith`. If the claim is for $n \geq b$, use `Nat.le_induction`. If the step needs $P(m)$ for an $m$ that is not $k$, such as $k - 1$ or $k / 2$, use strong induction. If the proof needs no hypothesis of induction, use `cases` or `rcases`, which are shorter.

Before `induction`, state the claim in its general form. The step of induction uses the same statement for $k$, so a hypothesis or a variable that is fixed for $n$ but must change for $k$ has to be in the target, with a `∀`. The tactic `induction n generalizing m` does this for a variable `m`.

### What it cannot do

#### Names that are not given

A bare `induction n` gives the new variable and the hypothesis of induction inaccessible names, `n✝` and `a✝`, that the proof cannot use. On the goal `0 ≤ n`, the case `succ` is:

```text
case succ
n✝ : ℕ
a✝ : 0 ≤ n✝
⊢ 0 ≤ n✝ + 1
```

Give the names in the `with` cases. A hypothesis on $n$ in the context becomes a premise of the hypothesis of induction. On `2 ^ n > n` with `h : 0 < n`, the case `succ k ih` has `ih : 0 < k → 2 ^ k > k` and `h : 0 < k + 1`. For $k = 0$ the premise of `ih` is false, so the step needs a case split on $k$.

#### A hypothesis of induction that is too weak

The tactic uses the target as it is, and sometimes the target is too weak to carry the step. The standard example is $\sum_{i=1}^{n} \frac{1}{i^2} \leq 2$. It is true, but the step fails: from $\sum_{i=1}^{k} \frac{1}{i^2} \leq 2$, the next sum is at most $2 + \frac{1}{(k+1)^2}$, which is more than $2$. The fix is to prove the stronger claim $\sum_{i=1}^{n} \frac{1}{i^2} \leq 2 - \frac{1}{n}$ for $n \geq 1$. Its step is $2 - \frac1k + \frac{1}{(k+1)^2} \leq 2 - \frac{1}{k+1}$, which holds since $\frac1k - \frac{1}{k+1} = \frac{1}{k(k+1)} \geq \frac{1}{(k+1)^2}$. Then the claim follows. In Lean, state the stronger claim with `have`, prove it by induction, and finish with `linarith`.

#### A base other than 0

On the claim $n^2 \leq 2^n$ for $n \geq 4$, a plain `induction n` fails: the claim is false for $n = 3$, since $9 > 8$, so the step from $3$ to $4$ cannot be proved. The case `succ` has the hypothesis $4 \leq k + 1$, which does not give $4 \leq k$. Use `Nat.le_induction`.

#### A goal that interval_cases cannot bound

The tactic `interval_cases n` needs an upper bound and a lower bound of $n$ in the context, as numerals. A variable of `ℕ` has the lower bound $0$. With no upper bound, it fails. Add the bound with `have : n < 5 := by omega` first.

### Examples

**Example (A sum).** For each $n \in \mathbb{N}$, $\sum_{i=0}^{n} i = \frac{n(n + 1)}{2}$. The proof by hand: for $n = 0$ both sides are $0$. If the claim holds for $k$, then $\sum_{i=0}^{k+1} i = \frac{k(k + 1)}{2} + (k + 1) = \frac{(k + 1)(k + 2)}{2}$. In Lean the sum is over `ℚ`, so that the division is exact.

```lean
open Finset in
example (n : ℕ) : ∑ i ∈ range (n + 1), (i : ℚ) = n * (n + 1) / 2 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, ih]
    push_cast
    ring
```

At the start of the case `succ`, the goal state is:

```text
case succ
k : ℕ
ih : ∑ i ∈ range (k + 1), ↑i = ↑k * (↑k + 1) / 2
⊢ ∑ i ∈ range (k + 1 + 1), ↑i = ↑(k + 1) * (↑(k + 1) + 1) / 2
```

The step `rw [sum_range_succ]` splits off the last term $k + 1$, and `rw [ih]` replaces the sum up to $k$. The step `push_cast` moves the cast of $k + 1$ to $k + 1$ in `ℚ`, and `ring` checks the identity.

**Example (Divisibility by induction).** For each $n$, $2 \mid n(n + 1)$. In the step, `ih` gives $k(k + 1) = 2m$, and $(k + 1)(k + 2) = k(k + 1) + 2(k + 1) = 2(m + k + 1)$.

```lean
example (n : ℕ) : 2 ∣ n * (n + 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
    obtain ⟨m, hm⟩ := ih
    exact ⟨m + k + 1, by linarith⟩
```

**Example (Induction from a base).** For $n \geq 4$, $n^2 \leq 2^n$. Base: $16 \leq 16$. Step: from $k \geq 4$ and $k^2 \leq 2^k$, $(k + 1)^2 = k^2 + 2k + 1 \leq 2k^2 \leq 2 \cdot 2^k$, where $2k + 1 \leq k^2$ holds since $k \geq 4$ gives $k^2 \geq 4k \geq 2k + 1$.

```lean
example (n : ℕ) (h : 4 ≤ n) : n ^ 2 ≤ 2 ^ n := by
  induction n, h using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    rw [pow_succ 2 k]
    nlinarith
```

The case `succ` has the context `hk : 4 ≤ k` and `ih : k ^ 2 ≤ 2 ^ k`, and the target `(k + 1) ^ 2 ≤ 2 ^ (k + 1)`. The step `rw [pow_succ 2 k]` makes the target `(k + 1) ^ 2 ≤ 2 ^ k * 2`, and `nlinarith` finds the products of `hk` with itself and with `ih`. The arguments of `pow_succ` are necessary: a bare `rw [pow_succ]` rewrites the first power that it finds, which is `(k + 1) ^ 2`, and then `nlinarith` fails on the target `(k + 1) ^ 1 * (k + 1) ≤ 2 ^ (k + 1)`.

**Example (Strong induction).** Each $n \geq 2$ has a prime factor. The proof by strong induction: if $n$ is prime, it is its own factor; otherwise $n = ab$ with $1 < a < n$, and by the hypothesis $a$ has a prime factor, which divides $n$. In Lean, the library has the least prime factor `Nat.minFac`, so the hypothesis of induction is not needed in this example. The goal state of the step shows the form of `ih`:

```text
case ind
n : ℕ
ih : ∀ m < n, m ≥ 2 → ∃ p, Nat.Prime p ∧ p ∣ m
h : n ≥ 2
⊢ ∃ p, Nat.Prime p ∧ p ∣ n
```

```lean
example (n : ℕ) (h : n ≥ 2) : ∃ p, p.Prime ∧ p ∣ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    exact ⟨n.minFac, Nat.minFac_prime (by omega), Nat.minFac_dvd n⟩
```

**Example (Cases).** Each $n$ is $0$ or at least $1$. The split `cases n` gives the goals for `0` and for `m + 1`, with no hypothesis of induction.

```lean
example (n : ℕ) : n = 0 ∨ 1 ≤ n := by
  cases n with
  | zero => left; rfl
  | succ m => right; omega
```

**Example (Parity).** For each $n$, $n^2 \bmod 2 = n \bmod 2$. The split on the parity gives $n = k + k$ and $n = 2k + 1$. After `ring_nf`, each case is a fact of linear arithmetic with the atom $k^2$, and `omega` closes it.

```lean
example (n : ℕ) : n ^ 2 % 2 = n % 2 := by
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · ring_nf; omega
  · ring_nf; omega
```

**Example (interval_cases).** For $n < 2$, $n^2 = n$. The tactic makes the two goals `0 ^ 2 = 0` and `1 ^ 2 = 1`, with the names `«0»` and `«1»`, and `rfl` closes them.

```lean
example (n : ℕ) (h : n < 2) : n ^ 2 = n := by
  interval_cases n
  all_goals rfl
```

### Exercises

1. (A) Prove $\sum_{i=0}^{n} (2i + 1) = (n + 1)^2$ over `ℕ` by induction, with `sum_range_succ` and `ring`.
2. (A) Prove $2^n \geq n + 1$ for each $n$ by induction, and write the goal state of the case `succ`.
3. (A) Prove $3 \mid n^3 + 2n$ for each $n$ by induction. Find the witness of the step.
4. (B) Prove $6 \mid n(n + 1)(2n + 1)$ by induction. In the step, use `refine ⟨m + (k + 1) ^ 2, ?_⟩`, then `push_cast` and `nlinarith`.
5. (B) Prove $2^n > n^2$ for $n \geq 5$ with `Nat.le_induction`. Tell why the claim fails for $n = 4$.
6. (B) Prove the theorem of induction from a base with strong induction, in place of the reduction to $Q(j) = P(b + j)$.
7. (C) Define the Fibonacci numbers by $F_0 = 0$, $F_1 = 1$, $F_{n+2} = F_{n+1} + F_n$, and prove $F_n \leq 2^n$ by strong induction. The step needs the two values $n - 1$ and $n - 2$, so split $n$ into $0$, $1$ and $m + 2$ with `match`.
8. (C) Prove the well-ordering of $\mathbb{N}$ from strong induction, so that the three principles are equivalent.

### Reference

<?reference?>
