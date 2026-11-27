---
title: Working with casts
kind: theory
modules:
  - Mathlib.Data.Nat.Cast.Field
  - Mathlib.Data.Nat.Cast.Order.Field
  - Mathlib.Data.Int.Cast.Field
explains:
  E3: [Nat.cast_div, Nat.cast_sub]
  E2: [Nat.cast_div_charZero, Nat.cast_div_le, Nat.cast_pred, Int.cast_div, Nat.cast_div_div_div_cancel_right]
  E1: auto
families: []
requires: [V02.C04]
reads_with: ["MIL"]
lean:
  - MathlibHandbook/V02/C05/Examples.lean
  - MathlibHandbook/V02/C05/Exercises.lean
  - MathlibHandbook/V02/C05/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Working with casts

### Overview

This section uses the rules of the casts in proofs. The method has three steps. First, move the statement from $\mathbb{N}$ to $\mathbb{Z}$, where subtraction is the real subtraction, or to $\mathbb{Q}$, where division is the real division. Second, prove the statement there with the laws of a ring or a field. Third, come back with the injectivity of the cast. The truncated subtraction and the rounded division of $\mathbb{N}$ do not commute with the cast, so the first step needs a hypothesis for each of them.

The main results are the rule $\uparrow (m / n) = \uparrow m / \uparrow n$ when $n \mid m$, the inequality $\uparrow (m / n) \le \uparrow m / \uparrow n$ in general, and the facts that bring an integer that is not negative back to $\mathbb{N}$.

### Definitions

**Definition (The natural part and the absolute value of an integer).** For $z \in \mathbb{Z}$, $\operatorname{toNat}(z)$ is $z$ if $z \ge 0$ and $0$ if $z < 0$, and $\operatorname{natAbs}(z)$ is $|z|$ as a natural number. In Lean they are `Int.toNat` and `Int.natAbs`.

**Definition (Lift).** Let $T$ be a type with a cast from $S$, and let $C$ be a property of the terms of $T$. The cast *lifts along* $C$ if each $x \in T$ with $C(x)$ is $\uparrow s$ for some $s \in S$.

The cast $\mathbb{N} \to \mathbb{Z}$ lifts along $z \ge 0$, with $s = \operatorname{toNat}(z)$. A proof with a lift replaces a variable of the big type by a cast of a variable of the small type.

::: mathlib
`CanLift` · `Mathlib.Tactic.Lift`

The class `CanLift α β coe cond` says that each `x : α` with `cond x` is `coe y` for some `y : β`. The tactic `lift x to ℕ using hx` uses it to replace `x : ℤ` by `↑n` with `n : ℕ`.

<?decl CanLift?>
:::

### Theorems and proofs

**Theorem (Cast of an exact division).** Let $K$ be a division semiring and let $m, n \in \mathbb{N}$ with $n \mid m$ and $\uparrow n \ne 0$ in $K$. Then $\uparrow (m / n) = \uparrow m / \uparrow n$.

*Proof.* Write $m = n q$. Since $\uparrow n \ne 0$, also $n \ne 0$, so $m / n = q$ in $\mathbb{N}$. The cast gives $\uparrow m = \uparrow n \cdot \uparrow q$. Multiply by $(\uparrow n)^{-1}$, which exists because $\uparrow n \ne 0$. The casts of natural numbers commute with each element, so $\uparrow q = \uparrow m / \uparrow n$. $\square$

In characteristic zero the hypothesis $\uparrow n \ne 0$ follows from $n \ne 0$, and for $n = 0$ both sides are the junk value $0$. So there only $n \mid m$ is needed.

::: mathlib
`Nat.cast_div` · `Mathlib.Data.Nat.Cast.Field`

The second hypothesis is necessary in positive characteristic: in `ZMod 3`, $\uparrow (3 / 3) = 1$, but $\uparrow 3 / \uparrow 3 = 0$.

<?decl Nat.cast_div?>
:::

::: mathlib
`Nat.cast_div_charZero` · `Mathlib.Data.Nat.Cast.Field`

The form for `ℚ` and `ℝ`: `CharZero K` replaces the hypothesis `(n : K) ≠ 0`.

<?decl Nat.cast_div_charZero?>
:::

::: mathlib
`Int.cast_div` · `Mathlib.Data.Int.Cast.Field`

The same rule for the division of `ℤ`, which also rounds, so it also needs `n ∣ m`.

<?decl Int.cast_div?>
:::

**Theorem (Cast of a rounded division).** Let $K$ be an ordered field and let $m, n \in \mathbb{N}$. Then $\uparrow (m / n) \le \uparrow m / \uparrow n$.

*Proof.* If $n = 0$, both sides are $0$. If $n > 0$, write $m = n q + r$ with $q = m / n$ and $r < n$. Then $\uparrow m = \uparrow n \cdot \uparrow q + \uparrow r$ with $\uparrow n > 0$, so $\uparrow m / \uparrow n = \uparrow q + \uparrow r / \uparrow n \ge \uparrow q$. $\square$

::: mathlib
`Nat.cast_div_le` · `Mathlib.Data.Nat.Cast.Order.Field`

There is no hypothesis on `n`, because the case `n = 0` holds with the junk values.

<?decl Nat.cast_div_le?>
:::

**Theorem (Cast of a truncated subtraction).** Let $R$ be a ring and $m \le n$ in $\mathbb{N}$. Then $\uparrow (n - m) = \uparrow n - \uparrow m$. In particular, $\uparrow (n - 1) = \uparrow n - 1$ for $n > 0$.

*Proof.* The first statement is the theorem on subtraction of the previous section. For the second, $n > 0$ means $1 \le n$. $\square$

::: mathlib
`Nat.cast_sub` · `Mathlib.Data.Int.Cast.Basic`

The target is an `AddGroupWithOne`, so the lemma needs a negation but no multiplication. In `ℝ≥0` the form is `Nat.cast_tsub`, with no hypothesis.

<?decl Nat.cast_sub?>
:::

::: mathlib
`Nat.cast_pred` · `Mathlib.Data.Int.Cast.Basic`

The case $m = 1$, with the hypothesis `0 < n`. It is useful for the last index `n - 1` of a sum over `Finset.range n`.

<?decl Nat.cast_pred?>
:::

**Theorem (Integers that are not negative).** Let $z \in \mathbb{Z}$. If $z \ge 0$, then $\uparrow \operatorname{toNat}(z) = z$. For each $z$, $\uparrow \operatorname{natAbs}(z) = |z|$.

*Proof.* If $z \ge 0$, then $\operatorname{toNat}(z)$ is $z$ as a natural number, and $\operatorname{natAbs}(z) = z = |z|$. If $z < 0$, then $\operatorname{natAbs}(z)$ is the natural number $-z$, with cast $-z = |z|$. $\square$

::: mathlib
`Nat.cast_div_div_div_cancel_right` · `Mathlib.Data.Nat.Cast.Field`

A common divisor $d$ of $m$ and $n$ divides out: $\uparrow (m / d) / \uparrow (n / d) = \uparrow m / \uparrow n$. The proof applies the rule for an exact division twice.

<?decl Nat.cast_div_div_div_cancel_right?>
:::

### Examples

**Example (The sum of the first n numbers).** Claim: $\sum_{i = 1}^{n} i = n (n + 1) / 2$ in $\mathbb{N}$, with the division of $\mathbb{N}$. Step 1: in $\mathbb{Q}$, $\sum_{i = 1}^{n} \uparrow i = \uparrow n (\uparrow n + 1) / 2$ by induction, because $\uparrow n (\uparrow n + 1) / 2 + (\uparrow n + 1) = (\uparrow n + 1)(\uparrow n + 2) / 2$. Step 2: $2 \mid n (n + 1)$, because one of $n$ and $n + 1$ is even, so the cast of the right side is $\uparrow n (\uparrow n + 1) / 2$. Step 3: the two sides have the same cast, and injectivity gives the claim.

**Example (An identity with subtraction).** Claim: $(n - 1)(n + 1) = n^2 - 1$ in $\mathbb{N}$ for $n \ge 1$. Since $1 \le n$ and $1 \le n^2$, the casts to $\mathbb{Z}$ are $\uparrow n - 1$ and $\uparrow n^2 - 1$. In $\mathbb{Z}$, $(\uparrow n - 1)(\uparrow n + 1) = \uparrow n^2 - 1$ by the ring laws, and injectivity gives the claim. For $n = 0$ the cast of $0 - 1$ is $0$, not $-1$.

**Counterexample (The hypothesis of the division rule).** In $\mathbb{N}$, $7 / 2 = 3$ and $2 \nmid 7$. The cast of $7 / 2$ to $\mathbb{Q}$ is $3$, but $\uparrow 7 / \uparrow 2 = 7/2$. Only the inequality $3 \le 7/2$ remains.

**Example (A lift).** Claim: if $z \in \mathbb{Z}$, $z \ge 0$ and $z^2 = 9$, then $z = 3$. Lift $z$ to $n \in \mathbb{N}$ with $z = \uparrow n$. Then $n^2 = 9$ in $\mathbb{N}$, so $n = 3$. Without $z \ge 0$ the claim fails: $z = -3$.

### The library around it

The tactic `push_cast` moves each cast to the leaves, and it uses `Nat.cast_sub` and `Nat.cast_div` when the hypotheses are given, as in `push_cast [h]`. The tactic `norm_cast` moves the casts to the outside and removes them, and `exact_mod_cast h` closes a goal that is `h` up to casts. The tactics `zify` and `qify` do Step 1, and `lift` does the lift. The tactic `omega` knows the cast from `ℕ` to `ℤ` and the truncated subtraction.

### Exercises

1. (A) Compute both sides of $\uparrow (m / n) \le \uparrow m / \uparrow n$ in $\mathbb{Q}$ for $m = 17$ and $n = 5$. *Hint.* Use $17 = 5 \cdot 3 + 2$.
2. (A) Give $\operatorname{toNat}(-4)$, $\operatorname{natAbs}(-4)$ and the cast of each to $\mathbb{Z}$. *Hint.* Only one of the casts is $|-4|$.
3. (B) Prove $\sum_{i = 1}^{n} i^3 = (n (n + 1) / 2)^2$ in $\mathbb{N}$ with the method of the first example. *Hint.* Prove the cast form in $\mathbb{Q}$ by induction.
4. (B) Prove that $\uparrow m / \uparrow n < \uparrow (m / n) + 1$ in $\mathbb{Q}$ for $n > 0$, so $m / n$ is the floor of the rational $m/n$. *Hint.* Use $\uparrow r < \uparrow n$.
5. (B) Prove that $\uparrow m \mid \uparrow n$ in $\mathbb{Z}$ if and only if $m \mid n$ in $\mathbb{N}$. *Hint.* If $\uparrow n = \uparrow m \cdot c$ with $n > 0$, then $c > 0$, so $c$ lifts to $\mathbb{N}$.
6. (B) Prove that $\operatorname{natAbs}(a b) = \operatorname{natAbs}(a) \operatorname{natAbs}(b)$ for $a, b \in \mathbb{Z}$. *Hint.* Cast both sides to $\mathbb{Z}$.
7. (C) Let $d = \gcd(m, n) > 0$. Prove that $(m / d) \cdot n = m \cdot (n / d)$ in $\mathbb{N}$. *Hint.* Both sides are $m n / d$ after a cast to $\mathbb{Q}$.

### Notes and history

The proof of an identity of natural numbers in a bigger ring is the usual practice of algebra. In a proof assistant each step must be justified, and the truncated subtraction and the rounded division make this visible. The tactics `push_cast`, `norm_cast` and `exact_mod_cast` come from the work of Lewis and Madelaine (2020).

### Reference

<?reference?>
