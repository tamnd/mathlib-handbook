---
title: Casts between number types
kind: theory
modules:
  - Mathlib.Data.Nat.Cast.Defs
  - Mathlib.Data.Nat.Cast.Basic
  - Mathlib.Data.Nat.Cast.Order.Basic
  - Mathlib.Data.Int.Cast.Basic
  - Mathlib.Data.Int.Cast.Lemmas
  - Mathlib.Data.Rat.Cast.Defs
explains:
  E3: [Nat.cast_le]
  E2: [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Int.cast_inj, Rat.cast_natCast]
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

## Casts between number types

### Overview

In a textbook, $\mathbb{N} \subseteq \mathbb{Z} \subseteq \mathbb{Q} \subseteq \mathbb{R}$. In Lean, `ℕ`, `ℤ`, `ℚ` and `ℝ` are different types, and a term has one type. So the natural number `n` and the integer `(n : ℤ)` are different terms, and a function called a cast connects them. Lean writes the cast with the arrow `↑n`. A statement that mixes number types has casts in it, and a proof must move the casts through the operations. Mathlib gives a lemma for each operation and each cast, and the tactics `push_cast`, `norm_cast` and `exact_mod_cast` use them. This section shows the casts, the lemmas, and the places where a cast does not commute with an operation.

### Definitions

**Definition (The cast from ℕ).** For a type `R` with `0`, `1` and `+`, the class `NatCast R` gives a function `Nat.cast : ℕ → R`. In an `AddMonoidWithOne`, the axioms say that $\uparrow 0 = 0$ and $\uparrow (n + 1) = \uparrow n + 1$.

**Definition (The cast from ℤ).** For a type `R` with a negation, the class `IntCast R` gives `Int.cast : ℤ → R`. In an `AddGroupWithOne`, it agrees with the cast from `ℕ` on the natural numbers.

**Definition (The cast from ℚ).** For a division ring `R`, the class `RatCast R` gives `Rat.cast : ℚ → R`, and its value at $a / b$ is $\uparrow a / \uparrow b$.

**Definition (Characteristic zero).** A type `R` with `CharZero R` has an injective cast from `ℕ`. The rings `ℤ`, `ℚ`, `ℝ` and `ℂ` have characteristic zero, and `ZMod n` for $n > 0$ does not.

### Theorems and proofs

**Theorem (The cast is a map of semirings).** In a semiring $R$, $\uparrow (m + n) = \uparrow m + \uparrow n$, $\uparrow (m n) = \uparrow m \cdot \uparrow n$ and $\uparrow (m^k) = (\uparrow m)^k$.

*Proof.* The first identity follows by induction on $n$ from the two axioms. The second follows by induction on $n$ from the first and the distributive law. The third follows by induction on $k$ from the second. $\square$

**Theorem (The cast keeps the order).** In an ordered semiring of characteristic zero, $\uparrow m \leq \uparrow n$ if and only if $m \leq n$.

*Proof.* If $m \leq n$, then $n = m + k$, and $\uparrow n = \uparrow m + \uparrow k \geq \uparrow m$, because $\uparrow k \geq 0$ by induction. If $n < m$, the same argument gives $\uparrow n + 1 \leq \uparrow m$, and $\uparrow n < \uparrow n + 1$ in characteristic zero. $\square$

**Theorem (Subtraction).** If $m \leq n$, then $\uparrow (n - m) = \uparrow n - \uparrow m$ in a ring.

*Proof.* The hypothesis gives $n = (n - m) + m$ in $\mathbb{N}$. Apply the cast and subtract $\uparrow m$. $\square$

### Mathlib boxes

::: mathlib
`Nat.cast_le` · `Mathlib.Data.Nat.Cast.Order.Basic`

The lemma is an equivalence and a `simp` lemma, so `simp` removes the casts from an inequality of casts. The form for the strict order is `Nat.cast_lt`, and the form for `ℤ` is `Int.cast_le`.

<?decl Nat.cast_le?>
:::

::: mathlib
`Nat.cast_add` · `Mathlib.Data.Nat.Cast.Defs`

The lemma holds in each `AddMonoidWithOne`, so it needs no ring. It is a `push_cast` lemma: the tactic rewrites with it from left to right.

<?decl Nat.cast_add?>
:::

::: mathlib
`Int.cast_inj` · `Mathlib.Data.Int.Cast.Lemmas`

The cast from `ℤ` is injective in characteristic zero. In `ZMod n`, two different integers can have the same cast, so the lemma needs `CharZero`.

<?decl Int.cast_inj?>
:::

### Examples

**Example (Addition and multiplication).**

<?lean MathlibHandbook/V02/C05/Examples.lean#cast_add_mul?>

**Example (Powers).** The lemma `Nat.cast_ofNat` says that the cast of the literal `2` is the literal `2`.

<?lean MathlibHandbook/V02/C05/Examples.lean#cast_pow?>

**Example (Order).**

<?lean MathlibHandbook/V02/C05/Examples.lean#cast_le?>

**Counterexample (Subtraction).** In `ℕ`, $2 - 5 = 0$, so the cast of $2 - 5$ is $0$ in `ℤ`, but $\uparrow 2 - \uparrow 5 = -3$.

<?lean MathlibHandbook/V02/C05/Examples.lean#cast_sub?>

**Example (Injectivity).**

<?lean MathlibHandbook/V02/C05/Examples.lean#cast_inj?>

**Example (A cast through ℚ).**

<?lean MathlibHandbook/V02/C05/Examples.lean#rat_cast?>

**Example (A tactic for casts).**

<?lean MathlibHandbook/V02/C05/Examples.lean#norm_cast?>

### The library around it

The names of the lemmas follow one pattern: `Nat.cast_add`, `Int.cast_add` and `Rat.cast_add` move a cast through an addition, and the same holds for `mul`, `pow`, `sub`, `le`, `lt` and `inj`. The lemmas for `ℕ` are in `Mathlib/Data/Nat/Cast`, the lemmas for `ℤ` are in `Mathlib/Data/Int/Cast`, and the lemmas for `ℚ` are in `Mathlib/Data/Rat/Cast`. The lemma `Nat.cast_sub` is in `Mathlib.Data.Int.Cast.Basic`, because it needs a negation. The lemma `Int.cast_natCast` says that a cast through `ℤ` is the direct cast. The lemma `Rat.cast_add` needs `CharZero`, because the cast of a fraction divides by its denominator. The tactics `push_cast`, `norm_cast` and `exact_mod_cast` are the subject of a chapter of Volume 34. The tactic `omega` also understands the cast from `ℕ` to `ℤ`.

### Exercises

1. (A) Give the value of `((3 - 7 : ℕ) : ℤ)` and of `((3 : ℕ) : ℤ) - (7 : ℕ)`.
2. (A) Explain why `Int.cast_inj` needs `CharZero` and `Nat.cast_add` does not.
3. (B) Show that the cast from `ℕ` to `ZMod 5` is not injective.
4. (B) Show that $\uparrow (m / n) \leq \uparrow m / \uparrow n$ in `ℚ`, where the left division is the division of `ℕ`.
5. (L) Prove that the cast of $(m + n)^2$ to `ℤ` is $m^2 + 2 m n + n^2$. The solution is `cast_add_sq`.
6. (L) Prove that $\uparrow m < \uparrow n$ in `ℚ` gives $m < n$. The solution is `lt_of_cast_lt`.
7. (L) Prove the cast of a subtraction to `ℚ` with the hypothesis $m \leq n$. The solution is `cast_sub_of_le`.
8. (L) Prove that $\uparrow n \neq \uparrow (n + 1)$ in `ℤ`. The solution is `int_cast_ne_succ`.

### Notes and history

The casts are a cost of the type theory of Lean: a set theory can say that $\mathbb{N} \subseteq \mathbb{R}$, but a type theory must give a function. Lean 3 Mathlib introduced the tactic `norm_cast` in 2019, and the paper of Lewis and Madelaine describes it. In Lean 4, the tactic is part of the core of the language.

### Reference

<?reference?>
