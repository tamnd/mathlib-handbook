---
title: Coercions
kind: guide
modules: []
explains: {}
families: []
requires: [V00.C01]
reads_with: ["MIL Ch. 2", "TPIL"]
lean:
  - MathlibHandbook/V00/C02/Examples.lean
  - MathlibHandbook/V00/C02/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Coercions

### Overview

In a textbook, $\mathbb{N} \subseteq \mathbb{Z} \subseteq \mathbb{Q} \subseteq \mathbb{R}$, and the number $3$ is the same object in each of them. In Lean, each term has exactly one type. The natural number `(3 : ℕ)` and the real number `(3 : ℝ)` are different terms of different types. To use a natural number as a real number, Lean applies a function, the *cast* from `ℕ` to `ℝ`. Lean inserts the cast by itself, and it prints it as an arrow `↑`. This is a *coercion*.

The arrow `↑` is in many signatures of Mathlib, for example in `Nat.cast_add : ↑(m + n) = ↑m + ↑n`. This section explains what the arrow means, proves the basic laws of the cast from `ℕ` from its definition, and shows which laws need a hypothesis. It then shows the two other common coercions: from a set to a type, and from a bundled map to a function. It ends with the tactics that move casts. After this section the reader can read a statement with arrows and see which cast each arrow is.

### The cast from ℕ

**Definition (Cast from ℕ).** Let $R$ be a type with an addition, a zero and a one. The *cast* $\mathbb{N} \to R$, written $n \mapsto \bar n$ here and `↑n` or `(n : R)` in Lean, is the function defined by recursion:
$$\bar 0 = 0, \qquad \overline{n + 1} = \bar n + 1.$$

So $\bar n = 1 + 1 + \dots + 1$ with $n$ terms. In Mathlib the cast is a field `natCast` of the class `AddMonoidWithOne`, with the two equations above as axioms. A type can then use its own fast definition of the cast, as `ℤ` does, as long as it proves the two equations.

The cast has the laws of a map of semirings. Each law has a short proof by induction.

**Theorem (The cast preserves addition).** Let $R$ be an additive monoid with a one. For all $m, n \in \mathbb{N}$, $\overline{m + n} = \bar m + \bar n$.

*Proof.* Fix $m$ and use induction on $n$. For $n = 0$: $\overline{m + 0} = \bar m = \bar m + 0 = \bar m + \bar 0$. For the step, suppose $\overline{m + n} = \bar m + \bar n$. Then
$$\overline{m + (n+1)} = \overline{(m + n) + 1} = \overline{m + n} + 1 = (\bar m + \bar n) + 1 = \bar m + (\bar n + 1) = \bar m + \overline{n + 1}.$$
The first step is associativity in $\mathbb{N}$, the second is the definition of the cast, the third is the hypothesis of the induction, the fourth is associativity in $R$, and the last is the definition again. $\square$

**Theorem (The cast preserves multiplication).** Let $R$ be a semiring, not necessarily associative or commutative for the multiplication. For all $m, n \in \mathbb{N}$, $\overline{mn} = \bar m \, \bar n$.

*Proof.* Fix $m$ and use induction on $n$. For $n = 0$: $\overline{m \cdot 0} = \bar 0 = 0 = \bar m \cdot 0$, by the law $x \cdot 0 = 0$ of a semiring. For the step, suppose $\overline{mn} = \bar m \bar n$. Then
$$\overline{m(n+1)} = \overline{mn + m} = \overline{mn} + \bar m = \bar m \bar n + \bar m \cdot 1 = \bar m (\bar n + 1) = \bar m \, \overline{n+1},$$
by the previous theorem, the hypothesis of the induction with $x \cdot 1 = x$, and distributivity. $\square$

::: mathlib
`Nat.cast_add` · `Mathlib.Data.Nat.Cast.Defs`

The arrow `↑(m + n)` is the cast of the natural number `m + n` to `R`. The arrows in `↑m + ↑n` are two casts, and the `+` is the addition of `R`. The signature does not show the target `R` in the statement. It is the implicit type `R`, and Lean finds it from the goal. The lemma has the attribute `simp`.

<?decl Nat.cast_add?>
:::

::: mathlib
`Nat.cast_mul` · `Mathlib.Data.Nat.Cast.Basic`

The class `NonAssocSemiring` is a semiring in which the multiplication need not be associative. The proof above uses no associativity of the multiplication, and the class says so.

<?decl Nat.cast_mul?>
:::

### Laws that need a hypothesis

Not every law holds in every target. Three examples show the hypotheses that appear in the signatures.

**Theorem (The cast is monotone).** Let $R$ be an additive monoid with a one and a partial order, such that $0 \le 1$ and $b \le c$ implies $a + b \le a + c$. If $m \le n$ in $\mathbb{N}$, then $\bar m \le \bar n$ in $R$.

*Proof.* First, $0 \le \bar k$ for each $k$, by induction: $\bar 0 = 0$, and if $0 \le \bar k$, then $\overline{k+1} = \bar k + 1 \ge \bar k + 0 = \bar k \ge 0$, where the middle step adds $\bar k$ on the left of $0 \le 1$. Now let $m \le n$, and write $n = m + k$. Then $\bar n = \bar m + \bar k \ge \bar m + 0 = \bar m$, by the theorem on addition and by adding $\bar m$ on the left of $0 \le \bar k$. $\square$

**Theorem (The cast reflects the order).** Let $R$ be as in the previous theorem, and suppose also that the cast is injective. Then $\bar m \le \bar n$ if and only if $m \le n$.

*Proof.* The direction from right to left is the previous theorem. For the other direction, let $\bar m \le \bar n$, and suppose, for a contradiction, that $m \not\le n$. The order of $\mathbb{N}$ is total, so $n < m$, and so $n \le m$. The previous theorem gives $\bar n \le \bar m$. With $\bar m \le \bar n$, antisymmetry gives $\bar m = \bar n$, and injectivity gives $m = n$. This contradicts $n < m$. $\square$

The injectivity of the cast is the class `CharZero`: a type in which $\bar n = 0$ only for $n = 0$, which means $\bar m = \bar n$ only for $m = n$. The fields $\mathbb{Q}$, $\mathbb{R}$ and $\mathbb{C}$ have characteristic zero. The ring $\mathbb{Z}/2\mathbb{Z}$, which is `ZMod 2` in Mathlib, does not: there $\bar 2 = 1 + 1 = 0 = \bar 0$.

::: mathlib
`Nat.cast_le` · `Mathlib.Data.Nat.Cast.Order.Basic`

The conditions are those of the theorem: `AddMonoidWithOne`, `PartialOrder`, `AddLeftMono` (adding on the left keeps the order), `ZeroLEOneClass` ($0 \le 1$) and `CharZero` (the cast is injective). The lemma is an equivalence, so `simp` uses it to remove the casts from an inequality.

<?decl Nat.cast_le?>
:::

::: mathlib
`Nat.cast_sub` · `Mathlib.Data.Int.Cast.Basic`

The cast of a difference is the difference of the casts only when $m \le n$. For $m = 5$ and $n = 2$, the natural number $2 - 5$ is $0$, so its cast to `ℤ` is $0$, but $(2 : ℤ) - 5 = -3$. The hypothesis `m ≤ n` is the first explicit argument.

<?decl Nat.cast_sub?>
:::

::: mathlib
`Nat.cast_div` · `Mathlib.Data.Nat.Cast.Field`

The cast of a quotient needs two hypotheses: $n \mid m$, and $\bar n \ne 0$. For $m = 7$ and $n = 2$, the quotient $7 / 2$ in `ℕ` is $3$, but $7/2 = 3.5$ in `ℚ`.

<?decl Nat.cast_div?>
:::

### The other casts of numbers

The cast from `ℤ` to a ring, `Int.cast`, and the cast from `ℚ` to a division ring of characteristic zero, `Rat.cast`, have the same laws, with the same names in their own namespaces: `Int.cast_add`, `Int.cast_mul`, `Rat.cast_add`. The cast from `ℕ` to `ℝ` is a single cast, not the cast to `ℤ` followed by the cast to `ℝ`, and the lemma `Int.cast_natCast` connects the two routes.

A numeral is not a cast. The term `(2 : ℝ)` is the real number two, written by the class `OfNat`, and no arrow appears. A cast appears when a variable of type `ℕ` is used as a real number. The lemma `Nat.cast_ofNat` says that the cast of the numeral `2 : ℕ` is the numeral `2 : ℝ`, and `simp` uses it.

::: mathlib
`Int.cast_add` · `Mathlib.Data.Int.Cast.Basic`

The class `AddGroupWithOne` is an additive group with a one, with the casts from `ℕ` and `ℤ`. Each ring is one.

<?decl Int.cast_add?>
:::

### Sets as types

A set `s : Set α` is not a type. Mathlib turns it into a type when a type is needed: the type `↥s` has as terms the pairs `⟨x, hx⟩` of an element `x : α` and a proof `hx : x ∈ s`. This is a coercion to a type, and its name is `Set.Elem`. A term `y : ↥s` gives back the element of `α` by a second coercion, written `↑y` or `y.val`.

So a function on a subset, as $f : [0, 1] \to \mathbb{R}$, becomes a function `f : ↥(Set.Icc 0 1) → ℝ`. Each use of $f$ needs a proof that the point is in the interval. That is why Mathlib prefers functions on the whole type, with a hypothesis such as `ContinuousOn f (Set.Icc 0 1)`, Section 1.3.

### Bundled maps as functions

A group homomorphism in Mathlib is a structure `f : G →* H`. It holds the function and the proofs that it preserves the product and the unit. A structure is not a function, but Lean lets the user write `f x`. Lean inserts the coercion `DFunLike.coe f`, which takes the function out of the structure. In the infoview the coercion is invisible or appears as `⇑f`.

::: mathlib
`map_mul` · `Mathlib.Algebra.Group.Hom.Defs`

The lemma applies to each `f : F` for a type `F` of bundled maps with the class `MulHomClass F M N`. So the same lemma `map_mul` works for group homomorphisms, ring homomorphisms, algebra homomorphisms and isomorphisms. The term `f (x * y)` uses the coercion of `f` to a function.

<?decl map_mul?>
:::

### Tactics for casts

Three tactics move casts, and they use the lemmas of this section marked with the attribute `norm_cast`.

1. `push_cast` moves casts to the leaves: it rewrites `↑(m + n)` to `↑m + ↑n`.
2. `norm_cast` moves casts up and removes them where it can: it turns `(↑m : ℝ) ≤ ↑n` into `m ≤ n`.
3. `exact_mod_cast h` closes the goal with `h` when the two differ only by casts.

**Example (Moving a cast).** Let `m n : ℕ` and `h : m ≤ n`. The goal is `(m : ℝ) ≤ n + 1`. The infoview shows it with arrows:

```text
m n : ℕ
h : m ≤ n
⊢ ↑m ≤ ↑n + 1
```

The tactic `norm_cast` sees that `↑n + 1` is the cast of `n + 1`, by `Nat.cast_succ`, and that `↑m ≤ ↑(n + 1)` is `m ≤ n + 1`, by `Nat.cast_le`. The new goal `m ≤ n + 1` has no casts, and `omega` closes it with `h`. The step that removes the casts uses the hypothesis `CharZero ℝ` and the order conditions, as the theorem above does.

**Example (A cast that does not move).** Let `n : ℕ` with `1 ≤ n`. The real number `((n - 1 : ℕ) : ℝ)` is the cast of a truncated difference. The tactic `push_cast` does not rewrite it to `(n : ℝ) - 1` without a proof of `1 ≤ n`, because the law `Nat.cast_sub` needs it. The call `push_cast [Nat.cast_sub h]` with `h : 1 ≤ n` gives the lemma.

### Common errors

1. Writing `(n - 1 : ℝ)` and expecting the cast of `n - 1 : ℕ`. Lean reads `(n - 1 : ℝ)` as `↑n - 1`, the difference in `ℝ`, and that is usually what the user wants. The term `((n - 1 : ℕ) : ℝ)` is a different number for $n = 0$.
2. Writing `(n / 2 : ℝ)` for a natural number `n` and getting the cast of `n / 2 : ℕ`, or the other way round. Look at the arrows in the infoview: `↑n / 2` is the real quotient, `↑(n / 2)` is the cast of the rounded quotient.
3. Expecting `Nat.cast_le` to hold in every ordered ring. It needs `CharZero`, and Lean says `failed to synthesize CharZero` when it is missing.
4. Treating `↥s` as a subset. It is a type, and its terms are pairs.

### Exercises

1. (A) Give the value of `((7 : ℕ) / 2 : ℚ)`, which Lean reads as `(↑7 : ℚ) / 2`, and of `(((7 : ℕ) / 2 : ℕ) : ℚ)`.
2. (A) Prove from the definition that $\bar 1 = 1$ in each additive monoid with a one.
3. (A) Prove that the cast is injective in $\mathbb{Q}$. Hint: the cast from $\mathbb{N}$ to $\mathbb{Q}$ is monotone and $0 < 1$.
4. (B) Prove that $\overline{m^k} = \bar m^k$ in each semiring, by induction on $k$.
5. (B) In `ZMod 3`, compute $\bar 0, \bar 1, \dots, \bar 5$. Show that the theorem on the order cannot hold for any partial order on `ZMod 3` with $0 \le 1$ and the condition `AddLeftMono`.
6. (B) Find natural numbers $m, n$ with $n \mid m$ and $\overline{m / n} \ne \bar m / \bar n$ in `ZMod 2`. Which hypothesis of `Nat.cast_div` fails?
7. (C) Let $R$ be a ring. Show that there is exactly one ring homomorphism from $\mathbb{Z}$ to $R$, and that it is the cast `Int.cast`.

### Notes and history

The coercion system of Lean 4 was designed by Leonardo de Moura and Sebastian Ullrich. The tactic `norm_cast` was first written for Lean 3 by Paul-Nicolas Madelaine and Robert Lewis, and their paper "Simplifying casts and coercions" (2020) explains its method. The class `CharZero` and the lemmas on casts are among the oldest parts of Mathlib, and the unbundled form of `AddMonoidWithOne` with a field `natCast` dates from 2022.
