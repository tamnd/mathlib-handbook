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
  E3: [Nat.cast_le, Nat.castRingHom, Int.castRingHom]
  E2: [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Int.cast_inj, Rat.cast_natCast, Int.cast_natCast, RingHom.ext_int, map_intCast, Nat.cast_succ]
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

A textbook writes $\mathbb{N} \subseteq \mathbb{Z} \subseteq \mathbb{Q} \subseteq \mathbb{R}$. Each step of this inclusion is an injective map that keeps the operations and the order. In Lean the four sets are four different types, so the identification must be a function, a *cast*, written with an arrow: `↑n`, or `(n : ℤ)` when the target type is given.

This section proves that the casts are the only maps of their kind, proves the rules that move a cast through an operation, and shows where a rule fails. The main theorem: the cast from $\mathbb{N}$ to a semiring is the unique map of semirings, and in an ordered semiring of characteristic zero it keeps the order.

### Definitions

**Definition (The cast from ℕ).** Let $R$ be a type with an element $0$, an element $1$ and an addition. The cast $\mathbb{N} \to R$ is the function defined by recursion: $\uparrow 0 = 0$ and $\uparrow (n + 1) = \uparrow n + 1$. So $\uparrow n = 1 + \dots + 1$ with $n$ terms.

::: mathlib
`Nat.cast_succ` · `Mathlib.Data.Nat.Cast.Defs`

The class `NatCast R` carries a function `Nat.cast : ℕ → R`, and `AddMonoidWithOne R` adds the axioms `natCast_zero` and `natCast_succ`. A type can so give a faster cast, such as `Int.ofNat` for `ℤ`.

<?decl Nat.cast_succ?>
:::

**Definition (The cast from ℤ).** Let $R$ be a ring. The cast $\mathbb{Z} \to R$ agrees with the cast from $\mathbb{N}$ on $n \in \mathbb{N}$, and $\uparrow (-(n + 1)) = -\uparrow (n + 1)$.

**Definition (The cast from ℚ).** Let $K$ be a division ring. The cast $\mathbb{Q} \to K$ takes $a/b$ in lowest terms, with $a \in \mathbb{Z}$ and $b \in \mathbb{N}$, $b > 0$, to $\uparrow a \cdot (\uparrow b)^{-1}$.

If $\uparrow b = 0$ in $K$, the value is $\uparrow a \cdot 0^{-1} = 0$, a junk value. In characteristic zero this does not happen.

**Definition (Characteristic zero).** A type $R$ with a cast from $\mathbb{N}$ has *characteristic zero* if the cast is injective: $\uparrow m = \uparrow n$ gives $m = n$.

The rings $\mathbb{Z}$, $\mathbb{Q}$ and $\mathbb{R}$ have characteristic zero. The ring $\mathbb{Z}/n\mathbb{Z}$ for $n > 0$ does not, because $\uparrow n = 0 = \uparrow 0$. In Lean the property is the class `CharZero R`.

::: mathlib
`Nat.castRingHom` · `Mathlib.Data.Nat.Cast.Basic`

The bundled form of the cast is `Nat.castRingHom R : ℕ →+* R`. General lemmas about ring maps, for example `map_sum`, apply to it, and its value at `n` is `↑n` by `rfl`.

<?decl Nat.castRingHom?>
:::

### Theorems and proofs

**Theorem (The cast from ℕ is unique).** Let $M$ be an additive monoid and let $x \in M$. There is exactly one map $f : \mathbb{N} \to M$ with $f(m + n) = f(m) + f(n)$ for all $m, n$, $f(0) = 0$ and $f(1) = x$. It is the map $n \mapsto n \cdot x$, where $0 \cdot x = 0$ and $(n + 1) \cdot x = n \cdot x + x$.

*Proof.* Uniqueness. Let $f$ and $g$ be two such maps. Show $f(n) = g(n)$ by induction on $n$. For $n = 0$, both values are $0$. If $f(n) = g(n)$, then $f(n + 1) = f(n) + f(1) = g(n) + x = g(n) + g(1) = g(n + 1)$.

Existence. The map $f(n) = n \cdot x$ has $f(0) = 0$ and $f(1) = x$. For a fixed $m$, use induction on $n$: $f(m + 0) = f(m) + f(0)$, and $f(m + (n + 1)) = f(m + n) + x = (f(m) + f(n)) + x = f(m) + f(n + 1)$ by the associative law of $M$. $\square$

With $x = 1$ the map is the cast. So the cast is the only additive map that sends $1$ to $1$.

::: mathlib
`AddMonoidHom.ext_nat` · `Mathlib.Algebra.Group.Nat.Hom`

This is the uniqueness part: two maps `ℕ →+ A` that agree at `1` are equal. The existence part is `Nat.castAddMonoidHom`.

<?decl AddMonoidHom.ext_nat?>
:::

**Theorem (The cast is a map of semirings).** Let $R$ be a semiring and let $m, n, k \in \mathbb{N}$. Then $\uparrow (m + n) = \uparrow m + \uparrow n$, $\uparrow (m n) = \uparrow m \cdot \uparrow n$ and $\uparrow (m^k) = (\uparrow m)^k$.

*Proof.* The first identity is the existence part of the theorem above, with $x = 1$.

For the second, fix $m$ and use induction on $n$. For $n = 0$ both sides are $0$. For the step, $\uparrow (m (n + 1)) = \uparrow (m n) + \uparrow m = \uparrow m \cdot \uparrow n + \uparrow m = \uparrow m \cdot (\uparrow n + 1)$, by the first identity, the hypothesis of the induction and the distributive law.

For the third, use induction on $k$: $\uparrow (m^0) = \uparrow 1 = 1$, and $\uparrow (m^{k + 1}) = \uparrow (m^k) \cdot \uparrow m = (\uparrow m)^{k + 1}$ by the second identity. $\square$

::: mathlib
`Nat.cast_add` · `Mathlib.Data.Nat.Cast.Defs`

The lemma holds in each `AddMonoidWithOne`. It has the attributes `simp` and `norm_cast`: `push_cast` uses it from left to right and moves the cast to the leaves, and `norm_cast` uses it from right to left.

<?decl Nat.cast_add?>
:::

::: mathlib
`Nat.cast_mul` · `Mathlib.Data.Nat.Cast.Basic`

The hypothesis is `NonAssocSemiring α`, because the proof above does not use the associative law of the multiplication.

<?decl Nat.cast_mul?>
:::

::: mathlib
`Nat.cast_pow` · `Mathlib.Data.Nat.Cast.Basic`

The exponent stays a natural number on both sides. Only the base is cast.

<?decl Nat.cast_pow?>
:::

**Theorem (The ring map from ℤ is unique).** Let $R$ be a ring and let $f : \mathbb{Z} \to R$ be a map of rings. Then $f(n) = \uparrow n$ for each $n \in \mathbb{Z}$.

*Proof.* The restriction of $f$ to $\mathbb{N}$ is additive and sends $1$ to $1$, so $f(n) = \uparrow n$ for $n \in \mathbb{N}$ by the uniqueness theorem. Also $f(-n) + f(n) = f(0) = 0$, so $f(-n) = -\uparrow n$, the cast of $-n$. Each integer is $n$ or $-n$ for some $n \in \mathbb{N}$. $\square$

So $\mathbb{Z}$ is the initial ring, and the cast is its unique map to $R$.

::: mathlib
`RingHom.ext_int` · `Mathlib.Data.Int.Cast.Lemmas`

Two ring maps `ℤ →+* R` are equal, with no hypothesis.

<?decl RingHom.ext_int?>
:::

::: mathlib
`Int.castRingHom` · `Mathlib.Data.Int.Cast.Lemmas`

The bundled cast from `ℤ`. The rules `Int.cast_add`, `Int.cast_mul`, `Int.cast_neg` and `Int.cast_sub` have the same names as for `ℕ`.

<?decl Int.castRingHom?>
:::

::: mathlib
`map_intCast` · `Mathlib.Data.Int.Cast.Lemmas`

A ring map commutes with the cast: `f ↑n = ↑n`. It applies to each type with a `RingHomClass` instance.

<?decl map_intCast?>
:::

**Theorem (Composite casts).** Let $R$ be a ring and $n \in \mathbb{N}$. The cast of $n$ to $\mathbb{Z}$, followed by the cast from $\mathbb{Z}$ to $R$, is the cast of $n$ to $R$. In a division ring $K$, the cast of $n$ to $\mathbb{Q}$, followed by the cast from $\mathbb{Q}$ to $K$, is the cast of $n$ to $K$.

*Proof.* The first is the definition of the cast from $\mathbb{Z}$ at a natural number. For the second, $n = n/1$ in lowest terms, so its cast is $\uparrow n \cdot 1^{-1} = \uparrow n$. $\square$

::: mathlib
`Int.cast_natCast` · `Mathlib.Data.Int.Cast.Basic`

The left side is `((n : ℤ) : R)`. As a `simp` lemma it replaces a double cast by the direct cast, which is the normal form.

<?decl Int.cast_natCast?>
:::

::: mathlib
`Rat.cast_natCast` · `Mathlib.Data.Rat.Cast.Defs`

The lemma holds in each division ring, with no hypothesis of characteristic, because the denominator is `1`.

<?decl Rat.cast_natCast?>
:::

**Theorem (The cast keeps the order).** Let $R$ be a partially ordered additive monoid with a one and characteristic zero, with $0 \le 1$, such that $a \le b$ gives $c + a \le c + b$. Then $\uparrow m \le \uparrow n$ if and only if $m \le n$.

*Proof.* First, $\uparrow k \ge 0$ by induction, because $\uparrow (k + 1) = \uparrow k + 1 \ge \uparrow k + 0$. If $m \le n$, then $n = m + k$ and $\uparrow n = \uparrow m + \uparrow k \ge \uparrow m$.

Conversely, suppose $\uparrow m \le \uparrow n$ and $n < m$. By the first part $\uparrow n \le \uparrow m$, so $\uparrow m = \uparrow n$, and injectivity gives $m = n$, a contradiction. $\square$

The hypothesis of characteristic zero is necessary. In $\mathbb{Z}/2\mathbb{Z}$ with the order $0 \le 1$, $\uparrow 2 = 0 \le \uparrow 1$ but $2 > 1$.

::: mathlib
`Nat.cast_le` · `Mathlib.Data.Nat.Cast.Order.Basic`

The hypotheses are the ones of the theorem: `PartialOrder α`, `AddLeftMono α`, `ZeroLEOneClass α` and `CharZero α`. It is a `simp` lemma. The strict form is `Nat.cast_lt`.

<?decl Nat.cast_le?>
:::

::: mathlib
`Int.cast_inj` · `Mathlib.Data.Int.Cast.Lemmas`

In characteristic zero the cast from `ℤ` is injective. The proof reduces to `ℕ`: $a - b$ or $b - a$ is a natural number with cast $0$.

<?decl Int.cast_inj?>
:::

**Theorem (Subtraction).** Let $R$ be a ring and let $m \le n$ in $\mathbb{N}$. Then $\uparrow (n - m) = \uparrow n - \uparrow m$.

*Proof.* The hypothesis gives $(n - m) + m = n$ in $\mathbb{N}$. Apply the cast and the rule for a sum: $\uparrow (n - m) + \uparrow m = \uparrow n$. Subtract $\uparrow m$ on both sides. $\square$

Without the hypothesis the statement is false, because the subtraction of $\mathbb{N}$ is truncated.

### Examples

**Example (Addition and multiplication).** The rules `Nat.cast_add` and `Nat.cast_mul` move the cast of $m + n m$ to $\uparrow m + \uparrow n \cdot \uparrow m$.

<?lean MathlibHandbook/V02/C05/Examples.lean#cast_add_mul?>

**Example (Powers).** The rule for powers gives $(\uparrow 2)^n$, and `Nat.cast_ofNat` turns the cast of the literal `2` into the literal `2` of `ℚ`.

<?lean MathlibHandbook/V02/C05/Examples.lean#cast_pow?>

**Example (Order).**

<?lean MathlibHandbook/V02/C05/Examples.lean#cast_le?>

**Counterexample (Subtraction).** In $\mathbb{N}$, $2 - 5 = 0$, so the cast of $2 - 5$ to $\mathbb{Z}$ is $0$. But $\uparrow 2 - \uparrow 5 = -3$ in $\mathbb{Z}$. With the hypothesis $m \le n$ the rule holds.

<?lean MathlibHandbook/V02/C05/Examples.lean#cast_sub?>

**Counterexample (Division).** In $\mathbb{N}$, $7 / 2 = 3$, but $\uparrow 7 / \uparrow 2 = 3.5$ in $\mathbb{Q}$. The next section proves the rule when $n \mid m$.

**Example (Injectivity).**

<?lean MathlibHandbook/V02/C05/Examples.lean#cast_inj?>

**Example (A cast through ℚ).**

<?lean MathlibHandbook/V02/C05/Examples.lean#rat_cast?>

**Example (A tactic for casts).** The tactic `exact_mod_cast` moves a hypothesis in `ℤ` and a goal in `ℕ` to the same form.

<?lean MathlibHandbook/V02/C05/Examples.lean#norm_cast?>

### The library around it

The names follow one pattern: the prefix is the source type (`Nat.cast_`, `Int.cast_`, `Rat.cast_`) and the suffix is the operation (`add`, `mul`, `pow`, `sub`, `le`, `lt`, `inj`). The lemmas `Rat.cast_add` and `Rat.cast_mul` are in `Mathlib.Data.Rat.Cast.CharZero`, because they need `CharZero`. The attribute `norm_cast` is how `push_cast`, `norm_cast` and `exact_mod_cast` find these lemmas.

### Exercises

1. (A) Give the value of `((3 - 7 : ℕ) : ℤ)` and of `((3 : ℕ) : ℤ) - (7 : ℕ)`. *Hint.* The first subtraction is in `ℕ`.
2. (B) Show that $\uparrow (m / n) \le \uparrow m / \uparrow n$ in $\mathbb{Q}$ for $n > 0$, where the left division is the division of $\mathbb{N}$. *Hint.* Write $m = n q + r$ with $r < n$.
3. (C) Show that an ordered field has characteristic zero. *Hint.* Show $\uparrow (n + 1) \ge 1 > 0$.
4. (L) Prove that the cast of $(m + n)^2$ to `ℤ` is $m^2 + 2 m n + n^2$. The solution is `cast_add_sq`.
5. (L) Prove that $\uparrow m < \uparrow n$ in `ℚ` gives $m < n$. The solution is `lt_of_cast_lt`.
6. (L) Prove the cast of a subtraction to `ℚ` with the hypothesis $m \le n$. The solution is `cast_sub_of_le`.
7. (L) Prove that $\uparrow n \ne \uparrow (n + 1)$ in `ℤ`. The solution is `int_cast_ne_succ`.

### Notes and history

Set theory identifies $\mathbb{N}$ with a subset of $\mathbb{R}$ by a change of the definitions. A type theory cannot, so the casts are a cost of the foundation of Lean. The tactic `norm_cast` came to Lean 3 Mathlib in 2019, and Lewis and Madelaine describe it in *Simplifying casts and coercions* (2020).

### Reference

<?reference?>
