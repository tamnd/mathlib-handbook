---
title: Junk values
kind: guide
modules: []
explains: {}
families: []
requires: [V00.C03]
reads_with: ["MIL Ch. 2"]
lean:
  - MathlibHandbook/V00/C05/Examples.lean
  - MathlibHandbook/V00/C05/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Junk values

### Overview

In Lean, each function is total: it has a value at each point of its domain type. Division on `ℚ` is a function from `ℚ × ℚ` to `ℚ`, so `1 / 0` has a value. Mathlib chooses the value `0`. A value that is outside the usual definition is a junk value. This section shows the junk values that a reader meets first, and the reason for them.

### The junk values

| Expression | Value in Mathlib | The usual law and its hypothesis |
|---|---|---|
| `a / 0` in a field | `0` | `a / a = 1` needs `a ≠ 0` |
| `a - b` in `ℕ` with `a < b` | `0` | `a - b + b = a` needs `b ≤ a` |
| `a / b` in `ℕ` | the quotient, rounded down | `a / b * b = a` needs `b ∣ a` |
| `√x` in `ℝ` with `x < 0` | `0` | `√x ^ 2 = x` needs `0 ≤ x` |
| `0⁻¹` in a field | `0` | `a * a⁻¹ = 1` needs `a ≠ 0` |

**Example (Division by zero).** The lemma `div_zero` states that `a / 0 = 0` in each group with zero.

<?lean MathlibHandbook/V00/C05/Examples.lean#div_zero?>

**Example (Subtraction in ℕ).** Subtraction in `ℕ` stops at zero. Lean computes the value, so `rfl` is a proof.

<?lean MathlibHandbook/V00/C05/Examples.lean#nat_sub?>

**Example (Division in ℕ).** Division in `ℕ` rounds down.

<?lean MathlibHandbook/V00/C05/Examples.lean#nat_div?>

**Example (The square root of a negative number).** The square root of a negative real number is zero.

<?lean MathlibHandbook/V00/C05/Examples.lean#sqrt_neg?>

**Example (A law with its hypothesis).** The law `a / a = 1` is false for `a = 0`, so the lemma `div_self` has the hypothesis `a ≠ 0`.

<?lean MathlibHandbook/V00/C05/Examples.lean#div_self?>

### Why Mathlib uses junk values

A total function is easier to use than a partial function. With a junk value, the expression `a / b` is a rational number for all `a` and `b`, and a statement can use it with no proof that `b ≠ 0`. The hypothesis goes to the lemmas that need it.

The junk value never makes a false theorem. A theorem that uses `a / a = 1` must have the hypothesis `a ≠ 0`, because the lemma `div_self` asks for it. A theorem whose statement has `a / b` with $b = 0$ says something about the number $0$, and it is true or false as a statement about $0$.

::: mathlib
`div_self` · `Mathlib.Algebra.GroupWithZero.Units.Basic`

The element `a` is an implicit argument. The explicit argument is the proof of `a ≠ 0`, and Lean finds `a` from its type.

<?decl div_self?>
:::

### The inverse of zero

**Definition (Group with zero).** A *group with zero* is a monoid $G$ with an element $0$ and a map $a \mapsto a^{-1}$ such that $0 \ne 1$, $0 \cdot a = a \cdot 0 = 0$ for all $a$, $a a^{-1} = 1$ for $a \ne 0$, and $0^{-1} = 0$. Division is $a / b = a b^{-1}$.

The last axiom is a choice. No other value is possible for a true inverse:

**Theorem (Zero has no inverse).** In a ring with $0 \ne 1$, no element $b$ satisfies $0 \cdot b = 1$.

*Proof.* For each $b$, $0 \cdot b = (0 + 0) b = 0 \cdot b + 0 \cdot b$, so $0 \cdot b = 0$. If $0 \cdot b = 1$, then $0 = 1$, against the hypothesis. $\square$

So the value of $0^{-1}$ is junk in each case, and $0$ is the choice that keeps the most laws true with no hypothesis.

**Theorem (Laws of the inverse with no hypothesis).** In a commutative group with zero, for all $a$ and $b$:

1. $(a^{-1})^{-1} = a$;
2. $(ab)^{-1} = a^{-1} b^{-1}$;
3. $(a + b)/c = a/c + b/c$, in a field.

*Proof.* (1) If $a = 0$, both sides are $0$, by $0^{-1} = 0$ twice. If $a \ne 0$, then $a^{-1} \ne 0$, since $a a^{-1} = 1 \ne 0$. So $a^{-1}$ has the inverse $(a^{-1})^{-1}$, and also the inverse $a$, since $a^{-1} a = 1$. An inverse in a monoid is unique: if $xy = 1$ and $xz = 1$ with commutativity, then $y = y(xz) = (yx)z = z$. So $(a^{-1})^{-1} = a$.

(2) If $a = 0$ or $b = 0$, then $ab = 0$, so the left side is $0^{-1} = 0$, and the right side is a product with the factor $0^{-1} = 0$, so it is $0$. If $a, b \ne 0$, then $ab \ne 0$, because $ab = 0$ would give $a = a b b^{-1} = 0$. Then $(ab)(a^{-1}b^{-1}) = (a a^{-1})(b b^{-1}) = 1$, and by uniqueness of the inverse, $(ab)^{-1} = a^{-1}b^{-1}$.

(3) By the definition of division and distributivity, $(a + b)/c = (a + b) c^{-1} = a c^{-1} + b c^{-1} = a/c + b/c$. No step uses $c \ne 0$. $\square$

::: mathlib
`inv_zero` · `Mathlib.Algebra.GroupWithZero.Defs`

The junk value of the inverse, as an axiom of a group with zero. It has the attribute `simp`, so `simp` replaces `0⁻¹` by `0`.

<?decl inv_zero?>
:::

::: mathlib
`mul_inv` · `Mathlib.Algebra.Group.Basic`

The class `DivisionCommMonoid` covers both commutative groups and commutative groups with zero, because the law holds in both with no hypothesis. The theorem above is the proof for the second case.

<?decl mul_inv?>
:::

::: mathlib
`add_div` · `Mathlib.Algebra.Field.Basic`

All three arguments are explicit and none has a hypothesis. The class `DivisionSemiring` is the weakest class with division and addition.

<?decl add_div?>
:::

### Truncated subtraction

In `ℕ`, $a - b$ is the difference when $b \le a$ and $0$ otherwise.

**Theorem (Laws of truncated subtraction).** For all $a, b \in \mathbb{N}$:

1. $a - b = 0$ if and only if $a \le b$;
2. $(a - b) + b = \max(a, b)$.

*Proof.* (1) If $a \le b$, the value is $0$ by definition. If $a > b$, the value is the true difference $a - b > 0$. (2) If $b \le a$, then $(a - b) + b = a = \max(a, b)$. If $a < b$, then $(a - b) + b = 0 + b = b = \max(a, b)$. $\square$

So the law $(a - b) + b = a$ needs the hypothesis $b \le a$, and for $a = 5$, $b = 7$ the left side is $7$.

::: mathlib
`tsub_eq_zero_iff_le` · `Mathlib.Algebra.Order.Sub.Basic`

The prefix `tsub` names the truncated subtraction. The lemma holds in each canonically ordered monoid with a subtraction of this kind, the class `OrderedSub`. The type `ℕ` is one, and so is the type `ℝ≥0` of nonnegative reals.

<?decl tsub_eq_zero_iff_le?>
:::

### Junk values in analysis

The same choice appears for each partial function of analysis. Each lemma of the table gives the value in Mathlib.

| Expression | Junk value | Lemma |
|---|---|---|
| `Real.log 0` | `0` | `Real.log_zero` |
| `Real.log x` for `x < 0` | `Real.log (-x)` | `Real.log_neg_eq_log` |
| `√x` for `x ≤ 0` | `0` | `Real.sqrt_eq_zero_of_nonpos` |
| `deriv f x`, `f` not differentiable at `x` | `0` | `deriv_zero_of_not_differentiableAt` |
| `∫ x, f x ∂μ`, `f` not integrable | `0` | `MeasureTheory.integral_undef` |
| `sSup s` in `ℝ`, `s` not bounded above | `0` | `Real.sSup_of_not_bddAbove` |

The logarithm is defined on all of $\mathbb{R}$ by $\log x = \log |x|$ for $x \ne 0$. So `Real.log (-1) = 0` and `Real.log (-e) = 1`. The square root is defined by $\sqrt{x} = \sqrt{\max(x, 0)}$, so the law $\sqrt{x}^2 = x$ needs $0 \le x$.

::: mathlib
`Real.sq_sqrt` · `Mathlib.Analysis.Real.Sqrt`

The hypothesis `0 ≤ x` is the explicit argument, and `x` is implicit. Without it the law fails: $\sqrt{-1}^2 = 0^2 = 0 \ne -1$.

<?decl Real.sq_sqrt?>
:::

::: mathlib
`deriv_zero_of_not_differentiableAt` · `Mathlib.Analysis.Calculus.Deriv.Basic`

The derivative `deriv f x` is defined for all `f` and `x`. When `f` has no derivative at `x`, its value is `0`. So `deriv (fun x => |x|) 0 = 0`. A theorem on derivatives needs the hypothesis `DifferentiableAt 𝕜 f x` to say that `deriv f x` is a true derivative.

<?decl deriv_zero_of_not_differentiableAt?>
:::

::: mathlib
`MeasureTheory.integral_undef` · `Mathlib.MeasureTheory.Integral.Bochner.Basic`

The integral of a function that is not integrable is `0`. So the law of linearity `∫ (f + g) = ∫ f + ∫ g` needs the hypotheses that `f` and `g` are integrable.

<?decl MeasureTheory.integral_undef?>
:::

### Common errors

1. Writing `x / y` and proving a property that needs `y ≠ 0` with no hypothesis. The goal stays open, and the search finds lemmas with the hypothesis.
2. Reading `Real.log x` as the logarithm of a positive number. A statement on `Real.log x` with no hypothesis `0 < x` is a statement about $\log |x|$.
3. Expecting `deriv f x` to fail when `f` is not differentiable. It gives `0`, and a proof that uses it as a derivative is false.
4. Moving a law with a hypothesis to a law with no hypothesis. The law $(a - b) + c = (a + c) - b$ is false in `ℕ` for $a = 0$, $b = 1$, $c = 1$.

### Exercises

1. (A) Give the value of `(5 : ℕ) - 7 + 7` in Mathlib. Compare it with `5`.
2. (A) Give the value of `(7 : ℤ) / 2` and of `(-7 : ℤ) / 2`. Check the second value in an editor with `#eval`.
3. (A) Give `Real.log (-1)`, `Real.sqrt (-4)` and `deriv (fun x : ℝ => |x|) 0` in Mathlib.
4. (B) Show that `(a + b) / c = a / c + b / c` is true in `ℚ` for `c = 0`.
5. (B) Show that the law $a / (b / c) = a c / b$ holds in a field with $0^{-1} = 0$ for all $a, b, c$.
6. (B) Find a law of division in a field that fails for some value with $0^{-1} = 0$, and give its hypothesis.
7. (C) In a field, give $0^{-1}$ some value $t$, and keep the true inverse of each $a \ne 0$. Prove that the law $(a^{-1})^{-1} = a$ for all $a$ forces $t = 0$. Prove that the law $(ab)^{-1} = a^{-1} b^{-1}$ for all $a, b$ forces $t = 0$ in a field with more than two elements. Hint: take $a = 0$, and then $a = 0$ and $b = c$ with $c \ne 0, 1$.
8. (L) Prove `MathlibHandbook.V00.C05.Exercises.zero_div_example`.
9. (L) Prove `MathlibHandbook.V00.C05.Exercises.nat_sub_add_example`.

### Notes and history

Kevin Buzzard explains the choice of junk values for a general reader in his blog post "Division by zero in type theory: a FAQ" (2020). The same choice is in Isabelle/HOL and in other provers. Volume 1 gives the full table of junk values of Mathlib.
