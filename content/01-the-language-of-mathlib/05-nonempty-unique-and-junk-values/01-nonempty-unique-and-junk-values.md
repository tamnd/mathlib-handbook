---
title: Nonempty, Unique and junk values
kind: theory
modules:
  - Mathlib.Basic.Unique
  - Mathlib.Basic.Nonempty
explains:
  E3: [Unique]
  E2: [Unique.instSubsingleton, Nonempty.some, uniqueOfSubsingleton]
  E1: [div_zero, inv_zero, Real.sqrt_eq_zero_of_nonpos, Real.log_zero, Real.log_neg_eq_log, tsub_eq_zero_of_le]
families: []
requires: [V01.C04]
reads_with: ["MIL"]
lean:
  - MathlibHandbook/V01/C05/Examples.lean
  - MathlibHandbook/V01/C05/Exercises.lean
  - MathlibHandbook/V01/C05/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Nonempty, Unique and junk values

### Overview

In Lean, a function `f : α → β` has a value at each element of `α`. A textbook says that $x / 0$ is not defined. Mathlib gives it a value instead, the junk value $0$. Each theorem that needs $b \neq 0$ then states it as a hypothesis. This section shows the classes `Nonempty`, `Inhabited`, `Subsingleton` and `Unique`, and the table of junk values.

### Definitions

**Definition (Nonempty and Inhabited).** `Nonempty α` is the proposition that `α` has an element. `Inhabited α` is data: it gives one element, `default`.

**Definition (Subsingleton and Unique).** `Subsingleton α` says that any two elements of `α` are equal. `Unique α` gives an element and says that each element is equal to it.

**Definition (Junk value).** A junk value is the value that Mathlib gives a function outside the domain of a textbook. The choice makes the function total and makes many lemmas true with no hypothesis.

### Theorems and proofs

**Theorem (Unique gives Subsingleton).** If $\alpha$ is `Unique`, then any two elements of $\alpha$ are equal.

*Proof.* Each element is equal to the default element, so two elements are equal to each other. $\square$

**Theorem (Subsingleton and an element give Unique).** If $\alpha$ is a subsingleton and $a \in \alpha$, then $\alpha$ is `Unique`.

*Proof.* Take $a$ as the default element. Each element is equal to $a$ because $\alpha$ is a subsingleton. $\square$

**Theorem (Division by zero).** In a group with zero, $x / 0 = 0$ for every $x$.

*Proof.* By definition, $x / 0 = x \cdot 0^{-1}$, and $0^{-1} = 0$ is an axiom of the structure. So $x / 0 = x \cdot 0 = 0$. $\square$

The table gives the junk values that a reader meets most often.

| Expression | Value in Mathlib | Lemma |
|---|---|---|
| `x / 0` in a field | `0` | `div_zero` |
| `0⁻¹` in a field | `0` | `inv_zero` |
| `a - b` in `ℕ` with `a ≤ b` | `0` | `tsub_eq_zero_of_le` |
| `a / b` in `ℤ` | rounds toward negative infinity for `b > 0` | |
| `Real.sqrt x` with `x ≤ 0` | `0` | `Real.sqrt_eq_zero_of_nonpos` |
| `Real.log 0` | `0` | `Real.log_zero` |
| `Real.log (-x)` | `Real.log x` | `Real.log_neg_eq_log` |

::: mathlib
`div_zero` · `Mathlib.Algebra.GroupWithZero.Basic`

The lemma has no hypothesis. A proof that divides by a term must show that the term is not zero only when a lemma needs it, for example `div_mul_cancel₀`.

<?decl div_zero?>
:::

::: mathlib
`Real.sqrt_eq_zero_of_nonpos` · `Mathlib.Analysis.Real.Sqrt`

The square root of a negative real number is `0`. So the equation `Real.sqrt x ^ 2 = x` needs the hypothesis `0 ≤ x`.

<?decl Real.sqrt_eq_zero_of_nonpos?>
:::

::: mathlib
`Unique` · `Mathlib.Basic.Unique`

The class has two fields: a default element and a proof that each element is equal to it. The instance `Unique.instSubsingleton` gives `Subsingleton`, and `uniqueOfSubsingleton` goes in the other direction.

<?decl Unique?>
:::

### Examples

**Example (Nonempty).** The anonymous constructor gives a proof that `ℕ` has an element.

<?lean MathlibHandbook/V01/C05/Examples.lean#nonempty?>

**Example (Inhabited).** The default natural number is `0`.

<?lean MathlibHandbook/V01/C05/Examples.lean#inhabited?>

**Example (A unique type).** The type `Fin 1` has one element, so any two of its elements are equal.

<?lean MathlibHandbook/V01/C05/Examples.lean#unique?>

**Example (Junk values in a field).**

<?lean MathlibHandbook/V01/C05/Examples.lean#div_zero?>

**Example (Truncated subtraction).** On `ℕ`, the value of `3 - 5` is `0`, and `rfl` proves it.

<?lean MathlibHandbook/V01/C05/Examples.lean#nat_sub?>

**Example (Integer division).** On `ℤ`, the value of `-7 / 2` is `-4`, not `-3`.

<?lean MathlibHandbook/V01/C05/Examples.lean#int_div?>

**Example (Square root and logarithm).**

<?lean MathlibHandbook/V01/C05/Examples.lean#sqrt_log?>

**Counterexample (A false identity).** The equation `(a - b) + b = a` is false on `ℕ` for `a = 2` and `b = 5`, because `2 - 5 = 0`. The lemma for `ℕ` needs the hypothesis `b ≤ a`.

### The library around it

The lemmas with a junk value have no hypothesis, and the lemmas that need the usual domain have one. For example, `div_zero` has no hypothesis, and `div_mul_cancel₀` needs `b ≠ 0`. The same pattern holds for `Real.sqrt` and `Real.log`. For `ℕ`, the subtraction is the truncated subtraction of an ordered monoid, and its lemmas have the prefix `tsub_`. The class `Nonempty` is a proposition, so a proof can use it with no cost. To get an element from it, `Nonempty.some` uses choice.

### Exercises

1. (A) Give the value of `(1 : ℝ) / 0 + Real.log 0` in Mathlib.
2. (A) Explain why the lemma `div_zero` needs no hypothesis.
3. (B) Show that the equation `a / b * b = a` is false in `ℚ` for some `a` and `b`.
4. (B) Show that a type with a `Unique` instance and a type with one element have the same cardinality.
5. (L) Prove that `2 - 7 = 0` in `ℕ`. The solution is `nat_sub_example`.
6. (L) Prove that `q / 0 = 0` in `ℚ`. The solution is `rat_div_zero_example`.
7. (L) Prove that any two elements of `Fin 1` are equal. The solution is `subsingleton_fin_one`.

### Notes and history

Total functions with junk values are common in proof assistants such as HOL and Isabelle. The choice makes the algebra simpler, because most lemmas hold with no side condition. The cost is that a reader must know the junk values to read a statement correctly.

### Reference

<?reference?>
