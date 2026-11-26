---
title: to_additive and the names of lemmas
kind: theory
modules: []
explains:
  E1: [mul_one, add_zero, mul_inv_cancel_right, add_neg_cancel_right, two_mul, add_le_add, lt_of_lt_of_le]
families: []
requires: [V01.C04]
reads_with: ["MIL"]
lean:
  - MathlibHandbook/V01/C06/Examples.lean
  - MathlibHandbook/V01/C06/Exercises.lean
  - MathlibHandbook/V01/C06/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## to_additive and the names of lemmas

### Overview

Mathlib has more than two hundred thousand theorems. A user finds a lemma by its name more often than by a search. The names follow fixed rules, so a user can often guess the name from the statement. Many lemmas about groups also come in two forms, one with `*` and one with `+`. The attribute `@[to_additive]` makes the second form from the first. This section shows both.

### Definitions

**Definition (Multiplicative and additive forms).** A lemma about a `Group` has an additive form about an `AddGroup`. The additive form replaces `*` by `+`, `1` by `0`, `⁻¹` by `-` and `mul` by `add` in the name.

**Definition (The attribute to_additive).** A theorem with the attribute `@[to_additive]` gets a second theorem, the additive form, with the translated name and statement.

**Definition (A name that says the statement).** The name of a lemma reads the statement from left to right. The symbols become words: `mul`, `add`, `inv`, `neg`, `le`, `lt`, `one` and `zero`. The word `of` comes before the hypotheses.

### Theorems and proofs

**Theorem (Cancel on the right).** In a group, $(a \cdot b) \cdot b^{-1} = a$.

*Proof.* By associativity, $(a \cdot b) \cdot b^{-1} = a \cdot (b \cdot b^{-1}) = a \cdot 1 = a$. $\square$

**Theorem (The additive form).** In an additive group, $(a + b) + (-b) = a$.

*Proof.* This is the same proof with the additive symbols. In Mathlib, `to_additive` writes it. $\square$

::: mathlib
`mul_inv_cancel_right` · `Mathlib.Algebra.Group.Defs`

The lemma has the attribute `@[to_additive]`, so the additive form `add_neg_cancel_right` exists. The name reads the left side: `mul`, then `inv`, then `cancel` on the right.

<?decl mul_inv_cancel_right?>
:::

### Examples

**Example (One lemma in two forms).** The lemmas `mul_one` and `add_zero` are the two forms of one statement.

<?lean MathlibHandbook/V01/C06/Examples.lean#mul_one_add_zero?>

**Example (Our own lemma with to_additive).** The attribute makes the theorem `add_neg_cancel_right_example`.

<?lean MathlibHandbook/V01/C06/Examples.lean#own_to_additive?>

<?lean MathlibHandbook/V01/C06/Examples.lean#use_additive?>

**Example (A name that adds two inequalities).** The name `add_le_add` reads the conclusion `a + c ≤ b + d`.

<?lean MathlibHandbook/V01/C06/Examples.lean#naming?>

**Example (A name with of).** In `lt_of_lt_of_le`, the conclusion `<` comes first, and the hypotheses `<` and `≤` follow, each after `of`.

<?lean MathlibHandbook/V01/C06/Examples.lean#naming_of?>

### The library around it

The rules for names give a few more patterns. A lemma with the suffix `_iff` states an equivalence, for example `Set.mem_union`. A lemma with a dot in the name lives in the namespace of a hypothesis, so `h.trans` is `LT.lt.trans h` for `h : a < b`. The suffixes `_left` and `_right` say which side of an operation the lemma acts on. The names of `ℕ` and `ℤ` lemmas often have the namespace `Nat` or `Int`. The tactic `exact?` searches the library for a lemma that closes the goal, and it shows the name.

### Exercises

1. (A) Guess the name of the lemma $a \cdot b = b \cdot a$ in a commutative monoid, and its additive form.
2. (A) Guess the name of the lemma that gives $a \leq c$ from $a \leq b$ and $b < c$.
3. (B) Write a lemma with `@[to_additive]` about $a^{-1} \cdot (a \cdot b) = b$, and give the name of its additive form.
4. (L) Prove that $-a + a = 0$ in an additive group. The solution is `neg_add_cancel_example`.
5. (L) Prove that $2a = a + a$ in `ℕ`. The solution is `two_mul_example`.
6. (L) Prove that $a < b$ implies $a \leq b$ in `ℕ`. The solution is `le_of_lt_example`.

### Notes and history

The attribute `to_additive` came to the Lean 3 library in 2018. It halves the work on the theory of groups and monoids. The rules for names are in the documentation of Mathlib, and they change little from one version to the next.

### Reference

<?reference?>
