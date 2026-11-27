---
title: The naming convention
kind: theory
modules: []
explains:
  E1: [le_of_lt, lt_of_lt_of_le, two_mul, add_le_add, sub_nonneg, mul_pos, mul_inv_eq_one, sub_eq_zero, mul_left_cancel, mul_right_cancel, ne_of_gt, mul_self_nonneg, Nat.exists_infinite_primes, Real.pi_gt_three, LT.lt.le, LE.le.trans]
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

## The naming convention

### Overview

Mathlib has more than two hundred thousand theorems. A textbook gives a theorem a number or the name of a person. Mathlib gives most theorems a name that describes the statement. The name `add_le_add` is the statement $a \leq b \to c \leq d \to a + c \leq b + d$, read from the conclusion: "add, le, add". A user who knows the rules can often write the name of a lemma before finding it, and a reader can often read the statement from the name.

This section gives the rules, shows how to decode and encode a name, and proves the small theorems that the examples name. The proofs show that each name labels a short argument from the axioms of an order or a ring.

### Definitions

**Definition (Case of a name).** Mathlib uses three cases.

1. Theorems and proofs of propositions use `snake_case`: `mul_comm`, `le_of_lt`.
2. Types, structures and classes use `UpperCamelCase`: `Group`, `Function.Injective`.
3. Functions and other data use `lowerCamelCase`: `Nat.succ`, `Finset.card`.

A name inside a theorem name keeps the case of a theorem: the theorem about `Function.Injective` is `Function.Injective.comp`, but in a snake case name the word is `injective`, as in `Function.injective_id`.

**Definition (Words for symbols).** The parts of a theorem name are the words of the symbols in the statement:

| Symbol | Word | Symbol | Word |
|---|---|---|---|
| `+` | `add` | `≤` | `le` |
| `*` | `mul` | `<` | `lt` |
| `-` (binary) | `sub` | `≠` | `ne` |
| `-` (unary) | `neg` | `∣` | `dvd` |
| `⁻¹` | `inv` | `∈` | `mem` |
| `/` | `div` | `⊆` | `subset` |
| `^` | `pow` | `∘` | `comp` |
| `0`, `1`, `2` | `zero`, `one`, `two` | `¬` | `not` |

**Definition (Order of the words).** The name describes the conclusion first, in the order of the symbols. The hypotheses follow the word `of`, also in order. So `lt_of_lt_of_le` is: the conclusion `<`, from the hypotheses `<` and `≤`.

**Definition (Fixed words).** Some words name standard properties: `comm` (commutativity), `assoc` (associativity), `cancel`, `inj` (injectivity as an equivalence), `injective`, `mono`, `self`, `left` and `right`, `iff` for an equivalence, `ext` for extensionality, and `eq` and `ne`. The suffix `'` marks a variant, and `₀` marks a form for a group with zero, as in `div_mul_cancel₀`.

::: mathlib
`le_of_lt` · `Mathlib.Order.Defs.PartialOrder`

The statement is `a < b → a ≤ b` in a preorder. The name is the conclusion `le` and the hypothesis `of_lt`. The dot form `h.le` gives the same proof from `h : a < b`, because `LT.lt.le` is an alias.

<?decl le_of_lt?>
:::

### Theorems and proofs

**Theorem (le_of_lt).** In a preorder, $a < b$ implies $a \leq b$.

*Proof.* In a Mathlib preorder, $a < b$ is defined as $a \leq b \land \lnot (b \leq a)$. The first component is the conclusion. $\square$

**Theorem (lt_of_lt_of_le).** In a preorder, $a < b$ and $b \leq c$ imply $a < c$.

*Proof.* From $a < b$, $a \leq b$, so $a \leq c$ by transitivity. Assume $c \leq a$. Then $b \leq c \leq a$, so $b \leq a$, which contradicts $a < b$. So $\lnot (c \leq a)$, and $a < c$. $\square$

**Theorem (two_mul).** In a semiring, $2a = a + a$.

*Proof.* $2 = 1 + 1$, so $2a = (1 + 1) a = 1 a + 1 a = a + a$, by distributivity and the identity law. $\square$

**Theorem (add_le_add).** In an ordered additive commutative monoid, $a \leq b$ and $c \leq d$ imply $a + c \leq b + d$.

*Proof.* The order is compatible with addition: $x \leq y$ implies $x + z \leq y + z$ and $z + x \leq z + y$. So $a + c \leq b + c \leq b + d$, and transitivity gives the result. $\square$

**Theorem (sub_nonneg).** In an ordered additive commutative group, $0 \leq a - b$ if and only if $b \leq a$.

*Proof.* Addition of $b$ to both sides preserves the order, and addition of $-b$ reverses this step. So $0 \leq a - b$ implies $0 + b \leq (a - b) + b$, that is $b \leq a$. Conversely, $b \leq a$ implies $b + (-b) \leq a + (-b)$, that is $0 \leq a - b$. $\square$

The name reads the left side of the equivalence, `sub` and `nonneg`, where `nonneg` is the fixed word for $0 \leq x$. The words `pos` for $0 < x$, `nonpos` for $x \leq 0$ and `neg` for $x < 0$ are used in the same way, so `mul_pos` is $0 < a \to 0 < b \to 0 < a b$. The word `neg` also names the unary minus, and the statement decides which meaning applies.

The four names come from the four statements by the rules: the conclusion, then `of` and the hypotheses. For `add_le_add`, the hypotheses are not in the name, because the name `add_le_add` already shows the form $a + c \leq b + d$, and the hypotheses follow from it. This is a frequent pattern: the name of a monotonicity lemma is its conclusion only.

### Examples

**Example (Decoding a name).** The name `add_le_add` reads "add, le, add": a sum is at most a sum.

<?lean MathlibHandbook/V01/C06/Examples.lean#naming?>

**Example (The word of).** In `lt_of_lt_of_le`, the conclusion comes first and the hypotheses follow.

<?lean MathlibHandbook/V01/C06/Examples.lean#naming_of?>

**Example (Encoding a name).** The statement $a \cdot b^{-1} = 1 \leftrightarrow a = b$ in a group has the conclusion an `iff`. Read the left side: `mul`, `inv`, `eq`, `one`. Then `iff`, then `eq`. The name is `mul_inv_eq_one`, since Mathlib usually leaves out the right side of an `iff` when it is clear. The same rules give `sub_eq_zero` for $a - b = 0 \leftrightarrow a = b$.

**Example (Left and right).** `mul_left_cancel` cancels the factor on the left: $a b = a c \to b = c$. `mul_right_cancel` cancels on the right: $b a = c a \to b = c$. The word gives the position of the term that is removed.

**Counterexample (A name that is not a description).** Some theorems have a traditional name, not a description of the statement. `Nat.exists_infinite_primes` states that for every $n$ there is a prime $p \geq n$, and `Real.pi_gt_three` states $\pi > 3$. Their names follow the rules only in part. `Function.cantor_surjective` has the name of a person. A user who does not find a lemma by its descriptive name must use a search tool.

### The library around it

The rules are written in the Mathlib documentation, in the page "Naming conventions". Two search tools help when a guess fails. The tactic `exact?` searches the library for a lemma that closes the goal, and the tactic `apply?` lists lemmas that apply. The website search tools search by natural language or by a pattern of the statement, such as `_ * _ ≤ _ * _`.

The namespace of a lemma is the type or the structure of the main object: `Nat.Prime.two_le` is about prime natural numbers, and `Finset.card_union_le` is about finsets. With dot notation, `h.trans h'` calls `LE.le.trans` when `h : a ≤ b`. So the namespace is also a part of the name to guess.

#### Common errors

1. A learner reads `le_of_lt` as "from le, get lt". The conclusion comes first.
2. A learner searches for `add_sub_cancel` and finds a lemma with another order of terms. The variants `add_sub_cancel_left` and `add_sub_cancel_right` differ in the position of the cancelled term. Read the statement before use.
3. A learner writes `lt_le_trans`. The Mathlib name is `lt_of_lt_of_le`, or the dot form `h.trans_le`.

### Exercises

1. (A) Decode the names `mul_le_mul`, `sub_nonneg`, `abs_nonneg`, `mul_self_nonneg` and `ne_of_gt`, and write their statements.
2. (A) Encode the statements $a + b = b + a$, $a \leq b \to b \leq a \to a = b$ and $0 < a \to 0 < b \to 0 < a b$.
3. (B) Prove `ne_of_gt`: in a preorder, $b < a$ implies $a \neq b$.
4. (B) Prove `mul_self_nonneg`: in a linearly ordered ring, $0 \leq a a$. Split on the sign of $a$.
5. (C) Find three lemmas in Mathlib whose names do not follow the rules, and explain the reason for each.
6. (L) Prove that $2a = a + a$ in $\mathbb{N}$. The solution is `two_mul_example` in `Solutions.lean`.
7. (L) Prove that $a < b$ implies $a \leq b$ in $\mathbb{N}$. The solution is `le_of_lt_example` in `Solutions.lean`.

### Notes and history

Descriptive names were used in the libraries of the HOL family and in the Lean 3 library before Mathlib. The search tools Loogle and LeanSearch, and the tactic `exact?`, reduce the need to guess a name.

### Reference

<?reference?>
