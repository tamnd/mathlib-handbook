---
title: Names and search
kind: guide
modules: []
explains: {}
families: []
requires: [V00.C02]
reads_with: ["MSG", "MIL Ch. 2"]
lean:
  - MathlibHandbook/V00/C04/Examples.lean
  - MathlibHandbook/V00/C04/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Names and search

### Overview

Mathlib has more than 250,000 theorems, and a user cannot remember their names. The names follow a convention, so the user can often guess the name from the statement, and read the statement from the name. This section gives the convention, decodes many names of real lemmas, and proves one of them on paper to show that the name lists the hypotheses. Section 4.2 gives the tools for the case when the guess fails.

### The naming convention

**Definition (Name of a lemma).** The *name* of a lemma of Mathlib is a sequence of words joined by `_`, in a namespace. The words read the statement: first the conclusion, then the word `of`, then the hypotheses.

The rules are in the style guide of Mathlib. The main rules are these.

1. Each symbol has a word: `mul` for `*`, `add` for `+`, `sub` for `-`, `div` for `/`, `neg` for unary `-`, `inv` for `⁻¹`, `pow` for `^`, `le` for `≤`, `lt` for `<`, `eq` for `=`, `ne` for `≠`, `zero` for `0`, `one` for `1`, `two` for `2`, `abs` for `|x|`, `sq` for `x ^ 2`, `dvd` for `∣`, `mem` for `∈`, `subset` for `⊆`, `inter` for `∩`, `union` for `∪`.
2. The words `pos` for `0 < x`, `nonneg` for `0 ≤ x`, `neg` for `x < 0` and `nonpos` for `x ≤ 0` name the sign of a term.
3. The name reads the conclusion first. The hypotheses come after the word `of`, in the order of the arguments.
4. An equivalence has `iff` in the name, or it has the name of its left side alone when the right side is the simpler form, as `sub_nonneg`.
5. A lemma about one type or one structure is in the namespace of that type, as `Nat.` or `Finset.`.
6. The words `left` and `right` say on which side a term is, or on which side an operation acts.
7. A name ends with `'` when it is a variant of the name without the mark, and the docstring says how they differ.
8. The suffix `₀` marks a lemma for a group with zero, a type in which each element except `0` has an inverse. It is the variant, with a hypothesis `≠ 0`, of a lemma for groups.

**Example (A name that reads the left side).** The statement of `two_mul` is `2 * a = a + a`. The name reads `2 * a` as `two_mul`. The lemma `mul_two` is `a * 2 = a + a`.

<?lean MathlibHandbook/V00/C04/Examples.lean#two_mul?>

**Example (A name that reads the conclusion).** The conclusion of `add_pos` is that a sum is positive. The hypotheses `0 < a` and `0 < b` are not in the name. When the hypotheses are the expected ones, the name gives only the conclusion, and a variant with other hypotheses gets the longer name, as `add_pos_of_pos_of_nonneg`.

<?lean MathlibHandbook/V00/C04/Examples.lean#add_pos?>

**Example (A hypothesis in the name).** The name `mul_le_mul_of_nonneg_left` reads the conclusion `a * b ≤ a * c`, then the hypothesis `0 ≤ a` after `of`, and `left` says that `a` is on the left.

<?lean MathlibHandbook/V00/C04/Examples.lean#mul_le_mul_of_nonneg_left?>

**Theorem (Multiplying an inequality).** Let $R$ be an ordered ring, $a, b, c \in R$, $b \le c$ and $0 \le a$. Then $ab \le ac$.

*Proof.* From $b \le c$, $0 \le c - b$, by adding $-b$ to both sides. The product of two nonnegative elements of an ordered ring is nonnegative, so $0 \le a(c - b) = ac - ab$. Adding $ab$ to both sides gives $ab \le ac$. $\square$

The hypothesis $0 \le a$ is needed: for $a = -1$, $b = 0$ and $c = 1$, the conclusion $0 \le -1$ is false. So the name must say `of_nonneg`, and the variant with a strict sign, `mul_lt_mul_of_pos_left`, has a strict conclusion `a * b < a * c` from `b < c` and `0 < a`.

::: mathlib
`mul_le_mul_of_nonneg_left` · `Mathlib.Algebra.Order.GroupWithZero.Defs`

The signature does not ask for an ordered ring. It asks for a multiplication, a zero, a preorder, and the class `PosMulMono`: multiplication on the left by a nonnegative element is monotone. That class is the content of the theorem above, so in Mathlib the lemma is close to an axiom, and the proof above is the proof that an ordered ring has the class. The two hypotheses are explicit, in the order of the name: first `b ≤ c`, then `0 ≤ a`.

<?decl mul_le_mul_of_nonneg_left?>
:::

**Example (A namespace).** A lemma about finite sums is in the namespace `Finset`. The command `open Finset` lets the proof write `sum_range_succ` and not `Finset.sum_range_succ`.

<?lean MathlibHandbook/V00/C04/Examples.lean#sum_range_succ?>

### Decoding names

The table decodes the names of lemmas used in this volume and of a few others. Each statement is the one of the signature in the index, with the hypotheses as arrows.

| Name | Statement |
|---|---|
| `add_comm` | `a + b = b + a` |
| `mul_self_nonneg` | `0 ≤ a * a` |
| `sub_nonneg` | `0 ≤ a - b ↔ b ≤ a` |
| `sub_pos` | `0 < a - b ↔ b < a` |
| `sub_eq_zero` | `a - b = 0 ↔ a = b` |
| `abs_sub_comm` | `abs (a - b) = abs (b - a)` |
| `inv_pos` | `0 < a⁻¹ ↔ 0 < a` |
| `le_div_iff₀` | `0 < c → (a ≤ b / c ↔ a * c ≤ b)` |
| `div_le_iff₀` | `0 < c → (b / c ≤ a ↔ b ≤ a * c)` |
| `add_lt_add_of_lt_of_le` | `a < b → c ≤ d → a + c < b + d` |
| `pow_le_pow_left₀` | `0 ≤ a → a ≤ b → a ^ n ≤ b ^ n` |
| `Nat.factorial_pos` | `0 < n !` |
| `Finset.prod_range_succ` | product over `range (n + 1)` is product over `range n` times `f n` |

Three remarks on the table. First, `sub_nonneg` has no `iff` in its name, because the left side `0 ≤ a - b` is the form to rewrite. Second, `le_div_iff₀` reads only the left side of the equivalence, `a ≤ b / c`, and the hypothesis `0 < c` is not in the name: it is the condition of the variant `₀` for a group with zero. Third, `pow_le_pow_left₀` says `left` because the base moves and the exponent `n` is fixed: the operation `^` is monotone in its left argument.

### Dot notation

A lemma in the namespace of a predicate can be used with a dot. If `h : a ≤ b` and `h' : b < c`, then `h.trans_lt h'` is `LE.le.trans_lt h h'`, because the type of `h` is `LE.le a b`. Lean looks at the head of the type of `h`, and finds the lemma in that namespace. In the same way, `hp.two_le` for `hp : Nat.Prime p` is `Nat.Prime.two_le hp`.

::: mathlib
`LE.le.trans_lt` · `Mathlib.Order.Basic`

The name has two parts: the namespace `LE.le`, the predicate `≤`, and the word `trans_lt`, a transitivity with a strict second step. The first explicit argument is `a ≤ b`, so the dot form `h.trans_lt h'` puts `h` in that place. The conclusion is `a < c`.

<?decl LE.le.trans_lt?>
:::

::: mathlib
`LT.lt.le` · `Mathlib.Order.Basic`

The name in the namespace `LT.lt` with the word `le` turns a strict inequality into a weak one: `h.le : a ≤ b` for `h : a < b`. It is one of the most used lemmas in Mathlib, always in the dot form.

<?decl LT.lt.le?>
:::

### Names of additive and multiplicative lemmas

Mathlib states most lemmas for a multiplicative structure, a monoid or a group, and the attribute `to_additive` makes the additive lemma with the words changed: `mul` to `add`, `one` to `zero`, `inv` to `neg`, `prod` to `sum`, `pow` to `nsmul`. So `mul_comm` gives `add_comm`, and `Finset.prod_range_succ` gives `Finset.sum_range_succ`. The two lemmas have the same proof. The additive lemma has a link to the multiplicative lemma in the documentation, under the heading of the source.

### Truncated names

Some names have a word for a special operation. The word `tsub` is the truncated subtraction of `ℕ`, as in `tsub_add_cancel_of_le : a ≤ b → b - a + a = b`. The prefix `nat` or `int` names a cast, as `Nat.cast_le`. The word `zpow` is a power with an integer exponent, and `nsmul` is the multiple `n • a` of an element of an additive monoid by a natural number.

### Common errors

1. Guessing `add_pos_of_pos_of_pos`. The name is `add_pos`. The expected hypotheses are not in the name.
2. Guessing `le_div_iff` for a field. The name without `₀` was deprecated and then removed, and at the commit of the handbook Lean answers `unknown identifier`. Use the name with `₀`.
3. Reading `left` as the side of the equation. In `mul_le_mul_of_nonneg_left` it is the side of the factor `a`.
4. Writing `h.trans` for `h : a < b` and `h' : b ≤ c`. The lemma `LT.lt.trans` needs two strict inequalities. Use `h.trans_le h'`.

### Exercises

1. (A) Guess the name of the lemma `a + 0 = a`. Check the guess on the site.
2. (A) Guess the name of the lemma `0 < a → 0 < b → 0 < a * b`.
3. (A) Guess the statement of `mul_lt_mul_of_pos_left` from its name, and compare it with the variant in the text.
4. (B) The lemma `sub_nonneg` is an equivalence. Prove its statement on paper in an ordered additive group.
5. (B) Guess the statement of `div_le_one`, with its hypothesis. Then prove it on paper in an ordered field.
6. (B) Give the dot form of `le_trans h₁ h₂`, and of `Nat.Prime.one_lt hp`.
7. (C) Prove `pow_le_pow_left₀` on paper by induction on $n$, with `mul_le_mul` as the step. State which of the hypotheses $0 \le a$ and $a \le b$ each step uses.
8. (L) Prove `MathlibHandbook.V00.C04.Exercises.mul_two_example` with one lemma. Find it by its name.
9. (L) Prove `MathlibHandbook.V00.C04.Exercises.mul_pos_example`.
10. (L) Prove `MathlibHandbook.V00.C04.Exercises.sum_range_one_example`.

### Notes and history

The naming convention is in the Mathlib style guide, in the part on naming. It grew from the conventions of the library of Lean 2 and of the first Mathlib, and the community changed it many times, for example when the variants with `₀` replaced the lemmas for linear ordered fields in 2024. Volume 1 of the handbook gives the full convention, with the rules for structures, for `to_additive` and for the order of the words.
