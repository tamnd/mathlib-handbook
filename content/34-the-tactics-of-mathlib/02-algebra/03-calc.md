---
title: calc
kind: tactic
modules: []
explains:
  E1: [abs_add_le, le_trans, lt_of_le_of_lt]
families: []
requires: [V00]
reads_with: ["MIL"]
lean: [MathlibHandbook/V34/C02/Examples.lean, MathlibHandbook/V34/C02/Solutions.lean]
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## calc

### Overview

A written estimate is a chain: $a = b \leq c < d = e$, so $a < e$. Each link has its own reason, and the reader checks the links one at a time. The term `calc` writes such a chain in Lean. Each step is a relation between two terms, with its own proof, and Lean combines the steps by transitivity.

The `calc` block is the form in which a proof of Mathlib looks most like a proof on paper. It is also the place where the tactics of this chapter meet: `ring` proves the steps of the form $=$, `gcongr` and `positivity` the steps of the form $\leq$, and `linarith` and `norm_num` the small steps of arithmetic. This section explains the syntax, the rule that combines two relations, and the errors that a chain can have.

### What it does

#### The syntax

A `calc` block has a first step and then a list of steps that start with `_`:

```lean
calc a = b := proof₁
  _ ≤ c := proof₂
  _ < d := proof₃
```

The `_` stands for the right side of the step before. So the second line states $b \leq c$, and the third line states $c < d$. Each proof is a term, or a tactic block `by tac`. The result of the block is the relation between the first term and the last term: here $a < d$.

In tactic mode, `calc` closes the goal when the result is the goal. The first term of the chain must be the left side of the goal, up to definitional equality. If the last term of the chain is not the right side of the goal, the tactic `calc` adds one more goal, the relation between the last term and the right side of the goal. This lets a chain stop early and leave the last step to another tactic.

#### Combining two relations

**Theorem (Transitivity of the order).** Let $a, b, c$ be elements of a preorder. Then:

1. $a \leq b$ and $b \leq c$ give $a \leq c$;
2. $a \leq b$ and $b < c$ give $a < c$;
3. $a < b$ and $b \leq c$ give $a < c$;
4. $a < b$ and $b < c$ give $a < c$;
5. $a = b$ and $b \mathrel{R} c$ give $a \mathrel{R} c$, for each relation $R$, and $a \mathrel{R} b$ and $b = c$ give $a \mathrel{R} c$.

*Proof.* (1) is the axiom of transitivity of a preorder. In a preorder, $a < b$ means $a \leq b$ and not $b \leq a$.

(2) From $a \leq b$ and $b \leq c$ follows $a \leq c$ by (1). Assume $c \leq a$. Then $c \leq a \leq b$ gives $c \leq b$ by (1), which contradicts $b < c$. So not $c \leq a$, and $a < c$.

(3) In the same way, $a \leq c$ by (1). If $c \leq a$, then $b \leq c \leq a$ gives $b \leq a$, which contradicts $a < b$. So $a < c$.

(4) From $a < b$ follows $a \leq b$, and then (2) applies.

(5) is the substitution of equals: replace $b$ with $a$, or $b$ with $c$, in the relation. $\square$

Lean has a class `Trans r s t` for this. An instance says: from `r a b` and `s b c` follows `t a c`. The four cases of the theorem are instances for `≤` and `<`, and the equality has an instance with each relation. For the subset relation, `⊆` with `⊆` gives `⊆`. For divisibility, `∣` with `∣` gives `∣`. A user can add an instance for a new relation. When the block has the steps $r_1, r_2, \ldots$, Lean combines the first two with an instance, then the result with the third, and so on.

The lemmas `le_trans` and `lt_of_le_of_lt` are the forms of (1) and (2) that a proof term uses. In a `calc` block the user does not name them.

#### Why a chain is better than one tactic

A single `nlinarith` can sometimes prove an estimate that has four steps on paper. But when it fails, it says nothing about which step is the problem. A `calc` block has the steps that the author has in mind, and each step has a small proof that a simple tactic finds. If a step fails, the error is at this step, and the goal of the step is shown. So a `calc` block is easier to write, to read and to repair.

::: mathlib
`le_trans` · `Mathlib.Order.Defs.PartialOrder`

The transitivity of `≤` in a preorder. The `Trans` instance for two steps `≤` uses it. The lemma takes the two inequalities as explicit arguments, so `le_trans h₁ h₂` is the term form of a two-step chain.

<?decl le_trans?>
:::

::: mathlib
`lt_of_le_of_lt` · `Mathlib.Order.Defs.PartialOrder`

Case (2) of the theorem. The `Trans` instance for a step `≤` followed by a step `<` uses it, so a chain with one strict step gives a strict result.

<?decl lt_of_le_of_lt?>
:::

::: mathlib
`abs_add_le` · `Mathlib.Algebra.Order.Group.Unbundled.Abs`

The triangle inequality $|a + b| \leq |a| + |b|$ in a linearly ordered additive group. It is the typical middle step of a `calc` block in analysis. The lemma takes $a$ and $b$ as explicit arguments, so `abs_add_le _ _` lets Lean find them from the step.

<?decl abs_add_le?>
:::

### How to use it

Write the chain on paper first. Then write one `calc` step for each link, and put `sorry` as the proof of each step. Lean checks that the chain has the right form: that the first term matches the goal, and that the relations combine to the relation of the goal. Then replace each `sorry` by a proof.

For the proofs of the steps, use this table as a guide.

1. A step $=$ by algebra: `by ring`, or `by field_simp` and `by ring` for fractions.
2. A step $=$ by a hypothesis: `by rw [h]`.
3. A step $\leq$ or $<$ that changes one part of a term: `by gcongr`, with the side goals closed by `positivity` or by a hypothesis.
4. A step $\leq$ or $<$ of linear arithmetic: `by linarith`.
5. A step that is a lemma: the term itself, such as `abs_add_le _ _` or `h`.
6. A step of numerals at the end: `by norm_num`.

Indent the lines with `_` by the same amount, more than the word `calc` or at least more than the line before the block. Write the relation in the direction of the goal: for a goal `a < b`, the chain goes from `a` up to `b`.

### What it cannot do

#### The first term is not the left side of the goal

On the goal `a ≤ c` with the chain `calc b ≤ c := h2`, Lean stops with the error "invalid 'calc' step, left-hand side is b but is expected to be a". The chain must start at the left side of the goal. For a goal `b ≥ a`, which is `a ≤ b`, the chain can start at `b` with steps `≥`, or the goal can be rewritten with `ge_iff_le` first.

#### The relation of the result is not the relation of the goal

A chain with a strict step gives a strict result. On the goal `x ≤ y + 1`, the chain `x ≤ y` and `_ < y + 1` gives `x < y + 1`, and Lean stops with the error "'calc' expression has type x < y + 1 but is expected to have type x ≤ y + 1". The fix is to write the last step as `≤`, or to use `le_of_lt` on the result. The opposite case, a chain of `≤` for a goal `<`, is a real gap: no chain of $\leq$ proves a strict inequality, and one step must be made strict.

#### No instance of Trans

Two relations that have no `Trans` instance cannot follow each other. A step `≤` followed by a step `≥` fails with "invalid 'calc' step, failed to synthesize `Trans` instance". The chain must go in one direction. Turn the step around: $b \geq c$ is the same as $c \leq b$, but then it is a step from $c$ to $b$, and the chain must be written again.

#### A step is false

The chain can have the right form and a false step. The proof of this step then fails, and the error is at this step. On the step `_ = y + 1 := by ring` from `y`, `ring` fails and prints the normal forms `y = 1 + y`. Look at the step: it claims $y = y + 1$. A false step often comes from a copy of the line before with a change that was not made.

#### The chain ends early

If the last term is not the right side of the goal, the tactic `calc` makes a new goal. On the goal `a ≤ c + 1` with the chain $a \leq b \leq c$, the new goal is `c ≤ c + 1`. If no tactic follows, Lean reports it as an unsolved goal named `calc.step`. This is not a bug: add the last step, or prove the new goal after the block.

### Examples

**Example (The arithmetic and geometric means).** For $a, b \in \mathbb{R}$, $2ab \leq a^2 + b^2$. On paper: $2ab = a^2 + b^2 - (a - b)^2 \leq a^2 + b^2$, since a square is not negative. The `calc` block has the two steps. The first is an identity, for `ring`. The second uses `sq_nonneg (a - b)` and `linarith`.

```lean
example (a b : ℝ) : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  calc 2 * a * b = a ^ 2 + b ^ 2 - (a - b) ^ 2 := by ring
    _ ≤ a ^ 2 + b ^ 2 := by
      have := sq_nonneg (a - b)
      linarith
```

**Example (A chain of monotone steps).** For $0 \leq a \leq b$, $a^2 + a \leq b^2 + b$. Each step changes one summand, and `gcongr` proves it.

```lean
example (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) : a ^ 2 + a ≤ b ^ 2 + b := by
  calc a ^ 2 + a ≤ b ^ 2 + a := by gcongr
    _ ≤ b ^ 2 + b := by gcongr
```

In the first step, `gcongr` reduces $a^2 + a \leq b^2 + a$ to $a^2 \leq b^2$ and then to $a \leq b$, with the side goal $0 \leq a$. The hypotheses close both. In the second step it reduces the goal to $a \leq b$.

**Example (An estimate of natural numbers).** For $n \geq 1$, $n^2 + n \leq 2n^2$. On paper: $n^2 + n = n \cdot n + n \cdot 1 \leq n \cdot n + n \cdot n = 2n^2$.

```lean
example (n : ℕ) (hn : 1 ≤ n) : n ^ 2 + n ≤ 2 * n ^ 2 := by
  calc n ^ 2 + n = n * n + n * 1 := by ring
    _ ≤ n * n + n * n := by gcongr
    _ = 2 * n ^ 2 := by ring
```

The middle step reduces $n \cdot n + n \cdot 1 \leq n \cdot n + n \cdot n$ to $n \cdot 1 \leq n \cdot n$ and then to $1 \leq n$, which is `hn`.

**Example (A chain with a side goal).** For $x \geq 1$, $x \leq x^2$. The chain $x = x \cdot 1 \leq x \cdot x = x^2$ has one step $\leq$. The tactic `gcongr` reduces it to $1 \leq x$, which is `h`, with the side goal $0 \leq x$. The side goal is closed by `positivity`: for an atom such as $x$, `positivity` also reads a hypothesis of the form $c \leq x$ or $c < x$ with a numeral $c \geq 0$, here `h : 1 ≤ x`.

```lean
example (x : ℝ) (h : 1 ≤ x) : x ≤ x ^ 2 := by
  calc x = x * 1 := by ring
    _ ≤ x * x := by gcongr
    _ = x ^ 2 := by ring
```

**Example (The triangle inequality).** Let $|x - 1| < 1$. Then $|x| < 2$. On paper: $|x| = |(x - 1) + 1| \leq |x - 1| + |1| < 1 + |1| = 2$. The chain has the four steps of this line.

```lean
example (x : ℝ) (h : |x - 1| < 1) : |x| < 2 := by
  calc |x| = |(x - 1) + 1| := by ring_nf
    _ ≤ |x - 1| + |1| := abs_add_le _ _
    _ < 1 + |1| := by gcongr
    _ = 2 := by norm_num
```

The result is strict, because one step is strict: by case (3) and case (5) of the theorem, the steps $=$, $\leq$, $<$, $=$ combine to $<$.

**Example (Other relations).** The chain works for each relation with a `Trans` instance. For sets, $s \subseteq t \subseteq u$ gives $s \subseteq u$. For integers, $a \mid b \mid 12$ gives $a \mid 12$.

```lean
example (s t u : Set ℕ) (h1 : s ⊆ t) (h2 : t ⊆ u) : s ⊆ u := by
  calc s ⊆ t := h1
    _ ⊆ u := h2

example (a b : ℤ) (h1 : a ∣ b) (h2 : b ∣ 12) : a ∣ 12 := by
  calc a ∣ b := h1
    _ ∣ 12 := h2
```

### Exercises

1. (A) Write a `calc` block that proves $a < c$ from $a < b$ and $b \leq c$. Tell which case of the theorem Lean uses.
2. (A) On the goal `x ≤ y + 1` with `h : x ≤ y`, write the chain `x ≤ y` and `_ < y + 1`. Read the error, and repair the chain in two ways.
3. (A) Prove $(x + 1)^2 \geq 0$ with a `calc` block of one step. Then tell why the block is not needed.
4. (B) Prove $\frac{x}{y} < 1$ for $0 < x < y$ with a `calc` block of two steps, in the manner of the last example of the previous section.
5. (B) Prove that $|a| - |b| \leq |a - b|$ with a `calc` block that starts from $|a| = |(a - b) + b|$. Hint: Mathlib has the result as `abs_sub_abs_le_abs_sub`. Do not use it.
6. (B) For $n \geq 3$, prove $2n + 1 \leq n^2$ in $\mathbb{N}$ with a chain $2n + 1 \leq 3n \leq n \cdot n = n^2$. Tell which tactic proves each step.
7. (C) Define a relation $a \sim b$ on $\mathbb{Z}$ by $5 \mid a - b$. Prove that it is transitive. Explain what Lean needs so that a `calc` block can chain two steps $\sim$.

### Reference

<?reference?>
