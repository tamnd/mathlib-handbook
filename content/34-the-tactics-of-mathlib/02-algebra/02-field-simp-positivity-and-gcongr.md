---
title: field_simp, positivity and gcongr
kind: tactic
modules: [Mathlib.Tactic.FieldSimp.Discharger, Mathlib.Tactic.Positivity.Core, Mathlib.Tactic.GCongr.Core]
explains:
  E2: [Mathlib.Tactic.FieldSimp.discharge, Mathlib.Meta.Positivity.core, Mathlib.Tactic.GCongr.gcongrExt]
  E1: [mul_le_mul_of_nonneg_right]
families: []
requires: [V00]
reads_with: ["MIL"]
lean: [MathlibHandbook/V34/C02/Examples.lean, MathlibHandbook/V34/C02/Solutions.lean]
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## field_simp, positivity and gcongr

### Overview

Three tactics do the steps of a computation in a field or in an ordered ring. The tactic `field_simp` clears the denominators of an equation. The tactic `positivity` proves that a term is positive, not negative or not zero. The tactic `gcongr` reduces an inequality between two terms of the same form to inequalities between their parts.

The three tactics work together. A typical estimate of analysis has the form "$\frac{x}{x + 1} < 1$ since $x < x + 1$ and $x + 1 > 0$". Here `gcongr` reduces the inequality of fractions to the inequality of the numerators, `positivity` proves that the denominator is positive, and `field_simp` simplifies $\frac{x + 1}{x + 1}$ to $1$. This section explains the rules behind each tactic, so that the reader can see which side goals each one makes and why it fails.

### What it does

#### field_simp

In a field, the rules of fractions hold under conditions.

**Theorem (Sum of fractions).** Let $F$ be a field, and let $a, b, c, d \in F$ with $b \neq 0$ and $d \neq 0$. Then
$$\frac{a}{b} + \frac{c}{d} = \frac{ad + bc}{bd}.$$

*Proof.* Since $b \neq 0$ and $d \neq 0$, also $bd \neq 0$, because a field has no zero divisors. By definition, $\frac{a}{b} = a b^{-1}$. Then
$$\frac{a}{b} + \frac{c}{d} = a b^{-1} + c d^{-1} = (a d + c b) \, b^{-1} d^{-1} = \frac{ad + bc}{bd},$$
where the middle step uses $d d^{-1} = 1$ and $b b^{-1} = 1$: indeed $a b^{-1} = a d \, d^{-1} b^{-1}$ and $c d^{-1} = c b \, b^{-1} d^{-1}$. The last step uses $(bd)^{-1} = b^{-1} d^{-1}$, which holds since $bd \cdot b^{-1} d^{-1} = 1$. $\square$

In Mathlib the division is total: $x / 0 = 0$. With this convention, the formula is false without the hypotheses. For $b = 0$ and $d = 1$, the left side is $0 + c = c$ and the right side is $\frac{a + 0}{0} = 0$. So `field_simp` needs a proof that each denominator is not zero.

The tactic `field_simp` rewrites the goal with lemmas of this kind: the sum, the difference, the product and the quotient of fractions, and the cancellation $\frac{a}{b} = c \iff a = cb$ for $b \neq 0$. It brings each side of an equation to one fraction and then cross-multiplies. The result is an equation with no division, which `ring` can usually close. For each lemma with a hypothesis $b \neq 0$, it calls its discharger.

**The discharger.** The discharger `Mathlib.Tactic.FieldSimp.discharge` tries, in order: a hypothesis of the form `b ≠ 0` in the context, `norm_num` for a numeral, `positivity` for a term whose form shows that it is positive, and a split of a product $b_1 b_2 \neq 0$ into $b_1 \neq 0$ and $b_2 \neq 0$. So `field_simp` can clear the denominator $x^2 + 1$ with no hypothesis: `positivity` proves $x^2 + 1 > 0$.

#### positivity

The tactic `positivity` works on a goal `0 < e`, `0 ≤ e` or `e ≠ 0`. It goes through the term `e` from its leaves to its root. At each node it computes one of three facts: positive, not negative, or not zero. It uses rules of the following kind.

**Theorem (Rules of signs).** Let $a, b$ be elements of an ordered field.

1. If $0 < a$ and $0 \leq b$, then $0 < a + b$. If $0 \leq a$ and $0 \leq b$, then $0 \leq a + b$.
2. If $0 < a$ and $0 < b$, then $0 < ab$ and $0 < a / b$.
3. For each $a$, $0 \leq a^2$. If $a \neq 0$, then $0 < a^2$.
4. For each $a$, $0 \leq |a|$.

*Proof.* (1) From $0 \leq b$ follows $a \leq a + b$, by adding $a$ to both sides. With $0 < a$ this gives $0 < a + b$. The second claim is the same with $\leq$.

(2) In an ordered field, the product of two positive elements is positive by an axiom of ordered rings. The inverse of a positive $b$ is positive: if $b^{-1} \leq 0$, then $1 = b \cdot b^{-1} \leq 0$, a contradiction. So $a / b = a \cdot b^{-1}$ is a product of two positive elements.

(3) If $a \geq 0$, then $a^2 = a \cdot a \geq 0$. If $a < 0$, then $-a > 0$ and $a^2 = (-a)(-a) > 0$. If $a \neq 0$, then one of $a > 0$ and $-a > 0$ holds, and $a^2 > 0$ in both cases.

(4) $|a|$ is $a$ or $-a$, and it is the one of the two that is not negative. $\square$

Each such rule is an extension of `positivity` for one function: for `+`, for `*`, for `/`, for the powers, for `|·|`, for `Real.exp`, for `Real.sqrt` and many more. A leaf that is a variable gets its sign from a hypothesis such as `hx : 0 < x`, or from a bound by a numeral such as `hx : 1 ≤ x`. It does not combine two hypotheses: from `y ≤ x` and `0 < y` it does not get `0 < x`. A numeral gets its sign by `norm_num`.

The method is syntactic: the result depends on the form of the term, not on its value. For this reason `positivity` fails on $0 \leq x^2 - 2x + 1$ for $x \in \mathbb{R}$, though the term is $(x - 1)^2$. At the root it sees a sum whose second summand $-2x$ has no sign. It has no way to see the square.

#### gcongr

**Theorem (Monotonicity of the operations).** Let $a, b, c, d$ be elements of an ordered field.

1. If $a \leq b$ and $c \leq d$, then $a + c \leq b + d$.
2. If $a \leq b$ and $0 \leq c$, then $ac \leq bc$.
3. If $0 \leq a \leq b$, then $a^n \leq b^n$ for each $n \in \mathbb{N}$.
4. If $0 < a \leq b$, then $\frac1b \leq \frac1a$.

*Proof.* (1) $a + c \leq b + c \leq b + d$, by adding $c$ and then $b$ to the two inequalities.

(2) $bc - ac = (b - a) c$ is a product of two elements that are not negative, so it is not negative.

(3) Induction on $n$. For $n = 0$ both sides are $1$. If $a^n \leq b^n$, then $a^{n+1} = a^n a \leq a^n b \leq b^n b = b^{n+1}$: the first step is (2) with $0 \leq a^n$ and $a \leq b$, and the second step is (2) with $0 \leq b$ and $a^n \leq b^n$.

(4) $\frac1a - \frac1b = \frac{b - a}{ab}$, and this is not negative by the rules of signs, since $b - a \geq 0$ and $ab > 0$. $\square$

The tactic `gcongr` uses lemmas of this form, the lemmas with the attribute `gcongr`. On a goal $L \leq R$ or $L < R$, it compares the two sides. If they have the same head function, for example both are sums, it finds a lemma for this function and this relation. The lemma reduces the goal to the relations between the arguments that differ. The arguments that are the same on the two sides need no goal. The tactic goes on into the new goals, until the two sides differ in a way that no lemma covers. The rest is the main goal, such as $a \leq b$.

A lemma can have side conditions, such as $0 \leq c$ in (2). The tactic tries to close each side condition with `positivity`. A main goal that is a hypothesis is closed with `assumption`. What is left is shown to the user.

::: mathlib
`Mathlib.Tactic.FieldSimp.discharge` · `Mathlib.Tactic.FieldSimp.Discharger`

The discharger of `field_simp`. It proves the side goals `b ≠ 0` of the lemmas of fractions, by assumption, by `norm_num`, by `positivity` and by the splitting of a product. A user can give another discharger with `field_simp (disch := tac)`.

<?decl Mathlib.Tactic.FieldSimp.discharge?>
:::

::: mathlib
`Mathlib.Meta.Positivity.core` · `Mathlib.Tactic.Positivity.Core`

The core of `positivity`. It runs the extensions on the term, from the leaves to the root, and it returns one of the facts positive, not negative or not zero, with a proof. An extension is a function with the attribute `positivity`, and each file that defines a new function can add one.

<?decl Mathlib.Meta.Positivity.core?>
:::

::: mathlib
`Mathlib.Tactic.GCongr.gcongrExt` · `Mathlib.Tactic.GCongr.Core`

The attribute that registers a lemma for `gcongr`. A lemma has the right form when its conclusion is a relation between two terms with the same head function, and its hypotheses are relations between the arguments that differ, plus side conditions. Thus `mul_le_mul_of_nonneg_right` is such a lemma.

<?decl Mathlib.Tactic.GCongr.gcongrExt?>
:::

::: mathlib
`mul_le_mul_of_nonneg_right` · `Mathlib.Algebra.Order.GroupWithZero.Defs`

This is the lemma that `gcongr` uses for a product on the right, rule (2) of the theorem. Its hypothesis on the sign of the factor is the side goal of `gcongr`.

<?decl mul_le_mul_of_nonneg_right?>
:::

### How to use it

Write `field_simp` with the facts `hx : x ≠ 0` in the context, and then `ring` if the goal is still open. The order "first `field_simp`, then `ring`" is the standard pattern for an identity of rational functions. Write `field_simp at h` to clear the denominators of a hypothesis.

Write `positivity` on a goal of sign. It is the fastest way to prove the side goals that other tactics leave: the `0 ≤ c` of `gcongr`, the `0 < ε / 2` of an estimate, the `x ^ 2 + 1 ≠ 0` of a division.

Write `gcongr` on an inequality whose two sides have the same form. If a side goal stays open, `gcongr` shows it as a new goal. To tell `gcongr` which parts vary, give a pattern with `?_` in the places that differ: `gcongr ?_ + ?_` on $x + 2 \leq y + 5$ makes the goals $x \leq y$ and $2 \leq 5$, and closes the first one by the hypothesis.

### What it cannot do

The tactic `field_simp` does not prove that a denominator is not zero when neither the context nor its discharger gives it. On `1 / x + 1 = (1 + x) / x` with no hypothesis about `x`, it leaves the goal open. On `1 / x * x = 1`, it changes the goal to `x / x = 1` and stops. The goal is false for $x = 0$ in Mathlib.

The tactic `positivity` does not prove the sign of a variable with no hypothesis. On `0 < x ^ 2` for `x : ℝ` with no hypothesis, it fails with the message "failed to prove strict positivity, but it would be possible to prove nonnegativity if desired". The goal is false for $x = 0$. With `hx : x ≠ 0` in the context, it succeeds. It also fails on a term whose sign comes from a cancellation, such as $x^2 - 2x + 1$, and on a term with a function whose sign is not fixed, such as $\log x + 1$ for $x > 0$. It fails on a goal that is not of the form `0 < e`, `0 ≤ e` or `e ≠ 0`: for `a < b`, write it as `0 < b - a` first.

The tactic `gcongr` needs the same form on the two sides. On `x * 2 ≤ 2 * y`, the factors are in a different order. The tactic matches the first factors with each other and the second factors with each other, and it leaves the two goals `x ≤ 2` and `2 ≤ y`, which do not follow from `x ≤ y`. Rewrite with `mul_comm` first. On `c * a + 1 ≤ b * c + 1` it also matches the wrong factors. On `a * c ≤ b * c` with no fact about the sign of `c`, the side goal `0 ≤ c` stays open.

The tactic `gcongr` chooses one lemma for each node, and a mixed relation can make the wrong choice. On `a + c < b + d` from `a ≤ b` and `c < d`, the tactic takes the lemma for `<` on both summands, closes `c < d`, and leaves `a < b`, which does not follow. Use the lemma `add_lt_add_of_le_of_lt` directly, or `linarith`.

### Examples

**Example (Clearing a denominator).** From $x \neq 0$, $\frac1x + 1 = \frac{1 + x}{x}$. The tactic `field_simp` brings both sides to the form with the denominator $x$, cross-multiplies, and closes the result.

<?lean MathlibHandbook/V34/C02/Examples.lean#field_simp?>

**Example (Two denominators).** From $x \neq 0$ and $y \neq 0$, $\frac1x + \frac1y = \frac{x + y}{xy}$. After `field_simp`, the goal is an equation of polynomials:

```lean
example (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) : 1 / x + 1 / y = (x + y) / (x * y) := by
  field_simp
  ring
```

```text
x y : ℝ
hx : x ≠ 0
hy : y ≠ 0
⊢ y + x = x + y
```

**Example (A telescoping term).** For $x \neq 0$ and $x + 1 \neq 0$, $\frac1x - \frac1{x+1} = \frac1{x(x+1)}$. This is the step of the sum $\sum \frac{1}{k(k+1)} = 1 - \frac{1}{n+1}$. After `field_simp`, the goal is `x + 1 - x = 1`, and `ring` closes it.

```lean
example (x : ℝ) (hx : x ≠ 0) (hx1 : x + 1 ≠ 0) :
    1 / x - 1 / (x + 1) = 1 / (x * (x + 1)) := by
  field_simp
  ring
```

**Example (Signs).** The term $x^2 + y^2 + 1$ is a sum of two squares and a positive numeral. By rule (1), the sum is positive. The term $\frac{x}{x + 1}$ with $x > 0$ is a quotient of two positive terms, by rule (2).

<?lean MathlibHandbook/V34/C02/Examples.lean#positivity?>

Other goals that `positivity` closes: `0 < 2 ^ n` for `n : ℕ`, `0 < Real.exp x + |x|`, `0 < ε / 2` from `0 < ε`, and `0 ≤ Real.sqrt x * y` from `0 ≤ y`.

**Example (Monotonicity).** From $a \leq b$ and $0 \leq c$, $ac + 3 \leq bc + 3$. The tactic sees two sums with the same second summand, and reduces the goal to $ac \leq bc$. Then it sees two products with the same second factor, and uses rule (2), with the side goal $0 \leq c$. The hypotheses close both goals. The second proof is $x^3 \leq y^3$ from $0 \leq x \leq y$, by rule (3).

<?lean MathlibHandbook/V34/C02/Examples.lean#gcongr?>

Without the hypothesis `hc`, the goal state after `gcongr` shows the side goal:

```text
case ha
a b c : ℝ
h : a ≤ b
⊢ 0 ≤ c
```

**Example (The three tactics together).** For $x > 0$, $\frac{x}{x + 1} < 1$. The proof is a chain (next section): $\frac{x}{x+1} < \frac{x+1}{x+1} = 1$. In the first step, `gcongr` reduces the goal to $x < x + 1$, and its side goal $0 < x + 1$ is closed by `positivity`; `linarith` proves $x < x + 1$. In the second step, `field_simp` proves $\frac{x + 1}{x + 1} = 1$, since its discharger proves $x + 1 \neq 0$.

```lean
example (x : ℝ) (hx : 0 < x) : x / (x + 1) < 1 := by
  calc x / (x + 1) < (x + 1) / (x + 1) := by gcongr; linarith
    _ = 1 := by field_simp
```

### Exercises

1. (L) Prove that `x ^ 4 + 2` is positive for each real `x` (`fourth_power_add_two_pos` in `Exercises.lean`).
2. (L) Prove `c * a + 1 ≤ c * b + 1` from `a ≤ b` and `0 ≤ c` (`mul_add_le_mul_add` in `Exercises.lean`).
3. (A) Tell which side goal `gcongr` makes on `x ^ 3 ≤ y ^ 3` from `x ≤ y`.
4. (A) Prove $\frac{a}{b} \cdot \frac{c}{d} = \frac{ac}{bd}$ in a field for $b, d \neq 0$. Tell whether the formula holds in Mathlib without the hypotheses.
5. (B) Give a goal `0 < e` that is true and that `positivity` cannot prove. Tell which step of the term has no extension.
6. (B) Tell why `field_simp` needs the hypothesis `x ≠ 0` and why Mathlib does not add it.
7. (B) Prove $0 \leq x^2 - 2x + 1$ for $x \in \mathbb{R}$ in two steps: first rewrite the term as a square, then use `positivity`.
8. (B) On `a + c < b + d` from `a ≤ b` and `c < d`, tell what `gcongr` leaves, and give a proof.
9. (C) Prove rule (4) of the theorem on monotonicity in the form $0 < a \leq b \Rightarrow \frac{c}{b} \leq \frac{c}{a}$ for $c \geq 0$. Tell which side goals `gcongr` makes on this goal.

### Reference

<?reference?>
