---
title: The absolute value and the positive part
kind: theory
modules:
  - Mathlib.Algebra.Order.Group.Unbundled.Abs
  - Mathlib.Algebra.Order.Group.Abs
  - Mathlib.Algebra.Order.Group.PosPart
explains:
  E3: [abs]
  E2: [abs_nonneg, abs_add_le, abs_sub_comm, abs_le, abs_eq_max_neg, abs_sub_abs_le_abs_sub, abs_abs_sub_abs_le_abs_sub, posPart_sub_negPart, posPart_add_negPart, posPart_def, negPart_def]
  E1: auto
families: []
requires: [V04.C01, V01.C04]
reads_with: ["MIL"]
lean:
  - MathlibHandbook/V04/C08/Examples.lean
  - MathlibHandbook/V04/C08/Exercises.lean
  - MathlibHandbook/V04/C08/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The absolute value and the positive part

### Overview

The absolute value of a real number is its distance from $0$. With it, the distance between $a$ and $b$ is $|a - b|$, and the triangle inequality $|a + b| \le |a| + |b|$ is the basis of each estimate in analysis. Neither the definition nor the inequality needs the real numbers. Each needs only an order that is a lattice and a group whose addition keeps the order, as in the previous section.

This section defines the absolute value as $|a| = a \sqcup (-a)$, which is $\max(a, -a)$ in a linear order. It proves the basic properties, the bound $|a| \le b \iff -b \le a \le b$, the triangle inequality and the reverse triangle inequality. It then splits each element into a positive part and a negative part, $a = a^+ - a^-$, and proves $|a| = a^+ + a^-$.

The proofs are in a linearly ordered additive group $G$ unless the text says otherwise. Some of them use only the lattice operations, and they hold in a lattice-ordered group such as $\mathbb{R}^2$ with the product order. The Mathlib boxes say which ones.

### Definitions

**Definition (Absolute value).** Let $G$ be an additive group with a lattice order. The *absolute value* of $a \in G$ is $|a| = a \sqcup (-a)$. If the order is linear, then $|a| = \max(a, -a)$.

**Definition (Positive part and negative part).** The *positive part* of $a$ is $a^+ = a \sqcup 0$, and the *negative part* of $a$ is $a^- = (-a) \sqcup 0$.

So for a real number, $a^+ = \max(a, 0)$ and $a^- = \max(-a, 0)$. The negative part is a nonnegative element: for $a = -4$ it is $4$, not $-4$.

**Definition (Distance).** The *distance* between $a$ and $b$ in $G$ is $|a - b|$.

::: mathlib
`abs` · `Mathlib.Algebra.Order.Group.Unbundled.Abs`

The definition is `abs a = a ⊔ -a`, for `[Lattice α] [AddGroup α]`, and the notation `|a|` stands for `abs a`. The notation must have no space after the first bar and no space before the second bar. The definition is the additive form of `mabs`, with the notation `|a|ₘ`. Since it uses `⊔` and not `max`, it applies to a lattice-ordered group, for instance to functions `ι → ℝ`, where `|f|` is the function `fun i ↦ |f i|`.

<?decl abs?>
:::

::: mathlib
`abs_eq_max_neg` · `Mathlib.Algebra.Order.Group.Unbundled.Abs`

In a linear order, `|a| = max a (-a)`. The lemma `abs_by_cases` states that a property of `a` and of `-a` is a property of `|a|`, and it is the formal form of a proof by the two cases below.

<?decl abs_eq_max_neg?>
:::

::: mathlib
`posPart_def` · `Mathlib.Algebra.Order.Group.PosPart`

The positive part has the notation `a⁺`, from the class `PosPart` of `Mathlib.Algebra.Notation`, and `posPart_def` states `a⁺ = a ⊔ 0`. The notation class lets the same symbol mean the positive part of a function or of a measure in other files. The lemmas `posPart_of_nonneg` and `posPart_of_nonpos` give the two cases.

<?decl posPart_def?>
:::

::: mathlib
`negPart_def` · `Mathlib.Algebra.Order.Group.PosPart`

The negative part has the notation `a⁻`, and `negPart_def` states `a⁻ = -a ⊔ 0`. The lemmas `negPart_of_nonneg` and `negPart_of_nonpos` give the two cases.

<?decl negPart_def?>
:::

### Theorems and proofs

The first theorem settles the value of $|a|$ in each case.

**Theorem (The two cases).** In $G$, if $0 \le a$ then $|a| = a$, and if $a \le 0$ then $|a| = -a$.

*Proof.* Suppose $0 \le a$. Negation reverses the order (previous section), so $-a \le 0 \le a$, and $\max(a, -a) = a$. Suppose $a \le 0$. Then $a \le 0 \le -a$, and $\max(a, -a) = -a$. $\square$

**Theorem (Basic properties).** In $G$, for all $a$:

1. $a \le |a|$ and $-a \le |a|$;
2. $|-a| = |a|$;
3. $0 \le |a|$;
4. $|a| = 0$ if and only if $a = 0$.

*Proof.* 1. The supremum $a \sqcup (-a)$ is an upper bound of $a$ and of $-a$.

2. $|-a| = (-a) \sqcup (-(-a)) = (-a) \sqcup a = a \sqcup (-a) = |a|$, since $\sqcup$ is commutative.

3. In a linear order, $0 \le a$ or $a \le 0$. In the first case $|a| = a \ge 0$. In the second case $|a| = -a \ge 0$.

4. If $a = 0$, then $|a| = 0 \sqcup 0 = 0$. Conversely, let $|a| = 0$. If $0 \le a$, then $a = |a| = 0$. If $a \le 0$, then $-a = |a| = 0$, so $a = 0$. $\square$

**Theorem (A bound on the absolute value).** In $G$, $|a| \le b$ if and only if $-b \le a$ and $a \le b$. Also $|a| < b$ if and only if $-b < a$ and $a < b$.

*Proof.* A supremum is at most $b$ exactly when each of its terms is at most $b$. So $|a| \le b$ if and only if $a \le b$ and $-a \le b$. Negation reverses the order, so $-a \le b$ is equivalent to $-b \le a$. This proves the first claim. For the second claim, the order is linear, so $\max(a, -a) < b$ if and only if $a < b$ and $-a < b$. The strict form of the rule on negation gives $-a < b \iff -b < a$. $\square$

The first half of the proof uses only the lattice, so $|a| \le b \iff a \le b \text{ and } -a \le b$ holds in each lattice-ordered group. The triangle inequality uses only this half.

**Theorem (Triangle inequality).** In $G$, $|a + b| \le |a| + |b|$.

*Proof.* By the basic properties, $a \le |a|$ and $b \le |b|$. Add the two inequalities: $a + b \le |a| + |b|$. Also $-a \le |a|$ and $-b \le |b|$, so $-a + (-b) \le |a| + |b|$. Since $G$ is commutative, $-(a + b) = -a + (-b)$. So $a + b$ and $-(a + b)$ are both at most $|a| + |b|$, and the theorem on a bound gives $|a + b| \le |a| + |b|$. $\square$

**Theorem (Distance).** In $G$, for all $a, b, c$:

1. $|a - b| = |b - a|$;
2. $|a - c| \le |a - b| + |b - c|$.

*Proof.* 1. $b - a = -(a - b)$, and $|-x| = |x|$ by the basic properties.

2. $a - c = (a - b) + (b - c)$. Apply the triangle inequality to the two terms. $\square$

Part 2 is the triangle inequality for the distance: the direct path from $a$ to $c$ is at most the path through $b$. With part 1 and part 4 of the basic properties, it makes $G$ a metric space when $G = \mathbb{R}$.

**Theorem (Reverse triangle inequality).** In $G$, for all $a, b$:

1. $|a| - |b| \le |a - b|$;
2. $\bigl||a| - |b|\bigr| \le |a - b|$.

*Proof.* 1. Write $a = (a - b) + b$. The triangle inequality gives $|a| \le |a - b| + |b|$. Subtract $|b|$ from both sides (previous section): $|a| - |b| \le |a - b|$.

2. Part 1 with $a$ and $b$ exchanged gives $|b| - |a| \le |b - a|$, and $|b - a| = |a - b|$. So $-(|a| - |b|) \le |a - b|$. With part 1, both $|a| - |b|$ and its negative are at most $|a - b|$. The theorem on a bound gives the claim. $\square$

The reverse inequality says that the map $a \mapsto |a|$ does not increase distances. In analysis this shows that $|x_n| \to |x|$ when $x_n \to x$.

**Theorem (Positive and negative parts).** In $G$, for all $a$:

1. $0 \le a^+$ and $0 \le a^-$;
2. $a = a^+ - a^-$;
3. $|a| = a^+ + a^-$;
4. $\min(a^+, a^-) = 0$.

*Proof.* Part 1 holds because $0 \le x \sqcup 0$ for each $x$. For the other parts, take the two cases.

Suppose $0 \le a$. Then $a^+ = a \sqcup 0 = a$. Also $-a \le 0$, so $a^- = (-a) \sqcup 0 = 0$. So $a^+ - a^- = a - 0 = a$, $a^+ + a^- = a = |a|$, and $\min(a, 0) = 0$.

Suppose $a \le 0$. Then $a^+ = 0$. Also $0 \le -a$, so $a^- = -a$. So $a^+ - a^- = 0 - (-a) = a$, $a^+ + a^- = -a = |a|$, and $\min(0, -a) = 0$.

In each case parts 2, 3 and 4 hold. $\square$

Parts 2 and 3 give $a^+ = \frac{1}{2}(|a| + a)$ and $a^- = \frac{1}{2}(|a| - a)$ in $\mathbb{R}$, where division by $2$ is available. Part 4 says that the two parts are *disjoint*: at most one of them is not zero. In a lattice-ordered group all four parts still hold, but the proof needs the distributive law of the lattice, because the two cases are not available.

::: mathlib
`abs_nonneg` · `Mathlib.Algebra.Order.Group.Unbundled.Abs`

The lemma `abs_nonneg a : 0 ≤ |a|` asks for `[Lattice α] [AddGroup α] [AddLeftMono α] [AddRightMono α]`, and no linear order. So it holds in a lattice-ordered group. Part 1 of the basic properties is `le_abs_self` and `neg_le_abs`, part 2 is `abs_neg`, and part 4 is `abs_eq_zero`, which needs a linear order. The theorem on the two cases is `abs_of_nonneg` and `abs_of_nonpos`.

<?decl abs_nonneg?>
:::

::: mathlib
`abs_le` · `Mathlib.Algebra.Order.Group.Abs`

The lemma states `|a| ≤ b ↔ -b ≤ a ∧ a ≤ b` in a linearly ordered group. The lattice form is `abs_le'`, as `|a| ≤ b ↔ a ≤ b ∧ -a ≤ b`, and the strict form is `abs_lt`. In a proof, `abs_le.mpr ⟨h₁, h₂⟩` proves a bound, and `(abs_le.mp h).1` gets the lower inequality. The lemma `abs_sub_lt_iff` is the form for a distance.

<?decl abs_le?>
:::

::: mathlib
`abs_add_le` · `Mathlib.Algebra.Order.Group.Unbundled.Abs`

This is the triangle inequality, for `[Lattice α] [AddCommGroup α] [AddLeftMono α]`. So it holds in each lattice-ordered commutative group, with the proof of the text. The equality case is `abs_add_eq_add_abs_iff`: `|a + b| = |a| + |b|` if and only if `a` and `b` have the same sign. The form for three points is `abs_sub_le`.

<?decl abs_add_le?>
:::

::: mathlib
`abs_sub_comm` · `Mathlib.Algebra.Order.Group.Unbundled.Abs`

The lemma `abs_sub_comm a b : |a - b| = |b - a|` needs no order axiom other than the lattice, and no commutativity of the group.

<?decl abs_sub_comm?>
:::

::: mathlib
`abs_sub_abs_le_abs_sub` · `Mathlib.Algebra.Order.Group.Abs`

This is part 1 of the reverse triangle inequality, as `|a| - |b| ≤ |a - b|`, in a linearly ordered group.

<?decl abs_sub_abs_le_abs_sub?>
:::

::: mathlib
`abs_abs_sub_abs_le_abs_sub` · `Mathlib.Algebra.Order.Group.Abs`

This is part 2 of the reverse triangle inequality, as `||a| - |b|| ≤ |a - b|`.

<?decl abs_abs_sub_abs_le_abs_sub?>
:::

::: mathlib
`posPart_sub_negPart` · `Mathlib.Algebra.Order.Group.PosPart`

The lemma states `a⁺ - a⁻ = a`, for `[Lattice α] [AddGroup α] [AddLeftMono α]`. It holds in each lattice-ordered group. The disjointness of part 4 is `posPart_inf_negPart_eq_zero : a⁺ ⊓ a⁻ = 0`.

<?decl posPart_sub_negPart?>
:::

::: mathlib
`posPart_add_negPart` · `Mathlib.Algebra.Order.Group.PosPart`

The lemma states `a⁺ + a⁻ = |a|`, for a lattice-ordered group with monotone translations on both sides.

<?decl posPart_add_negPart?>
:::

### Examples

**Example (Values).** In $\mathbb{Z}$, $|-3| = \max(-3, 3) = 3$ and $|5| = 5$. The distance between $2$ and $7$ is $|2 - 7| = |-5| = 5 = |7 - 2|$.

**Example (Basic facts in Lean).** For each real $x$, $0 \le |x|$ and $x \le |x|$.

<?lean MathlibHandbook/V04/C08/Examples.lean#abs?>

**Example (The triangle inequality).** Take $a = 3$ and $b = -5$. Then $|a + b| = |-2| = 2$ and $|a| + |b| = 8$, so the inequality is strict. Take $a = 3$ and $b = 5$. Then both sides are $8$. The inequality is an equality exactly when $a$ and $b$ have the same sign.

<?lean MathlibHandbook/V04/C08/Examples.lean#triangle?>

**Example (A bound as two inequalities).** The condition $|x - 2| \le 3$ on a real $x$ is, by the theorem on a bound, $-3 \le x - 2 \le 3$, that is, $-1 \le x \le 5$. So the set of solutions is the closed interval $[-1, 5]$ of Chapter 7, the interval of center $2$ and radius $3$.

<?lean MathlibHandbook/V04/C08/Examples.lean#abs_le?>

**Example (Distance is symmetric).** For reals $a$ and $b$, $|a - b| = |b - a|$.

<?lean MathlibHandbook/V04/C08/Examples.lean#dist?>

**Example (Positive and negative parts).** For $a = 6$: $a^+ = 6$, $a^- = 0$, $a^+ - a^- = 6$ and $a^+ + a^- = 6 = |a|$. For $a = -4$: $a^+ = 0$, $a^- = 4$, $a^+ - a^- = -4$ and $a^+ + a^- = 4 = |a|$. For the function $f(x) = \sin x$ on $\mathbb{R}$, with the pointwise order, $f^+$ is $\sin x$ where $\sin x \ge 0$ and $0$ elsewhere. This split $f = f^+ - f^-$ is the first step of the definition of the Lebesgue integral.

**Counterexample (The plane).** Give $\mathbb{R}^2$ the product order of the previous section. It is a lattice: $(x_1, y_1) \sqcup (x_2, y_2) = (\max(x_1, x_2), \max(y_1, y_2))$. So $|(1, -2)| = (1, -2) \sqcup (-1, 2) = (1, 2)$. This is neither $(1, -2)$ nor $(-1, 2)$, so the theorem on the two cases fails, because the order is not linear. The triangle inequality still holds, component by component. Also $(1, -2)^+ = (1, 0)$ and $(1, -2)^- = (0, 2)$, and these are disjoint: $(1, 0) \sqcap (0, 2) = (0, 0)$.

**Counterexample (The strict bound needs a linear order).** In $\mathbb{R}^2$ with the product order, take $a = (1, -1)$ and $b = (1, 1)$. Then $a < b$ and $-a = (-1, 1) < b$, while $|a| = (1, 1) = b$, so $|a| < b$ is false. The strict form of the theorem on a bound fails without the linear order.

### The library around it

The definitions and the lemmas that need only a lattice are in `Mathlib.Algebra.Order.Group.Unbundled.Abs`. The lemmas for a linearly ordered group with the class `IsOrderedAddMonoid` are in `Mathlib.Algebra.Order.Group.Abs`. The positive and negative parts are in `Mathlib.Algebra.Order.Group.PosPart`. The multiplicative lemmas have the same names with `mabs` in the place of `abs`, and they come from the additive ones through `to_additive`.

Other useful lemmas: `abs_le_abs` (from `a ≤ b` and `-a ≤ b` follows `|a| ≤ |b|`), `abs_abs`, `abs_pos` (`0 < |a| ↔ a ≠ 0`), `le_abs` (`a ≤ |b| ↔ a ≤ b ∨ a ≤ -b`) and `max_sub_min_eq_abs` (`max a b - min a b = |b - a|`). In an ordered ring, `abs_mul` states `|a * b| = |a| * |b|`. That lemma is not a statement about groups, and it is in `Mathlib.Algebra.Order.Ring.Abs`.

On `ℝ`, the distance of the metric space is `dist a b = |a - b|`, by `Real.dist_eq`, so the lemmas of this section prove the facts about real balls. The tactic `linarith` does not know the absolute value: give it `abs_le.mp h` or the two cases from `abs_by_cases`.

### Exercises

1. (A) Compute $|{-12}|$, $|4 - 9|$, $(-3)^+$ and $(-3)^-$ in $\mathbb{Z}$.
2. (A) In $G$, show that $|a| \le |b|$ when $0 \le a \le b$.
3. (A) Solve $|x + 1| < 4$ in $\mathbb{R}$, and write the answer as an interval.
4. (B) In $G$, show that $\max(a, b) - \min(a, b) = |b - a|$. *Hint:* take the cases $a \le b$ and $b \le a$.
5. (B) In $\mathbb{R}$, show that $\max(a, b) = \frac{1}{2}(a + b + |a - b|)$ and $\min(a, b) = \frac{1}{2}(a + b - |a - b|)$.
6. (B) In $G$, show that $|a + b| = |a| + |b|$ if $0 \le a$ and $0 \le b$, and give an example in $\mathbb{Z}$ where $|a + b| < |a| + |b|$.
7. (B) In $G$, show that $(a + b)^+ \le a^+ + b^+$. *Hint:* $a + b \le a^+ + b^+$ and $0 \le a^+ + b^+$.
8. (C) In $G$, show that $|a| \le b$ and $|c| \le d$ give $|a - c| \le b + d$, and that $|a - b| < \varepsilon$ and $|b - c| < \varepsilon$ give $|a - c| < \varepsilon + \varepsilon$.
9. (C) In the plane with the product order, show that $|a| \le b$ if and only if $-b \le a$ and $a \le b$, so the first claim of the theorem on a bound holds without a linear order. *Hint:* the first half of its proof uses only the lattice, and the rule on negation uses only the ordered group.
10. (L) Prove that $|-x| = |x|$ for each real $x$. The solution is `abs_neg_example`.
11. (L) Prove the triangle inequality for three points, $|a - c| \le |a - b| + |b - c|$, for reals. The solution is `abs_sub_le_example`.

### Notes and history

The notation $|x|$ is due to Weierstrass, around 1841, and the triangle inequality for real and complex numbers was standard in the analysis of the nineteenth century. The absolute value in a lattice-ordered group, with the decomposition $a = a^+ - a^-$, is in Birkhoff, *Lattice theory* (1940, 3rd edition 1967), and in the work of Riesz on vector lattices in the 1930s, where the positive and negative parts of a function or a measure come first. The Jordan decomposition of a measure of bounded variation is the same split.

In Mathlib, the first lemmas on the absolute value come from the core library of Lean 3, by Jeremy Avigad, Leonardo de Moura, Mario Carneiro and Johannes Hölzl. The file on positive and negative parts is by Christopher Hoskin and Yaël Dillies.

### Reference

<?reference?>
