---
title: choose, lift and filter_upwards
kind: tactic
modules: [Mathlib.Tactic.Lift, Mathlib.Tactic.Choose]
explains:
  E2: [CanLift, Mathlib.Tactic.Lift.main, Mathlib.Tactic.Choose.choose1]
  E1: [Filter.mp_mem, Filter.Eventually.mono]
families: []
requires: [V00]
reads_with: ["MIL"]
lean: [MathlibHandbook/V34/C05/Examples.lean, MathlibHandbook/V34/C05/Solutions.lean]
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## choose, lift and filter_upwards

### Overview

Three steps of analysis have their own tactics. The first step is "for each $\varepsilon > 0$ choose a $\delta(\varepsilon)$": from a hypothesis $\forall x,\ \exists y,\ P(x, y)$, it makes a function $f$ with $P(x, f(x))$ for each $x$. The tactic `choose` makes this step. The second step is "since $n \geq 0$, $n$ is a natural number": it moves a variable to a smaller type, with the hypothesis that makes this possible. The tactic `lift` makes this step. The third step is "for $n$ large, both facts hold, so the claim holds": it combines facts that hold eventually. The tactic `filter_upwards` makes this step.

The section proves the theorem behind each step: the axiom of choice in the form of Lean, the property of a lift, and the closure of a filter under intersection and under supersets.

### What it does

#### choose

**Theorem (Choice).** Let $\alpha$ and $\beta$ be types, and let $P$ be a relation on $\alpha \times \beta$. If $\forall x : \alpha,\ \exists y : \beta,\ P(x, y)$, then there is a function $f : \alpha \to \beta$ with $\forall x,\ P(x, f(x))$.

*Proof.* Lean has the axiom `Classical.choice`: from a proof that a type is not empty, it gives an element of the type. From it, the library defines `Classical.choose h : β` for `h : ∃ y, P x y`, and proves `Classical.choose_spec h : P x (Classical.choose h)`. Let $h$ be the hypothesis. Define $f(x) = $ `Classical.choose (h x)`. Then `Classical.choose_spec (h x)` is a proof of $P(x, f(x))$, for each $x$. $\square$

The tactic `choose f hf using h` makes this proof. It adds `f : α → β` and `hf : ∀ x, P x (f x)` to the context. It accepts several variables and several existential quantifiers: for $\forall \varepsilon,\ \varepsilon > 0 \to \exists \delta,\ \delta > 0 \wedge Q(\varepsilon, \delta)$, the call `choose δ hδpos hδ using h` gives

```text
δ : (ε : ℝ) → ε > 0 → ℝ
hδpos : ∀ (ε : ℝ) (h : ε > 0), δ ε h > 0
hδ : ∀ (ε : ℝ) (h : ε > 0), Q ε (δ ε h)
```

The function $\delta$ takes the proof of $\varepsilon > 0$ as an argument, since the hypothesis gives a $\delta$ only for a positive $\varepsilon$.

::: mathlib
`Mathlib.Tactic.Choose.choose1` · `Mathlib.Tactic.Choose`

One step of the tactic `choose`: it takes one existential quantifier, or one conjunction, from the hypothesis, under the universal quantifiers, and it defines the function with `Classical.choose`. The tactic calls it once for each name in the list.

<?decl Mathlib.Tactic.Choose.choose1?>
:::

#### lift

**Definition (Lift).** Let $\beta$ be a type, $\alpha$ a type with a map $c : \alpha \to \beta$, and $p$ a predicate on $\beta$. A lift of $\beta$ to $\alpha$ under $p$ is the fact: for each $y : \beta$ with $p(y)$, there is $x : \alpha$ with $c(x) = y$. In the library this is an instance of the class `CanLift β α c p`.

Examples: `CanLift ℤ ℕ (↑) (0 ≤ ·)`, since each integer that is not negative is the cast of a natural number. `CanLift ℝ NNReal (↑) (0 ≤ ·)`, since each real number that is not negative is the cast of an element of `NNReal`.

**Theorem (Property of a lift).** Let $P$ be a predicate on $\beta$, and assume a lift of $\beta$ to $\alpha$ under $p$. If $p(y)$ and $\forall x : \alpha,\ P(c(x))$, then $P(y)$.

*Proof.* By the lift, there is $x$ with $c(x) = y$. By the hypothesis, $P(c(x))$. Rewrite with $c(x) = y$: this gives $P(y)$. $\square$

The tactic `lift n to ℕ using h` makes this proof on the goal. It finds the instance of `CanLift`, it takes the $x$ from `h : 0 ≤ n`, and it replaces `n` by `↑n` everywhere, with the new `n : ℕ`. The hypothesis `h` is gone, since it is now true by the type.

::: mathlib
`CanLift` · `Mathlib.Tactic.Lift`

The class of the lifts. It has the field `prf : ∀ y, p y → ∃ x, c x = y`. An instance tells `lift` the map $c$ and the condition $p$.

<?decl CanLift?>
:::

::: mathlib
`Mathlib.Tactic.Lift.main` · `Mathlib.Tactic.Lift`

The implementation of `lift`. It finds the instance, uses `prf`, and substitutes the variable in the goal and in the context. With `lift n to ℕ using h with k hk`, it keeps the equation `hk : ↑k = n` and the old variable.

<?decl Mathlib.Tactic.Lift.main?>
:::

#### filter_upwards

**Definition (Filter).** A filter $F$ on a type $\alpha$ is a set of subsets of $\alpha$ with three properties: $\alpha \in F$; if $s \in F$ and $s \subseteq t$, then $t \in F$; if $s \in F$ and $t \in F$, then $s \cap t \in F$. A property $P$ holds eventually for $F$, written `∀ᶠ x in F, P x`, when the set $\{x : P(x)\}$ is in $F$.

The filter `atTop` on `ℕ` consists of the sets that contain all $n \geq N$ for some $N$. So "eventually for `atTop`" is "for $n$ large".

**Theorem (Combination of eventual facts).** Let $F$ be a filter. If $P_1, \ldots, P_k$ hold eventually for $F$, and $\forall x,\ P_1(x) \to \cdots \to P_k(x) \to Q(x)$, then $Q$ holds eventually for $F$.

*Proof.* Let $s_i = \{x : P_i(x)\}$. Each $s_i$ is in $F$. By the third property and an induction on $k$, $s = s_1 \cap \cdots \cap s_k$ is in $F$. For $k = 0$, use the first property: $s = \alpha$. By the hypothesis, each $x \in s$ satisfies $Q(x)$, so $s \subseteq \{x : Q(x)\}$. By the second property, $\{x : Q(x)\} \in F$. $\square$

The tactic `filter_upwards [h₁, …, hₖ] with x hx₁ … hxₖ` makes this proof. It turns the goal `∀ᶠ x in F, Q x` into the goal `Q x` with the hypotheses `hxᵢ : Pᵢ x`. With no `with`, the goal is the implication `∀ x, P₁ x → ⋯ → Q x`.

::: mathlib
`Filter.mp_mem` · `Mathlib.Order.Filter.Defs`

The step of the proof for two sets: if $s \in F$ and $\{x : x \in s \to x \in t\} \in F$, then $t \in F$. The tactic `filter_upwards` uses it once for each fact of the list.

<?decl Filter.mp_mem?>
:::

::: mathlib
`Filter.Eventually.mono` · `Mathlib.Order.Filter.Basic`

The case $k = 1$ of the theorem: if $P$ holds eventually and $P \to Q$ for each $x$, then $Q$ holds eventually. A term `hf.mono fun n h => …` is the same step as `filter_upwards [hf] with n h`.

<?decl Filter.Eventually.mono?>
:::

### How to use it

Write `choose f hf using h` on a hypothesis `h : ∀ x, ∃ y, P x y`, and `choose f g hf using h` for two existential quantifiers in a chain. To make the function for an existence statement in the goal, write `choose` on the hypothesis first, and then use the function as the witness.

Write `lift x to ℕ using hx` when the proof is easier over `ℕ`, or `lift x to NNReal using hx` for a real number that is not negative. Use the variant `with k hk` to keep the old name.

Write `filter_upwards [h₁, h₂] with n hn₁ hn₂` on a goal `∀ᶠ n in F, Q n`. Add facts of the library to the list: `eventually_ge_atTop 1` gives the fact $n \geq 1$ for large $n$.

### What it cannot do

#### choose on a hypothesis of the wrong form

The tactic `choose` needs a hypothesis of the form `∀ x, ∃ y, P x y` or `∀ x, P x ∧ Q x`. On `h : ∃ y, ∀ x, P x y`, the first quantifier is `∃`, and the choice is not needed: use `obtain ⟨y, hy⟩ := h`. On a hypothesis with no `∃` and no `∧`, it fails:

```text
choose: expected a term of the shape `∀ xs, ∃ a, p xs a` or `∀ xs, p xs ∧ q xs`
```

#### lift with no instance or no proof

The tactic `lift` needs an instance of `CanLift` and a proof of the condition. On a variable of `ℝ` with the goal to lift to `ℕ`, there is no instance, since a real number that is not negative is not always a natural number. If the proof of the condition is not in the context, `lift n to ℕ` with no `using` leaves the condition as a new goal.

#### filter_upwards on a goal that is not eventual

The goal must be `∀ᶠ x in F, Q x` or `s ∈ F`. On `0 ≤ f 5`, it fails with a message that it "could not unify" the goal with `?s ∈ ?f`. A fact that holds eventually says nothing about one value such as $f(5)$.

#### filter_upwards with a missing fact

The tactic combines only the facts of the list. With `filter_upwards [hf]` on the goal `∀ᶠ n in atTop, f n ≤ 2` and `hf : ∀ᶠ n in atTop, f n ≤ 1`, the goal becomes

```text
⊢ ∀ (a : ℕ), f a ≤ 1 → f a ≤ 2
```

Here the goal closes with `intro a h; linarith`. If the goal needs a second fact, such as $n \geq 1$, add it to the list: the goal shows the facts that the tactic has, and nothing more.

### Examples

**Example (A function from an existence statement).** For each $n$ there is $m > n$, so there is $f$ with $n < f(n)$ for each $n$.

<?lean MathlibHandbook/V34/C05/Examples.lean#choose?>

**Example (A function of ε).** From the definition of continuity at a point in the form $\forall \varepsilon > 0,\ \exists \delta > 0,\ \forall x,\ |x - a| < \delta \to |f(x) - f(a)| < \varepsilon$, the step `choose δ hδpos hδ using h` gives a function $\delta$ of $\varepsilon$ and of the proof of $\varepsilon > 0$, with its two properties. A proof that needs a sequence $\delta(1/n)$ starts with this step.

**Example (lift to ℕ).** A statement that holds for each natural number holds for each integer that is not negative.

<?lean MathlibHandbook/V34/C05/Examples.lean#lift?>

**Example (lift to NNReal).** For $x \geq 0$ in `ℝ`, the step `lift x to NNReal using hx` replaces `x` by the cast of a new `x : NNReal`. Then the lemmas of `NNReal`, where no hypothesis of sign is needed, apply.

```lean
example (x : ℝ) (hx : 0 ≤ x) : 0 ≤ x ^ 3 := by
  lift x to NNReal using hx
  positivity
```

**Example (Two eventual facts).** If $f(n) \geq 0$ and $g(n) \geq 0$ for $n$ large, then $f(n) + g(n) \geq 0$ for $n$ large.

<?lean MathlibHandbook/V34/C05/Examples.lean#filter_upwards?>

**Example (A fact of the library in the list).** If $f(n) \leq 1$ for $n$ large, then $f(n) \leq n$ for $n$ large. The second fact, $n \geq 1$ for large $n$, comes from the library.

```lean
open Filter in
example (f : ℕ → ℝ) (hf : ∀ᶠ n in atTop, f n ≤ 1) : ∀ᶠ n in atTop, f n ≤ n := by
  filter_upwards [hf, eventually_ge_atTop 1] with n h1 h2
  have : (1 : ℝ) ≤ n := by exact_mod_cast h2
  linarith
```

### Exercises

1. (L) Make a function `f` with `2 * n ≤ f n` for each `n` (`exists_bound_function` in `Exercises.lean`).
2. (L) Prove that `f n + g n ≤ 3` holds eventually from `f n ≤ 1` and `g n ≤ 2` eventually (`eventually_le_add` in `Exercises.lean`).
3. (A) Write the context after `choose g hg using h` for `h : ∀ x : ℝ, ∃ y, y ^ 2 = x ^ 2 + 1`.
4. (A) Prove the theorem of choice in Lean with `Classical.choose` and `Classical.choose_spec`, with no tactic `choose`.
5. (A) Tell why `filter_upwards` fails on the goal `0 ≤ f 5`.
6. (B) Prove the theorem of the combination of eventual facts for $k = 2$ from the three properties of a filter.
7. (B) Prove that each $n : ℤ$ with $0 \leq n$ satisfies $0 \leq n(n + 1)$, with `lift` and then a tactic of Chapter 2.
8. (C) Show that `atTop` on `ℕ` is a filter: check the three properties of the definition.

### Reference

<?reference?>
