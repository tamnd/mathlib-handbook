---
title: fun_prop, continuity and grind
kind: tactic
modules: [Mathlib.Tactic.FunProp.Core]
explains:
  E2: [Mathlib.Meta.FunProp.funProp]
  E1: [Continuous.add, Continuous.div₀]
families: []
requires: [V00]
reads_with: ["MIL"]
lean: [MathlibHandbook/V34/C04/Examples.lean, MathlibHandbook/V34/C04/Solutions.lean]
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## fun_prop, continuity and grind

### Overview

A written proof says "the function $x \mapsto e^{\sin x} \cdot x$ is continuous, as a product and a composition of continuous functions". The tactic `fun_prop` makes this step. It proves a property of a function, such as `Continuous`, `Differentiable ℝ` or `Measurable`, from the structure of the function: it takes the function apart into sums, products, compositions and constants, and it uses one lemma for each part. The tactic `continuity` proves the goals of continuity with a rule set of `aesop`, by a search.

The tactic `grind` comes from the core of Lean. It keeps the facts of the context and the negation of the goal in one store. It finds the consequences by congruence closure, it splits on `∨` and on `if`, and it has procedures for linear arithmetic and for commutative rings. It proves goals that mix equalities of functions, case splits and arithmetic.

The section proves the theorem that the decomposition of `fun_prop` is correct, and the theorem of soundness of congruence closure. With them, the reader can predict the side conditions of `fun_prop` and the goals that `grind` closes.

### What it does

#### The decomposition of fun_prop

**Definition (Function property).** A function property is a predicate $P$ on functions $X \to Y$ between spaces of some class, such as `Continuous`. A composition rule for $P$ is a theorem: if $P(f)$ and $P(g)$, then $P(g \circ f)$. A lemma of `fun_prop` for a function $h$ of two arguments has the form: if $P(f)$ and $P(g)$, then $P(x \mapsto h(f(x), g(x)))$.

The tactic `fun_prop` reads the body of `fun x => e` from the outside. If `e` does not contain `x`, it uses the rule for a constant. If `e` is `x`, it uses the rule for the identity. If `e` is `h a b` for a function `h` with a lemma of `fun_prop`, it uses the lemma, and then it proves the property of `fun x => a` and of `fun x => b`. If `e` is `g a` with a lemma for `g`, it uses the composition rule. Each step reduces the size of the term, so the process ends.

**Theorem (Continuity of a sum).** Let $X$ be a topological space, and let $f, g : X \to \mathbb{R}$ be continuous. Then $x \mapsto f(x) + g(x)$ is continuous.

*Proof.* The map $p : X \to \mathbb{R}^2$, $p(x) = (f(x), g(x))$, is continuous, by the universal property of the product topology: a map into a product is continuous if and only if each component is continuous. The addition $a : \mathbb{R}^2 \to \mathbb{R}$, $a(u, v) = u + v$, is continuous: for $\varepsilon > 0$, if $|u - u_0| < \varepsilon/2$ and $|v - v_0| < \varepsilon/2$, then $|(u + v) - (u_0 + v_0)| \leq |u - u_0| + |v - v_0| < \varepsilon$. The function of the theorem is $a \circ p$, a composition of continuous maps, so it is continuous. $\square$

The same proof, with the multiplication in place of the addition, gives the continuity of a product. For a quotient, the map $(u, v) \mapsto u / v$ is continuous only at the points with $v \neq 0$. So the lemma for the quotient has a side condition.

**Theorem (Continuity of a quotient).** Let $f, g : X \to \mathbb{R}$ be continuous, with $g(x) \neq 0$ for each $x$. Then $x \mapsto f(x) / g(x)$ is continuous.

*Proof.* The map $p(x) = (f(x), g(x))$ is continuous, and its values are in the open set $U = \{(u, v) : v \neq 0\}$. On $U$, the quotient $q(u, v) = u / v$ is continuous: it is the product of $u$ and $1/v$, and $v \mapsto 1/v$ is continuous at each $v_0 \neq 0$, since for $|v - v_0| < |v_0|/2$ one has $|v| > |v_0|/2$ and $\left|\frac1v - \frac1{v_0}\right| = \frac{|v - v_0|}{|v|\,|v_0|} < \frac{2|v - v_0|}{|v_0|^2}$. So the composition $q \circ p$ is continuous. $\square$

In Lean, the side condition becomes a hypothesis of the lemma. The tactic `fun_prop` passes this hypothesis to a discharger. The default discharger proves only very simple facts. A failure of the discharger gives the message "Failed to prove necessary assumption", with the name of the lemma.

::: mathlib
`Mathlib.Meta.FunProp.funProp` · `Mathlib.Tactic.FunProp.Core`

The main loop of the tactic. It reads the function, finds the lemmas with the attribute `fun_prop` for its head symbol, and calls itself on the parts. It also handles the functions of several variables, by the rules for the projections and for the pairs. The option `disch` gives the tactic for the side conditions: `fun_prop (disch := positivity)`.

<?decl Mathlib.Meta.FunProp.funProp?>
:::

::: mathlib
`Continuous.add` · `Mathlib.Topology.Algebra.Monoid.Defs`

The theorem of the continuity of a sum, for a topological space with a continuous addition. It has the attribute `fun_prop` and `continuity`, so both tactics use it.

<?decl Continuous.add?>
:::

::: mathlib
`Continuous.div₀` · `Mathlib.Topology.Algebra.GroupWithZero`

The theorem of the continuity of a quotient, with the hypothesis `∀ x, g x ≠ 0`. This hypothesis is the side condition that `fun_prop` passes to its discharger.

<?decl Continuous.div₀?>
:::

#### Congruence closure in grind

**Definition (Congruence closure).** Let $E$ be a set of equations between terms. The congruence closure of $E$ is the smallest equivalence relation $\sim$ on the terms that contains $E$ and satisfies the rule of congruence: if $a_1 \sim b_1, \ldots, a_k \sim b_k$, then $f(a_1, \ldots, a_k) \sim f(b_1, \ldots, b_k)$ for each function symbol $f$.

**Theorem (Soundness of congruence closure).** If $a \sim b$ in the congruence closure of $E$, then $a = b$ follows from the equations of $E$.

*Proof.* Let $\approx$ be the relation "$a = b$ follows from $E$". It contains $E$. It is reflexive, symmetric and transitive, by the rules of equality. It satisfies the rule of congruence: if $a_i = b_i$ follows from $E$ for each $i$, then $f(a_1, \ldots, a_k) = f(b_1, \ldots, b_k)$ follows by $k$ rewrites. So $\approx$ is an equivalence relation that contains $E$ and is closed under congruence. The closure $\sim$ is the smallest such relation, so $\sim$ is contained in $\approx$. $\square$

The tactic `grind` computes the congruence closure on the terms that occur in the facts, with a union-find structure. A hypothesis with a quantifier, such as $\forall x,\ f(f(x)) = x$, is used by instantiation: `grind` chooses the terms $x$ from patterns, that is, it adds the instance $f(f(t)) = t$ for each term $f(f(t))$ in the store. When two terms that must differ, such as the two sides of the negated goal, are in one class, the store is contradictory, and the goal is proved.

On top of this, `grind` splits on `∨`, on `if` and on the constructors, it runs a procedure for linear arithmetic over ordered fields and over `ℤ`, and it runs a procedure for commutative rings by normal forms (Chapter 2).

### How to use it

Write `fun_prop` on a goal `Continuous f`, `Differentiable ℝ f`, `ContinuousOn f s` or `Measurable f`, when `f` is built from functions with a lemma of `fun_prop`. When a lemma has a side condition, give a discharger: `fun_prop (disch := intro x; positivity)` for a condition `∀ x, g x ≠ 0` with a positive `g`.

Write `continuity` on a goal `Continuous f` when a needed lemma has the attribute `continuity` but not the attribute `fun_prop`. It is slower, because it is a search.

Write `grind` on a goal that needs equalities and case splits together, or on an identity of a commutative ring after a substitution, or on a small fact of linear arithmetic. Add a lemma to the call with `grind [h]`.

### What it cannot do

#### fun_prop and a side condition

The default discharger does not prove positivity. On the goal `Continuous (fun x : ℝ => 1 / (x ^ 2 + 1))`, `fun_prop` fails:

```text
Failed to prove necessary assumption `∀ (x : ℝ), x ^ 2 + 1 ≠ 0` when applying theorem `Continuous.div₀`.
```

The message names the side condition. The fix is a discharger: `fun_prop (disch := intro x; positivity)`.

#### fun_prop and a false goal

On `Continuous (fun x : ℝ => 1 / x)` the tactic fails with the side condition `∀ x, x ≠ 0`, and this condition is false at $x = 0$. The goal is false too, in Mathlib, where $1 / 0 = 0$: the function jumps at $0$. The true statement is the continuity on a set that does not contain $0$: `ContinuousOn (fun x : ℝ => 1 / x) (Set.Ioi 0)`, with `fun_prop (disch := intro x hx; exact ne_of_gt hx)`. The tactic `continuity` also fails on the false goal, and it shows the goal that remains after the search of `aesop`: `Continuous fun x => x⁻¹`.

#### grind and induction

The tactic `grind` does not do induction. On `2 ∣ n * (n + 1)` over `ℕ`, it fails with the message "`grind` has failed". The proof needs a case split on the parity of $n$ (Chapter 5), which is not a split on a fact of the context.

#### grind and signs

The procedure for linear arithmetic does not know the sign of a square. On `0 ≤ x ^ 2` for `x : ℝ`, `grind` fails. Use `positivity`, or `nlinarith`.

### Examples

**Example (fun_prop on a sum).** For `fun x => x ^ 2 + 3 * x`, the tactic uses `Continuous.add`, then the rule for a power of a continuous function, and the rule for a product of a constant and the identity.

<?lean MathlibHandbook/V34/C04/Examples.lean#fun_prop?>

**Example (Three properties).** The function $x \mapsto e^{\sin x} \cdot x$ is continuous, differentiable and measurable. One tactic proves the three goals, with three different sets of lemmas.

```lean
example : Continuous (fun x : ℝ => Real.exp (Real.sin x) * x) := by fun_prop

example : Differentiable ℝ (fun x : ℝ => Real.exp (Real.sin x) * x) := by fun_prop

example : Measurable (fun x : ℝ => Real.exp (Real.sin x) * x) := by fun_prop
```

**Example (A discharger).** The function $x \mapsto \frac{1}{x^2 + 1}$ is continuous, since the denominator is positive.

```lean
example : Continuous (fun x : ℝ => 1 / (x ^ 2 + 1)) := by
  fun_prop (disch := intro x; positivity)

example : ContinuousOn (fun x : ℝ => 1 / x) (Set.Ioi 0) := by
  fun_prop (disch := intro x hx; exact ne_of_gt hx)
```

In the second example, the side condition is `∀ x ∈ Set.Ioi 0, x ≠ 0`, and `hx : x ∈ Set.Ioi 0` unfolds to `0 < x`.

**Example (continuity).** The same goal as the first example, with the search of `aesop`.

<?lean MathlibHandbook/V34/C04/Examples.lean#continuity?>

**Example (grind).** In the first goal, from $f(f(x)) = x$ for each $x$, the term $f(f(f(a)))$ is $f$ applied to $f(f(a))$, and the instance $f(f(a)) = a$ gives $f(f(f(a))) = f(a)$ by congruence. The second goal is an identity of rings after the substitution $x = y + 1$. The third goal is linear arithmetic over `ℕ`.

<?lean MathlibHandbook/V34/C04/Examples.lean#grind?>

**Example (grind with a case split).** From $(x - 2)(x - 3) = 0$ over `ℝ`, the tactic gets $x - 2 = 0$ or $x - 3 = 0$ from the lemma `mul_eq_zero` in the call, splits, and solves each case by linear arithmetic.

```lean
example (x : ℝ) (h : (x - 2) * (x - 3) = 0) : x = 2 ∨ x = 3 := by
  grind [mul_eq_zero]
```

### Exercises

1. (L) Prove that `fun x => x ^ 3 - 2 * x + 1` is continuous on `ℝ` (`continuous_cubic` in `Exercises.lean`).
2. (L) Prove that an involution of `ℕ` is injective (`involution_injective` in `Exercises.lean`).
3. (A) Write the lemmas that `fun_prop` uses for `Continuous (fun x : ℝ => x ^ 3 - 2 * x + 1)`, in the order of the decomposition.
4. (A) Tell why `fun_prop` fails on `Continuous (fun x : ℝ => 1 / x)`, and prove that the goal is false: find a sequence $x_n \to 0$ with $1 / x_n \not\to 1 / 0$.
5. (B) Prove `Continuous (fun x : ℝ => x / (x ^ 2 + 1))` with `fun_prop` and a discharger.
6. (B) For the proof of Exercise 2 by hand: from $f(f(x)) = x$ and $f(a) = f(b)$, apply $f$ to both sides. Name the step of congruence closure that this is.
7. (B) Prove `2 ∣ n * (n + 1)` for `n : ℕ` with `Nat.even_or_odd` and a case split, since `grind` alone fails.
8. (C) Prove the continuity of a product $x \mapsto f(x) g(x)$ by hand, from the continuity of $f$ and $g$, in the style of the proof of the sum.

### Reference

<?reference?>
