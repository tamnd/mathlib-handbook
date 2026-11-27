---
title: intro, exact, apply and refine
kind: tactic
modules: []
explains:
  E1: [le_trans, exists_between]
families: []
requires: [V00]
reads_with: ["MIL"]
lean: [MathlibHandbook/V34/C05/Examples.lean, MathlibHandbook/V34/C05/Solutions.lean]
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## intro, exact, apply and refine

### Overview

The basic tactics of Lean are the words of a written proof. "Let $\varepsilon > 0$" is `intro ε hε`. "This is the hypothesis $h$" is `exact h`. "By the transitivity, it is sufficient to show $a \leq b$ and $b \leq c$" is `apply le_trans`. "Take $\delta = \varepsilon / 2$" is `use ε / 2`. "First, $p$. Second, $q$" is `constructor`. "Note that $f(3) = 6$" is `have h : f 3 = 6`. The tactic `refine` gives a term with holes, and each hole becomes a goal.

The section explains the goal state, the meaning of a proof term, and the rule of each tactic as a step on the goal state. It also explains the common errors: a type mismatch, a goal with a metavariable, a variable of the wrong type, and a witness that makes the goal false.

### What it does

#### The goal state

**Definition (Goal).** A goal is a context, a list of variables and hypotheses `x : α`, `h : P`, and a target `⊢ Q`. A proof of the goal is a term of type `Q` in this context. A goal state is a list of goals. The proof is complete when the list is empty.

In Lean, a proof of a proposition is a term of the type of this proposition. A proof of $P \to Q$ is a function that maps each proof of $P$ to a proof of $Q$. A proof of $\forall x : \alpha,\ P(x)$ is a function that maps each $x$ to a proof of $P(x)$. A proof of $P \wedge Q$ is a pair. A proof of $\exists x,\ P(x)$ is a pair of a witness and a proof. Each tactic builds a part of the term, and it leaves holes for the parts that it does not build. Each hole is a new goal.

**Theorem (Rule of intro).** Let $\Gamma$ be a context. If there is a proof of $Q$ in the context $\Gamma, h : P$, then there is a proof of $P \to Q$ in the context $\Gamma$. If there is a proof of $Q(x)$ in the context $\Gamma, x : \alpha$, with $x$ not in $\Gamma$, then there is a proof of $\forall x : \alpha,\ Q(x)$ in $\Gamma$.

*Proof.* Let $t$ be the proof of $Q$ in the context $\Gamma, h : P$. The function $\lambda h.\ t$ maps each proof $p$ of $P$ to $t[h := p]$, which is a proof of $Q$ in $\Gamma$. So $\lambda h.\ t$ has the type $P \to Q$. The second claim has the same proof with $\lambda x.\ t$. The condition that $x$ is not in $\Gamma$ makes sure that no hypothesis of $\Gamma$ says something about this $x$. $\square$

So `intro h` turns the goal `Γ ⊢ P → Q` into `Γ, h : P ⊢ Q`, and `intro x` turns `Γ ⊢ ∀ x, Q x` into `Γ, x : α ⊢ Q x`. The notation `∀ ε > 0, P ε` is `∀ ε, ε > 0 → P ε`, so `intro ε hε` makes two steps. The step `intro` also unfolds a definition to find the binder: on `s ⊆ t` it introduces an element.

#### exact, apply and refine

The tactic `exact e` closes the goal with the term `e`, if the type of `e` is the target, up to the unfolding of definitions. The tactic `apply e` uses the term `e : ∀ x, A₁ → ⋯ → Aₙ → B`: it unifies `B` with the target, and it leaves one goal for each `Aᵢ` and for each variable `x` that the unification does not fill (Chapter 4, soundness of `apply`). The tactic `refine e` takes a term with holes `?_`: the holes become the new goals, and all other parts must be complete.

**Definition (Metavariable).** A metavariable is a hole in a term, with a type and a context. It is written `?b` or `?_` in the goal state. A metavariable named `?b` that occurs in a target can be filled later by the unification of another goal.

The step `apply le_trans` on the goal `a ≤ c` is the example. The lemma is `le_trans : a ≤ b → b ≤ c → a ≤ c`, with `b` free. The unification fills `a` and `c` from the target, but not `b`. The goal state after the step has three goals: `a ≤ ?b`, `?b ≤ c`, and the goal `ℝ` for the value of `?b`. The step `exact h1` with `h1 : a ≤ b` on the first goal fills `?b := b`, and the other two goals change at the same time.

#### constructor, use and have

The tactic `constructor` applies the first constructor of the inductive type of the target that unifies with it. On `p ∧ q` it applies `And.intro` and leaves the goals `p` and `q`, with the names `left` and `right`. On `p ↔ q` it leaves `p → q` and `q → p`. The tactic `use t` on a target `∃ x, P x` gives the witness `t`, leaves the goal `P t`, and tries to close it with `rfl` and a few easy steps. The tactic `have h : P := proof` adds `h : P` to the context. With no `:= proof`, it adds a goal for `P` first. The form `have h := e` takes the type of `h` from `e`.

::: mathlib
`le_trans` · `Mathlib.Order.Defs.PartialOrder`

The transitivity of `≤` in a preorder. It is the standard example of a lemma with a variable in the middle: `apply le_trans` leaves the middle term as a goal, and `exact le_trans h1 h2` or `h1.trans h2` gives it by the hypotheses.

<?decl le_trans?>
:::

::: mathlib
`exists_between` · `Mathlib.Order.Basic`

In a dense order, from $a < b$ there is $c$ with $a < c < b$. For `ℝ` the witness $(a + b)/2$ gives a direct proof with `refine`. The lemma gives the same result in each dense order, with no formula.

<?decl exists_between?>
:::

### How to use it

Start each proof by reading the target. A target `∀` or `→` calls for `intro`. A target `∧` or `↔` calls for `constructor`, or for `refine ⟨?_, ?_⟩`. A target `∃` calls for `use t`, or for `refine ⟨t, ?_⟩`. A target that is a hypothesis, or a lemma with its arguments, calls for `exact`. A target that is the conclusion of a lemma calls for `apply`. Use `have` to state a step in the middle of the proof, with its name, as a written proof does with "note that". Write the type of each variable in a statement with `∀`: `∀ ε : ℝ, ε > 0 → …`.

### What it cannot do

#### exact with a hypothesis of the wrong type

The tactic `exact` does not prove a consequence of the hypothesis. On the goal `0 < x` with `h : 1 < x`, the step `exact h` fails:

```text
Type mismatch
  h
has type
  1 < x
but is expected to have type
  0 < x
```

The fix is a term of the right type: `exact lt_trans one_pos h`, or the tactic `linarith`.

#### intro with no binder

On the goal `0 < x`, the step `intro y` fails with "There are no additional binders or `let` bindings in the goal to introduce". The target has no `∀` and no `→`.

#### A variable with no type

In the statement `∀ ε > 0, ∃ δ > 0, δ < ε`, the variable `ε` has no type. Lean takes the default type `ℕ` for the numeral `0`. The context after `intro ε hε` shows the problem:

```text
ε : ℕ
hε : ε > 0
⊢ ∃ δ > 0, δ < ε
```

After `use ε / 2`, the division is the division of `ℕ` with a remainder, and `linarith` fails on `ε / 2 > 0`: for $\varepsilon = 1$, $1 / 2 = 0$ in `ℕ`. The statement is false for `ℕ`. The fix is the type in the statement: `∀ ε : ℝ, ε > 0 → ∃ δ > 0, δ < ε`.

#### use with a wrong witness

The tactic `use` accepts each witness of the right type, also a witness that makes the goal false. On `∃ y : ℝ, x < y`, the step `use x` leaves the false goal `x < x`, and the tactic reports it as an unsolved goal. Choose the witness with care: `use x + 1`.

### Examples

**Example (apply and the middle term).** From $a \leq b$ and $b \leq c$, $a \leq c$. After `apply le_trans`, the goal state is:

```text
case a
a b c : ℝ
h1 : a ≤ b
h2 : b ≤ c
⊢ a ≤ ?b

case a
a b c : ℝ
h1 : a ≤ b
h2 : b ≤ c
⊢ ?b ≤ c

case b
a b c : ℝ
h1 : a ≤ b
h2 : b ≤ c
⊢ ℝ
```

The step `exact h1` closes the first goal and fills `?b := b`. Then the second goal is `b ≤ c`, and `exact h2` closes it. The third goal is filled too.

```lean
example (a b c : ℝ) (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  apply le_trans
  · exact h1
  · exact h2
```

**Example (refine and the midpoint).** For $a < b$ in $\mathbb{R}$, the midpoint is between: $a < \frac{a + b}{2} < b$. The term `⟨(a + b) / 2, ?_, ?_⟩` gives the witness and leaves the two inequalities:

```text
case refine_1
a b : ℝ
hab : a < b
⊢ a < (a + b) / 2

case refine_2
a b : ℝ
hab : a < b
⊢ (a + b) / 2 < b
```

```lean
example (a b : ℝ) (hab : a < b) : ∃ c, a < c ∧ c < b := by
  refine ⟨(a + b) / 2, ?_, ?_⟩
  · linarith
  · linarith
```

**Example (A proof of ε and δ).** For each $\varepsilon > 0$ there is $\delta > 0$ with $\delta < \varepsilon$. The proof by hand: let $\varepsilon > 0$, take $\delta = \varepsilon / 2$, then $\delta > 0$ and $\delta < \varepsilon$.

```lean
example : ∀ ε : ℝ, ε > 0 → ∃ δ > 0, δ < ε := by
  intro ε hε
  use ε / 2
  constructor <;> linarith
```

After `use ε / 2` the target is `ε / 2 > 0 ∧ ε / 2 < ε`, and `constructor` gives the two goals `left` and `right`.

**Example (have).** From $f(x) = 2x$ for each $x$, $f(3) = 6$. The step `have h := hf 3` adds the instance:

```text
f : ℕ → ℕ
hf : ∀ (x : ℕ), f x = 2 * x
h : f 3 = 2 * 3
⊢ f 3 = 6
```

The tactic `omega` treats `f 3` as an atom and closes the goal with `h`. The step `have` is necessary here: `omega` does not instantiate `hf` by itself.

### Exercises

1. (A) Prove $p \to q \to p \wedge q$ with `intro` and `constructor`, and then with one term `fun hp hq => ⟨hp, hq⟩`.
2. (A) Prove `0 < x` from `1 < x` over `ℝ` with `exact` and a term of the library, and with `linarith`.
3. (A) Write the goal state after `apply lt_of_lt_of_le` on the goal `a < c`. Tell which goals have a metavariable.
4. (A) Prove `∃ y : ℝ, x < y` with `use`. Tell why `use x` fails.
5. (B) Prove the statement `∀ ε : ℝ, ε > 0 → ∃ δ > 0, 2 * δ < ε`, by hand and in Lean.
6. (B) Prove that the statement `∀ ε > 0, ∃ δ > 0, δ < ε` with `ε : ℕ` is false. Give the value of `ε` that refutes it.
7. (B) Prove the rule of intro for a proof of $P \to Q \to R$ from a proof of $R$ in the context $\Gamma, h_1 : P, h_2 : Q$.
8. (C) For $a < b$ in $\mathbb{R}$, prove that there are $c$ and $d$ with $a < c$, $c < d$ and $d < b$. Give the witnesses in one `refine` and close the three goals with `linarith`.

### Reference

<?reference?>
