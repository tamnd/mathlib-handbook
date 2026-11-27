---
title: rcases, obtain and rintro
kind: tactic
modules: []
explains:
  E1: [Set.mem_inter_iff]
families: []
requires: [V00]
reads_with: ["MIL"]
lean: [MathlibHandbook/V34/C05/Examples.lean, MathlibHandbook/V34/C05/Solutions.lean]
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## rcases, obtain and rintro

### Overview

A written proof uses a hypothesis in a few standard ways. From "$p$ and $q$" it takes $p$ and $q$. From "$p$ or $q$" it treats two cases. From "there is an $n$ with $P(n)$" it says "take such an $n$". From "$a$ divides $b$" it writes "$b = ak$". The tactic `rcases` makes all these steps with one syntax, the pattern. The tactic `obtain` is the same step written as a line of the proof: `obtain ⟨n, hn⟩ := h`. The tactic `rintro` introduces the variables of the goal and takes them apart in the same step.

The section explains the rules of elimination that these tactics use, the language of the patterns, and the restriction that forbids the extraction of a witness from a proof of `∃` inside a definition.

### What it does

#### Elimination rules

In Lean, `∧`, `∨` and `∃` are inductive types. Each one has constructors, the ways to prove it, and a rule of elimination, the way to use it.

**Definition (Constructors of the connectives).** A proof of $p \wedge q$ is a pair $\langle h_p, h_q \rangle$ of a proof of $p$ and a proof of $q$. A proof of $p \vee q$ is `Or.inl h` with $h : p$, or `Or.inr h` with $h : q$. A proof of $\exists x,\ P(x)$ is a pair $\langle t, h \rangle$ of a term $t$ and a proof $h : P(t)$.

**Theorem (Rules of elimination).** Let $r$ be a proposition.

1. If $p \wedge q$ holds, and $p \to q \to r$, then $r$.
2. If $p \vee q$ holds, and $p \to r$ and $q \to r$, then $r$.
3. If $\exists x,\ P(x)$ holds, and $\forall x,\ P(x) \to r$, where $r$ does not depend on $x$, then $r$.

*Proof.* (1) A proof of $p \wedge q$ is a pair $\langle h_p, h_q \rangle$. Apply the implication to $h_p$ and then to $h_q$. (2) A proof of $p \vee q$ is `Or.inl h` or `Or.inr h`. In the first case, apply $p \to r$ to $h$. In the second case, apply $q \to r$ to $h$. (3) A proof of $\exists x,\ P(x)$ is a pair $\langle t, h \rangle$ with $h : P(t)$. Apply the hypothesis to $t$ and $h$: this gives $r$, since $r$ does not depend on $x$. $\square$

The tactic `rcases h with ⟨a, b⟩` applies the rule (1) or (3) to `h`: it removes `h` and adds `a` and `b` to the context. The tactic `rcases h with a | b` applies the rule (2): it gives two goals, one with `a : p` and one with `b : q`. The names of the two cases are `inl` and `inr`.

The rule (3) has the condition that $r$ does not depend on $x$. In Lean, there is one more restriction. A proof of `∃ x, P x` is a proof: it is in the universe `Prop`, and the rule of elimination of `Exists` can only produce a proof, not a value of a type such as `ℕ`. The reason is proof irrelevance: two proofs of one proposition are equal in Lean. If the witness could be taken out as a value, then two proofs $\langle 4, h \rangle$ and $\langle 5, h' \rangle$ of $\exists n,\ n > 3$ would give the values $4$ and $5$ from one proof, a contradiction. So inside a proof, `obtain` takes out the witness, but inside a definition of a number, it fails. To get a value, use `Classical.choose h` or the tactic `choose` (next section).

#### Patterns

A pattern is built from these parts:

1. a name `x`, which keeps the part with this name;
2. `_`, which keeps the part with a name made by Lean;
3. `-`, which removes the part from the context;
4. `⟨p₁, p₂, …, pₙ⟩`, which takes apart a structure with $n$ fields, from the left, so that `⟨a, b, c⟩` is `⟨a, ⟨b, c⟩⟩`;
5. `p₁ | p₂`, which takes apart an `∨` or an inductive type with two constructors, with one goal for each case;
6. `rfl`, which takes an equation `x = t` or `t = x`, where `x` is a free variable, and substitutes `t` for `x` everywhere.

A pattern can nest: `⟨n, hn | hn⟩` takes apart $\exists n,\ P(n) \vee Q(n)$. The pattern `rfl` is the reason why `rcases` is shorter than a chain of `cases` and `subst`. On `h : a ∣ b`, the pattern `⟨k, rfl⟩` uses the definition of `∣`: $a \mid b$ means $\exists k,\ b = a k$. It replaces `b` by `a * k` in the goal and in all the hypotheses.

::: mathlib
`Set.mem_inter_iff` · `Mathlib.Data.Set.Basic`

The membership in an intersection: $x \in s \cap t \iff x \in s \wedge x \in t$. The two sides are equal by definition, so `rcases h with ⟨hs, ht⟩` works on `h : x ∈ s ∩ t` with no rewrite. The lemma is for `simp` and `rw`, when the form of the goal must change.

<?decl Set.mem_inter_iff?>
:::

### How to use it

Write `obtain ⟨x, hx⟩ := h` to take a witness from `h : ∃ x, P x`, and `obtain ⟨hp, hq⟩ := h` to split a conjunction. Write `obtain h1 | h2 := h` for a case split on `h : p ∨ q`. Write `rcases h with ⟨x, rfl⟩` when the equation of the hypothesis defines a variable that the rest of the proof does not need. Write `rintro x ⟨hs, ht⟩` on a goal `∀ x, x ∈ s ∩ t → …` or `s ∩ t ⊆ u`, where the inclusion unfolds to this form. Write `obtain ⟨k, hk⟩ : ∃ k, n = 2 * k := h` to state the form of the hypothesis that the pattern expects, when the definition of `h` is not visible.

### What it cannot do

#### A pattern with too many parts

On `h : p ∧ q`, the pattern `⟨a, b, c⟩` reads as `⟨a, ⟨b, c⟩⟩`, so `rcases` tries to take apart the proof of `q`. It fails:

```text
Tactic `rcases` failed: `right✝ : q` is not an inductive datatype
```

The fix is to make the pattern match the statement: `⟨a, b⟩` for a conjunction of two parts.

#### rfl with an equation that is not a definition

The pattern `rfl` needs a free variable on one side. On `h : x + 1 = 2 * y`, it fails:

```text
Tactic `subst` failed: invalid equality proof, it is not of the form (x = t) or (t = x)
  x + 1 = 2 * y
```

Keep the equation with a name, and use it with `rw`, `omega` or `linarith`.

#### A witness in a definition

Inside a definition with a value in `ℕ`, `obtain ⟨n, hn⟩ := h` on `h : ∃ n : ℕ, n > 3` fails:

```text
Tactic `induction` failed: recursor `Exists.casesOn` can only eliminate into `Prop`
```

This is the restriction of the previous part. Inside a proof the step is correct. To define a value from an existence statement, use `Classical.choose h`, with its property `Classical.choose_spec h`.

#### rintro with no binder

The tactic `rintro` introduces the binders of the goal. On a goal that is not of the form `∀` or `→`, it fails with "There are no additional binders or `let` bindings in the goal to introduce". This happens when the hypothesis to take apart is already in the context. Use `obtain` in this case.

### Examples

**Example (A conjunction).** The commutativity of `∧`. The pattern `⟨hp, hq⟩` gives the context `hp : p` and `hq : q`, and the anonymous constructor builds the new pair.

<?lean MathlibHandbook/V34/C05/Examples.lean#rcases_and?>

**Example (Two cases).** If $x = 1$ or $x = -1$, then $x^2 = 1$. The pattern `rfl | rfl` gives two goals, `1 ^ 2 = 1` and `(-1) ^ 2 = 1`, and `norm_num` closes both.

<?lean MathlibHandbook/V34/C05/Examples.lean#rcases_or?>

**Example (A witness).** From $f(n) = 0$ for some $n$, $f(m) \leq 0$ for some $m$. The step `obtain` takes the witness `n` and its property.

<?lean MathlibHandbook/V34/C05/Examples.lean#obtain?>

**Example (Transitivity of divisibility).** If $a \mid b$ and $b \mid c$, then $a \mid c$. The proof by hand: write $b = ak$ and $c = bm$, so $c = a(km)$. In Lean, the two patterns `⟨k, rfl⟩` and `⟨m, rfl⟩` make the substitutions.

```lean
example (a b c : ℕ) (h1 : a ∣ b) (h2 : b ∣ c) : a ∣ c := by
  obtain ⟨k, rfl⟩ := h1
  obtain ⟨m, rfl⟩ := h2
  exact ⟨k * m, by ring⟩
```

After the two steps, the variables `b` and `c` are gone:

```text
a k m : ℕ
⊢ a ∣ a * k * m
```

**Example (A case split on a hypothesis).** From $p \vee q$, $p \to r$ and $q \to r$, the proposition $r$. After `obtain hp' | hq' := h`, there are two goals:

```text
case inl
p q r : Prop
hp : p → r
hq : q → r
hp' : p
⊢ r

case inr
p q r : Prop
hp : p → r
hq : q → r
hq' : q
⊢ r
```

**Example (rintro on an inclusion).** The inclusion $s \cap t \subseteq t \cap s$ unfolds to $\forall x,\ x \in s \cap t \to x \in t \cap s$. The step `rintro x ⟨hs, ht⟩` introduces `x` and takes apart the membership in the intersection.

<?lean MathlibHandbook/V34/C05/Examples.lean#rintro?>

### Exercises

1. (L) Prove `∃ n, q n` from `∃ n, p n ∧ q n` (`exists_of_exists_and` in `Exercises.lean`). Use the pattern `-` for the part that the proof does not need.
2. (A) Prove $(p \wedge q) \wedge r \to p \wedge (q \wedge r)$ with one `rintro` and a nested pattern.
3. (A) Prove that $x \in \{1, 2\}$ implies $x \leq 2$ for `x : ℕ`, with the pattern `rfl | rfl`.
4. (A) Tell why `rcases h with rfl` fails on `h : x + 1 = 2 * y`. Give a proof of `x < 2 * y` from `h`.
5. (B) Prove the rule of elimination (3) for the statement $\exists x,\ P(x) \wedge Q(x)$, with $r = \exists x,\ Q(x)$.
6. (B) Prove that $a \mid b$ and $a \mid c$ imply $a \mid b + c$ over `ℤ`, with two patterns `⟨k, rfl⟩` and `⟨m, rfl⟩`. Write the goal state after the two steps, and give the witness.
7. (C) Explain, with proof irrelevance, why a function `(∃ n : ℕ, n > 3) → ℕ` that returns the witness cannot be defined by `obtain`. Give a definition with `Classical.choose`.

### Reference

<?reference?>
