---
title: rw, nth_rw and conv
kind: tactic
modules: []
explains:
  E1: [mul_add, add_comm, add_assoc, Finset.sum_range_succ]
families: []
requires: [V00]
reads_with: ["MIL"]
lean: [MathlibHandbook/V34/C01/Examples.lean, MathlibHandbook/V34/C01/Solutions.lean]
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## rw, nth_rw and conv

### Overview

The tactic `rw` replaces a term with an equal term. It is the step "by $h$, the left side is ..." of a written proof. Where `simp` uses a large set of lemmas and decides itself which ones to apply, `rw` uses exactly the equations that the user gives, in the order of the list, once each. So a proof with `rw` is a proof that the reader can follow step by step, and its result does not change when the library changes.

This section explains how `rw` finds the place to rewrite, why it rewrites all the instances of a pattern at once, and what the message "motive is not type correct" means. It also shows `nth_rw` for a single occurrence and `conv` for a rewrite in a part of the goal. Most proofs of Mathlib use `rw` in some step, so the failures of this section are worth knowing well.

### What it does

#### The principle: substitution of equals

The logical basis of `rw` is the substitution of equals.

**Theorem (Substitution).** Let $a, b$ be terms of a type $\alpha$ with $a = b$. Let $P$ be a property of the elements of $\alpha$. If $P(a)$ holds, then $P(b)$ holds.

*Proof.* In the logic of Lean, equality is defined by one rule: $a = a$ for each $a$, and a property that holds for $a$ holds for each $b$ with $a = b$. This rule is the recursor of the type `Eq`, and the statement of the theorem is this recursor applied to $P$. In a first-order logic with equality, the statement is the axiom scheme of substitution. In both cases there is nothing more to prove. $\square$

The tactic uses the theorem in the backward direction. Let the goal be $G$, and let `h : a = b`. The tactic finds each instance of $a$ in $G$. It writes $G$ as $M(a)$, where $M$ is the function $x \mapsto G$ with each instance of $a$ replaced by $x$. This function is called the *motive*. The new goal is $M(b)$. A proof of $M(b)$ gives a proof of $M(a)$ by the theorem with the equation $b = a$. After the rewrite, `rw` tries to close the goal with `rfl`, so a goal that becomes $t = t$ is closed at once.

#### The pattern and its instances

The equation can be a hypothesis or a lemma with variables. The lemma `mul_add` states $a(b + c) = ab + ac$ for all $a, b, c$ of a ring. In `rw [mul_add]`, the left side `?a * (?b + ?c)` is a pattern with three metavariables. The tactic goes through the goal and takes the first subterm that matches the pattern. This fixes the values of `?a`, `?b` and `?c`. Then it rewrites each instance of this fixed term, and not the other matches of the pattern.

For example, on the goal $x(y + z) + u(v + w) = 0$, the call `rw [mul_add]` matches $x(y + z)$ first and rewrites only it. The second product $u(v + w)$ has other values of the metavariables. A second `rw [mul_add]` rewrites it. To fix the values in advance, give them: `rw [mul_add u]` rewrites $u(v + w)$.

The order in which `rw` visits the goal is the order of the term tree of Lean, not the left to right order of the printed goal. In practice it is close to the order of the printed goal, but for a precise choice, give the arguments of the lemma.

#### Rewriting from right to left and at a hypothesis

The call `rw [← h]` uses `h : a = b` from right to left: it replaces each $b$ with $a$. The call `rw [h] at h'` rewrites the hypothesis `h'` and not the goal. The call `rw [h] at h' ⊢` does both. The call `rwa [h] at h'` is `rw [h] at h'` followed by `assumption`.

A lemma of the form `p ↔ q` also works with `rw`. It replaces the proposition `p` with `q` in the goal. This is how `rw [Set.mem_inter_iff]` turns `x ∈ s ∩ t` into `x ∈ s ∧ x ∈ t`.

#### The motive and dependent types

The motive $M$ must be a well-typed function. Usually it is. It fails when a term of the goal has a type that depends on $a$. Let $n : \mathbb{N}$, let `x : Fin n`, an element of $\{0, \ldots, n - 1\}$, and let `h : n = 2`. The goal `(x : ℕ) < n` contains $n$ twice: once in the visible `< n`, and once in the hidden argument of the cast `Fin.val`, whose type is `Fin n → ℕ`. The motive replaces both instances by a variable $m$, and it gets `Fin.val (n := m) x < m`. This is not well typed, because `x` has the type `Fin n` and not `Fin m`. The tactic stops with the error "motive is not type correct".

The fix is to replace $n$ everywhere at once, in the context and in the goal. The tactic `subst h` does this when `h` is an equation between a variable and a term: it removes the variable $n$ and puts $2$ in its place, also in the type of `x`. The tactic `simp only [h]` is another fix, because `simp` can rewrite under a dependent function in some cases. A third fix is to avoid the rewrite: here `omega` with the fact `x.isLt` proves the goal.

### How to use it

Write `rw [h₁, h₂, h₃]` for a chain of rewrites. The tactic uses them in order. After each rewrite, the goal state is shown in the editor when the cursor is on the next name of the list. This makes `rw` the tactic in which a user can see each step.

Use these variants.

1. `rw [h]` rewrites each instance of the left side of `h` in the goal.
2. `rw [← h]` rewrites from right to left.
3. `rw [foo a b]` fixes the arguments of the lemma `foo`, to select an instance.
4. `nth_rw 2 [h]` rewrites only the second instance of the left side of `h`. The count starts at $1$.
5. `rw [h] at h'` rewrites a hypothesis. `rwa` closes the goal with an assumption after the rewrite.
6. `conv_lhs => rw [h]` rewrites only in the left side of an equation or an inequality, and `conv_rhs` only in the right side. The general form `conv in pat => rw [h]` rewrites only inside the subterm that matches `pat`.

Use `rw` when the proof needs a few named steps, when the order matters, or when `simp` rewrites too much. Use `simp only [h]` when the equation must be used many times in a term, or under a binder. The tactic `rw` cannot rewrite under a binder: in `∑ i ∈ range n, f i` it cannot rewrite `f i` with an equation that depends on `i`, because `i` is a bound variable. For this case, Mathlib has `Finset.sum_congr`, and `simp only` can do it with the equation as a lemma of the list.

### What it cannot do

#### Did not find an occurrence of the pattern

The message "Did not find an occurrence of the pattern" says that the left side of the equation does not occur in the goal. On `x * 2 = 2 * x` for `x : ℝ`, the call `rw [add_comm]` fails with this message: there is no sum. A less clear case comes from the form of the goal after earlier steps. On the goal `x * y / x = y`, the call `rw [mul_div_assoc]` makes `x * (y / x)`. A second call `rw [mul_div_cancel_left₀]` then fails: its pattern is `?a * ?b / ?a`, and that pattern was in the old goal, not in the new one.

The rule is: read the goal state after each step of a chain. In the editor, put the cursor after each name of the list. A working proof of the example is `rw [mul_comm, mul_div_assoc, div_self hx, mul_one]`: the goal goes through `y * x / x = y`, `y * (x / x) = y`, `y * 1 = y` and `y = y`.

The pattern also fails to match when the goal has the same term up to a definition that `rw` does not unfold. The tactic matches up to instances and reducible definitions only. A goal with `2 * n` does not contain `n + n`, though the two are equal, and the goal `Even n` does not contain `∃ r, n = r + r` until the definition is unfolded with `unfold Even`.

#### motive is not type correct

This error is explained above. It comes from a term whose type depends on the term that `rw` replaces. Use `subst`, `simp only [h]` or a proof that avoids the rewrite.

#### rw rewrites too much

Since `rw` rewrites each instance of the fixed term, it can change a place that the proof needs to keep. On the goal `a + a = b + a` with `h : a = b`, the call `rw [h]` makes `b + b = b + b` and closes the goal by `rfl`. This is fine here. But if the goal were `a + a = a + b` and the proof wanted to rewrite only the first `a`, then `nth_rw 1 [h]` is the right call.

#### rw does not close the goal

After the last rewrite, `rw` tries `rfl`, and only with the reducible definitions. A goal such as `2 * c + c = 3 * c` is not closed by `rw`: it needs `ring`. A goal `n + 0 = n` is closed, because `n + 0` reduces to `n` by the definition of the addition of `ℕ`.

### Examples

**Example (A chain of substitutions).** Let $a = b + c$ and $b = 2c$ in $\mathbb{R}$. Then $a = 3c$. By hand: $a = b + c = 2c + c = 3c$. In Lean each equation is a rewrite, and `ring` does the last step.

```lean
example (a b c : ℝ) (h₁ : a = b + c) (h₂ : b = 2 * c) : a = 3 * c := by
  rw [h₁]
  rw [h₂]
  ring
```

The goal state after each line:

```text
⊢ b + c = 3 * c
⊢ 2 * c + c = 3 * c
```

**Example (Lemmas of the library).** The goal is $a(b + c) = ac + ab$ in $\mathbb{N}$. The lemma `mul_add` makes the left side $ab + ac$. The lemma `add_comm` then matches the first sum of the goal, which is $ab + ac$ on the left side, and makes it $ac + ab$. The goal becomes $ac + ab = ac + ab$, and `rfl` closes it.

```lean
example (a b c : ℕ) : a * (b + c) = a * c + a * b := by
  rw [mul_add, add_comm]
```

This proof works because the first sum that `rw` meets is the one on the left side. If the sides were in the other order, `add_comm` would change the wrong sum. The precise form `rw [mul_add, add_comm (a * b)]` does not depend on the order of the visit.

**Example (Fixing the arguments).** The goal is $a + b + c = a + (c + b)$. The call `rw [add_comm c b]` rewrites only the sum $c + b$, and the goal becomes $a + b + c = a + (b + c)$. Then `rw [add_assoc]` closes it.

```lean
example (a b c : ℕ) : a + b + c = a + (c + b) := by
  rw [add_comm c b]
  rw [add_assoc]
```

A plain `rw [add_comm]` would match the first sum $a + b + c$, and make $c + (a + b)$, which is not the step that the proof needs.

**Example (Right to left).** Let $y = x^2$. Then $y + x^2 = 2 x^2$. The call `rw [← h]` replaces each $x^2$ with $y$. The goal becomes `y + y = 2 * y`. The call `ring` closes it.

```lean
example (x y : ℝ) (h : y = x ^ 2) : y + x ^ 2 = 2 * x ^ 2 := by
  rw [← h]
  ring
```

**Example (A sum).** The lemma `Finset.sum_range_succ` states $\sum_{i < n + 1} f(i) = \sum_{i < n} f(i) + f(n)$. It is the first step of each proof by induction of a formula for a sum (Chapter 5).

```lean
example (n : ℕ) : ∑ i ∈ Finset.range (n + 1), i = ∑ i ∈ Finset.range n, i + n := by
  rw [Finset.sum_range_succ]
```

**Example (A hypothesis).** The call `rwa [Nat.add_zero] at h` turns `h : a + 0 = b` into `h : a = b`, and then `assumption` closes the goal `a = b`.

```lean
example (a b : ℕ) (h : a + 0 = b) : a = b := by
  rwa [Nat.add_zero] at h
```

**Example (conv).** The goal is $(ab)c = a(cb)$, in Lean `a * b * c = a * (c * b)`. The left side needs `mul_assoc`, and the right side needs `mul_comm c b`. With `conv_lhs`, the first rewrite acts only on the left side. The goal after it is `a * (b * c) = a * (c * b)`. Then `conv_rhs => rw [mul_comm c b]` makes the two sides equal.

```lean
example (a b c : ℕ) : a * b * c = a * (c * b) := by
  conv_lhs => rw [mul_assoc]
  conv_rhs => rw [mul_comm c b]
```

**Example (The motive).** This is the failure of the section on dependent types, and its fix.

```lean
example (n : ℕ) (h : n = 2) (x : Fin n) : (x : ℕ) < n := by
  rw [h]   -- error: motive is not type correct

example (n : ℕ) (h : n = 2) (x : Fin n) : (x : ℕ) < 2 := by
  subst h
  exact x.isLt
```

After `subst h`, the context has `x : Fin 2`, and `x.isLt : ↑x < 2` is the goal.

### Exercises

1. (A) Prove $a + b + 0 = b + a$ in $\mathbb{N}$ with `rw`. Write the goal after each rewrite.
2. (A) On the goal `x * (y + z) + u * (v + w) = 0`, tell what `rw [mul_add]` does, and how to rewrite the second product first.
3. (A) Prove `x ∈ s ∩ t → x ∈ t` with `rw [Set.mem_inter_iff]` and the tactics of Chapter 5.
4. (B) Prove $x y / x = y$ for $x \neq 0$ in $\mathbb{R}$ with a chain of `rw`. Hint: the chain in the text uses four lemmas.
5. (B) On the goal `a + a = a + b` with `h : a = b`, tell the result of `rw [h]`, of `nth_rw 1 [h]` and of `nth_rw 2 [h]`.
6. (B) Tell why `rw` cannot prove $\sum_{i < n} (i + 0) = \sum_{i < n} i$ with `add_zero`, and give a proof with `simp only`.
7. (C) Let `v : Fin n → ℝ` and `h : n = m`. Give a goal about `v` on which `rw [h]` fails with the error on the motive. Explain the failure as in the text.

### Reference

<?reference?>
