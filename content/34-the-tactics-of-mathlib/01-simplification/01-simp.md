---
title: simp
kind: tactic
modules: []
explains:
  E1: [mul_comm, mul_left_comm]
families: [F-simp]
requires: [V00]
reads_with: ["MIL"]
lean: [MathlibHandbook/V34/C01/Examples.lean, MathlibHandbook/V34/C01/Solutions.lean]
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## simp

### Overview

The tactic `simp` rewrites the goal with a large set of equations and equivalences, the simp set. It stops when no lemma of the set applies. If the result is `True`, the goal is closed. A written proof says "after the obvious simplifications" in this place. The tactic `simp` does these simplifications, and it gives a proof of each step.

This section explains what a simp lemma is, in which order `simp` uses the lemmas, how it proves the hypotheses of a conditional lemma, and why it stops. Then it shows the forms of the call: `simp`, `simp only`, `simp at`, `simpa` and `simp?`. At the end, the reader can read a goal and tell whether `simp` is the right tactic for it, and can repair a call of `simp` that fails.

### What it does

#### Rewriting with a set of lemmas

**Definition (Simp lemma).** A simp lemma is a theorem whose statement, after its universal quantifiers and its hypotheses, is an equation $l = r$ or an equivalence $l \leftrightarrow r$. The tactic uses it from left to right: it replaces an instance of $l$ with the same instance of $r$. A statement $p$ that is not an equation is used as $p = \mathrm{True}$, and a statement $\neg p$ as $p = \mathrm{False}$.

A lemma gets into the default simp set with the attribute `@[simp]`. Mathlib has many thousands of such lemmas. Some examples: `List.length_append` says that the length of `xs ++ ys` is the sum of the lengths, `List.append_nil` says that `xs ++ []` is `xs`, `add_zero` says that `a + 0` is `a`, and `Set.mem_inter_iff` says that `x ∈ s ∩ t` is `x ∈ s ∧ x ∈ t`.

The tactic visits the term of the goal from the inside out. At a subterm $t$ it looks for a lemma whose left side $l$ matches $t$: there must be values of the variables of the lemma that make $l$ equal to $t$ up to the reducible definitions. The search uses a discrimination tree, an index of the left sides by their head symbols, so it does not test each lemma of the set. When a lemma matches, `simp` replaces $t$ with the instance of $r$ and visits the new term again. When no lemma matches at any subterm, it stops.

The proof that `simp` builds is a chain of equations. Each step is an instance of a lemma, put into context by congruence: if $t = t'$, then $f(t) = f(t')$. At the end, `simp` has a proof of $G = G'$, where $G$ is the old goal and $G'$ is the new one. If $G'$ is `True`, the goal is closed. Otherwise the goal becomes $G'$.

#### Conditional lemmas and the discharger

Many useful equations hold only under a hypothesis. The lemma `abs_of_pos` says that $|a| = a$ when $0 < a$. The lemma `div_self` says that $a / a = 1$ when $a \neq 0$. A simp lemma can have such hypotheses. When its left side matches, `simp` must prove the hypotheses for the values of the match. It calls a discharger for this. The default discharger is `simp` itself, with the same simp set and the hypotheses of the call. So `simp [hx]` with `hx : x ≠ 0` rewrites `x / x` to `1`: the hypothesis `x ≠ 0` of `div_self` becomes `True` by `hx`.

If the discharger fails, the lemma does not apply, and `simp` goes on with the other lemmas. It does not tell the user that a conditional lemma almost applied. This is one source of the surprise "`simp` made no progress".

#### Why simp stops

A rewriting system can run for ever. The two lemmas $a = b$ and $b = a$ together make `simp` go from $a$ to $b$ and back. Mathlib asks of each simp lemma that its right side is simpler than its left side, in a sense that a person can see: fewer symbols, fewer casts, a more standard form. This is a convention, not a theorem that Lean checks. A bad simp lemma can make `simp` loop, and then it stops with the error that the maximum recursion depth is reached.

A lemma such as `add_comm : a + b = b + a` has the same size on the two sides. It would loop. The tactic `simp` treats such a lemma in a special way, by ordered rewriting.

**Definition (Ordered rewriting).** Fix a total order $<$ on the terms. A permutation lemma is a lemma $l = r$ where $r$ is $l$ with the variables in another order. In ordered rewriting, `simp` uses a permutation lemma to rewrite $t$ to $t'$ only when $t' < t$.

**Theorem (Ordered rewriting stops).** Let $T$ be a set of terms, let $<$ be a well-founded strict order on $T$, and let a rewriting system rewrite $t$ to $t'$ only when $t' < t$. Then each sequence of rewriting steps is finite.

*Proof.* Take a sequence $t_0, t_1, t_2, \ldots$ in which $t_{i+1}$ is the result of one step from $t_i$. By the rule of the system, $t_{i+1} < t_i$ for each $i$. So the sequence is strictly decreasing. In a well-founded order, each nonempty set has a minimal element. If the sequence were infinite, the set $\{t_0, t_1, \ldots\}$ would have a minimal element $t_k$, and $t_{k+1} < t_k$ would contradict the minimality. So the sequence is finite. $\square$

For the commutativity of a sum of atoms, the order puts the atoms in a fixed order, and the result of `simp [add_comm, add_left_comm]` is the sum with the atoms sorted. For this reason, two sums with the same atoms get the same form, and `simp` proves that they are equal. The tactic `ring` does this job better (Chapter 2), but the method of `simp` also works in a commutative monoid with no ring structure.

#### Confluence

A second property of a good simp set is that the result does not depend on the order of the steps. A rewriting system is confluent if any two ways to rewrite a term can be continued to the same result. The simp set of Mathlib is not confluent in general. The library has a linter, `simpNF`, that tests a part of this property: for each simp lemma, it checks that `simp` cannot rewrite the left side by other lemmas first. If it can, the lemma never applies, because `simp` visits the inside of a term first. Thus the linter finds lemmas that are dead in the simp set.

::: mathlib
`mul_comm` · `Mathlib.Algebra.Group.Semigroup`

The lemma `mul_comm` is not in the simp set, because it is a permutation lemma. Given in the list of a call, as in `simp [mul_comm, mul_left_comm]`, it is used by ordered rewriting. The pair `mul_comm` and `mul_left_comm`, with `mul_assoc`, puts each product of a commutative monoid in one normal order: it is the standard way to make `simp` see that two products with the same factors are equal.

<?decl mul_comm?>
:::

::: mathlib
`mul_left_comm` · `Mathlib.Algebra.Group.Semigroup`

This lemma says $a \cdot (b \cdot c) = b \cdot (a \cdot c)$. It is the second permutation lemma that ordered rewriting needs. With `mul_comm` alone, `simp` can swap the two factors of a product, but it cannot move a factor past the first factor of a nested product.

<?decl mul_left_comm?>
:::

### How to use it

There are five forms of the call. Each one has a use.

1. `simp` uses the whole default simp set on the goal. Use it at the end of a proof, where it must close the goal.
2. `simp [h, foo]` adds the hypothesis `h` and the lemma `foo` to the set. A hypothesis `h : a = b` rewrites `a` to `b`. A hypothesis `h : p` rewrites `p` to `True`. Write `simp [← foo]` to use `foo` from right to left, and `simp [-foo]` to remove a lemma of the default set.
3. `simp only [foo, bar]` uses only the lemmas of the list, and a few basic facts of logic. Its result does not change when the library changes.
4. `simp at h` simplifies the hypothesis `h`. If `h` becomes `False`, the goal is closed. The form `simp at h ⊢` does the hypothesis and the goal, and `simp at *` does all hypotheses and the goal.
5. `simpa using e` simplifies the goal and the type of the term `e` with the same set, and then closes the goal with `e`. Use it when a hypothesis and the goal differ by simplification. A plain `simpa` uses the hypothesis `this`, or closes the goal with an assumption after simplification.

The call `simp?` does the work of `simp`, and then it prints a call `simp only [...]` with the lemmas that it used. Mathlib has a rule for this. A `simp` that does not close the goal is a non-terminal `simp`. A change of the simp set in a later version of Mathlib can change its result, and then the next step of the proof breaks. So in Mathlib a non-terminal `simp` is replaced by the `simp only` call that `simp?` prints. A terminal `simp`, which closes the goal, can stay: if a new version of the simp set still closes the goal, the proof still works.

On the goal of the first example below, `simp?` prints the call

```lean
simp only [List.append_nil, List.length_append, Nat.add_left_cancel_iff]
```

This tells the reader which three facts make the proof: `xs ++ []` is `xs`, the length of an append is a sum, and $a + b = a + c$ is equivalent to $b = c$. The last step closes the goal: after it, the goal is `True`.

Put the attribute `@[simp]` on a new lemma only when the right side is simpler than the left side, when the left side is not changed first by other simp lemmas, and when the hypotheses of the lemma are easy for the discharger. An equation that defines a function at a constructor, such as `double 0 = 0`, is a good simp lemma.

### What it cannot do

#### simp made no progress

The most common failure is the message "`simp` made no progress". It says that no lemma of the set matched any subterm of the goal. There are four common causes.

1. The needed fact is not a simp lemma. The commutativity `a * b = b * a` for `a b : ℕ` is the first case: `simp` fails on this goal. Give the lemma: `simp [mul_comm]`.
2. The needed fact is a hypothesis, and it is not in the call. On `f (f 0) = 2` with `h : ∀ x, f x = x + 1`, a plain `simp` fails. The call `simp [h]` rewrites `f 0` to `0 + 1`, simplifies it to `1`, rewrites `f 1` to `1 + 1`, and closes `1 + 1 = 2` by evaluation of numerals.
3. A conditional lemma needs a hypothesis that the discharger cannot prove. On `x / x = 1` for `x : ℝ` with no hypothesis, `simp` has no way to prove `x ≠ 0`. Give the hypothesis: `simp [hx]`.
4. The fact is not an equation, so it is not a rewriting at all. The tactic `simp` does not prove `0 < n → n ≠ 0` for `n : ℕ` by itself: on `h : 0 < n`, the call `simp at h` makes no progress, because `0 < n` is already in simp normal form. Use `omega` or `Nat.pos_iff_ne_zero`.

#### simp changes the goal to a form that is not useful

A plain `simp` that does not close the goal can leave a goal that is harder to read. On `x ^ 2 - 2 * x + 1 ≥ 0` for `x : ℝ`, `simp` only turns `≥` into `≤`, and the goal becomes `0 ≤ x ^ 2 - 2 * x + 1`. This is not wrong, but `simp` is the wrong tool. The goal needs the square $(x - 1)^2$, and the tactics of Chapter 2 and Chapter 3 find it: `nlinarith [sq_nonneg (x - 1)]`.

#### simp does not do algebra and does not do arithmetic reasoning

The simp set has no lemma that expands a product of sums, and it has no procedure for inequalities with variables. It does not prove `(a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2`; use `ring`. It does not prove `a ≤ a ^ 2` for `a : ℕ`; this needs a case split on `a = 0`, and the tactic `nlinarith` or a lemma of the library. It also does not prove `2 * x = 4 → x = 2` over `ℚ`: on `h : 2 * x = 4`, `simp at h` makes no progress. Use `linarith`.

#### simp loops

A hypothesis in the list can make `simp` loop. If `h : a = b` and `h' : b = a` are both in the list, each one undoes the other. Mathlib's `simp` detects some of these loops, and in other cases it stops with the error that the maximum recursion depth is reached. Remove one of the two equations. In the same way, `simp [h]` with `h : f x = f (f x)` loops, because the right side contains the left side.

### Examples

**Example (The length of a list).** The goal is $|xs \mathbin{+\!\!+} []| + |ys| = |xs \mathbin{+\!\!+} ys|$. On paper the proof is: $xs \mathbin{+\!\!+} [] = xs$, and the length of an append is the sum of the lengths. The simp set has the two facts, so `simp` closes the goal.

<?lean MathlibHandbook/V34/C01/Examples.lean#simp_list?>

The goal state goes through these forms. The first step uses `List.append_nil` inside the first length. The second step uses `List.length_append` on the right side. The third step cancels `xs.length` with `Nat.add_left_cancel_iff`.

```text
⊢ (xs ++ []).length + ys.length = (xs ++ ys).length
⊢ xs.length + ys.length = (xs ++ ys).length
⊢ xs.length + ys.length = xs.length + ys.length
⊢ True
```

**Example (Only the given lemmas).** The call `simp only` rewrites with `Nat.add_zero` and with the hypothesis `h`. The goal `a + 0 = b` becomes `a = b`, then `b = b`, and `simp only` closes it by reflexivity.

<?lean MathlibHandbook/V34/C01/Examples.lean#simp_only?>

**Example (At a hypothesis).** The call `simp at h` turns `a * 1 + 0 = 3` into `a = 3`. It uses `mul_one` and `add_zero`. After the call, the context is

```text
a : ℕ
h : a = 3
⊢ a = 3
```

and `exact h` closes the goal. The form `simpa using h` does the two steps at once.

<?lean MathlibHandbook/V34/C01/Examples.lean#simp_at?>

**Example (A new simp lemma).** The attribute `@[simp]` puts `double_zero` into the simp set. Then a plain `simp` uses it. The goal `double 0 + 1 = 1` becomes `0 + 1 = 1`, then `1 = 1`.

<?lean MathlibHandbook/V34/C01/Examples.lean#simp_attr?>

**Example (Commutativity).** With `mul_comm` and `mul_left_comm`, the two sides of $a(bc) = c(ba)$ get the same normal order. Ordered rewriting sorts the factors of each side, so both sides become the same product.

<?lean MathlibHandbook/V34/C01/Examples.lean#simp_comm?>

**Example (A hypothesis as a rewriting rule).** Let $f : \mathbb{N} \to \mathbb{N}$ with $f(x) = x + 1$ for each $x$. Then $f(f(0)) = 2$. The call `simp [h]` uses `h` as a rewriting rule from left to right.

```lean
example (f : ℕ → ℕ) (h : ∀ x, f x = x + 1) : f (f 0) = 2 := by
  simp [h]
```

The tactic works from the inside out. The inner term `f 0` becomes `0 + 1`, then `1` by `zero_add`. The outer term `f 1` becomes `1 + 1`. The simp set evaluates `1 + 1 = 2` on numerals, and the goal becomes `True`.

**Example (A conditional lemma).** For $x > 0$, $|x| = x$. The lemma `abs_of_pos` has the hypothesis `0 < a`. Given as a term `abs_of_pos hx`, it is an unconditional equation `|x| = x`, and `simp` uses it at once.

```lean
example (x : ℝ) (hx : 0 < x) : |x| = x := by
  simp [abs_of_pos hx]
```

In the same way, `simp [hx]` proves `x / x = 1` from `hx : x ≠ 0`. Here the lemma `div_self` comes from the default simp set, and the discharger proves its hypothesis `x ≠ 0` with `hx`.

**Example (Sets).** For a set $s$ of natural numbers, $x \in s \cap s$ if and only if $x \in s$. The simp set has `Set.inter_self`, so `simp` proves the statement in one step. On paper this is the idempotence of $\cap$.

```lean
example (s : Set ℕ) (x : ℕ) : x ∈ s ∩ s ↔ x ∈ s := by
  simp
```

### Exercises

1. (A) Run `simp?` on the goal of the first example. Write down the `simp only` call that it suggests, and say in words what each lemma of the call states.
2. (A) Find the name of a simp lemma about `List.reverse` in the Mathlib documentation. Tell why its right side is simpler than its left side.
3. (A) Prove `(a : ℤ) - b + b = a` with `simp`. Then find the lemma that `simp` used with `simp?`. Hint: the lemma has the word `cancel` in its name.
4. (B) Tell why the lemma `a + b = b + a` must not have the attribute `@[simp]` without ordered rewriting. Give a sequence of rewriting steps that does not stop.
5. (B) Give a goal that `simp only [h]` closes and a plain `simp` does not change in the same way. Hint: take a goal where `h` is needed and the default set has nothing to do.
6. (B) Prove $f(f(f(0))) = 3$ from $f(x) = x + 1$ with `simp`. Write the goal state after each rewriting step.
7. (B) Let `h : 0 < n` for `n : ℕ`. Tell why `simp at h` makes no progress, and prove `n ≠ 0` with another tactic.
8. (C) A rewriting system on terms rewrites by a lemma $l = r$ only if the number of symbols of $r$ is smaller than the number of symbols of $l$. Prove that each sequence of rewriting steps stops. Then explain why the simp set of Mathlib cannot follow this rule for all its lemmas. Hint: look at `Set.mem_inter_iff`.
9. (L) Prove that the length of `(xs ++ []).reverse` is the length of `xs` (`reverse_append_nil_length` in `Exercises.lean`).

### Reference

<?reference?>
