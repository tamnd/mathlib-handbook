---
title: exact?, apply? and aesop
kind: tactic
modules: []
explains:
  E1: [Order.lt_add_one_iff, Set.mem_of_subset_of_mem]
families: []
requires: [V00]
reads_with: ["MIL"]
lean: [MathlibHandbook/V34/C04/Examples.lean, MathlibHandbook/V34/C04/Solutions.lean]
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## exact?, apply? and aesop

### Overview

A mathematician often knows that a lemma is in the library, but not its name. The tactic `exact?` searches the library for a lemma that closes the goal, with the hypotheses of the context as arguments. The tactic `apply?` searches for a lemma whose conclusion matches the goal, and it shows the goals that remain. Both tactics print a line such as `Try this: exact Order.lt_add_one_iff.mpr h`. Copy the line into the file: the search is slow, and the result of a search can change with the version of the library.

The tactic `aesop` is a different kind of search. It does not look for one lemma. It applies rules from a rule set to the goal again and again: it splits the conjunctions, it introduces the variables, it calls `simp_all`, and it applies the lemmas with the attribute `aesop`. It is good on goals of logic and of sets, where the proof is a sequence of routine steps.

The section explains the unification that the three tactics use, the difference between a safe rule and an unsafe rule, and the reason for each common failure.

### What it does

#### Unification

**Definition (Unification).** Let $P$ be a statement with metavariables $?x_1, \ldots, ?x_k$, that is, holes that wait for a term. Let $G$ be a goal. A unifier of $P$ and $G$ is an assignment of terms to the holes such that $P$ becomes $G$, up to the unfolding of reducible definitions. The tactics compute a unifier by a recursive comparison of the two terms: two applications of the same function unify if their arguments unify, a hole unifies with each term of the right type, and two different constants do not unify unless one unfolds to the other.

The tactic `apply h` takes a term `h : ∀ x₁ … xₖ, A₁ → ⋯ → Aₘ → B`. It replaces each $x_i$ by a hole, it unifies $B$ with the goal, and it leaves the goals $A_1, \ldots, A_m$ with the holes filled. It also leaves a goal for each hole that the unification did not fill.

**Theorem (Soundness of apply).** Let $h : \forall x,\ A(x) \to B(x)$, and let $t$ be a term with $B(t)$ equal to the goal $G$. If $p$ is a proof of $A(t)$, then $h\ t\ p$ is a proof of $G$.

*Proof.* The term $h\ t$ has the type $A(t) \to B(t)$ by the rule of the application to a universal statement. The term $h\ t\ p$ has the type $B(t)$ by the rule of modus ponens. The type $B(t)$ is the goal $G$, by the choice of $t$. $\square$

So `apply` never makes a false step: the goal $G$ is proved once the new goals are proved. But `apply` can make a step that loses the proof. If $A(t)$ is false, the new goal has no proof, even if $G$ is true. An example: the goal $0 < 2$, with `apply lt_of_lt_of_le` and the hole filled with the bad middle term $-1$, leaves the false goal $0 < -1$.

#### The search of exact? and apply?

The library keeps an index of the conclusions of its lemmas, in a discrimination tree (Chapter 1). For the goal $G$, the tactic `exact?` finds in the index the lemmas whose conclusion can unify with $G$. For each candidate, it tries to unify, and it tries to prove the hypotheses $A_i$ of the lemma with the local hypotheses, with `rfl`, and with a short search of depth limited by a parameter. When all the hypotheses are closed, it prints the term. The tactic `apply?` reports also the candidates with open hypotheses, as partial results with the goals that remain.

The search is complete only with respect to its depth: a proof that needs two lemmas in a chain, or a `rw` before the application, is out of its reach.

#### The search of aesop

**Definition (Safe rule, unsafe rule).** A rule turns a goal into a list of new goals, with a proof of the goal from proofs of the new goals. A rule is safe when, for each goal it applies to, the goal is provable only if all the new goals are provable. A rule is unsafe when it is not known to have this property. The user declares a rule safe or unsafe, and gives an unsafe rule a probability of success.

Examples of safe rules: the introduction of the variable for a goal $\forall x, P(x)$; the split of a goal $P \wedge Q$ into $P$ and $Q$; the split of a hypothesis $h : P \wedge Q$; `simp_all`. An example of an unsafe rule: `apply Set.Subset.trans`, since its middle set is a free choice.

**Theorem (Safe rules lose no proof).** If the goal $G$ is provable and a safe rule turns it into $G_1, \ldots, G_k$, then each $G_i$ is provable.

*Proof.* This is the definition of a safe rule, read as a statement about one step. By induction on the number of steps, the same holds for each sequence of safe steps: if $G$ is provable, all the goals that remain after a sequence of safe steps are provable. $\square$

So `aesop` applies the safe rules first, with no backtracking, since by the theorem they never make the search fail on a provable goal. Then it applies the unsafe rules in a best-first search: it keeps a tree of the open goals, and at each step it expands the goal with the highest product of the probabilities of the unsafe rules on its path. When all the goals of a branch are closed, the search ends with a proof. The search also ends at a limit of rule applications, and then the tactic fails.

::: mathlib
`Order.lt_add_one_iff` · `Mathlib.Algebra.Order.SuccPred`

For an order with a successor where $x + 1$ is the successor of $x$, such as `ℕ` and `ℤ`, $x < y + 1 \iff x \leq y$. This is the lemma that `exact?` finds for `a < b + 1` from `a ≤ b` over `ℕ`. Its name does not start with `Nat`, because it holds for each such order. This is a common reason to use `exact?`: the lemma is in a general form with a name that is hard to guess.

<?decl Order.lt_add_one_iff?>
:::

::: mathlib
`Set.mem_of_subset_of_mem` · `Mathlib.Data.Set.Basic`

From $s \subseteq t$ and $x \in s$, $x \in t$. The term `h hx` proves the same goal, since $s \subseteq t$ unfolds to $\forall x, x \in s \to x \in t$. The tactic `apply?` reports this lemma by its name.

<?decl Set.mem_of_subset_of_mem?>
:::

### How to use it

Write `exact?` at the place of a step that is a lemma of the library. Wait for the message `Try this: exact …`, and replace `exact?` by the suggestion. If `exact?` fails, write `apply?` and read the partial suggestions: the goals that remain show which lemma is close. To guide the search, state the step in the form of the library: `0 ≤ x * y`, not `x * y ≥ 0`, since the library uses `≤` in its conclusions.

Write `aesop` on a goal of logic or of sets: a goal with `∧`, `∨`, `∃`, `→`, `∈`, `∪`, `∩` and `⊆`, where each step is an introduction, a split or a rewrite with a lemma of `simp`. Add a lemma as a rule for one call: `aesop (add safe apply h)` for a rule that loses no proof, or `aesop (add unsafe 50% apply Set.Subset.trans)` for a rule that can lose it. Write `aesop?` to get the proof script that the search found.

### What it cannot do

#### exact? and an identity that needs a rewrite

The tactic `exact?` does not combine lemmas, and it does not rewrite. On `(a + b) * c = c * b + a * c` over `ℕ`, it fails with the message "`exact?` could not close the goal. Try `apply?` to see partial suggestions." The goal is true, but it needs `add_mul`, two uses of `mul_comm` and `add_comm`. Use `ring`.

#### exact? and the form of the goal

The search compares the goal with the conclusions of the lemmas. A goal in an unusual form can have no match. On `x * y ≥ 0` the search unfolds `≥` and finds `Left.mul_nonneg hx hy`, but on a goal with a definition that the library does not use in its statements, the search fails. Unfold the definition first, with `unfold` or `simp only`.

#### aesop and a free middle term

The tactic `aesop` does not invent a middle term. On `s ⊆ u` from `s ⊆ t` and `t ⊆ u`, it fails:

```text
aesop: made no progress
```

The safe rules do not apply: `simp_all` does not know the transitivity of `⊆` as a rewrite. The fix is to give the rule: `aesop (add unsafe apply Set.Subset.trans)`. Then the unification of the conclusion `?a ⊆ ?c` with the goal fills `?a = s` and `?c = u`, and the hypotheses of the context fill the middle term `?b = t`. Or write the proof `exact h1.trans h2`.

#### aesop and arithmetic

The tactic `aesop` has no rules for inequalities, except the lemmas of `simp`. It proves `0 < x ^ 2` from `0 < x`, and `aesop?` shows the script `simp_all only [pow_succ_pos]`, but it does not prove a goal that needs `linarith`. Use `linarith` or `positivity`.

### Examples

**Example (exact? finds a general lemma).** For $a, b \in \mathbb{N}$ with $a \leq b$, $a < b + 1$. The goal state before the call:

```text
a b : ℕ
h : a ≤ b
⊢ a < b + 1
```

The tactic `exact?` prints `Try this: exact Order.lt_add_one_iff.mpr h`. The second example is $b \leq ab$ for $0 < a$, where the search finds a lemma about `ℕ`.

<?lean MathlibHandbook/V34/C04/Examples.lean#exact_search?>

**Example (Other suggestions).** The same search gives `Left.mul_nonneg hx hy` for `0 ≤ x * y` from `0 ≤ x` and `0 ≤ y` over `ℝ`, `exists_between hab` for `∃ c, a < c ∧ c < b` from `a < b`, and `StrictMono.le_apply hf` for `n ≤ f n` with a strictly monotone `f : ℕ → ℕ`. The last one is the theorem that a strictly monotone map of `ℕ` to itself is above the identity. A proof by hand is an induction on $n$: $f(0) \geq 0$, and $f(n + 1) > f(n) \geq n$, so $f(n + 1) \geq n + 1$.

**Example (apply? and a set).** The search of `apply?` gives a lemma of sets by name.

<?lean MathlibHandbook/V34/C04/Examples.lean#apply_search?>

**Example (aesop on logic and sets).** The first goal is the commutativity of `∧`: `aesop` splits the goal into `q` and `p`, and closes each one with a hypothesis. The second goal is the membership in a union: `simp_all` rewrites `x ∈ s ∪ t` to `x ∈ s ∨ x ∈ t`, and the hypothesis closes the left side.

<?lean MathlibHandbook/V34/C04/Examples.lean#aesop?>

**Example (aesop with a function).** From $x \in s$ and $\forall y \in s,\ f(y) \in s$, the element $f(f(x))$ is in $s$. The search applies the hypothesis `hf` two times, with the unsafe rule that `aesop` makes from each local hypothesis.

```lean
example (s : Set ℕ) (f : ℕ → ℕ) (hf : ∀ y ∈ s, f y ∈ s) (x : ℕ) (hx : x ∈ s) :
    f (f x) ∈ s := by
  aesop
```

**Example (A rule for one call).** The transitivity of the inclusion, with the rule given in the call.

```lean
example (s t u : Set ℕ) (h1 : s ⊆ t) (h2 : t ⊆ u) : s ⊆ u := by
  aesop (add unsafe apply Set.Subset.trans)
```

### Exercises

1. (L) Prove `x ∈ s ∪ t` from `x ∈ t` with `aesop` (`mem_union_of_mem_right` in `Exercises.lean`).
2. (A) Use `exact?` to find the name of the lemma $a \leq b \to a + c \leq b + c$ over `ℕ`. Write the term that it suggests.
3. (A) Tell why `exact?` fails on `(a + b) * c = c * b + a * c`, and give a tactic that proves it.
4. (A) Prove $s \cap t \subseteq s \cup t$ for sets of `ℕ` with `aesop`, and then by hand with `intro x hx` and `exact Or.inl hx.1`.
5. (B) Prove the soundness theorem of `apply` for a term $h : \forall x,\ A(x) \to C(x) \to B(x)$ with two hypotheses.
6. (B) Give a goal and a call `apply lt_of_lt_of_le` that turns a true goal into a false goal. Explain why `aesop` must declare this rule unsafe.
7. (B) Prove that a strictly monotone $f : \mathbb{N} \to \mathbb{N}$ satisfies $n \leq f(n)$, by hand, with an induction on $n$.
8. (C) The script that `aesop?` prints for the goal of Exercise 4 is `simp_all only [inf_right_le_sup_right]`. Find the statement of this lemma, and explain why it applies to sets, where `∩` and `∪` are the operations of a lattice.

### Reference

<?reference?>
