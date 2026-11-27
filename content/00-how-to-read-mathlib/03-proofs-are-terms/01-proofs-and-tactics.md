---
title: Proofs and tactics
kind: guide
modules: []
explains: {}
families: []
requires: [V00.C02]
reads_with: ["TPIL", "MIL Ch. 2"]
lean:
  - MathlibHandbook/V00/C03/Examples.lean
  - MathlibHandbook/V00/C03/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Proofs and tactics

### Overview

In Lean, a statement is a type, and a proof of the statement is a term of that type. Lean checks a proof as it checks the type of any term: it does not trust the author, it computes the type of the term and compares it with the statement. A tactic proof is a program that makes the term step by step. This section shows what a term of each logical form is, shows the two forms of proof on the same statements, and lists the axioms that a proof of Mathlib uses. After this section the reader can read a short proof term of Mathlib as a proof in the sense of a textbook.

### Statements are types

**Definition (Proposition, proof).** A *proposition* is a term `p : Prop`. A *proof* of `p` is a term `h : p`. Two proofs of the same proposition are equal, by definition: Lean does not distinguish them.

The last rule is *proof irrelevance*. It means that Mathlib never asks which proof of a fact a term uses, only that there is one. A function that takes a proof as an argument, as `Nat.cast_sub` takes a proof of `m ≤ n`, gives the same value for each proof.

Each logical form has its own kind of proof. The table gives the term for each form.

| Statement | A proof is | Lean syntax |
|---|---|---|
| `p → q` | a function from proofs of `p` to proofs of `q` | `fun hp => ...` |
| `p ∧ q` | a pair of a proof of `p` and a proof of `q` | `⟨hp, hq⟩` |
| `p ∨ q` | a proof of `p` or a proof of `q`, with a tag | `Or.inl hp`, `Or.inr hq` |
| `∀ x, P x` | a function that gives a proof of `P x` for each `x` | `fun x => ...` |
| `∃ x, P x` | a pair of a witness `x` and a proof of `P x` | `⟨t, ht⟩` |
| `¬ p` | a function from proofs of `p` to proofs of `False` | `fun hp => ...` |
| `p ↔ q` | a pair of two functions | `⟨fun hp => ..., fun hq => ...⟩` |
| `True` | the term `trivial` | `trivial` |
| `False` | no term | |

To *use* a proof, apply the reverse operation. A proof `h : p → q` is applied to `hp : p` and gives `h hp : q`. This is the rule of modus ponens. A proof `h : p ∧ q` gives `h.1 : p` and `h.2 : q`. A proof `h : ∀ x, P x` is applied to a term `t` and gives `h t : P t`. A proof of `False` gives a proof of each statement, by `absurd` or `False.elim`. A proof of `p ∨ q` and a proof of `∃ x, P x` are used by cases: the tactic `obtain` or `rcases`, or the function `Or.elim`.

The table is the *correspondence of Curry and Howard*: the rules of natural deduction are the rules of the types of functions and pairs.

### Two forms of the same proof

**Example (A proof as a term).** The term takes the pair `h` and gives the pair of its second and first parts.

<?lean MathlibHandbook/V00/C03/Examples.lean#and_swap_term?>

The type `p ∧ q → q ∧ p` is a type of functions. So the proof starts with `fun h =>`, and `h : p ∧ q`. Then `h.2 : q` and `h.1 : p`, and `⟨h.2, h.1⟩ : q ∧ p`. Lean checks each of these three types.

**Example (A proof by tactics).** The tactic `intro` takes the hypothesis. The tactic `obtain` cuts the pair into its parts. The tactic `exact` gives the final term.

<?lean MathlibHandbook/V00/C03/Examples.lean#and_swap_tactic?>

The two theorems have the same type. Lean stores a term for each of them, and the terms are almost the same: `intro h` makes `fun h =>`, `obtain` makes a match on the pair, and `exact` gives the body. In an editor, the goal view shows the goal after each tactic. Read a tactic proof with the goal view open. Section 3.2 does that in detail.

**Example (An existence proof).** The proof of an existence statement is the pair of a witness and a proof for it. Here the proof for the witness is `rfl`, because `4 * 4` and `16` compute to the same number.

<?lean MathlibHandbook/V00/C03/Examples.lean#exists_term?>

The term `rfl` is a proof of `a = a`. Lean accepts it as a proof of `4 * 4 = 16` because it computes `4 * 4` to `16` first. Section 3.3 explains when such a computation succeeds.

**Example (A proof for all n).** The proof of a statement for all `n` is a function of `n`.

<?lean MathlibHandbook/V00/C03/Examples.lean#forall_term?>

Here `Nat.le_succ` is a lemma of the core library of Lean, with the type `∀ n : ℕ, n ≤ n + 1`. So `fun n => Nat.le_succ n` is the function that sends `n` to the instance of the lemma at `n`. The term `Nat.le_succ` alone is the same proof.

**Example (A chain of steps).** The block `calc` writes a chain of relations. Each step has its own proof, and Lean joins the steps by transitivity.

<?lean MathlibHandbook/V00/C03/Examples.lean#calc_proof?>

The chain is $a \le b < c < c + 1$, and the result is $a < c + 1$. Lean joins `≤` with `<` to give `<` by the lemma `lt_of_le_of_lt`, and `<` with `<` by transitivity of `<`. A `calc` block is the closest form in Lean to a chain of equations on paper.

### Negation and contradiction

Negation is a function to `False`. So a proof of `¬ p` starts with `fun hp =>`, and the body is a proof of `False`.

**Theorem (Non-contradiction).** For each proposition $p$, $\neg(p \wedge \neg p)$.

*Proof.* Suppose $p \wedge \neg p$. Then $p$ holds, and $\neg p$ holds. Apply $\neg p$, which is a function from proofs of $p$ to proofs of `False`, to the proof of $p$. This gives a proof of `False`. $\square$

As a term the proof is `fun h => h.2 h.1`: the argument `h` is the pair, `h.2 : ¬ p` is a function, and `h.1 : p` is its argument.

**Theorem (Contrapositive).** If $p \to q$, then $\neg q \to \neg p$.

*Proof.* Let $f : p \to q$ and $g : \neg q$. To prove $\neg p$, suppose $hp : p$. Then $f(hp) : q$, and $g(f(hp)) :$ `False`. $\square$

As a term the proof is `fun f g hp => g (f hp)`: it is the composition of $f$ and $g$. The core library calls this term `mt`, for *modus tollens*. The converse, from $\neg q \to \neg p$ to $p \to q$, has no such term. Its proof needs the law of the excluded middle, and that law needs an axiom.

### Classical logic and the axioms

The rules of the table give *intuitionistic* logic: a proof of `p ∨ q` names the side, and a proof of `∃ x, P x` names the witness. The law of the excluded middle `p ∨ ¬ p` has no proof in this logic. Mathlib uses classical logic, and it adds three axioms.

1. `propext`: two equivalent propositions are equal. With `propext`, a rewrite with `p ↔ q` changes `p` to `q` inside each statement.
2. `Quot.sound`: the quotient of a type by a relation identifies related elements. From it Lean proves `funext`: two functions with the same values are equal.
3. `Classical.choice`: a nonempty type has an element, chosen with no rule. From it, and from the other two, Lean proves `Classical.em : p ∨ ¬ p`, by the argument of Diaconescu.

So the tactic `by_contra`, which proves `p` from a proof of `False` under `¬ p`, uses `Classical.choice`. A textbook uses the same principle with no comment.

**Definition (Axioms of a proof).** The command `#print axioms name` gives the axioms that the proof of `name` uses, through all the lemmas that it calls.

A proof that uses `sorryAx` is not complete: the tactic `sorry` puts this axiom in place of a missing proof. The companion package checks each example with this command, and it rejects each axiom outside the three.

**Example (The axioms of a classical proof).** The proof of `irrational_sqrt_two` in Mathlib uses all three axioms. The proof of `and_swap_term` above uses none. The output of `#print axioms` for it is the line `'MathlibHandbook.V00.C03.and_swap_term' does not depend on any axioms`.

### Proofs as arguments

A lemma can take a proof as an argument, and a proof can be the result of a function. Induction is an example. The principle of induction on `ℕ` is a function: it takes a proof of the base case and a function that sends a proof of `P n` to a proof of `P (n + 1)`, and it gives a proof of `P n` for each `n`.

::: mathlib
`Nat.strong_induction_on` · `Mathlib.Data.Nat.Init`

The principle of strong induction on `ℕ`. The implicit argument `motive : ℕ → Prop` is the statement to prove, and Lean finds it from the goal. The explicit `n` is the point. The last argument is the step of the induction as a function: for each `n`, a proof of `motive n` from proofs of `motive m` for all `m < n`. It has no separate base case: for `n = 0` the hypothesis `∀ m < 0, motive m` is empty, and the step must prove `motive 0` with no help.

<?decl Nat.strong_induction_on?>
:::

**Example (Strong induction on paper and in Lean).** Every $n \ge 2$ has a prime factor. On paper: if $n$ is prime, it is its own prime factor. Otherwise $n = ab$ with $2 \le a < n$, and $a$ has a prime factor by the hypothesis of the induction, which divides $n$. In Lean the proof is `Nat.strong_induction_on n (fun n ih => ...)`, where `ih : ∀ m < n, 2 ≤ m → ∃ p, p.Prime ∧ p ∣ m` is the hypothesis, and the body makes the case split. The structure of the term is the structure of the paper proof.

### Common errors

1. Writing `h 3` for a hypothesis `h : ∀ x > 0, P x`. The bounded quantifier hides an arrow, so `h 3` has type `3 > 0 → P 3`, and `h 3 (by norm_num)` is the proof of `P 3`.
2. Expecting `⟨4, rfl⟩` to prove a statement on the reals. On `ℝ` the computation does not run, and `rfl` fails on `(2 : ℝ) + 2 = 4`. Use `norm_num`.
3. Using `sorry` and forgetting it. Lean prints a warning `declaration uses 'sorry'`, and `#print axioms` shows `sorryAx`.
4. Proving `p → q` from `¬ q → ¬ p` with `mt`. The term `mt` goes the other way. Use `by_contra` or the lemma `not_imp_not`.

### Exercises

1. (A) Write the type of a proof of `p → (q → p)`. Give the term.
2. (A) Explain why `⟨4, rfl⟩` is not a proof of `∃ n : ℕ, n * n = 15`.
3. (B) Write a proof of `¬ (p ∧ ¬ p)` as a term, and explain each part.
4. (B) Write a term of type `(p → q) → (q → r) → p → r`. Which rule of a textbook is it?
5. (B) Write a term of type `(∃ x, P x) → ¬ (∀ x, ¬ P x)`. Explain why the converse needs classical logic.
6. (C) Prove `p ∨ ¬ p → (¬ ¬ p → p)` with no axiom. Explain why this shows that the law of the excluded middle gives the law of double negation.
7. (L) Prove `MathlibHandbook.V00.C03.Exercises.or_swap_term`, first as a term, then by tactics.
8. (L) Prove `MathlibHandbook.V00.C03.Exercises.exists_add_eq`.
9. (L) Prove `MathlibHandbook.V00.C03.Exercises.le_add_two` with `calc`.

### Notes and history

The identification of statements with types and of proofs with terms is the Curry and Howard correspondence. Haskell Curry saw it for the combinators in 1934, and William Howard wrote it for natural deduction in 1969. The type theory of Lean is the calculus of inductive constructions of Thierry Coquand and Christine Paulin-Mohring. Radu Diaconescu proved in 1975 that the axiom of choice gives the excluded middle in a topos, and the same argument works in Lean. *Theorem Proving in Lean 4* gives the full account in its chapters on propositions and on quantifiers.
