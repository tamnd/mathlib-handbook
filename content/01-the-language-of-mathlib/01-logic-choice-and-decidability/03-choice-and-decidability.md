---
title: Choice and decidability
kind: theory
modules:
  - Mathlib.Data.Bool.Basic
explains:
  E3: [Classical.axiom_of_choice, Classical.dec]
  E2: [dec_em, Classical.decPred, Classical.decEq, Classical.some_spec₂, Classical.prop_complete, Bool.decide_iff, Classical.existsCases]
  E1: auto
families: []
requires: [V00]
reads_with: ["TPIL", "MIL"]
lean:
  - MathlibHandbook/V01/C01/Examples.lean
  - MathlibHandbook/V01/C01/Exercises.lean
  - MathlibHandbook/V01/C01/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Choice and decidability

### Overview

The first section of this chapter used the law of the excluded middle as a principle. In Lean, the law is not an axiom. It is a theorem, and its proof uses three axioms: propositional extensionality, the soundness of quotients and the axiom of choice. This section states the three axioms, proves the axiom of choice in its usual form, and gives the complete proof of the theorem of Diaconescu, which derives the excluded middle from choice.

The second topic is decidability. A proposition is *decidable* when an algorithm tells whether it is true. In Lean, decidability is data: a term of the type `Decidable p` is either a proof of $p$ or a proof of $\lnot p$, and the program can look at which one it is. An expression `if p then a else b` needs such a term. The section shows how Lean finds it, how `decide` uses it to prove statements by computation, and how Mathlib makes every proposition decidable by the axiom of choice when no algorithm is needed.

### Definitions

**Definition (The three axioms).** Lean has a small kernel with three axioms beyond its type theory.

1. *Propositional extensionality* (`propext`): if $p \leftrightarrow q$, then $p = q$ as propositions.
2. *Quotient soundness* (`Quot.sound`): if $r(a, b)$, then the classes of $a$ and $b$ in the quotient by $r$ are equal. Section 4 of Chapter 3 uses it, and it implies *function extensionality*: if $f(x) = g(x)$ for all $x$, then $f = g$.
3. *Choice* (`Classical.choice`): from a proof of `Nonempty α`, there is an element of $\alpha$.

The type `Nonempty α` is a proposition. It states that $\alpha$ has an element, and it does not name one. Choice takes the statement and gives a specific element. This is the only step in Lean that goes from a proposition back to data.

**Definition (Choice function).** Let $h : \exists x : \alpha,\ p(x)$. The term `Classical.choose h` is an element of $\alpha$, and `Classical.choose_spec h` is a proof of $p(\texttt{Classical.choose}\ h)$. Both come from `Classical.choice`, applied to the type of pairs $\{x \mid p(x)\}$, which is nonempty by $h$.

A definition that uses `Classical.choose` has no algorithm, and Lean marks it `noncomputable`. Its value exists, and theorems about it are proved from `choose_spec`. Lean cannot evaluate it.

**Definition (Decidable proposition).** For a proposition $p$, the type `Decidable p` has two constructors: `isTrue h` with $h : p$, and `isFalse h` with $h : \lnot p$. A term of `Decidable p` is a *decision procedure* for $p$. A predicate $q$ on $\alpha$ is decidable (`DecidablePred q`) when each $q(a)$ is decidable. The type $\alpha$ has decidable equality (`DecidableEq α`) when each $a = b$ is decidable.

`Decidable` is a class. Lean finds its terms by instance search, as Chapter 4 explains. The library has instances for equality and order on $\mathbb{N}$, $\mathbb{Z}$ and $\mathbb{Q}$, for divisibility on $\mathbb{N}$, for the connectives of decidable propositions, and for bounded quantifiers such as $\forall n < 10$.

**Definition (Conditional expression).** For a decidable $p$ and terms $a, b : \beta$, the term `if p then a else b` is $a$ when the instance is `isTrue`, and $b$ when it is `isFalse`. The *dependent* form `if h : p then a h else b h` gives the branches the proof $h : p$ or $h : \lnot p$.

**Definition (Classical decidability).** The definition `Classical.dec p` is a term of `Decidable p` for every proposition $p$. It uses the excluded middle and choice. It is noncomputable.

::: mathlib
`Classical.dec` · `Mathlib.Basic.Logic.Basic`

`Classical.dec p : Decidable p` holds for every `p`. Its forms for predicates and for equality are `Classical.decPred` and `Classical.decEq`. The command `open Classical` makes them instances with a low priority, so an `if` on any proposition elaborates. Mathlib prefers the tactic `classical` inside a proof to `open Classical` around a definition, because a classical instance in a statement can differ from the instance that a user supplies later.

<?decl Classical.dec?>
:::

### Theorems and proofs

**Theorem (Axiom of choice).** Let $r$ be a relation between $\alpha$ and the types $\beta(x)$. If for each $x$ there is a $y$ with $r(x, y)$, then there is a function $f$ with $r(x, f(x))$ for every $x$.

*Proof.* Let $h : \forall x,\ \exists y,\ r(x, y)$. Define $f(x) = \texttt{Classical.choose}\ (h\ x)$. Then $\texttt{Classical.choose\_spec}\ (h\ x)$ proves $r(x, f(x))$. So $f$ is a witness for the statement. $\square$

::: mathlib
`Classical.axiom_of_choice` · `Mathlib.Basic.Logic.Basic`

The statement is `(∀ x, ∃ y, r x y) → ∃ f : (x : α) → β x, ∀ x, r x (f x)`. The conclusion is a proposition, so the lemma is a theorem and not a definition. When a proof needs the function itself, it uses `Classical.choose` directly, or the tactic `choose f hf using h`, which introduces `f` and `hf : ∀ x, r x (f x)`.

<?decl Classical.axiom_of_choice?>
:::

**Theorem (Diaconescu).** Propositional extensionality, function extensionality and choice imply the law of the excluded middle: for every proposition $p$, $p \lor \lnot p$.

*Proof.* Fix $p$. Define two predicates on the type $\mathrm{Bool} = \{\mathrm{true}, \mathrm{false}\}$:
$$U(x) := (x = \mathrm{true}) \lor p, \qquad V(x) := (x = \mathrm{false}) \lor p.$$
Both are satisfied by some element: $U(\mathrm{true})$ and $V(\mathrm{false})$ hold. By choice, let $u$ be an element with $U(u)$ and $v$ an element with $V(v)$, chosen as $u = c(U)$ and $v = c(V)$ for one choice function $c$ on nonempty predicates.

The proof has cases on $U(u)$ and $V(v)$.

1. If $p$ holds in one of the two, then $p \lor \lnot p$ holds.
2. Otherwise $u = \mathrm{true}$ and $v = \mathrm{false}$, so $u \neq v$. The claim is now $\lnot p$. Assume $p$. Then $U(x)$ and $V(x)$ are both true for every $x$, so $U(x) \leftrightarrow V(x)$. By propositional extensionality $U(x) = V(x)$ for each $x$, and by function extensionality $U = V$. So $c(U) = c(V)$, that is, $u = v$. This contradicts $u \neq v$. So $\lnot p$.

In both cases $p \lor \lnot p$ holds. $\square$

The proof needs that $c$ is a function: equal arguments give equal values. In the proof of Lean, the predicates carry proofs that they are nonempty, and proof irrelevance makes these proofs equal. Lean's own proof of `Classical.em` follows this argument.

**Theorem (Decidability of the excluded middle).** If $p$ is decidable, then $p \lor \lnot p$ holds without any axiom.

*Proof.* A term of `Decidable p` is `isTrue h` or `isFalse h`. In the first case $h$ proves $p$, and in the second case $h$ proves $\lnot p$. $\square$

::: mathlib
`dec_em` · `Mathlib.Basic.Logic.Basic`

The lemma states `[Decidable p] : p ∨ ¬p`. It uses no axiom. The general `em` uses the three axioms. The command `#print axioms` shows which axioms a theorem uses. For most theorems of Mathlib the answer is `propext`, `Classical.choice` and `Quot.sound`.

<?decl dec_em?>
:::

**Theorem (Propositions are true or false).** In classical logic, every proposition $p$ is equal to $\mathrm{True}$ or to $\mathrm{False}$.

*Proof.* By the excluded middle, $p$ or $\lnot p$. If $p$, then $p \leftrightarrow \mathrm{True}$, and propositional extensionality gives $p = \mathrm{True}$. If $\lnot p$, then $p \leftrightarrow \mathrm{False}$, since both sides imply everything, and propositional extensionality gives $p = \mathrm{False}$. $\square$

This is `Classical.prop_complete`. It shows that $\mathrm{Prop}$ has exactly two elements up to equality in classical logic, although it is a type of types.

**Theorem (Correctness of decide).** Let $p$ be decidable, and let $\texttt{decide}\ p$ be the Boolean value of the instance: $\mathrm{true}$ for `isTrue`, $\mathrm{false}$ for `isFalse`. Then $\texttt{decide}\ p = \mathrm{true} \leftrightarrow p$.

*Proof.* Take cases on the instance. If it is `isTrue h`, then the left side holds by definition, and $h$ proves $p$. If it is `isFalse h`, then the left side is $\mathrm{false} = \mathrm{true}$, which is false, and $p$ is false by $h$. So both sides are false. $\square$

::: mathlib
`Bool.decide_iff` · `Mathlib.Data.Bool.Basic`

The tactic `decide` uses this theorem. It evaluates `decide p` in the kernel. If the value is `true`, then the theorem gives a proof of `p`. The evaluation fails when an instance is classical, because the kernel cannot evaluate `Classical.choice`. It is also slow when the computation is large.

<?decl Bool.decide_iff?>
:::

### Examples

**Example (A choice of witness).** Let $f : \mathbb{N} \to \mathbb{N}$ have a zero, so $h : \exists n,\ f(n) = 0$. Then `Classical.choose h` is a natural number, and `Classical.choose_spec h` states that $f$ vanishes at it. Nothing says which zero it is. If $f$ has the zeros $3$ and $7$, the chosen one can be either, and no proof can find out. For the least zero, Mathlib has `Nat.find`, which searches $0, 1, 2, \ldots$ and needs a decidable predicate.

<?lean MathlibHandbook/V01/C01/Examples.lean#choose?>

**Example (Proof by computation).** The statement $2^{10} = 1024 \land 7 \nmid 100$ is decidable. Equality on $\mathbb{N}$ is decidable, divisibility on $\mathbb{N}$ is decidable, and the connectives keep decidability. So `decide` evaluates both parts and proves the conjunction.

<?lean MathlibHandbook/V01/C01/Examples.lean#decide?>

**Example (A conditional on a decidable test).** The expression `if n = 0 then 1 else n` is never $0$. The instance comes from decidable equality on $\mathbb{N}$. The tactic `split_ifs with h` makes two goals, one with $h : n = 0$ and one with $h : n \neq 0$.

<?lean MathlibHandbook/V01/C01/Examples.lean#dite?>

**Example (A classical conditional).** For an arbitrary proposition $p$, no algorithm decides $p$. With `open Classical`, the instance `Classical.dec p` makes `if p then 1 else 0` a valid term, and the proof works by cases as before.

<?lean MathlibHandbook/V01/C01/Examples.lean#classical_if?>

**Counterexample (A function that Lean cannot evaluate).** Define $g : \mathbb{N} \to \mathbb{N}$ by $g(n) = 1$ if the Goldbach conjecture holds and $g(n) = 0$ otherwise. In classical mathematics, $g$ is a function: it is constant, and it is one of the two constant functions. In Lean, `if Goldbach then 1 else 0` needs `Classical.dec`, and the definition must be `noncomputable`. Lean cannot evaluate $g(0)$, because that would decide the conjecture. A theorem about $g$, such as $g(0) \leq 1$, still has a proof by cases.

### The library around it

The core library defines `Classical.choice`, `Classical.choose`, `Classical.em` and `Decidable`. The module `Mathlib.Basic.Logic.Basic` adds the classical forms of the laws in Section 1, the definitions `Classical.dec`, `Classical.decPred`, `Classical.decEq` and `Classical.decRel`, and the lemmas `Classical.some_spec₂` and `Classical.existsCases`. The library note `LibraryNote.decidable_arguments` gives the rule for statements: a lemma takes `[DecidableEq α]` as an argument and does not use a classical instance inside its statement.

The tactic `classical` at the start of a proof adds the classical instances for that proof only. It is the normal way to use an `if` on an arbitrary proposition in a proof. The tactic `decide` proves closed decidable goals.

#### Common errors

1. A learner writes `def f (x : ℝ) : ℕ := if x = 0 then 0 else 1` and gets an error. Equality on $\mathbb{R}$ is not decidable. The fix is `noncomputable def` with `open Classical`, or the tactic `classical` in a proof.
2. A learner uses `decide` on a goal with a free variable, such as `n + 0 = n`. The tactic needs a closed goal. Use `simp` or a lemma.
3. A learner gets two different instances of `Decidable p`, one classical and one from the library, and a rewrite fails. The lemma `Subsingleton.elim` proves that any two instances are equal, and the tactic `congr` often closes the goal.

### Exercises

1. (A) Prove from `Decidable p` and `Decidable q` that $p \to q$ is decidable. Write the four cases.
2. (A) Explain why `decide` proves $3 \mid 123$ but cannot prove $\forall n,\ 2 \mid n(n + 1)$.
3. (B) Let $h : \forall x : \alpha,\ \exists y : \beta,\ r(x, y)$. Use the axiom of choice to show that there is $f : \alpha \to \beta$ with $\forall x,\ r(x, f(x))$, and then show $\exists y,\ r(a, y)$ for a given $a$ without choice.
4. (B) Prove the converse of the choice theorem: if $f$ satisfies $r(x, f(x))$ for every $x$, then $\forall x,\ \exists y,\ r(x, y)$. No axiom is needed.
5. (B) Prove `Classical.some_spec₂`: if $h : \exists a,\ p(a)$ and every $a$ with $p(a)$ has $q(a)$, then $q(\texttt{Classical.choose}\ h)$.
6. (C) In the proof of Diaconescu, find where each of the three axioms is used. Explain why the proof fails if $c$ may give different values on equal arguments.
7. (C) Show that if every proposition is decidable by a computable procedure, then the halting problem is solvable. Conclude that `Classical.dec` cannot be computable.
8. (L) Prove that $3$ divides $123$ by computation. The solution is `three_dvd_example` in `Solutions.lean`.

### Notes and history

Zermelo stated the axiom of choice in 1904 to prove the well-ordering theorem. Diaconescu proved in 1975 that choice implies the excluded middle in a topos, and Goodman and Myhill gave the form for set theory in 1978. The idea that a constructive proof of an existence statement is an algorithm comes from Brouwer, Heyting and Kolmogorov, and the notion of a decidable predicate comes from the work of Church and Turing on computability (1936).

### Reference

<?reference?>
