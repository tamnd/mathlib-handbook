---
title: Propositions, proofs and classical logic
kind: theory
modules:
  - Mathlib.Basic.Logic.Basic
explains:
  E3: [em, by_contra]
  E2: [by_cases, of_not_not, peirce, Function.mt, not_and_or, imp_iff_not_or]
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

## Propositions, proofs and classical logic

### Overview

A course in mathematics uses logic long before it names it. A proof of "if $n$ is even, then $n^2$ is even" assumes that $n$ is even and derives that $n^2$ is even. A proof by contradiction assumes the negation of the goal and derives an absurdity. This section makes these habits precise. It gives the rules for the connectives "and", "or", "not", "implies" and "if and only if", and it shows which rules hold in every logic and which rules need the law of the excluded middle.

Lean adds one more idea, and it is the base of the whole library. A proposition is a type, and a proof of the proposition is a term of that type. To prove $p \to q$ is to give a function that sends each proof of $p$ to a proof of $q$. To prove $p \land q$ is to give a pair. This reading is called *propositions as types*. It explains the form of almost every statement and proof in Mathlib.

The main results of the section are the laws of De Morgan, the law of contraposition and the equivalence of three classical principles: the excluded middle, the elimination of double negation, and the law of Peirce.

### Definitions

**Definition (Proposition and proof).** A *proposition* is a statement that can be true or false. In Lean, a proposition is a term `p : Prop`, and `p` is itself a type. A *proof* of `p` is a term `h : p`. The proposition `p` is *true* when some term of type `p` exists.

Two proofs of the same proposition are equal in Lean. This rule is called *proof irrelevance*. It says that a proof carries no information beyond the fact that the proposition is true.

**Definition (The connectives).** Let $p$ and $q$ be propositions.

1. The *implication* $p \to q$ is the type of functions from proofs of $p$ to proofs of $q$.
2. The *conjunction* $p \land q$ is the type of pairs $\langle h_1, h_2 \rangle$ with $h_1 : p$ and $h_2 : q$.
3. The *disjunction* $p \lor q$ has two kinds of proofs: $\mathrm{inl}(h)$ with $h : p$, and $\mathrm{inr}(h)$ with $h : q$.
4. The proposition $\mathrm{False}$ has no proof. The proposition $\mathrm{True}$ has exactly one proof.
5. The *negation* $\lnot p$ is the implication $p \to \mathrm{False}$.
6. The *equivalence* $p \leftrightarrow q$ is the conjunction of $p \to q$ and $q \to p$.

Each connective has rules to *introduce* it and rules to *use* it. To prove $p \land q$, prove $p$ and prove $q$. To use $h : p \land q$, take its two parts. To prove $p \lor q$, prove one of the two sides. To use $h : p \lor q$ for a goal $r$, prove $r$ from $p$ and prove $r$ from $q$: this is a proof by cases. To prove $p \to q$, assume $p$ and prove $q$. To use $h : p \to q$, apply it to a proof of $p$; this rule is *modus ponens*. From a proof of $\mathrm{False}$, every proposition follows; this rule is called *ex falso*.

*Remark.* The definition of $\lnot p$ as $p \to \mathrm{False}$ has a direct consequence. To prove $\lnot p$, assume $p$ and derive a contradiction. This is not a proof by contradiction in the classical sense. It is the introduction rule of the negation, and it holds in every logic. A proof by contradiction proves $p$ itself from the assumption $\lnot p$, and that step needs more.

::: mathlib
`Function.mt` · `Mathlib.Basic.Logic.Basic`

The rule of contraposition has the name `Function.mt`, for *modus tollens*. Its statement is `(a → b) → ¬b → ¬a`. Because `¬b` is a function to `False`, the proof is the composite of two functions: `fun h hb ha => hb (h ha)`. With dot notation, a proof `h : a → b` gives `h.mt : ¬b → ¬a`.

<?decl Function.mt?>
:::

**Definition (Classical principles).** The *law of the excluded middle* says that $p \lor \lnot p$ holds for every proposition $p$. The *elimination of double negation* says that $\lnot\lnot p \to p$ holds for every $p$. The *law of Peirce* says that $((p \to q) \to p) \to p$ holds for all $p$ and $q$.

A logic that uses only the rules of the connectives is *intuitionistic* or *constructive*. A logic that also accepts one of the classical principles is *classical*. Theorem (Three classical principles) below shows that the three principles are equivalent, so a classical logic accepts all three.

::: mathlib
`em` · `Mathlib.Basic.Logic.Basic`

The excluded middle is `em p : p ∨ ¬p`, with the same content as `Classical.em` of the core library. The core of Lean is constructive, and it proves `Classical.em` from the axiom of choice. Section 3 of this chapter gives that proof. A Mathlib user does not need to think about the axiom: the excluded middle is available in every proof.

<?decl em?>
:::

### Theorems and proofs

The first theorems hold in intuitionistic logic. Their proofs use only the rules of the connectives.

**Theorem (Contraposition).** For all propositions $p$ and $q$, $(p \to q) \to (\lnot q \to \lnot p)$.

*Proof.* Assume $h : p \to q$ and $h' : \lnot q$. The goal $\lnot p$ is $p \to \mathrm{False}$, so assume $a : p$. Then $h(a)$ is a proof of $q$, and $h'(h(a))$ is a proof of $\mathrm{False}$. So $\lnot p$ holds. $\square$

**Theorem (Double negation introduction).** For every proposition $p$, $p \to \lnot\lnot p$. Also $\lnot\lnot\lnot p \leftrightarrow \lnot p$.

*Proof.* Assume $a : p$. The goal $\lnot\lnot p$ is $(p \to \mathrm{False}) \to \mathrm{False}$. Assume $n : \lnot p$. Then $n(a)$ is a proof of $\mathrm{False}$. This proves the first claim.

For the second claim, the direction $\lnot p \to \lnot\lnot\lnot p$ is the first claim applied to the proposition $\lnot p$. For the other direction, assume $t : \lnot\lnot\lnot p$ and $a : p$. By the first claim, $a$ gives a proof $d : \lnot\lnot p$. Then $t(d)$ is a proof of $\mathrm{False}$. So $\lnot p$ holds. $\square$

**Theorem (De Morgan, constructive part).** For all propositions $p$ and $q$:

1. $\lnot(p \lor q) \leftrightarrow \lnot p \land \lnot q$;
2. $(\lnot p \lor \lnot q) \to \lnot(p \land q)$.

*Proof.* 1. Assume $h : \lnot(p \lor q)$. If $a : p$, then $\mathrm{inl}(a)$ proves $p \lor q$, and $h(\mathrm{inl}(a))$ proves $\mathrm{False}$. So $\lnot p$ holds. In the same way, $\lnot q$ holds. Conversely, assume $\lnot p$ and $\lnot q$, and assume $p \lor q$. Argue by cases. A proof of $p$ contradicts $\lnot p$, and a proof of $q$ contradicts $\lnot q$. In both cases $\mathrm{False}$ follows.

2. Assume $\lnot p \lor \lnot q$ and $\langle a, b \rangle : p \land q$. In the first case, $\lnot p$ applied to $a$ gives $\mathrm{False}$. In the second case, $\lnot q$ applied to $b$ gives $\mathrm{False}$. $\square$

The converse of part 2 is the classical half of the laws of De Morgan. The next theorem shows that classical logic is one principle, in three forms.

**Theorem (Three classical principles).** The following are equivalent, where each statement is quantified over all propositions:

1. the excluded middle, $p \lor \lnot p$;
2. the elimination of double negation, $\lnot\lnot p \to p$;
3. the law of Peirce, $((p \to q) \to p) \to p$.

*Proof.* The proof shows $1 \Rightarrow 2 \Rightarrow 3 \Rightarrow 1$.

$1 \Rightarrow 2$. Assume $d : \lnot\lnot p$. By the excluded middle, $p$ or $\lnot p$ holds. If $p$ holds, the goal is proved. If $n : \lnot p$, then $d(n)$ proves $\mathrm{False}$, and ex falso gives $p$.

$2 \Rightarrow 3$. Assume $h : (p \to q) \to p$. By 2, it suffices to prove $\lnot\lnot p$. So assume $n : \lnot p$, and derive $\mathrm{False}$. First, $p \to q$ holds: from $a : p$, the term $n(a)$ proves $\mathrm{False}$, and ex falso gives $q$. Then $h$ applied to this implication gives a proof of $p$, and $n$ applied to it gives $\mathrm{False}$.

$3 \Rightarrow 1$. Fix $p$, and let $r = p \lor \lnot p$. Apply the law of Peirce to $r$ and $q = \mathrm{False}$. It says $((r \to \mathrm{False}) \to r) \to r$, so it suffices to prove $\lnot r \to r$. Assume $n : \lnot r$. Then $\lnot p$ holds: from $a : p$, the term $\mathrm{inl}(a)$ proves $r$, and $n$ gives $\mathrm{False}$. So $\mathrm{inr}$ of this proof is a proof of $r$. $\square$

The proof of $3 \Rightarrow 1$ uses the principle for a proposition $r$ that differs from $p$. So the equivalence holds for the principles as schemes over all propositions. It does not say that $\lnot\lnot p \to p$ for one fixed $p$ gives $p \lor \lnot p$ for the same $p$.

::: mathlib
`by_contra` · `Mathlib.Basic.Logic.Basic`

Mathlib states the elimination of double negation in three forms. The lemma `of_not_not` is `¬¬a → a`. The lemma `by_contra` is `(¬p → False) → p`, which is the same statement with the negation unfolded. The tactic `by_contra h` applies it: the hypothesis `h : ¬p` appears and the goal becomes `False`. The law of Peirce is `peirce`.

<?decl by_contra?>
:::

**Theorem (Classical laws).** In classical logic, for all propositions $p$ and $q$:

1. $\lnot(p \land q) \leftrightarrow \lnot p \lor \lnot q$;
2. $(p \to q) \leftrightarrow \lnot p \lor q$;
3. $(\lnot q \to \lnot p) \to (p \to q)$.

*Proof.* 1. The direction from right to left is the constructive part of De Morgan. For the other direction, assume $h : \lnot(p \land q)$. By the excluded middle for $p$, there are two cases. If $\lnot p$ holds, then $\lnot p \lor \lnot q$ holds. If $a : p$, then $\lnot q$ holds: from $b : q$, the pair $\langle a, b\rangle$ and $h$ give $\mathrm{False}$. So again $\lnot p \lor \lnot q$ holds.

2. Assume $h : p \to q$. By the excluded middle for $p$: if $a : p$, then $h(a)$ proves $q$, so the right side holds; if $\lnot p$, the right side holds too. Conversely, assume $\lnot p \lor q$ and $a : p$. In the first case, $\lnot p$ and $a$ give $\mathrm{False}$, and ex falso gives $q$. In the second case, $q$ holds.

3. Assume $h : \lnot q \to \lnot p$ and $a : p$. By the elimination of double negation, it suffices to prove $\lnot\lnot q$. Assume $n : \lnot q$. Then $h(n)$ is a proof of $\lnot p$, and $h(n)(a)$ proves $\mathrm{False}$. $\square$

::: mathlib
`not_and_or` · `Mathlib.Basic.Logic.Basic`

The names of the classical laws read the statement from left to right: `not_and_or` is `¬(a ∧ b) ↔ ¬a ∨ ¬b`, and `imp_iff_not_or` is `(a → b) ↔ ¬a ∨ b`. The constructive laws `not_or` and `not_and` are in the core library. The tactic `push_neg` applies these lemmas from the outside in, so a negated statement becomes a statement with the negations on the atoms.

<?decl not_and_or?>
:::

### Examples

**Example (A truth table).** In classical logic, a proposition built from $p$ and $q$ has a truth value for each of the four cases. The table computes $p \to q$ and $\lnot p \lor q$.

| $p$ | $q$ | $p \to q$ | $\lnot p$ | $\lnot p \lor q$ |
|---|---|---|---|---|
| true | true | true | false | true |
| true | false | false | false | false |
| false | true | true | true | true |
| false | false | true | true | true |

The two columns agree, as Theorem (Classical laws), part 2, says. The table is a proof in classical logic only: it uses the fact that each proposition is true or false, which is the excluded middle.

**Example (The excluded middle in Lean).** The term `Classical.em p` proves `p ∨ ¬p` for any proposition `p`. The proof has no content beyond the axiom, so it gives no way to tell which side holds.

<?lean MathlibHandbook/V01/C01/Examples.lean#em?>

**Example (A proof by contradiction in Lean).** The tactic `by_contra hp` adds `hp : ¬p` and asks for `False`. The hypothesis `h : ¬¬p` is a function from `¬p` to `False`, so `h hp` closes the goal.

<?lean MathlibHandbook/V01/C01/Examples.lean#by_contra?>

**Example (A negation is not a proof by contradiction).** The standard proof that $\sqrt 2$ is irrational assumes $\sqrt 2 = a/b$ with integers $a, b$ and $b \neq 0$, and derives a contradiction. Its conclusion is a negation: "$\sqrt 2$ is not rational". So the proof is the introduction rule of $\lnot$, and it is valid in intuitionistic logic. The usual proof that there are infinitely many primes starts with "assume there are finitely many primes", but its goal is not a negation. A direct proof exists: for each $n$, a prime factor of $n! + 1$ is larger than $n$.

**Counterexample (Contraposition in the other direction).** The step $(\lnot q \to \lnot p) \to (p \to q)$ of Theorem (Classical laws), part 3, needs a classical principle. From part 3 with $p$ replaced by $\mathrm{True}$ and $q$ by an arbitrary $r$, the hypothesis $\lnot r \to \lnot\mathrm{True}$ holds as soon as $\lnot\lnot r$ holds, and the conclusion $\mathrm{True} \to r$ gives $r$. So part 3 implies the elimination of double negation. Since intuitionistic logic does not prove the elimination of double negation for every proposition, it does not prove part 3 either.

### The library around it

The module `Mathlib.Basic.Logic.Basic` has about 250 lemmas about the connectives. The names follow the statement: `not_and_or`, `imp_iff_not_or`, `not_imp_not`, `not_iff_not` and `or_iff_not_imp_left`. Many lemmas come in pairs. A lemma with the prefix `Decidable.` proves a classical law for a decidable proposition with no axiom; Section 3 explains decidability. A lemma with no prefix uses the excluded middle. The lemma `by_cases` is the proof by cases on `p ∨ ¬p`: from `p → q` and `¬p → q` it gives `q`. The tactic of the same name, `by_cases h : p`, splits a proof into the two cases.

The tactics follow the introduction and use rules. The tactic `intro` introduces an implication or a negation. The tactic `constructor` splits a goal `p ∧ q` or `p ↔ q`. The tactics `left` and `right` choose a side of `p ∨ q`. The tactic `obtain ⟨h₁, h₂⟩ := h` takes a conjunction apart, and `rcases h with h₁ | h₂` argues by cases on a disjunction.

#### Common errors

1. A learner writes `by_contra` to prove a negation `¬p`. This works, but `intro hp` is the direct step, and it does not use the axiom.
2. A learner reads `¬p` as a primitive. It is the function type `p → False`, so `h hp` applies a negation `h : ¬p` to a proof `hp : p` and gives `False`.
3. A learner confuses `↔` with `=` for propositions. Both are true for equivalent propositions in Lean, by the axiom of propositional extensionality, but `rw` with an `↔` lemma is the normal way to rewrite.

### Exercises

1. (A) Prove $(p \land q) \to (q \land p)$ and $(p \lor q) \to (q \lor p)$ with the rules of the connectives. Say which rule each step uses.
2. (A) Prove $(p \to q) \to (q \to r) \to (p \to r)$. Write the proof term as a function.
3. (A) Prove $\lnot\lnot p \to p$ on paper from the excluded middle. Name the step that uses the excluded middle.
4. (B) Prove intuitionistically that $\lnot\lnot(p \lor \lnot p)$ holds. Hint: assume $n : \lnot(p \lor \lnot p)$, and use De Morgan to get $\lnot p$ and $\lnot\lnot p$.
5. (B) Prove intuitionistically that $(p \to q) \to (\lnot\lnot p \to \lnot\lnot q)$.
6. (B) Prove classically that $(p \to q) \lor (q \to p)$ for all $p$ and $q$. Hint: argue by cases on $q$.
7. (C) Show that the scheme $\lnot(p \land q) \to (\lnot p \lor \lnot q)$, for all $p$ and $q$, implies the scheme $\lnot p \lor \lnot\lnot p$. This scheme is weaker than the excluded middle, and it is known as the law of the weak excluded middle.
8. (L) Prove `¬¬p ↔ p` in Lean. The solution is `not_not_example` in `Solutions.lean`.

### Notes and history

The rules for the connectives in the form of introduction and use are due to Gentzen (1935), who called the system *natural deduction*. Heyting gave the formal rules of intuitionistic logic in 1930. Curry (1934) and Howard (1969) saw that the rules of the connectives are the typing rules of a functional language, and this observation is now called the Curry-Howard correspondence. Lean takes it from the calculus of constructions of Coquand and Huet (1988). The book *Theorem Proving in Lean 4*, Chapter 3, gives the same rules with Lean syntax.

### Reference

<?reference?>
