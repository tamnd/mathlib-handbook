---
title: Quantifiers, negation and unique existence
kind: theory
modules:
  - Mathlib.Basic.ExistsUnique
explains:
  E3: [ExistsUnique, not_forall_not]
  E2: [ExistsUnique.intro, ExistsUnique.exists, ExistsUnique.unique, existsUnique_of_exists_of_unique, ExistsUnique.elim, forall_and_left, exists_or_forall_not]
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

## Quantifiers, negation and unique existence

### Overview

Most theorems of analysis and algebra have quantifiers in front: "for every $\varepsilon > 0$ there is a $\delta > 0$ such that ...". A student must be able to negate such a statement correctly, to see which quantifiers commute, and to prove that an object exists and is unique. This section gives the rules for the quantifiers $\forall$ and $\exists$ and for unique existence $\exists!$, with complete proofs of the laws of negation.

In Lean, the quantifiers continue the pattern of the previous section. A proof of $\forall x, p(x)$ is a function that sends each $x$ to a proof of $p(x)$. A proof of $\exists x, p(x)$ is a pair: a witness $a$ and a proof of $p(a)$. A quantifier always ranges over a type, so the domain of the quantifier is part of the statement. The section shows one effect of this that a textbook often hides: some laws fail when the type is empty.

### Definitions

**Definition (Predicate).** Let $\alpha$ be a type. A *predicate* on $\alpha$ is a function $p : \alpha \to \mathrm{Prop}$. For each $a : \alpha$, the value $p(a)$ is a proposition. A *relation* between $\alpha$ and $\beta$ is a function $r : \alpha \to \beta \to \mathrm{Prop}$.

**Definition (The quantifiers).** Let $p$ be a predicate on $\alpha$.

1. The *universal statement* $\forall x : \alpha,\ p(x)$ is the type of functions $h$ that send each $a : \alpha$ to a proof $h(a) : p(a)$. To prove it, fix an arbitrary $a$ and prove $p(a)$. To use it, apply it to an element.
2. The *existential statement* $\exists x : \alpha,\ p(x)$ has as proofs the pairs $\langle a, h \rangle$ with $a : \alpha$ and $h : p(a)$. To prove it, give a witness and a proof for the witness. To use it for a goal $q$ that does not mention the witness, fix a new $a$ with $h : p(a)$ and prove $q$.

The function type in part 1 is a *dependent* function type: the type $p(a)$ of the value depends on the argument $a$. The implication $p \to q$ is the special case in which the value type does not depend on the argument.

*Remark.* The rule for using $\exists$ has a condition: the goal $q$ must not depend on the witness. In Lean, the condition is stronger. An existential statement is a proposition, and Lean does not let a proof of a proposition produce data, such as a natural number. So `obtain ⟨a, ha⟩ := h` works when the goal is a proposition, and it fails when the goal is a definition of a number. To get the witness as data, a proof uses the axiom of choice, as Section 3 shows.

**Definition (Bounded quantifiers).** For a set $s$ of elements of $\alpha$, the statement $\forall x \in s,\ p(x)$ means $\forall x : \alpha,\ x \in s \to p(x)$. The statement $\exists x \in s,\ p(x)$ means $\exists x : \alpha,\ x \in s \land p(x)$.

The implication in the first form and the conjunction in the second form are a common source of errors. The form $\exists x,\ x \in s \to p(x)$ is almost always true and useless: any $x \notin s$ is a witness.

**Definition (Unique existence).** The statement $\exists! x : \alpha,\ p(x)$ means that there is an $a$ with $p(a)$ such that every $y$ with $p(y)$ is equal to $a$:
$$\exists x,\ p(x) \land \forall y,\ p(y) \to y = x.$$

::: mathlib
`ExistsUnique` · `Mathlib.Basic.ExistsUnique`

Mathlib defines `ExistsUnique p` as `∃ x, p x ∧ ∀ y, p y → y = x`, the form of the definition above, and writes it `∃! x, p x`. The introduction rule is `ExistsUnique.intro`: a witness, its property and the uniqueness. The use rules are `ExistsUnique.exists` and `ExistsUnique.unique`. Mathlib uses `∃!` less than a textbook. A theorem often states existence and uniqueness as two lemmas, or it gives the unique object as a definition with a characterizing lemma.

<?decl ExistsUnique?>
:::

### Theorems and proofs

**Theorem (Negation of quantifiers, constructive part).** Let $p$ be a predicate on $\alpha$. Then:

1. $\lnot(\exists x,\ p(x)) \leftrightarrow \forall x,\ \lnot p(x)$;
2. $(\exists x,\ \lnot p(x)) \to \lnot(\forall x,\ p(x))$.

*Proof.* 1. Assume $h : \lnot(\exists x,\ p(x))$. Fix $a$ and assume $b : p(a)$. Then $\langle a, b \rangle$ proves $\exists x,\ p(x)$, and $h$ gives $\mathrm{False}$. So $\lnot p(a)$ holds for every $a$. Conversely, assume $h : \forall x,\ \lnot p(x)$ and $e : \exists x,\ p(x)$. Use $e$: fix $a$ with $b : p(a)$. Then $h(a)(b)$ proves $\mathrm{False}$. The goal $\mathrm{False}$ does not depend on $a$, so the use of $e$ is allowed.

2. Assume $\langle a, n \rangle$ with $n : \lnot p(a)$, and assume $h : \forall x,\ p(x)$. Then $n(h(a))$ proves $\mathrm{False}$. $\square$

**Theorem (Negation of quantifiers, classical part).** Let $p$ be a predicate on $\alpha$. In classical logic, $\lnot(\forall x,\ p(x)) \to \exists x,\ \lnot p(x)$. So $\lnot \forall$ and $\exists \lnot$ are equivalent, and so are $\lnot\exists \lnot$ and $\forall$.

*Proof.* Assume $h : \lnot(\forall x,\ p(x))$. By the elimination of double negation, it suffices to prove $\lnot\lnot(\exists x,\ \lnot p(x))$. Assume $n : \lnot(\exists x,\ \lnot p(x))$. By part 1 of the previous theorem, $n$ gives $\forall x,\ \lnot\lnot p(x)$. By the elimination of double negation again, $p(x)$ holds for every $x$. This contradicts $h$.

For the last claim, apply part 1 of the previous theorem to the predicate $\lnot p$. It gives $\lnot(\exists x,\ \lnot p(x)) \leftrightarrow \forall x,\ \lnot\lnot p(x)$, and the right side is equivalent to $\forall x,\ p(x)$ by the elimination of double negation. $\square$

The rule that results is easy to apply. To negate a statement, move the negation inward. Each $\forall$ becomes $\exists$, each $\exists$ becomes $\forall$, each $\land$ becomes $\lor$, each $\lor$ becomes $\land$, and $\lnot(p \to q)$ becomes $p \land \lnot q$.

::: mathlib
`not_forall_not` · `Mathlib.Basic.Logic.Basic`

The lemma `not_forall_not` states `(¬∀ x, ¬p x) ↔ ∃ x, p x`. Its companions in the core library are `not_exists : (¬∃ x, p x) ↔ ∀ x, ¬p x` and `not_forall : (¬∀ x, p x) ↔ ∃ x, ¬p x`. The tactic `push_neg` uses all of them. It also writes `¬a ≤ b` as `b < a` in a linear order, so the result reads like a textbook statement.

<?decl not_forall_not?>
:::

**Theorem (Order of quantifiers).** Let $r$ be a relation between $\alpha$ and $\beta$. Then $(\exists x,\ \forall y,\ r(x, y)) \to (\forall y,\ \exists x,\ r(x, y))$. The converse fails in general.

*Proof.* Assume $\langle a, h \rangle$ with $h : \forall y,\ r(a, y)$. Fix $b : \beta$. Then $a$ is a witness for $\exists x,\ r(x, b)$, with the proof $h(b)$.

For the converse, take $\alpha = \beta = \mathbb{N}$ and $r(x, y)$ the relation $y < x$. For each $y$ there is an $x$ with $y < x$, namely $x = y + 1$. But no $x$ has $y < x$ for all $y$: the choice $y = x$ gives $x < x$, which is false. $\square$

In the first statement one $x$ works for every $y$. In the second statement $x$ can depend on $y$. This is the difference between uniform convergence and pointwise convergence, and between uniform continuity and continuity.

**Theorem (Quantifiers over an empty type).** Let $\alpha$ be a type with no element, and let $p$ be a predicate on $\alpha$. Then $\forall x,\ p(x)$ is true and $\exists x,\ p(x)$ is false. Also, for a proposition $q$, the equivalence $(\forall x,\ q \land p(x)) \leftrightarrow (q \land \forall x,\ p(x))$ holds for every $q$ if and only if $\alpha$ has an element.

*Proof.* For each $a : \alpha$ there is nothing to prove, since no $a$ exists: formally, the assumption $a : \alpha$ gives $\mathrm{False}$, and ex falso gives $p(a)$. A proof of $\exists x,\ p(x)$ would contain an element of $\alpha$, so there is none.

Assume that $\alpha$ has an element $a_0$. If $h : \forall x,\ q \land p(x)$, then $h(a_0)$ gives $q$, and $h(x)$ gives $p(x)$ for each $x$. The other direction holds for every $\alpha$: from $q$ and $\forall x,\ p(x)$, each $x$ gives $q \land p(x)$. Now assume that $\alpha$ is empty, and take $q = \mathrm{False}$. The left side is true by the first part, and the right side is false. $\square$

::: mathlib
`forall_and_left` · `Mathlib.Basic.Logic.Basic`

The lemma has the hypothesis `[Nonempty α]`, an instance argument that Chapter 5 explains. The theorem above shows that the hypothesis is needed. Many lemmas about quantifiers in Mathlib have such a hypothesis, and a proof must supply it, for example from an element that the proof already has.

<?decl forall_and_left?>
:::

**Theorem (Unique existence).** Let $p$ be a predicate on $\alpha$. Then $\exists! x,\ p(x)$ holds if and only if both

1. $\exists x,\ p(x)$, and
2. $\forall y\ z,\ p(y) \to p(z) \to y = z$.

*Proof.* Assume $\exists! x,\ p(x)$, with witness $a$, $h_a : p(a)$ and $u : \forall y,\ p(y) \to y = a$. Then $\langle a, h_a\rangle$ proves 1. For 2, let $p(y)$ and $p(z)$. Then $u(y)$ gives $y = a$ and $u(z)$ gives $z = a$, so $y = z$ by symmetry and transitivity of equality.

Conversely, assume 1 and 2. Use 1: fix $a$ with $h_a : p(a)$. Then $a$ is a witness for $\exists!$. For each $y$ with $p(y)$, statement 2 applied to $y$ and $a$ gives $y = a$. $\square$

::: mathlib
`existsUnique_of_exists_of_unique` · `Mathlib.Basic.ExistsUnique`

This is the direction from right to left of the theorem. The lemma `ExistsUnique.unique` gives statement 2 from `∃!`. In practice, a proof of `∃! x, p x` starts with `refine ⟨a, ha, fun y hy => ?_⟩`, and the remaining goal is `y = a`.

<?decl existsUnique_of_exists_of_unique?>
:::

### Examples

**Example (Negating a limit).** A sequence $(a_n)$ of real numbers converges to $L$ when
$$\forall \varepsilon > 0,\ \exists N,\ \forall n \geq N,\ |a_n - L| < \varepsilon.$$
Its negation, by the rule after the classical theorem, is
$$\exists \varepsilon > 0,\ \forall N,\ \exists n \geq N,\ |a_n - L| \geq \varepsilon.$$
For $a_n = (-1)^n$ and $L = 1$, take $\varepsilon = 1$. For each $N$, the odd number $n = 2N + 1 \geq N$ has $|a_n - 1| = |-1 - 1| = 2 \geq 1$. So $(a_n)$ does not converge to $1$. In Lean, `push_neg` makes the same change to the hypothesis: from `¬ ∀ ε > 0, ∃ N, ∀ n ≥ N, |a n - L| < ε` it produces `∃ ε > 0, ∀ N, ∃ n ≥ N, ε ≤ |a n - L|`.

**Example (A unique solution).** The statement $\exists! n \in \mathbb{N},\ n + 3 = 5$ holds. For existence, $n = 2$ works, since $2 + 3 = 5$. For uniqueness, if $y + 3 = 5$ and $z + 3 = 5$, then $y + 3 = z + 3$, and the cancellation law of addition on $\mathbb{N}$ gives $y = z$. By the theorem on unique existence, this proves the claim. In contrast, $\exists! n \in \mathbb{N},\ n \cdot 0 = 0$ is false: every $n$ is a solution, and $0 \neq 1$ are two different ones.

**Counterexample (A wrong negation).** A student negates "every continuous function on $[0, 1]$ is bounded" as "every continuous function on $[0, 1]$ is unbounded". The correct negation is "some continuous function on $[0, 1]$ is unbounded". In symbols, $\lnot \forall f,\ (C(f) \to B(f))$ is $\exists f,\ C(f) \land \lnot B(f)$. Both negations are false here, so only the rule, not the truth value, tells them apart.

### The library around it

The core library and `Mathlib.Basic.Logic.Basic` contain the laws of the quantifiers. The names use `forall` and `exists`: `not_exists`, `not_forall`, `forall_and`, `exists_or`, `forall_or_left` and `exists_or_forall_not`. A lemma that needs an element of the domain has the hypothesis `[Nonempty α]`, for example `forall_and_left`. The lemmas `exists_eq_left` and `forall_eq` remove a quantifier over an equation: `(∃ a, a = b ∧ p a) ↔ p b`. The simp set uses them, so `simp` removes many quantifiers.

The module `Mathlib.Basic.ExistsUnique` has about 25 lemmas about `∃!`.

#### Common errors

1. A learner writes `∃ x, x ∈ s → p x` for "some element of $s$ has $p$". The correct form has `∧`.
2. A learner tries `obtain ⟨n, hn⟩ := h` with `h : ∃ n, f n = 0` to define a number. Lean refuses, because the goal is not a proposition. Section 3 shows `Classical.choose`.
3. A learner assumes that a lemma about `∀` holds over an empty type in the same form. Check for a `Nonempty` hypothesis in the statement.

### Exercises

1. (A) Negate the definition of continuity of $f : \mathbb{R} \to \mathbb{R}$ at $a$: $\forall \varepsilon > 0,\ \exists \delta > 0,\ \forall x,\ |x - a| < \delta \to |f(x) - f(a)| < \varepsilon$.
2. (A) Prove $(\forall x,\ p(x) \land q(x)) \leftrightarrow (\forall x,\ p(x)) \land (\forall x,\ q(x))$.
3. (A) Prove $(\exists x,\ p(x) \lor q(x)) \leftrightarrow (\exists x,\ p(x)) \lor (\exists x,\ q(x))$. Show by an example that $\exists$ does not distribute over $\land$ in the same way.
4. (B) Prove that $\exists! x \in \mathbb{R},\ 2x + 1 = 7$, and that $\exists! x \in \mathbb{R},\ x^2 = 4$ is false.
5. (B) Prove classically that $\exists x,\ (p(x) \to \forall y,\ p(y))$ when $\alpha$ has an element. This is the "drinker paradox". Hint: argue by cases on $\forall y,\ p(y)$. Show that the statement is false when $\alpha$ is empty.
6. (B) Show that $\forall x,\ (q \lor p(x)) \leftrightarrow q \lor \forall x,\ p(x)$ holds classically. Say which direction needs the excluded middle.
7. (C) Let $r$ be a relation on $\alpha$. Prove that $\lnot \exists x,\ \forall y,\ (r(x, y) \leftrightarrow \lnot r(y, y))$. Use it to show that no barber shaves exactly those men who do not shave themselves. Section 2 of Chapter 3 uses the same argument for Cantor's theorem.
8. (L) Prove that if not every natural number fails `P`, then some number has `P`. The solution is `exists_of_not_forall_not_example` in `Solutions.lean`.

### Notes and history

The quantifiers in their modern form are due to Frege (1879) and to Peirce (1885), who introduced the symbols that became $\forall$ and $\exists$ in the work of Peano and of Gentzen. The paradox of the barber, in Exercise 7, is a popular form of the paradox of Russell (1901). The book *Mathematics in Lean*, Chapter 3, has many exercises with quantifiers and `push_neg`.

### Reference

<?reference?>
