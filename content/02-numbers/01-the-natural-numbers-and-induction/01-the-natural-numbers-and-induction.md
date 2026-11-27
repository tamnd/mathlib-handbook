---
title: The natural numbers and induction
kind: theory
modules:
  - Mathlib.Data.Nat.Init
explains:
  E3: [Nat.le_induction, Nat.strong_induction_on]
  E2: [Nat.twoStepInduction, Nat.case_strong_induction_on, Nat.rec_zero, Nat.rec_add_one, Nat.diag_induction]
  E1: auto
families: []
requires: [V01.C05]
reads_with: ["MIL", "TPIL"]
lean:
  - MathlibHandbook/V02/C01/Examples.lean
  - MathlibHandbook/V02/C01/Exercises.lean
  - MathlibHandbook/V02/C01/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The natural numbers and induction

### Overview

This section starts from the axioms of Dedekind and Peano, defines addition and multiplication by recursion, and proves the laws of arithmetic. Then it proves, from ordinary induction, the forms of induction in daily use: induction from a start value, strong induction and induction in two steps. In Lean, `ℕ` is an inductive type and induction is its eliminator, so a proof in Lean has a base case and a step, as on paper.

### Definitions

**Definition (Peano structure).** A Peano structure is a set $N$ with an element $0 \in N$ and a function $s : N \to N$, the successor, with three properties:

1. $s(n) \neq 0$ for each $n \in N$;
2. $s$ is injective: $s(m) = s(n)$ gives $m = n$;
3. (induction) if a subset $A \subseteq N$ contains $0$ and $s(n) \in A$ for each $n \in A$, then $A = N$.

The set $\mathbb{N}$ is a Peano structure, with $1 = s(0)$, $2 = s(1)$, and so on. The third axiom is the principle of induction: if $P(0)$ holds, and $P(n)$ gives $P(n + 1)$ for each $n$, then $P(n)$ holds for each $n$. Take $A = \{n : P(n)\}$.

The three axioms fix $\mathbb{N}$ up to a unique isomorphism, as the next part shows, and none of them follows from the other two (Exercise 5).

**Definition (Addition and multiplication).** For $m \in \mathbb{N}$, addition and multiplication are defined by recursion on the second argument:
$$m + 0 = m, \qquad m + s(n) = s(m + n),$$
$$m \cdot 0 = 0, \qquad m \cdot s(n) = m \cdot n + m.$$

From the definition, $m + 1 = m + s(0) = s(m + 0) = s(m)$. So the successor of $m$ is $m + 1$, and the rest of the text writes $n + 1$ for $s(n)$.

::: mathlib
`Nat.rec_add_one` · `Mathlib.Data.Nat.Init`

The type `ℕ` is the inductive type `Nat` of the core of Lean, with the constructors `Nat.zero` and `Nat.succ`, and `Nat.rec` is its recursor. The lemmas `Nat.rec_zero` and `Nat.rec_add_one` give the two equations of the recursion. The core defines `+` by recursion on the second argument, as above, so `n + 0 = n` holds by definition and `0 + n = n` needs a proof.

<?decl Nat.rec_add_one?>
:::

### Theorems and proofs

**Theorem (Recursion theorem).** Let $X$ be a set, $x_0 \in X$ and $g : \mathbb{N} \times X \to X$. There is exactly one function $f : \mathbb{N} \to X$ with $f(0) = x_0$ and $f(n + 1) = g(n, f(n))$ for each $n$.

*Proof.* Uniqueness. Let $f$ and $f'$ both satisfy the equations, and let $A = \{n : f(n) = f'(n)\}$. Then $0 \in A$, because $f(0) = x_0 = f'(0)$. If $n \in A$, then $f(n + 1) = g(n, f(n)) = g(n, f'(n)) = f'(n + 1)$, so $n + 1 \in A$. By induction, $A = \mathbb{N}$.

Existence. Call a set $R \subseteq \mathbb{N} \times X$ closed if $(0, x_0) \in R$, and $(n, x) \in R$ gives $(n + 1, g(n, x)) \in R$. The set $\mathbb{N} \times X$ is closed, so the intersection $F$ of all closed sets is defined, and $F$ is closed. Let $A$ be the set of $n$ for which exactly one $x$ has $(n, x) \in F$.

First, $0 \in A$. Suppose $(0, y) \in F$ with $y \neq x_0$. The set $F \setminus \{(0, y)\}$ is closed: it contains $(0, x_0)$, and a pair $(n + 1, g(n, x))$ is never $(0, y)$, because $n + 1 \neq 0$. So $F \subseteq F \setminus \{(0, y)\}$, which is false.

Next, let $n \in A$, with the unique value $x$, so $(n + 1, g(n, x)) \in F$. Suppose $(n + 1, y) \in F$ with $y \neq g(n, x)$. The set $F \setminus \{(n + 1, y)\}$ contains $(0, x_0)$, and it is closed: for $(k, z)$ in it, the pair $(k + 1, g(k, z))$ can equal $(n + 1, y)$ only if $k = n$ by injectivity, and then $z = x$ and $g(k, z) = g(n, x) \neq y$. This again contradicts the choice of $F$. Thus $n + 1 \in A$.

By induction $A = \mathbb{N}$. Define $f(n)$ as the unique $x$ with $(n, x) \in F$. Then $f(0) = x_0$, and $(n + 1, g(n, f(n))) \in F$ gives $f(n + 1) = g(n, f(n))$. $\square$

For addition, take $x_0 = m$ and $g(n, x) = x + 1$. For another Peano structure $(N', 0', s')$, the theorem gives a map $\mathbb{N} \to N'$ that sends $0$ to $0'$ and commutes with the successors, and the same argument in the other direction gives its inverse.

**Theorem (Laws of addition).** For all $k, m, n \in \mathbb{N}$:

1. $(k + m) + n = k + (m + n)$;
2. $0 + n = n$ and $(m + 1) + n = (m + n) + 1$;
3. $m + n = n + m$;
4. $k + n = m + n$ gives $k = m$.

*Proof.* Each part is an induction on $n$.

1. For $n = 0$ both sides are $k + m$. If the law holds for $n$, then $(k + m) + (n + 1) = ((k + m) + n) + 1 = (k + (m + n)) + 1 = k + ((m + n) + 1) = k + (m + (n + 1))$. Each step uses the definition of $+$ or the hypothesis.
2. For the first identity: $0 + 0 = 0$ by definition, and $0 + (n + 1) = (0 + n) + 1 = n + 1$. For the second: for $n = 0$ both sides are $m + 1$. If it holds for $n$, then $(m + 1) + (n + 1) = ((m + 1) + n) + 1 = ((m + n) + 1) + 1 = (m + (n + 1)) + 1$.
3. For $n = 0$, $m + 0 = m = 0 + m$ by part 2. If $m + n = n + m$, then $m + (n + 1) = (m + n) + 1 = (n + m) + 1 = (n + 1) + m$, by part 2 again.
4. For $n = 0$ the hypothesis is $k = m$. If the law holds for $n$ and $k + (n + 1) = m + (n + 1)$, then $(k + n) + 1 = (m + n) + 1$. The successor is injective, so $k + n = m + n$, and the hypothesis gives $k = m$. $\square$

**Theorem (Laws of multiplication).** For all $k, m, n \in \mathbb{N}$: $k(m + n) = km + kn$, $(km)n = k(mn)$ and $mn = nm$.

*Proof.* Distributivity, by induction on $n$: for $n = 0$ both sides are $km$, and $k(m + (n + 1)) = k(m + n) + k = km + kn + k = km + k(n + 1)$. Associativity, by induction on $n$: for $n = 0$ both sides are $0$, and $(km)(n + 1) = k(mn) + km = k(mn + m) = k(m(n + 1))$, with distributivity in the second step. Commutativity follows as for addition, from $0 \cdot n = 0$ and $(m + 1)n = mn + n$, which are inductions on $n$ (Exercise 1). $\square$

**Theorem (Induction from a start value).** Let $m \in \mathbb{N}$. If $P(m)$ holds and $P(n)$ gives $P(n + 1)$ for each $n \geq m$, then $P(n)$ holds for each $n \geq m$.

*Proof.* Let $Q(k)$ be the statement $P(m + k)$. Then $Q(0)$ is $P(m)$. If $Q(k)$ holds, then $m + k \geq m$, so the hypothesis gives $P(m + k + 1)$, which is $Q(k + 1)$. By ordinary induction, $Q(k)$ holds for each $k$. Each $n \geq m$ has the form $m + k$ with $k = n - m$, so $P(n)$ holds. $\square$

::: mathlib
`Nat.le_induction` · `Mathlib.Data.Nat.Init`

The property `P` takes the number `n` and a proof of `m ≤ n`, so the tactic `induction n, hn using Nat.le_induction` can use it. The case `base` has the goal `P m`, and the case `succ` gives `k`, `hk : m ≤ k` and `ih`. The recursor behind it is `Nat.leRec`.

<?decl Nat.le_induction?>
:::

**Theorem (Strong induction).** If, for each $n$, the statements $P(k)$ for all $k < n$ give $P(n)$, then $P(n)$ holds for each $n$.

Strong induction has no separate base case: for $n = 0$ there is no $k < 0$, so the hypothesis must prove $P(0)$ from nothing.

*Proof.* Let $Q(n)$ be the statement: $P(k)$ holds for each $k < n$. Then $Q(0)$ holds, because no $k$ is less than $0$. Suppose $Q(n)$. The hypothesis of the theorem gives $P(n)$. A number $k < n + 1$ is less than $n$ or equal to $n$, so $P(k)$ holds for each $k < n + 1$, which is $Q(n + 1)$. By ordinary induction, $Q(n)$ holds for each $n$. Then $Q(n + 1)$ contains $P(n)$. $\square$

::: mathlib
`Nat.strong_induction_on` · `Mathlib.Data.Nat.Init`

The tactic form is `induction n using Nat.strong_induction_on with | _ n ih => ...`, with `ih : ∀ m < n, P m`; `Nat.case_strong_induction_on` splits off the case $0$.

<?decl Nat.strong_induction_on?>
:::

**Theorem (Induction in two steps).** If $P(0)$ and $P(1)$ hold, and $P(n)$ and $P(n + 1)$ together give $P(n + 2)$ for each $n$, then $P(n)$ holds for each $n$.

*Proof.* Apply ordinary induction to the statement "$P(n)$ and $P(n + 1)$". $\square$

::: mathlib
`Nat.twoStepInduction` · `Mathlib.Data.Nat.Init`

The motive takes values in `Sort`, so the same function also defines sequences by a recursion of order two. For a property of two numbers, `Nat.diag_induction` is an induction on the pairs with $a \leq b$.

<?decl Nat.twoStepInduction?>
:::

### Examples

**Example (Induction from 1).** The inequality $n + 1 \leq 2^n$ holds for each $n \geq 1$. For $n = 1$ both sides are $2$. If $n + 1 \leq 2^n$, then $n + 2 \leq 2^n + 1 \leq 2^{n+1}$. In Lean, the case `succ` rewrites with `pow_succ` and ends with `omega`.

<?lean MathlibHandbook/V02/C01/Examples.lean#le_induction?>

**Example (Strong induction).** Each $n \in \mathbb{N}$ is a sum of distinct powers of $2$, where $0$ is the empty sum. For $n \geq 1$, let $2^k$ be the largest power of $2$ with $2^k \leq n$. Then $n - 2^k < 2^k$ and $n - 2^k < n$, so by strong induction $n - 2^k$ is a sum of distinct powers of $2$ less than $2^k$. Add $2^k$. For example $45 = 32 + 8 + 4 + 1$.

<?lean MathlibHandbook/V02/C01/Examples.lean#strong_induction?>

**Counterexample (A step that does not start).** The following argument is wrong: "all horses have one colour, by induction on the number $n$ of horses: a set of $n + 1$ horses is the union of two overlapping sets of $n$ horses, and each has one colour." For $n = 1$ the two sets of one horse do not overlap, so the step fails at $n = 1$. The step of an induction must hold for each $n$, including the smallest.

### The library around it

The file `Mathlib.Data.Nat.Init` collects the forms of induction on `ℕ`, and `induction n using r` accepts each of them. The laws of arithmetic are in the core of Lean as `Nat.add_comm`, `Nat.mul_comm` and `Nat.left_distrib`. Mathlib builds the instance `Nat.instCommSemiring` from them, so the general lemmas and the tactics `ring` and `omega` apply to `ℕ`.

### Exercises

1. (A) Prove that $0 \cdot n = 0$ and $(m + 1)n = mn + n$, and finish the proof of $mn = nm$. *Hint.* Induction on $n$, with the laws of addition.
2. (A) Prove that $1 + 3 + 5 + \dots + (2n - 1) = n^2$ for each $n \geq 1$. *Hint.* Induction from $1$.
3. (B) Prove that $m + n = 0$ gives $m = 0$ and $n = 0$, and that $mn = 0$ gives $m = 0$ or $n = 0$. *Hint.* Write $n = 0$ or $n = n' + 1$, and use the first axiom.
4. (B) Let $F_0 = 0$, $F_1 = 1$ and $F_{n+2} = F_{n+1} + F_n$. Prove that $F_n < 2^n$, and that $F_{m+n+1} = F_{m+1}F_{n+1} + F_m F_n$. *Hint.* Induction in two steps; for the identity, fix $m$.
5. (C) Show that the three axioms of a Peano structure are independent: for each axiom, give a structure that satisfies the other two and fails it. *Hint.* Try $\{0\}$ with $s(0) = 0$; $\{0, 1, 2\}$ with $s(2) = 1$; and $\mathbb{N} \cup \{\omega\}$ with $s(\omega) = \omega$.
6. (L) Prove that $2n \leq 2^n$ for each $n \geq 2$. The solution is `le_pow_self`.

### Notes and history

Dedekind gave the axioms of a simply infinite system and the recursion theorem in *Was sind und was sollen die Zahlen?* (1888). Peano published a form of the same axioms in 1889, and Landau, *Grundlagen der Analysis* (1930), derives the laws of arithmetic from them. In type theory the recursion theorem is the recursor of the inductive type.

### Reference

<?reference?>
