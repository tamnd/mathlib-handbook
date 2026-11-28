---
title: Well-founded orders
kind: theory
modules:
  - Mathlib.Order.WellFounded
  - Mathlib.Logic.Hydra
  - Mathlib.Order.GameAdd
explains:
  E3: [WellFounded.has_min, WellFoundedLT]
  E2: [WellFoundedLT.induction, IsWellOrder, WellFounded.min, WellFounded.not_rel_apply_succ, RelEmbedding.wellFounded_iff_isEmpty]
  E1: auto
families: []
requires: [V01]
reads_with: ["MIL", "TPIL"]
lean:
  - MathlibHandbook/V04/C01/Examples.lean
  - MathlibHandbook/V04/C01/Exercises.lean
  - MathlibHandbook/V04/C01/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Well-founded orders

### Overview

Induction on the natural numbers is the first proof method that a student learns that is special to an order. This section shows that induction works on each order with one property: each nonempty set has a minimal element. Such an order is well-founded. On $\mathbb{N}$ this is the least element principle, and it is the same as proof by strong induction. Well-founded relations are the general form of induction and of recursion. Lean uses them to accept a recursive definition, and Mathlib uses them to prove that a process stops.

The main results are: a relation is well-founded if and only if induction along it holds; a well-founded relation has no infinite descending sequence, and the converse holds with the axiom of choice; the natural numbers are well-ordered; and a lexicographic product of well-founded relations is well-founded. The examples show orders that are well-founded and orders that are not, and they compute descending sequences.

### Definitions

**Definition (Well-founded relation).** Let $r$ be a relation on a set $\alpha$. An element $m$ of a subset $S \subseteq \alpha$ is $r$-minimal in $S$ if there is no $x \in S$ with $r(x, m)$. The relation $r$ is well-founded if each nonempty subset of $\alpha$ has an $r$-minimal element. A preorder is well-founded if its strict relation $<$ is well-founded.

Read $r(x, m)$ as "$x$ is below $m$". The definition asks for a minimal element, not a least element. In a linear order, a minimal element of $S$ is the least element of $S$, by the dual of the theorem on maximal elements of the previous section.

::: mathlib
`WellFounded.has_min` · `Mathlib.Order.WellFounded`

In Lean, `WellFounded r` is a definition of the core library, and it does not use sets. An element $a$ is *accessible*, `Acc r a`, if each $y$ with `r y a` is accessible. This is an inductive definition, so the accessible elements are the ones from which each descending path stops. The relation is well-founded when each element is accessible. The lemma `WellFounded.has_min` proves the form of the text: each nonempty set `s` has an element `a ∈ s` with `¬ r x a` for each `x ∈ s`. The function `WellFounded.min` chooses one, and `WellFounded.min_mem` and `WellFounded.not_lt_min` give its properties. The form with `Acc` is the one that the kernel needs for recursion, and it does not use the axiom of choice.

<?decl WellFounded.has_min?>
:::

**Definition (Well-order).** A well-order is a linear order whose strict relation is well-founded. Equivalently, each nonempty subset has a least element.

::: mathlib
`WellFoundedLT` · `Mathlib.Order.RelClasses`

`WellFoundedLT α` is an abbreviation for `WellFounded (· < ·)` on `α`, and it is used as a class. So a lemma that needs a well-founded order takes `[WellFoundedLT α]`, and the instance for `ℕ` is found by the system. `WellFoundedGT α` is the dual: the order has no infinite ascending sequence. A well-order is a `LinearOrder` with `WellFoundedLT`. For a relation that is not written `<`, the class `IsWellOrder α r` says that `r` is trichotomous and well-founded.

<?decl WellFoundedLT?>
:::


### Theorems and proofs

**Theorem (Well-founded induction).** Let $r$ be a relation on $\alpha$. The following are equivalent.

1. The relation $r$ is well-founded.
2. For each property $P$ of the elements of $\alpha$: if, for each $x$, the truth of $P(y)$ for all $y$ with $r(y, x)$ gives $P(x)$, then $P(x)$ holds for each $x \in \alpha$.

*Proof.* (1) gives (2). Assume the hypothesis of (2), and suppose that $P$ fails for some element. Then the set $S = \{x \in \alpha : \lnot P(x)\}$ is nonempty. Let $m$ be an $r$-minimal element of $S$. Let $y$ satisfy $r(y, m)$. Then $y \notin S$ by minimality, so $P(y)$ holds. This holds for each $y$ with $r(y, m)$, and the hypothesis gives $P(m)$. This contradicts $m \in S$.

(2) gives (1). Let $S \subseteq \alpha$ be a set with no $r$-minimal element. It suffices to show that $S$ is empty. Apply (2) to the property $P(x)$: "$x \notin S$". Let $x \in \alpha$, and assume that $y \notin S$ for each $y$ with $r(y, x)$. If $x \in S$, then no element of $S$ is below $x$, so $x$ is an $r$-minimal element of $S$. There is none, so $x \notin S$. So the hypothesis of (2) holds, and (2) gives $x \notin S$ for each $x$. $\square$

On $\mathbb{N}$ with $<$, the second property is strong induction. So the theorem says that strong induction on $\mathbb{N}$ is the same as the least element principle, once the least element principle is known. The next theorem proves it from ordinary induction.

**Theorem (The natural numbers are well-ordered).** Each nonempty subset of $\mathbb{N}$ has a least element.

*Proof.* Let $S \subseteq \mathbb{N}$ have no least element. Prove by induction on $n$ the statement $Q(n)$: none of $0, 1, \dots, n$ is in $S$. For $n = 0$: if $0 \in S$, then $0$ is a least element of $S$, because $0 \le m$ for each $m$. So $0 \notin S$. Assume $Q(n)$. If $n + 1 \in S$, then each $m \in S$ satisfies $m \ge n + 1$, because $0, \dots, n$ are not in $S$. So $n + 1$ is a least element of $S$, a contradiction. So $Q(n+1)$ holds. By induction, $Q(n)$ holds for each $n$, and each $n$ is not in $S$. So $S$ is empty. $\square$

**Theorem (Descending sequences).** Let $r$ be a relation on $\alpha$.

1. If $r$ is well-founded, there is no sequence $(x_n)_{n \in \mathbb{N}}$ with $r(x_{n+1}, x_n)$ for each $n$.
2. Assume the axiom of choice. If there is no such sequence, then $r$ is well-founded.

*Proof.* 1. Let $(x_n)$ be such a sequence. The set $S = \{x_n : n \in \mathbb{N}\}$ is nonempty. Let $x_k$ be an $r$-minimal element of $S$. Then $x_{k+1} \in S$ and $r(x_{k+1}, x_k)$, which contradicts minimality.

2. Assume that $r$ is not well-founded. Then there is a nonempty set $S$ with no $r$-minimal element. So for each $x \in S$, the set $\{y \in S : r(y, x)\}$ is nonempty. By the axiom of choice, there is a function $c : S \to S$ with $r(c(x), x)$ for each $x \in S$. Choose $x_0 \in S$, and define $x_{n+1} = c(x_n)$ by recursion on $n$. Then $r(x_{n+1}, x_n)$ for each $n$. $\square$

The second part uses only the axiom of dependent choice, a weak form of the axiom of choice. Without any choice the converse can fail. In practice, the descending sequence form is the way to show that a relation is *not* well-founded, and the minimal element form or the induction form is the way to use it.

::: mathlib
`WellFounded.not_rel_apply_succ` · `Mathlib.Order.WellFounded`

For a well-founded `r` and a sequence `f : ℕ → α`, this lemma gives an `n` with `¬ r (f (n + 1)) (f n)`. It is part 1 of the theorem. Part 2 is `RelEmbedding.wellFounded_iff_isEmpty` in `Mathlib.Order.OrderIsoNat`: a strict order is well-founded if and only if there is no order embedding of $(\mathbb{N}, >)$ into it. The induction principle for an order with a well-founded `<` is `WellFoundedLT.induction`, and the tactic form is `induction x using WellFoundedLT.induction`. Lean also uses well-founded relations for recursive definitions: a clause `termination_by` gives a measure into a well-founded order, and the elaborator proves that each recursive call goes down.

<?decl WellFounded.not_rel_apply_succ?>
:::

**Theorem (Lexicographic product).** Let $r$ be a well-founded relation on $\alpha$ and $s$ a well-founded relation on $\beta$. On $\alpha \times \beta$ define $(a, b) \prec (a', b')$ if $r(a, a')$, or $a = a'$ and $s(b, b')$. Then $\prec$ is well-founded.

*Proof.* Let $S \subseteq \alpha \times \beta$ be nonempty. The set $A = \{a : (a, b) \in S \text{ for some } b\}$ is nonempty. Let $a_0$ be an $r$-minimal element of $A$. The set $B = \{b : (a_0, b) \in S\}$ is nonempty, because $a_0 \in A$. Let $b_0$ be an $s$-minimal element of $B$. Then $(a_0, b_0) \in S$. Suppose $(a, b) \in S$ and $(a, b) \prec (a_0, b_0)$. If $r(a, a_0)$, then $a \in A$ contradicts the minimality of $a_0$. If $a = a_0$ and $s(b, b_0)$, then $b \in B$ contradicts the minimality of $b_0$. So $(a_0, b_0)$ is $\prec$-minimal in $S$. $\square$


### Examples

**Example (Integers and reals).** The order $<$ on $\mathbb{Z}$ is not well-founded: the sequence $x_n = -n$ satisfies $x_{n+1} < x_n$, and the set $\mathbb{Z}$ has no minimal element. The order $<$ on $[0, 1]$ is not well-founded: $x_n = 1/(n+1)$ is a descending sequence, and the set $(0, 1]$ has no minimal element, although $[0,1]$ has the least element $0$. So a least element of the whole order does not make it well-founded. Each finite partial order is well-founded: a descending sequence $x_0 > x_1 > \dots$ has distinct terms, by the transitivity and the irreflexivity of $<$, and a finite set has no infinite sequence of distinct elements.

**Example (Proper divisibility).** On $\mathbb{N}$, let $r(d, n)$ mean $d \mid n$ and $d \ne n$. This relation is well-founded, although $0$ has infinitely many elements below it: each $d \ne 0$ divides $0$. Compute a descending sequence from $0$: $0, 360, 60, 12, 4, 2, 1$. It stops at $1$, because the only divisor of $1$ is $1$. For the proof, let $(x_n)$ be a sequence with $r(x_{n+1}, x_n)$ for each $n$. If $x_{n+1} = 0$, then $0 \mid x_n$ gives $x_n = 0 = x_{n+1}$, which is excluded. So $x_n \ne 0$ for $n \ge 1$. For $n \ge 1$, $x_{n+1} \mid x_n$ with $x_n \ne 0$ gives $x_n = k x_{n+1}$ with $k \ge 1$, so $x_{n+1} \le x_n$, and $x_{n+1} \ne x_n$ gives $x_{n+1} < x_n$. So $x_1 > x_2 > x_3 > \dots$ is a descending sequence in $\mathbb{N}$, which is impossible by part 1 of the theorem on descending sequences.

**Example (The lexicographic order on pairs).** By the theorem on the lexicographic product, the lexicographic order on $\mathbb{N} \times \mathbb{N}$ is a well-order. A descending sequence can still be long. From $(2, 0)$ the sequence can go to $(1, 1000)$, then down to $(1, 0)$ in $1000$ steps, then to $(0, 10^6)$, and then down in $10^6$ steps to $(0,0)$. The length of a descending sequence from $(2,0)$ has no bound, but each such sequence is finite. This is the reason why a proof of termination often uses a lexicographic measure: a step may increase the second coordinate if it decreases the first. The termination of the Ackermann function is the standard example.

### The library around it

The general theory of well-founded relations is in `Mathlib.Order.WellFounded`, and the classes `WellFoundedLT`, `WellFoundedGT` and `IsWellOrder` are in `Mathlib.Order.RelClasses`. The instances give `WellFoundedLT` for `ℕ`, for `Fin n`, for each finite linear order, and for products with the lexicographic order. A well-founded linear order has the minimum `WellFounded.min` of each nonempty set, and `WellFoundedLT.conditionallyCompleteLinearOrderBot` turns a well-ordered type into a conditionally complete lattice. The lemma `WellFounded.induction_bot` is an induction form for a process that goes down to a fixed element. The file `Mathlib.Logic.Hydra` proves that the order on multisets given by "replace one element by any finite number of smaller ones" is well-founded, which is the core of the game of the hydra. Its relation is `Relation.CutExpand`, `Relation.cutExpand_iff` unfolds it, and `WellFounded.cutExpand` gives the well-foundedness from a well-founded relation $r$. The file `Mathlib.Order.GameAdd` defines `Prod.GameAdd`: a pair goes down when one coordinate goes down and the other stays the same, which is a move in a sum of two games. The lemma `WellFounded.prod_gameAdd` says that this relation is well-founded when the two relations are well-founded, and `Prod.GameAdd.recursion` gives a recursion that calls itself on $(a', b)$ or on $(a, b')$. The relation `Sym2.GameAdd` and the lemma `WellFounded.sym2_gameAdd` are the same for unordered pairs.

### Exercises

1. (A) Show that $>$ on $\mathbb{N}$ is not well-founded, and that $<$ on $\{1/n : n \ge 1\}$ is not well-founded. *Hint:* give a descending sequence.
2. (A) Prove by well-founded induction that each natural number $n \ge 2$ is a product of primes. *Hint:* use proper divisibility, or $<$.
3. (B) Show that a relation $r$ is well-founded if and only if the transitive closure of $r$ is well-founded. *Hint:* use the descending sequence form for one direction, and induction for the other.
4. (B) Let $f : \alpha \to \mathbb{N}$, and let $r(x, y)$ mean $f(x) < f(y)$. Show that $r$ is well-founded. This is the base of a termination proof by a measure.
5. (B) Show that in a well-founded linear order, there is no strictly decreasing function $\mathbb{N} \to \alpha$, and that each strictly increasing function $h : \alpha \to \alpha$ satisfies $x \le h(x)$. *Hint:* take a minimal $x$ with $h(x) < x$.
6. (B) Show that $<$ on $\mathbb{N} \times \mathbb{N}$ with the product order is well-founded, and give a descending sequence with $11$ terms from $(5, 5)$. *Hint:* use the measure $a + b$ and Exercise 4.
7. (C) Order the finite sequences of natural numbers by the order of a dictionary: compare the first terms, then the second terms, and a proper initial part comes first. Show that this is a linear order that is not well-founded. *Hint:* consider $(1) > (0, 1) > (0, 0, 1) > \dots$.

### Notes and history

Proofs by infinite descent go back to Fermat, who used them for the equation $x^4 + y^4 = z^2$. Cantor introduced well-orders in 1883, and Zermelo proved in 1904 that each set has a well-order, with the axiom of choice. Emmy Noether used induction along a well-founded relation in commutative algebra in the 1920s, and the principle is still called Noetherian induction. Well-founded recursion and the accessibility predicate are the base of the treatment of recursion in type theory, see Nordström (1988) and the Lean book *Theorem Proving in Lean 4*, chapter on induction and recursion.

In Mathlib, the file `Mathlib.Order.WellFounded` has the authors Jeremy Avigad and Mario Carneiro. The definition of `WellFounded` with `Acc` is in the core library of Lean, because the kernel needs it for recursion.

### Reference

<?reference?>
