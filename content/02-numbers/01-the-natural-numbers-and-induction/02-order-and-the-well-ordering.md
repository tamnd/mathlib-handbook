---
title: Order, subtraction and the well ordering of ℕ
kind: theory
modules:
  - Mathlib.Data.Nat.Find
  - Mathlib.Data.Nat.Basic
explains:
  E3: [Nat.find, Nat.findGreatest]
  E2: [Nat.find_spec, Nat.find_min', Nat.find_min, Nat.find_eq_iff, Nat.find_le, Nat.find_le_iff, Nat.le_find_iff, Nat.findGreatest_spec, Nat.findGreatest_le, Nat.decreasingInduction, Nat.instLinearOrder]
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

## Order, subtraction and the well ordering of ℕ

### Overview

The order of the natural numbers comes from addition: $m \leq n$ means that $n = m + k$ for some $k$. This section proves that this relation is a total order compatible with addition and multiplication. Then it proves the well ordering principle: each nonempty set of natural numbers has a least element. It is equivalent to induction. The section also treats truncated subtraction, with its junk value $m - n = 0$ for $m < n$, and `Nat.find`, the well ordering principle as a function.

### Definitions

**Definition (Order).** For $m, n \in \mathbb{N}$, $m \leq n$ if there is $k \in \mathbb{N}$ with $n = m + k$. The strict order is $m < n$ if $m + 1 \leq n$.

The number $k$ is unique, by cancellation. The strict order agrees with "$m \leq n$ and $m \neq n$", as the next part proves.

::: mathlib
`Nat.instLinearOrder` · `Mathlib.Data.Nat.Basic`

The core of Lean defines `Nat.le` as an inductive predicate: `n ≤ n`, and `n ≤ m` gives `n ≤ m + 1`. The instance `Nat.instLinearOrder` makes the general lemmas of a linear order, such as `le_antisymm`, apply to `ℕ`.

<?decl Nat.instLinearOrder?>
:::

**Definition (Truncated subtraction).** For $m, n \in \mathbb{N}$, the truncated difference is $m - n = k$ if $m = n + k$, and $m - n = 0$ if $m < n$.

The value $0$ for $m < n$ is a junk value (Volume 1, Chapter 5), so $(m - n) + n = m$ holds only for $n \leq m$. In a general ordered monoid Mathlib calls this operation `tsub`, as in `tsub_add_cancel_of_le`.

**Definition (Least element).** An element $a \in S \subseteq \mathbb{N}$ is the least element of $S$ if $a \leq s$ for each $s \in S$. If some number has a property $P$, the least number with $P$ is written $\mu P$; the well ordering principle below says that it exists.

::: mathlib
`Nat.find` · `Mathlib.Data.Nat.Find`

The function takes a proof `h : ∃ n, P n` and needs an instance `DecidablePred P`, because it tests $P(0), P(1), \dots$ in turn. The two properties of the value are `Nat.find_spec h : P (Nat.find h)` and `Nat.find_min' h : P m → Nat.find h ≤ m`.

<?decl Nat.find?>
:::

**Definition (Greatest number below a bound).** For a property $P$ and a bound $n$, if some $m \leq n$ has $P$, the greatest such $m$ is the greatest number below $n$ with $P$.

::: mathlib
`Nat.findGreatest` · `Mathlib.Data.Nat.Find`

The function `Nat.findGreatest P n` needs no proof of existence: it returns the junk value `0` if no number in $\{1, \dots, n\}$ has $P$. So the lemma `Nat.findGreatest_spec` needs a witness `m ≤ n` with `P m`, and `Nat.findGreatest_le` says that the value is at most `n`.

<?decl Nat.findGreatest?>
:::

### Theorems and proofs

**Theorem (The order of ℕ).** The relation $\leq$ on $\mathbb{N}$ has these properties, for all $k, m, n$:

1. it is reflexive, transitive and antisymmetric;
2. it is total: $m \leq n$ or $n \leq m$;
3. $m < n$ holds if and only if $m \leq n$ and $m \neq n$;
4. $m \leq n$ holds if and only if $m + k \leq n + k$; and $m \leq n$ gives $mk \leq nk$;
5. there is no $m$ with $n < m < n + 1$; in other words, $m < n + 1$ holds if and only if $m \leq n$.

*Proof.* 1. Reflexivity: $n = n + 0$. Transitivity: $n = m + k$ and $p = n + l$ give $p = m + (k + l)$. Antisymmetry: $n = m + k$ and $m = n + l$ give $m = m + (k + l)$, so $k + l = 0$ by cancellation. A sum is $0$ only if both terms are $0$: if $l = l' + 1$, then $k + l = (k + l') + 1 \neq 0$ by the first Peano axiom, and the same for $k$. So $k = 0$ and $m = n$.

2. Fix $m$ and use induction on $n$. For $n = 0$, $0 \leq m$. If $m \leq n$, then $m \leq n + 1$. If $n \leq m$, write $m = n + k$: for $k = 0$, $m \leq n + 1$, and for $k = k' + 1$, $m = (n + 1) + k'$, so $n + 1 \leq m$.

3. If $m + 1 \leq n$, then $m \leq n$ by transitivity, and $m = n$ would give $n + 1 \leq n$, so $n = n + 1 + j$ and $0 = j + 1$ by cancellation, which is false. Conversely, if $n = m + k$ with $m \neq n$, then $k \neq 0$, so $k = k' + 1$ and $n = (m + 1) + k'$.

4. $n = m + j$ holds if and only if $n + k = (m + k) + j$, by cancellation. And $n = m + j$ gives $nk = mk + jk$.

5. If $m < n + 1$, then $m + 1 \leq n + 1$, so $n + 1 = m + 1 + j$, and cancellation gives $n = m + j$, so $m \leq n$. The converse is part 4 with $k = 1$. Now $n < m$ means $n + 1 \leq m$, and this contradicts $m < n + 1$ by antisymmetry and part 3. $\square$

**Theorem (Subtraction).** For $m, n \in \mathbb{N}$: if $n \leq m$, then $(m - n) + n = m$; if $m \leq n$, then $m - n = 0$; and $(m + n) - n = m$ always.

*Proof.* Each claim follows from the definition: for $n \leq m$ write $m = n + k$, so $m - n = k$; for $m = n$, $m = n + 0$; and $m + n = n + m$. $\square$

**Theorem (Well ordering principle).** Each nonempty set $S \subseteq \mathbb{N}$ has a least element.

*Proof.* Suppose that $S$ has no least element. Prove $n \notin S$ for each $n$ by strong induction, which contradicts $S \neq \emptyset$. Suppose that no $k < n$ is in $S$. If $n \in S$, then $n \leq s$ for each $s \in S$: by totality, $s < n$ is the only other case, and it gives $s \notin S$. So $n$ is a least element of $S$, which contradicts the assumption. Thus $n \notin S$. $\square$

The least element is unique, by antisymmetry. Conversely, the well ordering principle gives induction (Exercise 5).

**Corollary (Infinite descent).** There is no sequence $a_0 > a_1 > a_2 > \dots$ of natural numbers.

*Proof.* The set $\{a_0, a_1, \dots\}$ is not empty, so it has a least element $a_i$. Then $a_{i+1} < a_i$ is in the set, which contradicts the choice of $a_i$. $\square$

**Theorem (Decreasing induction).** Let $n \in \mathbb{N}$. If $P(n)$ holds, and $P(k + 1)$ gives $P(k)$ for each $k < n$, then $P(m)$ holds for each $m \leq n$.

*Proof.* Prove "$j \leq n$ gives $P(n - j)$" by induction on $j$. For $j = 0$ this is $P(n)$. If $j + 1 \leq n$, then $k = n - (j + 1) < n$ and $k + 1 = n - j$, so the step gives $P(k)$. For $m \leq n$, take $j = n - m$. $\square$

::: mathlib
`Nat.decreasingInduction` · `Mathlib.Data.Nat.Init`

The motive takes the number `m` and the proof of `m ≤ n`, as in `Nat.le_induction`, and the step goes from `k + 1` to `k` for `k < n`.

<?decl Nat.decreasingInduction?>
:::

**Theorem (The least number with a property).** Let $P$ be a property and suppose that some number has $P$. Then there is exactly one $m$ with $P(m)$ and $\neg P(k)$ for each $k < m$. This $m$ satisfies $m \leq n$ for each $n$ with $P(n)$.

*Proof.* The set $S = \{n : P(n)\}$ is not empty, so it has a least element $m$ by the well ordering principle. If $k < m$ and $P(k)$, then $k \in S$ and $m \leq k$, which contradicts $k < m$. If $m'$ is another number with the two properties, then $m < m'$ is false, because $P(m)$ and $m < m'$ contradict the second property of $m'$. In the same way $m' < m$ is false. By totality, $m = m'$. $\square$

::: mathlib
`Nat.find_eq_iff` · `Mathlib.Data.Nat.Find`

This is the uniqueness part of the theorem, and the normal way to compute a value of `Nat.find`. The lemmas `Nat.find_le_iff` and `Nat.le_find_iff` compare `Nat.find h` with a number, and `Nat.find_min` gives `¬ P m` for each `m < Nat.find h`.

<?decl Nat.find_eq_iff?>
:::

### Examples

**Example (A least element).** The least element of $\{n : n^2 > 50\}$ is $8$, since $8^2 = 64 > 50$ and $n^2 \leq 49$ for $n \leq 7$. In Lean, the same method computes `Nat.find` for the property $5 < 2n$: the lemma `Nat.find_eq_iff` reduces the goal to $5 < 2 \cdot 3$ and to $\neg (5 < 2m)$ for $m < 3$, and `omega` proves the second part.

<?lean MathlibHandbook/V02/C01/Examples.lean#find?>

**Example (The two properties of Nat.find).** The two lemmas of the library give the two properties of the least element.

<?lean MathlibHandbook/V02/C01/Examples.lean#find_spec?>

**Example (A least counterexample).** Claim: $3 \mid n^3 - n$ for each $n$. Let $n$ be the least counterexample. Then $n \neq 0$, so $n = m + 1$ and $3 \mid m^3 - m$. But $(m + 1)^3 - (m + 1) = (m^3 - m) + 3m^2 + 3m$ is divisible by $3$, a contradiction.

**Counterexample (Subtraction is not the inverse of addition).** In $\mathbb{N}$, $2 - 5 = 0$, so $(2 - 5) + 5 = 5 \neq 2$. The rule $(a - b) + c = (a + c) - b$ also fails: for $a = 2$, $b = 5$, $c = 4$ the left side is $4$ and the right side is $1$. A proof must carry the hypothesis $b \leq a$, or move the statement to `ℤ` (Chapter 5).

**Counterexample (The well ordering fails for ℤ and for ℚ).** The set $\mathbb{Z}$ has no least element, since $n - 1 < n$. The set $\{1/n : n \geq 1\}$ of positive rational numbers has no least element, since $1/(n + 1) < 1/n$.

### The library around it

The file `Mathlib.Data.Nat.Find` also has `Nat.find_pos`, `Nat.find_eq_zero` and `Nat.find_mono`, and the family of `Nat.findGreatest` has the same pattern. In a general well-ordered type, the least element of a nonempty set is `WellFounded.min` (Volume 4). The tactic `omega` decides linear statements on `ℕ` and `ℤ`, including truncated subtraction, so most goals of this section end with `omega`.

### Exercises

1. (A) Find the least $n$ with $2^n > 1000$, and prove that it is least. *Hint.* Compute $2^9$ and $2^{10}$.
2. (B) Prove that $(a - b) - c = a - (b + c)$ for all $a, b, c \in \mathbb{N}$, including the cases with truncation. *Hint.* Compare $a$ with $b$ and with $b + c$.
3. (B) Show that each nonempty set of natural numbers that is bounded above has a greatest element. *Hint.* Apply the well ordering principle to the set of upper bounds.
4. (B) Prove that $mk = nk$ with $k \neq 0$ gives $m = n$. *Hint.* By totality, $m < n$ or $n < m$ or $m = n$. Use part 4 of the theorem on the order.
5. (C) Prove that the well ordering principle, applied to the set of $n$ with $\neg P(n)$, gives strong induction directly. *Hint.* The least element $a$ of the set has $P(k)$ for each $k < a$.
6. (L) Prove that for each $k$ there is a least $n$ with $k < n^2$. The solution is `exists_least_square_gt`.

### Notes and history

Fermat used the method of infinite descent to prove that no right triangle with integer sides has a square area. The general notion of a well-ordered set is due to Cantor. The truncated subtraction is the monus of the literature on primitive recursive functions.

### Reference

<?reference?>
