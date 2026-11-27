---
title: From a textbook statement to a Mathlib statement
kind: guide
modules: []
explains: {}
families: []
requires: []
reads_with: ["MIL Ch. 2", "MIL Ch. 3"]
lean:
  - MathlibHandbook/V00/C01/Examples.lean
  - MathlibHandbook/V00/C01/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## From a textbook statement to a Mathlib statement

### Overview

A theorem of a textbook and the same theorem in Mathlib often look different. The Mathlib form can be more general, it can use a different but equivalent formulation, and it can avoid an operation such as division that causes trouble in a formal setting. A reader who wants to use a theorem of Mathlib must see that the two forms say the same thing. This section takes four classical results: the infinitude of the primes, the sum of the first natural numbers, the intermediate value theorem and the irrationality of a number. For each one it gives the textbook form, the Mathlib form, and a proof that the two forms are equivalent or a precise account of how they differ. The section ends with a dictionary of the common translations.

### The infinitude of the primes

The textbook says: *there are infinitely many prime numbers.* Mathlib states it in three forms.

1. `Nat.exists_infinite_primes`: for each $n \in \mathbb{N}$ there is a prime $p$ with $n \le p$.
2. `Nat.not_bddAbove_setOfPred_prime`: the set $\{p \mid p \text{ prime}\}$ has no upper bound.
3. `Nat.infinite_setOfPred_prime`: the set $\{p \mid p \text{ prime}\}$ is infinite.

The first form is the most direct to prove and to use: it is a statement about numbers, with no notion of a finite set. The third form is the closest to the textbook. They are equivalent by a general fact about subsets of $\mathbb{N}$.

**Theorem (Infinite subsets of ℕ).** Let $S \subseteq \mathbb{N}$. Then $S$ is infinite if and only if for each $n \in \mathbb{N}$ there is $p \in S$ with $n \le p$.

*Proof.* Suppose first that $S$ is infinite, and let $n \in \mathbb{N}$. Suppose, for a contradiction, that no $p \in S$ satisfies $n \le p$. Then each $p \in S$ satisfies $p < n$, so $S \subseteq \{0, 1, \dots, n-1\}$. A subset of a finite set is finite, so $S$ is finite. This is a contradiction, so there is $p \in S$ with $n \le p$.

Suppose now that for each $n$ there is $p \in S$ with $n \le p$, and suppose, for a contradiction, that $S$ is finite. For $n = 0$ there is an element of $S$, so $S$ is not empty. A finite nonempty set of natural numbers has a largest element $m$. For $n = m + 1$ there is $p \in S$ with $m + 1 \le p$. But $p \le m$, because $m$ is the largest element of $S$. So $m + 1 \le m$, which is false. So $S$ is infinite. $\square$

::: mathlib
`Nat.infinite_setOfPred_prime` · `Mathlib.Data.Nat.PrimeFin`

The set `{p | Nat.Prime p}` is the set of the natural numbers with the property `Nat.Prime`. The notation `s.Infinite` means `Set.Infinite s`, by dot notation. Mathlib proves this form from the first form with the lemma `Set.infinite_of_not_bddAbove`, which is the direction from right to left of the theorem above for any directed order.

<?decl Nat.infinite_setOfPred_prime?>
:::

::: mathlib
`Set.infinite_of_not_bddAbove` · `Mathlib.Data.Set.Finite.Lattice`

A set with no upper bound is infinite. The conditions `[Preorder α]`, `[IsDirectedOrder α]` and `[Nonempty α]` hold for `ℕ`. The lemma is stated for each such order, so it also applies to `ℤ` and `ℝ`.

<?decl Set.infinite_of_not_bddAbove?>
:::

### The sum of the first natural numbers

The textbook says: $1 + 2 + \dots + n = \dfrac{n(n+1)}{2}$. Mathlib has the result as `Finset.sum_range_id_mul_two`:

$$\Big(\sum_{i \in \operatorname{range} n} i\Big) \cdot 2 = n(n - 1).$$

There are three differences, and each one has a reason.

1. The set `Finset.range n` is $\{0, 1, \dots, n-1\}$, with $n$ elements. Mathlib sums over `range n` because each finite sum over the first $n$ natural numbers then has the same form, and the lemma `Finset.sum_range_succ` splits off the last term. So the Mathlib sum is $0 + 1 + \dots + (n-1)$, and the right side is $n(n-1)$ in place of $n(n+1)$.
2. The statement multiplies by $2$. It does not divide by $2$. Division in `ℕ` rounds down, so a statement with `/ 2` needs an argument that the number is even. A statement with `* 2` has no such problem.
3. The subtraction $n - 1$ is subtraction in `ℕ`. For $n = 0$ it gives $0 - 1 = 0$, and the statement reads $0 \cdot 2 = 0 \cdot 0$, which is true.

**Theorem (Gauss).** For each $n \in \mathbb{N}$, $2 \sum_{i=0}^{n-1} i = n(n - 1)$, where $n - 1$ means $0$ for $n = 0$.

*Proof.* Write $S(n) = \sum_{i=0}^{n-1} i$. Use induction on $n$. For $n = 0$ the sum is empty, so $S(0) = 0$, and $2 \cdot 0 = 0 = 0 \cdot (0 - 1)$.

Suppose $2S(n) = n(n-1)$. The sum $S(n+1)$ has one more term than $S(n)$, the term $i = n$, so $S(n+1) = S(n) + n$. Then $2 S(n+1) = 2 S(n) + 2n = n(n-1) + 2n$. The goal is $(n+1)\big((n+1) - 1\big) = (n+1) n$. There are two cases, because subtraction in $\mathbb{N}$ is truncated. If $n = 0$, then $n(n-1) + 2n = 0 = (n+1)n$. If $n \ge 1$, then $n - 1$ is the usual difference, and $n(n-1) + 2n = n\big((n-1) + 2\big) = n(n+1) = (n+1)n$. In both cases $2S(n+1) = (n+1)n$. $\square$

The case split in the proof is the price of the truncated subtraction. The proof in Mathlib avoids induction. It pairs the term $i$ with the term $n - 1 - i$, as the young Gauss did. Section 5.3 reads that proof.

::: mathlib
`Finset.sum_range_id_mul_two` · `Mathlib.Algebra.BigOperators.Intervals`

The sum notation `∑ i ∈ Finset.range n, i` is the sum of the function $i \mapsto i$ over the finite set `Finset.range n`. The parentheses around the sum matter: without them, `∑ i ∈ Finset.range n, i * 2` would be the sum of the terms $2i$.

<?decl Finset.sum_range_id_mul_two?>
:::

::: mathlib
`Finset.sum_range_id` · `Mathlib.Algebra.BigOperators.Intervals`

This is the form with division. The division is division in `ℕ`, which rounds down, but here it gives the exact quotient, because $n(n-1)$ is even. Mathlib has the parity fact as `Nat.even_mul_pred_self`. The proof of `Finset.sum_range_id` rewrites with `Finset.sum_range_id_mul_two` and cancels the factor $2$.

<?decl Finset.sum_range_id?>
:::

### The intermediate value theorem

The textbook says: *let $f : [a, b] \to \mathbb{R}$ be continuous. Then for each $y$ between $f(a)$ and $f(b)$ there is $c \in [a, b]$ with $f(c) = y$.* Mathlib has it as `intermediate_value_Icc`.

::: mathlib
`intermediate_value_Icc` · `Mathlib.Topology.Order.IntermediateValue`

The conclusion is the inclusion of sets `Set.Icc (f a) (f b) ⊆ f '' Set.Icc a b`. The domain `α` is any densely ordered, conditionally complete linear order with the order topology, and `ℝ` is one. The codomain `δ` is any linear order with an order closed topology. The function is defined on all of `α`, and only its restriction to the interval needs to be continuous: that is `ContinuousOn f (Set.Icc a b)`.

<?decl intermediate_value_Icc?>
:::

Read the conclusion with the definitions of the notation. The set `Set.Icc a b` is the closed interval $[a, b] = \{x \mid a \le x \le b\}$. The set `f '' s` is the image $f(s) = \{f(x) \mid x \in s\}$. The relation `s ⊆ t` means that each element of $s$ is an element of $t$. So the conclusion says: for each $y$ with $f(a) \le y \le f(b)$, there is $x$ with $a \le x \le b$ and $f(x) = y$. This is the textbook statement for the case $f(a) \le f(b)$. The case $f(b) \le f(a)$ is the lemma `intermediate_value_Icc'`.

Three things differ from the textbook. The domain of $f$ is the whole order, not only $[a, b]$: Mathlib avoids functions on subsets, because a function on a subset is a function on a different type, and Section 2.3 shows the cost of that. The hypothesis $a \le b$ is explicit. And the statement holds for many orders, not only for $\mathbb{R}$. It fails for $\mathbb{Q}$, and the condition that fails is `ConditionallyCompleteLinearOrder`: in $\mathbb{Q}$, the function $x \mapsto x^2 - 2$ is continuous on $[0, 2]$, it takes the values $-2$ and $2$ at the ends, and it never takes the value $0$, because $\sqrt 2$ is not rational.

### The irrationality of a number

The textbook says: *a real number $x$ is irrational if it is not of the form $a/b$ with $a, b \in \mathbb{Z}$ and $b \ne 0$.* Mathlib defines `Irrational x` as `x ∉ Set.range ((↑) : ℚ → ℝ)`. Read it in steps.

1. The term `((↑) : ℚ → ℝ)` is the map that sends a rational number to the same number as a real number. The arrow `↑` is a coercion, and Section 2.3 explains coercions.
2. `Set.range g` is the set of values of a function $g$, here the set of the real numbers that come from a rational number.
3. `x ∉ s` means `¬ (x ∈ s)`.

So `Irrational x` says: there is no $q \in \mathbb{Q}$ whose image in $\mathbb{R}$ is $x$. The textbook form is the theorem `irrational_iff_ne_rational`: `Irrational x ↔ ∀ a b : ℤ, b ≠ 0 → x ≠ a / b`. The two forms are equivalent because each rational number is a quotient $a/b$ of integers with $b \ne 0$, and each such quotient is rational.

::: mathlib
`Irrational` · `Mathlib.NumberTheory.Real.Irrational`

The definition is a predicate on `ℝ`. Its signature shows only `ℝ → Prop`. To see the body, open the source or use `#print Irrational` in the editor.

<?decl Irrational?>
:::

### A dictionary

The table gives the common translations from the language of a textbook to the language of Mathlib. Each row is explained in this volume or in Volume 1.

| Textbook | Mathlib |
|---|---|
| $x \in \mathbb{R}$ | `x : ℝ` |
| $A \subseteq \mathbb{R}$ | `A : Set ℝ` |
| $f : A \to \mathbb{R}$ with $A \subseteq \mathbb{R}$ | `f : ℝ → ℝ` and a hypothesis on `A`, such as `ContinuousOn f A` |
| $\{1, \dots, n\}$ | `Finset.Icc 1 n`, or `Finset.range n` for $\{0, \dots, n-1\}$ |
| $\sum_{i=1}^n a_i$ | `∑ i ∈ Finset.Icc 1 n, a i` |
| there are infinitely many $x$ with $P(x)$ | `∀ n, ∃ x, n ≤ x ∧ P x`, or `s.Infinite` for the set `s` of such `x` |
| $a_n \to L$ | `Filter.Tendsto a Filter.atTop (nhds L)`, Section 2.4 |
| $f$ is injective | `Function.Injective f` |
| $f(A)$, $f^{-1}(B)$ | `f '' A`, `f ⁻¹' B` |
| $p$ is prime | `Nat.Prime p` |
| $a \mid b$ | `a ∣ b`, typed as `\mid`, not the vertical bar |
| $\lfloor x/y \rfloor$ for $x, y \in \mathbb{N}$ | `x / y` in `ℕ` |

### Examples

**Example (Translating a statement).** The textbook statement "each prime $p > 2$ is odd" becomes `∀ p : ℕ, Nat.Prime p → 2 < p → Odd p`. The hypotheses become arrows, and Section 2.4 explains why. Mathlib states the result as `Nat.Prime.odd_of_ne_two`, with the hypothesis $p \ne 2$ in place of $p > 2$. The two forms are equivalent for primes, because each prime is at least $2$, so $p \ne 2$ and $2 \le p$ give $2 < p$.

**Example (A statement with a sum).** The statement $\sum_{i=1}^{n} (2i - 1) = n^2$ has a subtraction. In `ℕ`, the term $2i - 1$ is the usual value for $i \ge 1$, so a sum over `Finset.Icc 1 n` is safe. A sum over `Finset.range n` of `2 * i - 1` is not safe: its first term is $2 \cdot 0 - 1 = 0$, and the sum is $0 + 1 + 3 + \dots + (2n - 3) = (n-1)^2$ for $n \ge 1$. The safe form over `range n` is $\sum_{i < n} (2i + 1) = n^2$, with no subtraction at all. Section 3.2 proves it.

::: mathlib
`Nat.Prime.odd_of_ne_two` · `Mathlib.Data.Nat.Prime.Basic`

The hypothesis `p ≠ 2` is easier to check than `2 < p` in many proofs, so Mathlib takes it.

<?decl Nat.Prime.odd_of_ne_two?>
:::

### Common errors

1. Writing `Finset.range n` for $\{1, \dots, n\}$. It is $\{0, \dots, n-1\}$.
2. Stating a result with division in `ℕ`, as $n(n+1)/2$, and then trying to use the usual laws of division. Multiply out, or move to `ℚ`.
3. Defining a function only on a subset. Define it on the whole type, with a junk value outside the subset, and put the subset in the hypotheses.
4. Reading `f '' s` as $f(s)$ applied to one element. It is the image set.

### Exercises

1. (A) Write the textbook statement "the square of an odd integer is odd" in the form of a Mathlib statement, with `Odd`.
2. (A) Compute $\sum_{i \in \operatorname{range} 5} i$ and check `Finset.sum_range_id_mul_two` for $n = 5$.
3. (A) Unfold `Set.Icc 0 1 ⊆ f '' Set.Icc 0 1` into a statement with quantifiers and no set notation.
4. (B) Prove that $n(n-1)$ is even for each $n \in \mathbb{N}$, and deduce `Finset.sum_range_id` from `Finset.sum_range_id_mul_two` on paper.
5. (B) Prove that a subset $S \subseteq \mathbb{Z}$ with no upper bound is infinite. Show by an example that the converse is false in $\mathbb{Z}$.
6. (B) Prove that $\sum_{i < n} (2i + 1) = n^2$ for each $n$, by induction.
7. (C) Show that the statement "for each $n$ there is a prime $p$ with $n \le p$" implies that for each $k$ there are $k$ distinct primes. Do not use the notion of an infinite set.

### Notes and history

Euclid proves the infinitude of the primes in Book IX, Proposition 20 of the *Elements*, in the form "prime numbers are more than any assigned multitude of prime numbers". That form is close to the form of `Nat.exists_infinite_primes`: it is a statement about each finite stage, not about an infinite set. The story of the young Gauss and the sum $1 + 2 + \dots + 100$ comes from the biography of Gauss by Sartorius von Waltershausen (1856). Bolzano proved the intermediate value theorem in 1817. The form in Mathlib proves it for each conditionally complete, densely ordered linear order, through the fact that such an order has connected intervals.
