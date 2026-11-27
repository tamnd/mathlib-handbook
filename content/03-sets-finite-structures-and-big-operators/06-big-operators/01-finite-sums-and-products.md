---
title: Finite sums and products
kind: theory
modules:
  - Mathlib.Algebra.BigOperators.Group.Finset.Basic
  - Mathlib.Algebra.BigOperators.Group.Finset.Defs
explains:
  E3: [Finset.sum, Finset.sum_range_succ, Finset.sum_insert]
  E2: [Finset.prod, Finset.prod_range_succ, Finset.sum_range_id_mul_two, Finset.sum_add_distrib, Finset.mul_sum, Finset.card_eq_sum_ones, Finset.sum_empty, Finset.sum_const, Finset.prod_const, Finset.prod_insert]
  E1: auto
families: []
requires: [V03.C02, V03.C03]
reads_with: ["MIL", "MSG"]
lean:
  - MathlibHandbook/V03/C06/Examples.lean
  - MathlibHandbook/V03/C06/Exercises.lean
  - MathlibHandbook/V03/C06/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Finite sums and products

### Overview

A sum such as $1 + 2 + \cdots + n$ or a product such as $1 \cdot 2 \cdots n = n!$ is a *big operator*: one operation applied to a finite family of terms. The dots hide two questions: the order of the terms, and the meaning of an empty sum. A textbook answers both questions in a sentence: addition is commutative and associative, so the order does not matter, and the empty sum is $0$. A proof assistant must turn this sentence into a definition.

Mathlib defines the sum over a *finset*, a finite set with no order and no repetition (Chapter 3). The sum $\sum_{i \in s} f(i)$ is written `∑ i ∈ s, f i` and is the term `Finset.sum s f`. The product is `∏ i ∈ s, f i`, or `Finset.prod s f`. Because a finset has no order, the target type must be a commutative monoid, and the definition then needs no choice of an order. Because a finset can be empty, the empty sum is $0$ and the empty product is $1$ by definition.

This section gives the definition, the two rules that compute a sum (the empty sum and the sum over an insert), the induction on `Finset.range n`, and the first identities: the linear rules, constants, the card as a sum, the formula of Gauss, the odd numbers, the squares and the factorial. Section 2 gives the algebra of sums, and Section 3 the binomial theorem and counting.

### Definitions

Let $M$ be a commutative monoid, written with $\cdot$ and $1$. For a list $[a_1, \ldots, a_n]$ of elements of $M$, the product is $a_1 \cdot (a_2 \cdot (\cdots (a_n \cdot 1)))$, with the value $1$ for the empty list. If two lists are permutations of each other, they have the same product. Indeed every permutation of a list is a sequence of swaps of two adjacent entries, and a swap does not change the product, because $x \cdot (y \cdot r) = (x \cdot y) \cdot r = (y \cdot x) \cdot r = y \cdot (x \cdot r)$. A multiset is a list up to permutation (Chapter 2), so the product of a multiset is well defined. This is `Multiset.prod`.

**Definition (Product over a finset).** Let $s$ be a finset of a type $\alpha$, and let $f : \alpha \to M$. The product $\prod_{i \in s} f(i)$ is the product of the multiset $f(s)$ that has the value $f(a)$ once for each element $a$ of $s$. In Mathlib this multiset is `s.val.map f`.

If $a \ne b$ in $s$ have $f(a) = f(b)$, the multiset `s.val.map f` has this value twice. The image finset `s.image f` would keep it once, and for $f(i) = i \bmod 2$ on $\{0, 1, 2, 3\}$ it would give the wrong sum $1$ in place of $2$.

**Definition (Sum over a finset).** For an additive commutative monoid $M$, the sum $\sum_{i \in s} f(i)$ is the sum of the multiset `s.val.map f`. The empty sum is $0$.

**Definition (Range).** For $n \in \mathbb{N}$, the finset `Finset.range n` is $\{0, 1, \ldots, n - 1\}$. It has $n$ elements. So $\sum_{i \in \mathrm{range}\, n} f(i) = f(0) + f(1) + \cdots + f(n - 1)$, and a sum $\sum_{k=1}^{n} g(k)$ of a textbook is $\sum_{i \in \mathrm{range}\, n} g(i + 1)$.

*Remarks.* The textbook notation $\sum_{k=1}^{n}$ starts at $1$, and the sum over `range n` starts at $0$. A student must translate the bounds with care. When the term at $0$ is $0$, as for $\sum k^2$, the sum over `range (n + 1)` is the sum from $1$ to $n$.

::: mathlib
`Finset.sum` · `Mathlib.Algebra.BigOperators.Group.Finset.Defs`

The sum of `f : ι → M` over `s : Finset ι`, for `[AddCommMonoid M]`. The definition is `(s.val.map f).sum`. The notation `∑ i ∈ s, f i` unfolds to `Finset.sum s (fun i ↦ f i)`, and `∑ i, f i` sums over `Finset.univ` of a finite type (Chapter 4). The filter form `∑ i ∈ s with p i, f i` sums over `s.filter p`. For a function with finite support on an infinite type, Mathlib has `finsum` and the `Finsupp.sum` of Chapter 7.

<?decl Finset.sum?>
:::

::: mathlib
`Finset.prod` · `Mathlib.Algebra.BigOperators.Group.Finset.Defs`

The product of `f` over `s`, for `[CommMonoid M]`. Each lemma about products is stated once, with the attribute `to_additive`, and the tool makes the lemma about sums. So `Finset.prod_insert` and `Finset.sum_insert` have one proof, and the name of a lemma about sums is the name of the lemma about products with `sum` for `prod`.

<?decl Finset.prod?>
:::

### Theorems and proofs

**Theorem (The empty sum).** For each $f$, $\sum_{i \in \emptyset} f(i) = 0$ and $\prod_{i \in \emptyset} f(i) = 1$.

*Proof.* The multiset of the empty finset is the empty multiset. Its image under $f$ is empty, and the sum of the empty multiset is $0$ by the definition of the sum of a list. The product is the same with $1$. $\square$

**Theorem (The sum over an insert).** Let $s$ be a finset, let $a \notin s$ and let $f : \alpha \to M$. Then $$\sum_{i \in s \cup \{a\}} f(i) = f(a) + \sum_{i \in s} f(i), \qquad \prod_{i \in s \cup \{a\}} f(i) = f(a) \cdot \prod_{i \in s} f(i).$$

*Proof.* The finset `insert a s` has as its multiset the multiset `s.val` with $a$ added once. This is so because $a \notin s$, and the insert adds an element only when the element is new. The image of $a ::ₘ m$ under $f$ is $f(a) ::ₘ (m.\mathrm{map}\, f)$, because the image of a list is taken entry by entry. The product of $b ::ₘ m$ is $b$ times the product of $m$, by the definition of the product of a list. These three steps give the formula for products. The formula for sums is the same statement in additive notation. $\square$

The hypothesis $a \notin s$ is needed. If $a \in s$, then `insert a s = s`, and the formula would add the term $f(a)$ a second time. For $s = \{1\}$, $a = 1$ and $f(i) = 1$, the left side is $1$ and the right side is $2$.

::: mathlib
`Finset.sum_insert` · `Mathlib.Algebra.BigOperators.Group.Finset.Basic`

The rule needs `[DecidableEq ι]`, because `insert` needs it to decide whether `a` is new. A proof writes `rw [Finset.sum_insert ha]`. In a proof by `induction s using Finset.induction_on`, the step gives exactly a hypothesis `a ∉ s`, so this rule fits the induction.

<?decl Finset.sum_insert?>
:::

The empty sum and the sum over an insert determine every finite sum. Each finset is built from $\emptyset$ by a finite number of inserts of new elements. This is the induction principle `Finset.induction_on` of Chapter 3: to prove $P(s)$ for all finsets $s$, prove $P(\emptyset)$, and prove $P(s \cup \{a\})$ from $P(s)$ when $a \notin s$. Most theorems of this section have a proof by this induction.

**Theorem (One more term).** For each $n \in \mathbb{N}$ and $f : \mathbb{N} \to M$, $$\sum_{i \in \mathrm{range}(n + 1)} f(i) = \sum_{i \in \mathrm{range}\, n} f(i) + f(n).$$

*Proof.* The finset `range (n + 1)` is $\{0, \ldots, n\}$, and it is `insert n (range n)`. The number $n$ is not in `range n`, because each element of `range n` is less than $n$. The rule for an insert gives $f(n) + \sum_{i < n} f(i)$. Addition in $M$ is commutative, so this is the right side. $\square$

::: mathlib
`Finset.sum_range_succ` · `Mathlib.Algebra.BigOperators.Group.Finset.Basic`

The step of an induction on `n` for a sum over `range n`. The usual proof is `induction n with | zero => simp | succ n ih => rw [Finset.sum_range_succ, ih]; ring`. After the `rw`, the goal has no sum left, and `ring`, `omega` or `simp` closes it. The form that splits off the term at $0$ is `Finset.sum_range_succ'`.

<?decl Finset.sum_range_succ?>
:::

**Theorem (Linear rules).** Let $s$ be a finset and $f, g : \alpha \to M$. Then $$\sum_{i \in s} \bigl(f(i) + g(i)\bigr) = \sum_{i \in s} f(i) + \sum_{i \in s} g(i).$$ If $R$ is a semiring, $c \in R$ and $f : \alpha \to R$, then $c \cdot \sum_{i \in s} f(i) = \sum_{i \in s} c \cdot f(i)$.

*Proof.* Use induction on $s$. For $s = \emptyset$, both sides of the first rule are $0$, and both sides of the second rule are $0$, because $c \cdot 0 = 0$ in a semiring. Let $a \notin s$, and assume the rules for $s$. For the first rule, $$\sum_{i \in s \cup \{a\}} (f + g)(i) = f(a) + g(a) + \sum_{i \in s} f(i) + \sum_{i \in s} g(i),$$ by the insert rule and the hypothesis. Commutativity and associativity of $+$ move $g(a)$ past $\sum_{i \in s} f(i)$, and the result is $\bigl(f(a) + \sum_{s} f\bigr) + \bigl(g(a) + \sum_{s} g\bigr)$. The insert rule, read from right to left, gives the right side. For the second rule, $c \cdot \bigl(f(a) + \sum_{s} f\bigr) = c f(a) + c \sum_{s} f = c f(a) + \sum_{s} c f$, by the distributive law and the hypothesis. This is $\sum_{s \cup \{a\}} c f$ by the insert rule. $\square$

::: mathlib
`Finset.sum_add_distrib` · `Mathlib.Algebra.BigOperators.Group.Finset.Basic`

The additive form of `Finset.prod_mul_distrib`. It holds in each additive commutative monoid, so also in `ℕ`. The rule for a difference, `Finset.sum_sub_distrib`, needs an additive group, because the subtraction of `ℕ` truncates.

<?decl Finset.sum_add_distrib?>
:::

::: mathlib
`Finset.mul_sum` · `Mathlib.Algebra.BigOperators.Ring.Finset`

The constant goes in from the left: `a * ∑ i ∈ s, f i = ∑ i ∈ s, a * f i`. The rule `Finset.sum_mul` puts it on the right, and `Finset.sum_div` divides each term in a field.

<?decl Finset.mul_sum?>
:::

**Theorem (Constants).** For $c \in M$, $\sum_{i \in s} c = |s| \cdot c$, where $|s| \cdot c$ is the sum of $|s|$ copies of $c$. For a commutative monoid, $\prod_{i \in s} c = c^{|s|}$.

*Proof.* Use induction on $s$. For $s = \emptyset$, both sides are $0$. For $a \notin s$, the insert rule gives $c + |s| \cdot c = (|s| + 1) \cdot c = |s \cup \{a\}| \cdot c$, because the card of the insert of a new element is $|s| + 1$ (Chapter 3). The product is the same with powers. $\square$

::: mathlib
`Finset.sum_const` · `Mathlib.Algebra.BigOperators.Group.Finset.Basic`

The right side is `s.card • b`, with the scalar multiplication `•` of a natural number on an additive monoid. In `ℕ` the lemma `smul_eq_mul` turns `•` into `*`.

<?decl Finset.sum_const?>
:::

**Theorem (Card as a sum).** For each finset $s$, $|s| = \sum_{i \in s} 1$.

*Proof.* The rule of constants with $c = 1$ in $\mathbb{N}$ gives $\sum_{i \in s} 1 = |s| \cdot 1 = |s|$. $\square$

A count becomes a sum, and the rules of sums then apply. Section 3 uses this for double counting.

**Theorem (Gauss).** For each $n \in \mathbb{N}$, $$2 \sum_{i \in \mathrm{range}\, n} i = n(n - 1).$$ Equivalently, $1 + 2 + \cdots + m = \frac{m(m + 1)}{2}$.

*Proof.* Use induction on $n$. For $n = 0$, the sum is empty, and $0 \cdot (0 - 1) = 0$. Assume $2 \sum_{i < n} i = n(n - 1)$. The rule of one more term gives $$2 \sum_{i < n + 1} i = 2 \sum_{i < n} i + 2n = n(n - 1) + 2n.$$ If $n = 0$, this is $0 = (n + 1) n$. If $n \ge 1$, then $n(n - 1) + 2n = n^2 - n + 2n = n^2 + n = (n + 1)n$. In both cases the result is $(n + 1)((n + 1) - 1)$. The second form follows with $n = m + 1$, because the term at $0$ is $0$. $\square$

Section 2 gives a second proof, the proof of the story about Gauss: write the sum forwards and backwards and add.

::: mathlib
`Finset.sum_range_id_mul_two` · `Mathlib.Algebra.BigOperators.Intervals`

The statement is `(∑ i ∈ range n, i) * 2 = n * (n - 1)` in `ℕ`. The form with a division is `Finset.sum_range_id`: `∑ i ∈ range n, i = n * (n - 1) / 2`. The form with the factor $2$ is easier to use with `omega` and `ring`.

<?decl Finset.sum_range_id_mul_two?>
:::

**Theorem (Odd numbers).** For each $n$, $\sum_{i < n} (2i + 1) = n^2$. So $1 + 3 + \cdots + (2n - 1) = n^2$.

*Proof.* For $n = 0$, both sides are $0$. If the formula holds for $n$, then $\sum_{i < n + 1} (2i + 1) = n^2 + 2n + 1 = (n + 1)^2$. $\square$

**Theorem (Squares).** For each $n$, $$6 \sum_{i \in \mathrm{range}(n + 1)} i^2 = n(n + 1)(2n + 1).$$

*Proof.* For $n = 0$, the sum is $0^2 = 0$, and the right side is $0$. Assume the formula for $n$. The rule of one more term gives $6 \sum_{i < n + 2} i^2 = n(n + 1)(2n + 1) + 6(n + 1)^2$. Factor out $n + 1$: $$(n + 1)\bigl(n(2n + 1) + 6(n + 1)\bigr) = (n + 1)(2n^2 + 7n + 6) = (n + 1)(n + 2)(2n + 3).$$ The last step uses $(n + 2)(2n + 3) = 2n^2 + 7n + 6$. This is the formula for $n + 1$, because $2(n + 1) + 1 = 2n + 3$. $\square$

**Theorem (Factorial).** For each $n$, $\prod_{i \in \mathrm{range}\, n} (i + 1) = n!$.

*Proof.* The factorial is defined by $0! = 1$ and $(n + 1)! = (n + 1) \cdot n!$. For $n = 0$, the empty product is $1 = 0!$. If the formula holds for $n$, the rule of one more term for products gives $\prod_{i < n + 1} (i + 1) = n! \cdot (n + 1) = (n + 1)!$. $\square$

### Examples

**Example (A small sum).** The sum $\sum_{i < 5} i^2$ is $0 + 1 + 4 + 9 + 16 = 30$. The formula for the squares with $n = 4$ gives $6 \cdot 30 = 180 = 4 \cdot 5 \cdot 9$. In Lean, `decide` computes it.

<?lean MathlibHandbook/V03/C06/Examples.lean#notation?>

**Example (Gauss).** For $n = 101$, the theorem gives $2 \sum_{i < 101} i = 101 \cdot 100$, so $1 + 2 + \cdots + 100 = 5050$.

<?lean MathlibHandbook/V03/C06/Examples.lean#gauss?>

**Example (Odd numbers).** For $n = 5$: $1 + 3 + 5 + 7 + 9 = 25 = 5^2$. After `rw [sum_range_succ, ih]`, the goal is $n^2 + (2n + 1) = (n + 1)^2$, and `ring` closes it.

<?lean MathlibHandbook/V03/C06/Examples.lean#induction?>

**Example (Linear rules).** Let $s = \{1, 2, 3\}$, $f(i) = i$, $g(i) = i^2$ and $c = 4$. Then $\sum_{s} (4f + g) = (4 + 1) + (8 + 4) + (12 + 9) = 38$, and $4 \sum_s f + \sum_s g = 4 \cdot 6 + 14 = 38$.

<?lean MathlibHandbook/V03/C06/Examples.lean#linear?>

**Example (Factorial).** $\prod_{i < 5} (i + 1) = 1 \cdot 2 \cdot 3 \cdot 4 \cdot 5 = 120 = 5!$.

<?lean MathlibHandbook/V03/C06/Examples.lean#factorial?>

**Example (Card as a sum).** For $s = \{2, 3, 5, 7\}$, $\sum_{i \in s} 1 = 1 + 1 + 1 + 1 = 4 = |s|$.

<?lean MathlibHandbook/V03/C06/Examples.lean#card?>

**Counterexample (Subtraction in ℕ).** The Gauss formula has the form $2 \sum i = n(n - 1)$ and not $\sum i = n(n - 1)/2$. In `ℕ`, subtraction and division truncate, and a statement with them is harder to use. The rule $\sum (f - g) = \sum f - \sum g$ is false in `ℕ` in general. Take $s = \{0, 1\}$, $f(0) = 0$, $f(1) = 2$, $g(0) = 1$, $g(1) = 0$. Then $\sum_s (f - g) = (0 - 1) + (2 - 0) = 0 + 2 = 2$ in `ℕ`, but $\sum_s f - \sum_s g = 2 - 1 = 1$.

### Common errors

- A sum over `range n` stops at $n - 1$. The textbook sum $\sum_{k=1}^{n} k$ is `∑ k ∈ range (n + 1), k`, and not `∑ k ∈ range n, k`.
- A sum in `ℕ` of a term with subtraction or division is a trap. Cast to `ℤ` or `ℚ` first, or state the formula with a product, as in the Gauss form.
- The notation `∑ i ∈ s, f i * g i` is the sum of the products, not the product of the sum with `g i`. Write `(∑ i ∈ s, f i) * c` for the other meaning.

### The library around it

The file `Mathlib.Algebra.BigOperators.Group.Finset.Basic` has a rule of computation for each way to build a finset: `Finset.sum_empty`, `Finset.sum_singleton`, `Finset.sum_insert`, `Finset.sum_pair` for `{a, b}` with `a ≠ b`, `Finset.sum_cons`, and `Finset.sum_range_succ`, `Finset.sum_range_zero` and `Finset.sum_range_one` for ranges. These rules are in the simp set, so `simp [Finset.sum_range_succ]` expands a sum over a small range. The rule `Finset.sum_congr` changes the terms when they agree on `s`, and `Finset.sum_range_induction` proves a closed form from its recursion. Each rule has a twin for products, made by `to_additive`. The table at the end of the section lists the declarations of the two files.

### Exercises

1. (A) Write $\sum_{k=1}^{n} k^2$ and $\prod_{k=1}^{n} (2k - 1)$ as a sum and a product over `Finset.range`, without a subtraction in `ℕ`.
2. (A) Explain why `Finset.sum` needs a commutative monoid and `List.sum` does not.
3. (B) Prove that $\sum_{i < n} 2^i = 2^n - 1$ in `ℕ`. Use the form $\sum_{i < n} 2^i + 1 = 2^n$. Hint: induction on $n$ and the rule of one more term.
4. (B) Prove that $\prod_{i < n} (2i + 1) \cdot 2^n \cdot n! = (2n)!$. Hint: in the step, $(2n + 2)! = (2n + 2)(2n + 1)(2n)!$ and $2n + 2 = 2(n + 1)$.
5. (C) Prove by induction on $n$ that $\sum_{k=1}^{n} k \cdot k! = (n + 1)! - 1$, in the form $\sum_{k < n} (k + 1)(k + 1)! + 1 = (n + 1)!$ in `ℕ`.
6. (L) Prove the rule for the sum of a constant. The solution is `sum_const_example`.
7. (L) Prove that the product of a constant is a power. The solution is `prod_const_example`.
8. (L) Prove that two finite sums can change places. The solution is `sum_comm_example`.
9. (L) Prove that four times the sum of the cubes of $0, \ldots, n$ is $(n(n + 1))^2$. The solution is `sum_cubes_example`.

### Notes and history

The story says that Gauss, as a schoolboy in Braunschweig, found the sum $1 + 2 + \cdots + 100$ in a few moments, with the pairs $1 + 100$, $2 + 99$ and so on.  The sum of the squares is in the work *On Spirals* of Archimedes. The sign $\sum$ for a sum is due to Euler (1755), and the bounds below and above the sign to Fourier (1820).  Graham, Knuth and Patashnik, *Concrete Mathematics*, Chapter 2, is a standard reference for the manipulation of sums.

In Mathlib, the big operators come from the Lean 3 library, where Johannes Hölzl wrote the first file on finite sums and products in 2017. The notation `∑ x ∈ s, f x` replaced the older notation `∑ x in s, f x` in 2024. The file was later split into the files of the folder `Mathlib/Algebra/BigOperators/Group/Finset`.

### Reference

<?reference?>
