---
title: Intervals in an order
kind: theory
modules:
  - Mathlib.Order.Interval.Set.Defs
  - Mathlib.Order.Interval.Set.Basic
  - Mathlib.Order.Interval.Set.LinearOrder
explains:
  E3: [Set.Icc]
  E2: [Set.mem_Icc, Set.Icc_subset_Icc, Set.nonempty_Icc, Set.Icc_eq_empty, Set.Ico, Set.Ioo, Set.Icc_subset_Icc_iff, Set.Icc_inter_Icc, Set.Ico_union_Ico_eq_Ico, Set.Icc_union_Icc_eq_Icc, Set.nonempty_Ioo]
  E1: [Set.Ici, Set.Iic, Set.Ioi, Set.Iio, Set.Ioc, Set.mem_Ioo, Set.mem_Ico, Set.mem_Ioc, Set.mem_Ici, Set.Icc_self, Set.Ico_self, Set.Ioo_self, Set.Ioo_subset_Icc_self, Set.left_mem_Icc, Set.right_mem_Icc, Set.Icc_eq_empty_iff, Set.Ioo_eq_empty, Set.Ico_eq_empty, Set.nonempty_Ico, Set.Ici_inter_Iic, Set.Icc_union_Ioc_eq_Icc, Set.Ico_subset_Ico_iff]
families: []
requires: [V04.C01, V01.C02]
reads_with: ["MIL"]
lean:
  - MathlibHandbook/V04/C07/Examples.lean
  - MathlibHandbook/V04/C07/Exercises.lean
  - MathlibHandbook/V04/C07/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Intervals in an order

### Overview

An interval is the set of the elements between two bounds. The definition uses only the order, so it makes sense in each preorder: in $\mathbb{N}$, in $\mathbb{Z}$, in the subsets of a set, in the functions from a set to $\mathbb{R}$. Mathlib defines the intervals in this generality.

This section defines the nine kinds of intervals and gives their Mathlib names. It then proves when an interval is empty, when one interval is contained in another, what the intersection of two intervals is, and when a union of two intervals is an interval. Some facts hold in each preorder, some need antisymmetry, a lattice, a linear order or a dense order, and the examples show that each hypothesis is necessary.

### Definitions

The names of the intervals in Mathlib follow a code. The name starts with `I`. Two letters follow, the first for the left end and the second for the right end. The letter `c` means closed: the end belongs to the interval. The letter `o` means open: the end does not belong to the interval. The letter `i` means infinite: there is no bound on that side. So `Set.Icc a b` is $[a, b]$, `Set.Ico a b` is $[a, b)$ and `Set.Ioi a` is $(a, \infty)$.

**Definition (Bounded intervals).** Let $\alpha$ be a preorder and let $a, b \in \alpha$. The four bounded intervals with the ends $a$ and $b$ are:

- $[a, b] = \{x \in \alpha \mid a \le x \text{ and } x \le b\}$, in Mathlib `Set.Icc a b`;
- $[a, b) = \{x \in \alpha \mid a \le x \text{ and } x < b\}$, in Mathlib `Set.Ico a b`;
- $(a, b] = \{x \in \alpha \mid a < x \text{ and } x \le b\}$, in Mathlib `Set.Ioc a b`;
- $(a, b) = \{x \in \alpha \mid a < x \text{ and } x < b\}$, in Mathlib `Set.Ioo a b`.

**Definition (Unbounded intervals).** Let $a, b \in \alpha$. The four rays are $[a, \infty) = \{x \mid a \le x\}$, in Mathlib `Set.Ici a`, then $(a, \infty) = \{x \mid a < x\}$, in Mathlib `Set.Ioi a`, then $(-\infty, b] = \{x \mid x \le b\}$, in Mathlib `Set.Iic b`, and $(-\infty, b) = \{x \mid x < b\}$, in Mathlib `Set.Iio b`. The ninth interval is the whole type, $(-\infty, \infty)$. Mathlib has no special name for it and uses `Set.univ`.

*Remarks.* The definitions use $<$, which in a preorder means $a \le b$ and not $b \le a$ (Chapter 1). So $(a, b)$ is defined in each preorder. In a partial order, $a < b$ is the same as $a \le b$ and $a \ne b$, and this is the form that a student often uses for the real numbers.

The definition asks for two inequalities, $a \le x$ and $x \le b$, and nothing more. In a partial order that is not linear, an interval can contain elements that are not comparable. In the subsets of $\{1, 2\}$, the interval $[\emptyset, \{1, 2\}]$ contains $\{1\}$ and $\{2\}$.

::: mathlib
`Set.Icc` · `Mathlib.Order.Interval.Set.Defs`

The definition is `{x | a ≤ x ∧ x ≤ b}`, for a `Preorder`. The `simp` lemma `Set.mem_Icc` states `x ∈ Set.Icc a b ↔ a ≤ x ∧ x ≤ b`, and each interval has its membership lemma with the same pattern, such as `Set.mem_Ico` and `Set.mem_Ioo`. A proof of a membership is `simp only [Set.mem_Icc]` and then a proof of two inequalities.

<?decl Set.Icc?>
:::

::: mathlib
`Set.Ico` · `Mathlib.Order.Interval.Set.Defs`

The half-open interval `Set.Ico a b` is `{x | a ≤ x ∧ x < b}`. The library prefers it for sums and partitions: $[0, 1)$, $[1, 2)$, $[2, 3)$ are disjoint and cover $[0, \infty)$.

<?decl Set.Ico?>
:::

::: mathlib
`Set.Ioo` · `Mathlib.Order.Interval.Set.Defs`

The open interval `{x | a < x ∧ x < b}`. The open intervals are the basic open sets of the order topology.

<?decl Set.Ioo?>
:::

### Theorems and proofs

The first two results hold in each preorder. They use only reflexivity and transitivity.

**Theorem (Nonempty closed interval).** In a preorder, $[a, b]$ is nonempty if and only if $a \le b$. In particular, if $a \le b$, then $a \in [a, b]$ and $b \in [a, b]$.

*Proof.* Suppose $a \le b$. By reflexivity $a \le a$, so $a$ satisfies the two conditions $a \le a$ and $a \le b$. Thus $a \in [a, b]$, and the interval is nonempty. In the same way $a \le b$ and $b \le b$ give $b \in [a, b]$. Conversely, suppose that $x \in [a, b]$. Then $a \le x$ and $x \le b$, and transitivity gives $a \le b$. $\square$

**Theorem (Nonempty half-open interval).** In a preorder, $[a, b)$ is nonempty if and only if $a < b$, and the same holds for $(a, b]$.

*Proof.* If $a < b$, then $a \le a$ and $a < b$, so $a \in [a, b)$. Conversely, let $x \in [a, b)$. Then $a \le x$ and $x < b$. The mixed transitivity of Chapter 1 gives $a < b$. For $(a, b]$, the element $b$ is in the interval when $a < b$, and an element $x$ with $a < x \le b$ gives $a < b$ by the other mixed transitivity. $\square$

The open interval needs more. In $\mathbb{Z}$ the interval $(0, 1)$ is empty, although $0 < 1$. A preorder is *dense* if for any $a < b$ there is $c$ with $a < c < b$, as in $\mathbb{Q}$ and $\mathbb{R}$.

**Theorem (Nonempty open interval).** In a dense preorder, $(a, b)$ is nonempty if and only if $a < b$.

*Proof.* If $a < b$, density gives $c$ with $a < c$ and $c < b$, so $c \in (a, b)$. Conversely, an element $x$ with $a < x < b$ gives $a < b$ by transitivity of $<$. $\square$

**Theorem (Empty closed interval).** In a preorder, $[a, b] = \emptyset$ if and only if $\lnot (a \le b)$. In a linear order this condition is $b < a$.

*Proof.* The first claim is the negation of the two sides of the theorem on nonempty closed intervals. In a linear order, $\lnot (a \le b)$ is equivalent to $b < a$ by the lemma `not_le` of Chapter 1. $\square$

The next result is the first one that needs antisymmetry.

**Theorem (Degenerate intervals).** In a partial order, $[a, a] = \{a\}$. In a preorder, $[a, a)$, $(a, a]$ and $(a, a)$ are empty.

*Proof.* By reflexivity $a \in [a, a]$. Let $x \in [a, a]$. Then $a \le x$ and $x \le a$, and antisymmetry gives $x = a$. So $[a, a] = \{a\}$. For the second claim, an element $x$ of $[a, a)$ would satisfy $a \le x < a$, so $a < a$ by mixed transitivity, and this contradicts the irreflexivity of $<$. The other two cases are the same. $\square$

**Theorem (Inclusion of closed intervals).** Let $\alpha$ be a preorder.

1. If $a_2 \le a_1$ and $b_1 \le b_2$, then $[a_1, b_1] \subseteq [a_2, b_2]$.
2. If $a_1 \le b_1$, then $[a_1, b_1] \subseteq [a_2, b_2]$ holds if and only if $a_2 \le a_1$ and $b_1 \le b_2$.

*Proof.* 1. Let $x \in [a_1, b_1]$, so $a_1 \le x$ and $x \le b_1$. Then $a_2 \le a_1 \le x$ gives $a_2 \le x$, and $x \le b_1 \le b_2$ gives $x \le b_2$. So $x \in [a_2, b_2]$.

2. One direction is part 1. For the other, suppose $[a_1, b_1] \subseteq [a_2, b_2]$. Since $a_1 \le b_1$, the end $a_1$ is in $[a_1, b_1]$, so it is in $[a_2, b_2]$, and this gives $a_2 \le a_1$. In the same way $b_1 \in [a_1, b_1] \subseteq [a_2, b_2]$ gives $b_1 \le b_2$. $\square$

The hypothesis $a_1 \le b_1$ in part 2 is necessary: in $\mathbb{R}$, $[5, 0] = \emptyset \subseteq [1, 2]$, but $5 \le 2$ is false.

The intersection of two intervals uses the supremum and the infimum of a lattice (Chapter 3). In a linear order, $a_1 \sqcup a_2 = \max(a_1, a_2)$ and $b_1 \sqcap b_2 = \min(b_1, b_2)$.

**Theorem (Intersection).** In a lattice, $[a_1, b_1] \cap [a_2, b_2] = [a_1 \sqcup a_2, b_1 \sqcap b_2]$. In a preorder, $[a, \infty) \cap (-\infty, b] = [a, b]$.

*Proof.* The supremum is the least upper bound, so for each $x$, the element $x$ is above $a_1$ and above $a_2$ if and only if $a_1 \sqcup a_2 \le x$. This is the lemma `sup_le_iff`. In the same way $x$ is below $b_1$ and below $b_2$ if and only if $x \le b_1 \sqcap b_2$, by `le_inf_iff`. Now $x$ is in the intersection if and only if the four inequalities $a_1 \le x$, $a_2 \le x$, $x \le b_1$, $x \le b_2$ hold. By the two equivalences, this is the case if and only if $a_1 \sqcup a_2 \le x$ and $x \le b_1 \sqcap b_2$, that is, $x \in [a_1 \sqcup a_2, b_1 \sqcap b_2]$. The second claim is the definition: $x \in [a, \infty) \cap (-\infty, b]$ means $a \le x$ and $x \le b$. $\square$

The union of two intervals needs a linear order, for a split into two cases.

**Theorem (Union of adjacent intervals).** Let $\alpha$ be a linear order and let $a \le b \le c$. Then

1. $[a, b) \cup [b, c) = [a, c)$;
2. $[a, b] \cup [b, c] = [a, c]$;
3. $[a, b] \cup (b, c] = [a, c]$.

*Proof.* 1. First, each side of the union is in $[a, c)$. If $x \in [a, b)$, then $a \le x$, and $x < b \le c$ gives $x < c$. If $x \in [b, c)$, then $a \le b \le x$ gives $a \le x$, and $x < c$. Conversely, let $x \in [a, c)$, so $a \le x < c$. By totality, either $x < b$ or $b \le x$. In the first case $a \le x < b$, so $x \in [a, b)$. In the second case $b \le x < c$, so $x \in [b, c)$.

2. The inclusion of the union in $[a, c]$ is part 1 of the theorem on inclusion, applied twice: $[a, b] \subseteq [a, c]$ since $b \le c$, and $[b, c] \subseteq [a, c]$ since $a \le b$. Conversely, let $a \le x \le c$. If $x \le b$, then $x \in [a, b]$. Otherwise $b < x$ by totality, so $b \le x$ and $x \in [b, c]$.

3. The same argument as in part 2, with the cases $x \le b$ and $b < x$. In the second case $x \in (b, c]$. Each element of $(b, c]$ is in $[a, c]$, because $a \le b < x$. $\square$

The hypotheses $a \le b$ and $b \le c$ are needed. In $\mathbb{R}$, with $a = 0$, $b = 5$ and $c = 1$, the union $[0, 5) \cup [5, 1) = [0, 5) \cup \emptyset = [0, 5)$, which is not $[0, 1)$.

::: mathlib
`Set.nonempty_Icc` · `Mathlib.Order.Interval.Set.Basic`

The lemma states `(Set.Icc a b).Nonempty ↔ a ≤ b` in a preorder. The lemmas `Set.nonempty_Ico` and `Set.nonempty_Ioc` are the forms with `a < b`.

<?decl Set.nonempty_Icc?>
:::

::: mathlib
`Set.nonempty_Ioo` · `Mathlib.Order.Interval.Set.Basic`

The lemma takes the class `DenselyOrdered α`, the density of the text. Mathlib has the instance for `ℚ` and `ℝ`, and none for `ℤ`.

<?decl Set.nonempty_Ioo?>
:::

::: mathlib
`Set.Icc_eq_empty` · `Mathlib.Order.Interval.Set.Basic`

The hypothesis is `¬a ≤ b`. In a linear order, `not_le.mpr h` turns `h : b < a` into it. The equivalence is `Set.Icc_eq_empty_iff`.

<?decl Set.Icc_eq_empty?>
:::

::: mathlib
`Set.Icc_subset_Icc` · `Mathlib.Order.Interval.Set.Basic`

The lemma takes the inequality of the left ends and then that of the right ends.

<?decl Set.Icc_subset_Icc?>
:::

::: mathlib
`Set.Icc_subset_Icc_iff` · `Mathlib.Order.Interval.Set.Basic`

This is part 2 of the theorem, with the hypothesis `a₁ ≤ b₁` as an explicit argument.

<?decl Set.Icc_subset_Icc_iff?>
:::

::: mathlib
`Set.Icc_inter_Icc` · `Mathlib.Order.Interval.Set.Basic`

The statement is in a `Lattice`, with `⊔` and `⊓`. In a linear order these are `max` and `min` by `rfl`. The second claim of the theorem is `Set.Ici_inter_Iic`.

<?decl Set.Icc_inter_Icc?>
:::

::: mathlib
`Set.Ico_union_Ico_eq_Ico` · `Mathlib.Order.Interval.Set.LinearOrder`

The lemmas on unions need a `LinearOrder`, with the hypotheses `a ≤ b` and `b ≤ c`. The name gives the two intervals of the union and the result, as in `Set.Icc_union_Ioc_eq_Icc`.

<?decl Set.Ico_union_Ico_eq_Ico?>
:::

::: mathlib
`Set.Icc_union_Icc_eq_Icc` · `Mathlib.Order.Interval.Set.LinearOrder`

<?decl Set.Icc_union_Icc_eq_Icc?>
:::

### Examples

**Example (Membership).** The lemma `Set.mem_Icc` turns the membership into the two inequalities of the definition.

<?lean MathlibHandbook/V04/C07/Examples.lean#mem?>

**Example (A number in an open interval).** To prove $\frac12 \in (0, 1)$ in $\mathbb{R}$, the definition asks for $0 < \frac12$ and $\frac12 < 1$. The tactic `norm_num` unfolds the membership and proves the two inequalities.

<?lean MathlibHandbook/V04/C07/Examples.lean#half?>

**Example (Inclusion).** The interval $[1, 2]$ is in $[0, 3]$, by part 1 of the theorem on inclusion with $0 \le 1$ and $2 \le 3$.

<?lean MathlibHandbook/V04/C07/Examples.lean#subset?>

**Example (Computing an intersection).** In $\mathbb{R}$, $[0, 3] \cap [1, 5] = [\max(0, 1), \min(3, 5)] = [1, 3]$. When the two intervals do not meet, the formula still holds: $[0, 1] \cap [2, 3] = [2, 1]$, which is empty.

**Example (An empty interval).** The interval $[2, 1]$ in $\mathbb{R}$ is empty, because $2 \le 1$ is false.

<?lean MathlibHandbook/V04/C07/Examples.lean#empty?>

**Example (A singleton).** In a partial order, an interval with equal ends is a singleton, by antisymmetry.

<?lean MathlibHandbook/V04/C07/Examples.lean#self?>

**Counterexample (A degenerate interval in a preorder).** On $\mathbb{Z}$, define $m \preceq n$ when $|m| \le |n|$. This is a preorder: it is reflexive and transitive. It is not a partial order, because $1 \preceq -1$ and $-1 \preceq 1$. In this preorder the interval $[1, 1]$ is $\{x \mid |x| = 1\} = \{1, -1\}$. So antisymmetry is necessary in the theorem on degenerate intervals.

**Example (Union).** The intervals $[0, 1)$ and $[1, 2)$ of $\mathbb{R}$ make $[0, 2)$.

<?lean MathlibHandbook/V04/C07/Examples.lean#union?>

**Counterexample (A union in an order that is not linear).** In the subsets of $\{0, 1\}$, take $a = \emptyset$, $b = \{0\}$ and $c = \{0, 1\}$, so $a \le b \le c$. The interval $[a, b]$ is $\{\emptyset, \{0\}\}$ and $[b, c]$ is $\{\{0\}, \{0, 1\}\}$. Their union has three elements. The interval $[a, c]$ is the set of all four subsets, and it contains $\{1\}$. So $[a, b] \cup [b, c] \ne [a, c]$, and the theorem on unions fails without totality. The proof breaks at the case split, since $\{0\}$ and $\{1\}$ are not comparable.

### The library around it

The file `Mathlib.Order.Interval.Set.Defs` has the definitions and the membership lemmas, `Mathlib.Order.Interval.Set.Basic` has the lemmas for a preorder, a partial order and a lattice, and `Mathlib.Order.Interval.Set.LinearOrder` has the lemmas that need totality, such as the unions and `Set.compl_Ici`. The names in each family follow the pattern of the intervals: from `Set.Icc_subset_Icc` a reader can guess `Set.Ioo_subset_Ioo`. The lemmas `Set.left_mem_Icc` and `Set.right_mem_Icc` state that an end is in a closed interval when $a \le b$.

Most goals on intervals of numbers go in two steps: `simp only [Set.mem_Icc, Set.mem_Ioo]` to get inequalities, and then `linarith`, `norm_num` or `omega`.

### Exercises

1. (A) Write $(0, 1]$, $[2, \infty)$ and $(-\infty, 3)$ with the names of Mathlib. *Hint:* the first letter is for the left end.
2. (A) Compute $[0, 4] \cap [2, 6] \cap [3, 10]$ in $\mathbb{R}$. *Hint:* apply the theorem on intersection twice.
3. (A) Show that $(a, b) \subseteq [a, b)$ in a preorder. *Hint:* $a < x$ gives $a \le x$.
4. (B) Show that $(a, b)$ is empty when $\lnot (a < b)$, in each preorder. *Hint:* transitivity of $<$.
5. (B) In a linear order, show that $[a, b) \subseteq [a', b')$ implies $a' \le a$ and $b \le b'$ when $a < b$. Give a counterexample when $a = b$. *Hint:* the element $a$ is in $[a, b)$, and this gives $a' \le a$. For the right ends, suppose $b' < b$ and look at the element $\max(a, b')$.
6. (B) In a linear order, show that $(-\infty, a) \cup [a, \infty)$ is the whole type, and that the two sets are disjoint.
7. (C) Let $\alpha$ be a partial order with $a \le b$. Show that $[a, b] = [c, d]$ implies $a = c$ and $b = d$. Then let $\alpha$ be a dense linear order with $a < b$ and $c < d$, and show that $(a, b) = (c, d)$ implies $a = c$ and $b = d$. Show that the second claim fails in $\mathbb{Z}$. *Hint:* for the open intervals, suppose $c < a$ and use density to find $x$ with $c < x < \min(a, d)$. In $\mathbb{Z}$, look at empty open intervals.
8. (L) Prove that $3 \in [1, 5]$ in `ℝ`. The solution is `mem_Icc_example`.
9. (L) Prove that `Set.Ioo a b ⊆ Set.Icc a b`. The solution is `Ioo_subset_Icc_example`.
10. (L) Prove that $[0, 1]$ is nonempty in `ℝ`. The solution is `nonempty_Icc_example`.

### Notes and history

The notations for half-open intervals differ between books, for example $[a, b[$ in French texts and $[a, b)$ in English texts. Bourbaki, in the *Théorie des ensembles*, defines the intervals in an arbitrary ordered set, as this section does.

In Mathlib, Johannes Hölzl wrote the first version of `data.set.intervals.basic` in Lean 3 in 2017, and Mario Carneiro, Patrick Massot, Yury Kudryashov and Rémy Degenne extended it. The port to Lean 4 split it into the files of this section.

### Reference

<?reference?>
