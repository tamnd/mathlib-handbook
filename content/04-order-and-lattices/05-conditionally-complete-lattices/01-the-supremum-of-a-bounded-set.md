---
title: The supremum of a bounded set
kind: theory
modules:
  - Mathlib.Order.ConditionallyCompleteLattice.Defs
  - Mathlib.Order.ConditionallyCompleteLattice.Basic
explains:
  E3: [ConditionallyCompleteLattice, ConditionallyCompleteLinearOrder]
  E2: [le_csSup, csSup_le, isLUB_csSup, exists_lt_of_lt_csSup, IsLUB.csSup_eq, csSup_eq_of_forall_le_of_forall_lt_exists_gt]
  E1: [IsLUB, BddAbove, BddBelow, upperBounds, csSup_le_iff, le_csSup_iff, csSup_le_csSup, csInf_le, le_csInf, isGLB_csInf, exists_lt_of_csInf_lt, csSup_singleton, csSup_Icc, bddAbove_Icc, csSup_pair, csSup_union, csSup_insert, csInf_le_csSup, csSup_of_not_bddAbove, Real.sSup_empty, Real.sSup_univ, Real.sSup_of_not_bddAbove, Real.sSup_def, Real.exists_isLUB, Real.add_neg_lt_sSup, Real.sSup_le, Real.sSup_nonneg, Real.instConditionallyCompleteLinearOrder, Nat.sSup_def, Nat.sSup_mem, Nat.sSup_of_not_bddAbove, Int.csSup_mem]
families: []
requires: [V04.C04]
reads_with: ["MIL"]
lean:
  - MathlibHandbook/V04/C05/Examples.lean
  - MathlibHandbook/V04/C05/Exercises.lean
  - MathlibHandbook/V04/C05/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The supremum of a bounded set

### Overview

The completeness axiom of the real numbers says that a nonempty set of reals that is bounded above has a least upper bound. The limit of a monotone sequence, the intermediate value theorem and the existence of $\sqrt{2}$ all follow from it. The reals are not a complete lattice, because $\mathbb{R}$ and the empty set have no least upper bound in $\mathbb{R}$. A *conditionally complete lattice* is a lattice in which the sets that are nonempty and bounded have a supremum and an infimum.

This section defines the class, proves the basic properties of the supremum of a bounded set, and proves that $\mathbb{Q}$ is not conditionally complete. In Mathlib, `sSup s` has a value for each set `s`. For the empty set and for an unbounded set this is a junk value, and each lemma about `sSup` has the hypotheses that make the value meaningful.

### Definitions

**Definition (Bounds).** Let $P$ be a preorder and $S \subseteq P$. The set of the *upper bounds* of $S$ is $U(S) = \{ b \in P \mid s \le b \text{ for each } s \in S \}$. The set $S$ is *bounded above* if $U(S)$ is not empty. The lower bounds $L(S)$ and the property *bounded below* are dual.

**Definition (Least upper bound).** An element $a$ is a *least upper bound* of $S$ if $a \in U(S)$ and $a \le b$ for each $b \in U(S)$. In other words, $a$ is the least element of $U(S)$.

In a partial order the least upper bound is unique when it exists, by antisymmetry. The interval $(0, 1)$ has no greatest element, but it has the least upper bound $1$, which is not a member of the set.

::: mathlib
`IsLUB` · `Mathlib.Order.Bounds.Defs`

`IsLUB s a` is the proposition `IsLeast (upperBounds s) a`. It needs no operation `sSup`, so it makes sense in every preorder, for example in `ℚ`. The predicate `BddAbove s` is `(upperBounds s).Nonempty`. The lemma `IsLUB.csSup_eq` turns `IsLUB s a` into `sSup s = a`.

<?decl IsLUB?>
:::

**Definition (Conditionally complete lattice).** A *conditionally complete lattice* is a lattice $P$ with operations $\sup$ and $\inf$ on the subsets of $P$, such that:

1. if $S$ is nonempty and bounded above, then $\sup S$ is the least upper bound of $S$;
2. if $S$ is nonempty and bounded below, then $\inf S$ is the greatest lower bound of $S$.

A *conditionally complete linear order* is a conditionally complete lattice whose order is linear.

The definition says nothing about $\sup S$ when $S$ is empty or unbounded. Mathlib asks for a total function, and the value on these sets is a free choice of each instance. The empty set must be excluded: each element is an upper bound of $\emptyset$, so a least upper bound of $\emptyset$ is a least element of $P$, and $\mathbb{R}$ has none. The unbounded sets must be excluded: $U(\mathbb{N}) = \emptyset$ in $\mathbb{R}$, and $\emptyset$ has no least element.

::: mathlib
`ConditionallyCompleteLattice` · `Mathlib.Order.ConditionallyCompleteLattice.Defs`

The class extends `Lattice`, `SupSet` and `InfSet`, so `sSup` and `sInf` are total functions `Set α → α`. Its axioms are `isLUB_csSup` and `isGLB_csInf`, each with the hypotheses `s.Nonempty` and `BddAbove s` or `BddBelow s`. Each complete lattice is a conditionally complete lattice with the same `sSup`. The instance for `ℝ` is `Real.instConditionallyCompleteLinearOrder`.

<?decl ConditionallyCompleteLattice?>
:::

::: mathlib
`ConditionallyCompleteLinearOrder` · `Mathlib.Order.ConditionallyCompleteLattice.Defs`

The linear class adds the axiom `csSup_of_not_bddAbove`: `sSup s = sSup ∅` for an unbounded set, and dually for `sInf`. So all the junk values of `sSup` are one element, `sSup ∅`, which is `0` on `ℝ`.

<?decl ConditionallyCompleteLinearOrder?>
:::

### Theorems and proofs

Let $P$ be a conditionally complete lattice and $S \subseteq P$. The first two theorems are the axioms in the form that a proof uses, each with the hypothesis it needs and no other.

**Theorem (Upper bound).** If $S$ is bounded above and $a \in S$, then $a \le \sup S$.

*Proof.* The set $S$ is nonempty because $a \in S$, and it is bounded above by hypothesis. By the axiom, $\sup S$ is the least upper bound of $S$. In particular it is an upper bound of $S$, so $a \le \sup S$. $\square$

**Theorem (Least).** If $S$ is nonempty and $b$ is an upper bound of $S$, then $\sup S \le b$.

*Proof.* The element $b$ shows that $S$ is bounded above. With the hypothesis that $S$ is nonempty, the axiom says that $\sup S$ is the least upper bound. So it is below the upper bound $b$. $\square$

In the theorem "Upper bound", $a \in S$ gives that $S$ is nonempty. In the theorem "Least", $b$ gives that $S$ is bounded above. So `le_csSup` takes `BddAbove s` and `csSup_le` takes `s.Nonempty`.

**Theorem (Monotonicity).** If $S \subseteq T$, $S$ is nonempty and $T$ is bounded above, then $\sup S \le \sup T$.

*Proof.* The set $S$ is bounded above, since each upper bound of $T$ is an upper bound of $S$. Let $s \in S$. Then $s \in T$, and $T$ is bounded above, so $s \le \sup T$ by the theorem "Upper bound". So $\sup T$ is an upper bound of $S$. Since $S$ is nonempty, the theorem "Least" gives $\sup S \le \sup T$. $\square$

**Theorem (Approximation).** Let $P$ be a conditionally complete linear order, let $S$ be nonempty and let $b < \sup S$. Then there is $a \in S$ with $b < a$.

*Proof.* Suppose that no such $a$ exists. Then for each $a \in S$, $b < a$ is false, and in a linear order this gives $a \le b$. So $b$ is an upper bound of $S$. The set $S$ is nonempty, so the theorem "Least" gives $\sup S \le b$. This contradicts $b < \sup S$. $\square$

The proof does not use that $S$ is bounded above. For the reals, with $\varepsilon > 0$ and $b = \sup S - \varepsilon$, the theorem gives $a \in S$ with $\sup S - \varepsilon < a \le \sup S$.

**Theorem (Characterization).** Let $P$ be a conditionally complete lattice and let $S$ be nonempty. Let $u \in P$ satisfy: $s \le u$ for each $s \in S$, and for each $w < u$ there is $s \in S$ with $w < s$. Then $\sup S = u$.

*Proof.* The first condition says that $u$ is an upper bound, so $S$ is bounded above and $\sup S \le u$ by the theorem "Least". Suppose $\sup S < u$. Apply the second condition with $w = \sup S$: there is $s \in S$ with $\sup S < s$. But $s \le \sup S$ by the theorem "Upper bound". This is a contradiction. So $\sup S \le u$ and $\sup S \ne u$ cannot both hold, and $\sup S = u$. $\square$

This is the usual way to compute a supremum: guess the value $u$, show that it is an upper bound, and show that nothing smaller is an upper bound.

::: mathlib
`csSup_eq_of_forall_le_of_forall_lt_exists_gt` · `Mathlib.Order.ConditionallyCompleteLattice.Basic`

The long name lists the hypotheses: nonempty, `∀ a ∈ s, a ≤ b`, and `∀ w < b, ∃ a ∈ s, w < a`. Mathlib states it for a conditionally complete lattice, as in the text. A second route is to prove `IsLUB s b` and to apply `IsLUB.csSup_eq`.

<?decl csSup_eq_of_forall_le_of_forall_lt_exists_gt?>
:::

The next two theorems compare $\mathbb{Z}$ and $\mathbb{Q}$ with $\mathbb{R}$.

**Theorem (Integers).** Let $S \subseteq \mathbb{Z}$ be nonempty and bounded above. Then $S$ has a greatest element. So $\mathbb{Z}$ is a conditionally complete linear order, and $\sup S \in S$.

*Proof.* Let $b$ be an upper bound of $S$. The set $D = \{ b - s \mid s \in S \}$ consists of natural numbers, since $s \le b$, and it is nonempty. By the well ordering of $\mathbb{N}$, it has a least element $b - s_0$ with $s_0 \in S$. For each $s \in S$, $b - s_0 \le b - s$, so $s \le s_0$. Thus $s_0$ is the greatest element of $S$, and so it is the least upper bound. The same argument with $s - b$ for a lower bound $b$ gives the least element of a nonempty set that is bounded below. $\square$

**Theorem (The rationals are not conditionally complete).** The set $S = \{ x \in \mathbb{Q} \mid x^2 < 2 \}$ is nonempty and bounded above in $\mathbb{Q}$, and it has no least upper bound in $\mathbb{Q}$.

*Proof.* $0 \in S$, and $2$ is an upper bound: if $x > 2$, then $x^2 > 4$. Suppose $r \in \mathbb{Q}$ is a least upper bound. Since $1 \in S$, $r \ge 1 > 0$. There are three cases.

Case $r^2 < 2$. Let $h = (2 - r^2)/(2r + 1)$. Then $h > 0$, and $h < 1$ because $2 - r^2 \le 1 < 2r + 1$. So $h^2 < h$ and
$$(r + h)^2 = r^2 + 2rh + h^2 < r^2 + 2rh + h = r^2 + h(2r + 1) = 2.$$
So $r + h \in S$ and $r + h > r$. This contradicts that $r$ is an upper bound.

Case $r^2 > 2$. Let $k = (r^2 - 2)/(2r)$. Then $k > 0$, and $k < r$ because $r^2 - 2 < 2r^2$. So $r - k > 0$ and
$$(r - k)^2 = r^2 - 2rk + k^2 > r^2 - 2rk = 2.$$
Now $r - k$ is an upper bound of $S$. Indeed, let $x \in S$. If $x \le 0$, then $x < r - k$. If $x > 0$ and $x > r - k$, then $x^2 > (r - k)^2 > 2$, which is false for $x \in S$. So $x \le r - k$. Thus $r - k$ is an upper bound smaller than $r$, which contradicts that $r$ is least.

Case $r^2 = 2$. This is impossible for a rational $r$: if $r = p/q$ in lowest terms, then $p^2 = 2q^2$, so $p$ is even, $p = 2p'$, and $q^2 = 2p'^2$, so $q$ is even too. $\square$

In $\mathbb{R}$, the same set has the supremum $\sqrt{2}$.

::: mathlib
`le_csSup` · `Mathlib.Order.ConditionallyCompleteLattice.Basic`

The lemma takes a proof of `BddAbove s` and a proof of `a ∈ s`. Compare it with `le_sSup` of a complete lattice, which needs only the second proof. The lemma `le_csSup_of_le` combines it with transitivity.

<?decl le_csSup?>
:::

::: mathlib
`csSup_le` · `Mathlib.Order.ConditionallyCompleteLattice.Basic`

The lemma takes a proof of `s.Nonempty` and a proof that `b` is an upper bound. The lemma `csSup_le_iff` is the equivalence, with both hypotheses. For the reals there is a variant without nonemptiness: `Real.sSup_le` needs `0 ≤ a` in its place, because `sSup ∅ = 0`.

<?decl csSup_le?>
:::

::: mathlib
`exists_lt_of_lt_csSup` · `Mathlib.Order.ConditionallyCompleteLattice.Basic`

This is the theorem "Approximation". It needs `s.Nonempty` and no bound, as in the proof. The dual is `exists_lt_of_csInf_lt`. For the reals, the form `Real.add_neg_lt_sSup` takes `ε < 0` and gives `a ∈ s` with `sSup s + ε < a`.

<?decl exists_lt_of_lt_csSup?>
:::

### Examples

**Example (An element is below the supremum).**

<?lean MathlibHandbook/V04/C05/Examples.lean#le_csSup?>

**Example (The supremum is below an upper bound).**

<?lean MathlibHandbook/V04/C05/Examples.lean#csSup_le?>

**Example (The least upper bound).**

<?lean MathlibHandbook/V04/C05/Examples.lean#isLUB?>

**Example (Approximation).** This lemma is the usual way to use the supremum in an epsilon argument.

<?lean MathlibHandbook/V04/C05/Examples.lean#approx?>

**Example (A closed interval).** The lemma `csSup_Icc` needs only the hypothesis $a \le b$. The supremum of $[a, b]$ is its greatest element $b$.

<?lean MathlibHandbook/V04/C05/Examples.lean#icc?>

**Example (A computed supremum).** Let $S = \{ 1 - 1/n \mid n \ge 1 \} \subseteq \mathbb{R}$. Then $\sup S = 1$. Use the theorem "Characterization" with $u = 1$. The set is nonempty, since $0 \in S$. Each member satisfies $1 - 1/n < 1$. Let $w < 1$. By the Archimedean property there is an integer $n \ge 1$ with $n > 1/(1 - w)$, so $1/n < 1 - w$ and $w < 1 - 1/n$. So nothing below $1$ is an upper bound. The infimum of $S$ is its least element $0$, at $n = 1$. The supremum is not a member of $S$.

**Example (The square root of two).** Let $S = \{ x \in \mathbb{R} \mid x^2 < 2 \}$ and $u = \sup S$, which exists since $0 \in S$ and $2$ is an upper bound. The proof of the theorem on $\mathbb{Q}$ works word for word in $\mathbb{R}$ for the cases $u^2 < 2$ and $u^2 > 2$. So $u^2 = 2$, and $u > 0$. This proves that $2$ has a positive square root in $\mathbb{R}$. The same argument with $x^n < c$ proves that each $c > 0$ has a positive $n$-th root.

**Example (The natural numbers).** In $\mathbb{N}$, a nonempty set that is bounded above is finite, and its greatest element is the supremum. So $\sup \{ n \mid n^2 < 30 \} = 5$, since $5^2 = 25 < 30 \le 36 = 6^2$ and the set is $\{0, 1, 2, 3, 4, 5\}$. In Mathlib, `Nat.sSup_mem` states that the supremum is a member.

**Example (Junk values).** In `ℝ`, the supremum of the empty set is `0`, and the supremum of a set that is not bounded above is `0`. In `ℕ`, the supremum of the empty set is `0` too, and here it is the true least upper bound of $\emptyset$, because `0` is the least natural number. The supremum of an unbounded set of natural numbers is again `0` (`Nat.sSup_of_not_bddAbove`).

<?lean MathlibHandbook/V04/C05/Examples.lean#junk?>

**Counterexample (A false lemma).** The statement `∀ s : Set ℝ, ∀ a ∈ s, a ≤ sSup s` is false. For $s = \mathbb{N} \subseteq \mathbb{R}$ and $a = 1$, the value of `sSup s` is `0`, and $1 \le 0$ is false. So `le_csSup` needs the hypothesis `BddAbove s`. In the same way `csSup_le` needs `s.Nonempty`: for $s = \emptyset$ and $b = -1$, each member of $s$ is below $b$, since there is none, but `sSup ∅ = 0` is not below $-1$.

### The library around it

The lemmas of a conditionally complete lattice have a `c` in front of the name of the lemma of a complete lattice: `le_csSup`, `csSup_le`, `csInf_le`, `csSup_le_csSup`, `csSup_union`. The extra hypotheses are `Nonempty` and `BddAbove` or `BddBelow`. The hypothesis `BddAbove` comes from `bddAbove_Icc`, `BddAbove.mono`, `BddAbove.union` and `Set.Finite.bddAbove`. The explicit values are `csSup_singleton`, `csSup_pair` and `csSup_Icc`. For the integers, `Int.csSup_mem` gives the theorem "Integers".

For the reals, `Real.exists_isLUB` is the completeness axiom, and `Real.sSup_empty` and `Real.sSup_of_not_bddAbove` state the junk values. The lemmas `Real.sSup_nonneg` and `Real.sSup_le` use the junk value `0` to drop a hypothesis. The types `ℝ≥0∞` and `EReal` are complete lattices, so their lemmas need no hypothesis.

### Exercises

1. (A) Give the value of `sSup (Set.Ioi (0 : ℝ))` in Mathlib, and say why it is a junk value.
2. (A) Explain why `le_csSup` needs `BddAbove s` and `csSup_le` needs `s.Nonempty`.
3. (A) Compute $\sup$ and $\inf$ of $\{ (-1)^n (1 + 1/n) \mid n \ge 1 \}$ in $\mathbb{R}$. *Hint:* split the even and the odd $n$.
4. (B) Show that $\sup \{a\} = a$ in a conditionally complete lattice.
5. (B) Show that $\sup\, (0, 1) = 1$ in $\mathbb{R}$, with the theorem "Characterization".
6. (B) Show that $\sup S \le \sup T$ when $S \subseteq T$, $S$ is nonempty and $T$ is bounded above, and give a counterexample in $\mathbb{R}$ when $S$ is empty and $T = [-2, -1]$.
7. (B) Let $S \subseteq \mathbb{R}$ be nonempty and bounded below, and let $-S = \{ -s \mid s \in S \}$. Show that $\inf S = -\sup (-S)$. *Hint:* $x \mapsto -x$ reverses the order.
8. (C) Show that each nonempty subset of $\mathbb{Q}$ that is bounded above has a least upper bound in $\mathbb{R}$, and that the map $S \mapsto \sup S$ from the Dedekind cuts of $\mathbb{Q}$ to $\mathbb{R}$ is a bijection that keeps the order.
9. (L) Prove that $2 \le \sup\, [0, 2]$. The solution is `le_csSup_two_example`.
10. (L) Prove that a nonempty set of reals with the upper bound $1$ has a supremum at most $1$. The solution is `csSup_le_one_example`.
11. (L) Prove that the supremum of the empty set of reals is $0$. The solution is `sSup_empty_real_example`.

### Notes and history

Bolzano used the least upper bound in 1817 in his proof of the intermediate value theorem, without a construction of the reals. Dedekind gave the completeness of the reals in 1872 with his cuts, and Cantor gave a construction with Cauchy sequences in the same year. Rudin, *Principles of mathematical analysis*, Chapter 1, takes the least upper bound property as the definition of completeness.

Mathlib builds the reals from Cauchy sequences of rationals and proves the completeness axiom as a theorem. The junk value `0` of `sSup` on `ℝ` follows the other junk values of Mathlib, such as `x / 0 = 0`.

### Reference

<?reference?>
