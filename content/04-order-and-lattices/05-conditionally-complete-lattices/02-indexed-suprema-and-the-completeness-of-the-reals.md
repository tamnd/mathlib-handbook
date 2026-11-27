---
title: Indexed suprema and the completeness of the reals
kind: theory
modules:
  - Mathlib.Order.ConditionallyCompleteLattice.Indexed
  - Mathlib.Order.ConditionallyCompletePartialOrder.Indexed
  - Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
explains:
  E3: [ConditionallyCompleteLinearOrderBot, Monotone.ciSup_mem_iInter_Icc_of_antitone]
  E2: [le_ciSup, ciSup_le, exists_lt_of_lt_ciSup, ciSup_mono, isLUB_ciSup, Monotone.csSup_image_le, Monotone.le_csSup_image, csSup_add]
  E1: auto
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

## Indexed suprema and the completeness of the reals

### Overview

In analysis the supremum is most often the supremum of a family, such as a sequence $(a_n)$. This section treats the indexed supremum $\bigsqcup_i f(i)$ in a conditionally complete lattice, with its hypotheses: the index set must be nonempty and the family must be bounded above.

With the indexed supremum, the completeness of $\mathbb{R}$ gives three classical theorems in order form. A monotone sequence that is bounded above has all its late terms close to its supremum. A decreasing sequence of closed intervals has a nonempty intersection, the nested interval theorem. The supremum of a sum of two sets is the sum of the suprema. The section also treats a monotone map applied to a bounded set, and the class of conditionally complete linear orders with a bottom element, such as $\mathbb{N}$ and $[0, \infty)$, where the supremum of the empty set is a true supremum. Limits belong to the topology volumes.

### Definitions

Let $P$ be a conditionally complete lattice, $I$ a set and $f : I \to P$ a family.

**Definition (Indexed supremum).** The *supremum* of $f$ is $\bigsqcup_{i \in I} f(i) = \sup \{ f(i) \mid i \in I \}$, the supremum of the range of $f$. The family is *bounded above* if its range is bounded above. The infimum $\bigsqcap_{i \in I} f(i)$ and the property *bounded below* are dual.

The range of $f$ is nonempty exactly when $I$ is nonempty. So the two conditions of the definition of a conditionally complete lattice become: $I$ is nonempty and $f$ is bounded above. When one of them fails, the value is a junk value.

::: mathlib
`le_ciSup` · `Mathlib.Order.ConditionallyCompleteLattice.Indexed`

The notation `⨆ i, f i` is `iSup f`, defined as `sSup (Set.range f)` for any type with an `SupSet` instance. In a conditionally complete lattice the lemmas have the prefix `c`, as for `sSup`. The lemma `le_ciSup` takes `BddAbove (Set.range f)` and an index `c`, and gives `f c ≤ ⨆ i, f i`. The boundedness hypothesis is written for the range, so a proof often starts with `⟨M, Set.forall_mem_range.2 h⟩` from a bound `h : ∀ i, f i ≤ M`.

<?decl le_ciSup?>
:::

::: mathlib
`ciSup_le` · `Mathlib.Order.ConditionallyCompleteLattice.Indexed`

The nonemptiness of the index type is the instance argument `[Nonempty ι]`, not an explicit hypothesis. For `ι = ℕ` Lean finds it at once. For an index type that may be empty, the reader must supply the instance or use a variant for a bottom element. The lemma `ciSup_le_iff` is the equivalence and needs both hypotheses.

<?decl ciSup_le?>
:::

**Definition (Conditionally complete linear order with a bottom).** A *conditionally complete linear order with a bottom* is a conditionally complete linear order $P$ with a least element $\bot$ such that $\sup \emptyset = \bot$.

In such an order $\bot$ is the true least upper bound of $\emptyset$, since every element is an upper bound of $\emptyset$ and $\bot$ is the least element. So the nonemptiness hypothesis disappears from the statements about $\sup$: if $b$ is an upper bound of $S$, then $\sup S \le b$, also for $S = \emptyset$. The natural numbers and the nonnegative reals $[0, \infty)$ are examples. The reals are not, since they have no least element.

::: mathlib
`ConditionallyCompleteLinearOrderBot` · `Mathlib.Order.ConditionallyCompleteLattice.Defs`

The class extends `ConditionallyCompleteLinearOrder` and `OrderBot` with the axiom `csSup_empty : sSup ∅ = ⊥`. The instances include `ℕ` (`Nat.instConditionallyCompleteLinearOrderBot`) and `ℝ≥0` (`NNReal.instConditionallyCompleteLinearOrderBot`). The lemmas `csSup_le'` and `ciSup_le'` are the forms of `csSup_le` and `ciSup_le` with no nonemptiness hypothesis. The prime in the name marks this variant.

<?decl ConditionallyCompleteLinearOrderBot?>
:::

### Theorems and proofs

The basic properties of the indexed supremum are those of the previous section, applied to the range. Let $P$ be a conditionally complete lattice and $f : I \to P$.

**Theorem (Basic properties).**

1. If $f$ is bounded above, then $f(j) \le \bigsqcup_i f(i)$ for each $j \in I$.
2. If $I$ is nonempty and $f(i) \le c$ for each $i$, then $\bigsqcup_i f(i) \le c$.
3. If $f(i) \le g(i)$ for each $i$ and $g$ is bounded above, then $\bigsqcup_i f(i) \le \bigsqcup_i g(i)$.
4. If $P$ is linear, $I$ is nonempty and $b < \bigsqcup_i f(i)$, then $b < f(i)$ for some $i$.

*Proof.* Let $R = \{ f(i) \mid i \in I \}$. Part 1: $f(j) \in R$ and $R$ is bounded above, so $f(j) \le \sup R$ by the theorem "Upper bound" of the previous section. Part 2: $R$ is nonempty and $c$ is an upper bound of $R$, so $\sup R \le c$ by the theorem "Least".

Part 3. If $I$ is empty, both sides are $\sup \emptyset$ and the claim holds. Let $I$ be nonempty. For each $i$, part 1 for $g$ gives $f(i) \le g(i) \le \bigsqcup_j g(j)$. Part 2 for $f$ with $c = \bigsqcup_j g(j)$ gives the claim.

Part 4 is the theorem "Approximation" for the nonempty set $R$: there is a member $f(i)$ of $R$ with $b < f(i)$. $\square$

In part 3, $f$ is bounded above because $g$ is, so the hypothesis on $f$ is not needed.

::: mathlib
`exists_lt_of_lt_ciSup` · `Mathlib.Order.ConditionallyCompleteLattice.Indexed`

This is part 4. It needs a conditionally complete linear order and `[Nonempty ι]`. Part 3 is `ciSup_mono`, whose only hypothesis is `BddAbove (Set.range g)`, as in the text. The statement that `⨆ i, f i` is the least upper bound of the range is `isLUB_ciSup`.

<?decl exists_lt_of_lt_ciSup?>
:::

The first application is the order form of the monotone convergence theorem.

**Theorem (Monotone sequences).** Let $(a_n)_{n \in \mathbb{N}}$ be an increasing sequence of real numbers, $a_n \le a_{n+1}$, that is bounded above, and let $c = \bigsqcup_n a_n$. Then $a_n \le c$ for each $n$, and for each $\varepsilon > 0$ there is $N$ with $c - \varepsilon < a_n \le c$ for each $n \ge N$.

*Proof.* The inequality $a_n \le c$ is part 1 of the basic properties. Let $\varepsilon > 0$. Then $c - \varepsilon < c$, and part 4 gives $N$ with $c - \varepsilon < a_N$. For $n \ge N$, the sequence is increasing, so $a_N \le a_n$ by induction on $n - N$. Thus $c - \varepsilon < a_N \le a_n \le c$. $\square$

This is the statement that $a_n$ converges to $c$, written without the word limit. The topology volume derives the limit form from this theorem. The completeness of $\mathbb{R}$ enters only through the existence of $c$.

The second application is the nested interval theorem.

**Theorem (Nested intervals).** Let $(a_n)$ and $(b_n)$ be sequences in a conditionally complete lattice, with $(a_n)$ increasing, $(b_n)$ decreasing, and $a_n \le b_n$ for each $n$. Let $c = \bigsqcup_n a_n$. Then $a_n \le c \le b_n$ for each $n$, so $c \in \bigcap_n [a_n, b_n]$. In $\mathbb{R}$, if in addition $\bigsqcap_n (b_n - a_n) = 0$, then the intersection is exactly $\{c\}$.

*Proof.* Step 1: $a_m \le b_n$ for all $m$ and $n$. Let $k = \max(m, n)$. Since $(a_n)$ increases, $a_m \le a_k$. By hypothesis $a_k \le b_k$. Since $(b_n)$ decreases, $b_k \le b_n$. So $a_m \le b_n$.

Step 2: the bounds of $c$. Fix $n$. By Step 1, $b_n$ is an upper bound of the family $(a_m)_m$. So the family is bounded above, and the index set $\mathbb{N}$ is nonempty. Part 1 of the basic properties gives $a_n \le c$, and part 2 gives $c \le b_n$. So $c \in [a_n, b_n]$ for each $n$.

Step 3: uniqueness in $\mathbb{R}$. Let $x$ and $y$ be in every $[a_n, b_n]$. Then $|x - y| \le b_n - a_n$ for each $n$, because two points of an interval are at distance at most its length. So $|x - y|$ is a lower bound of the family $(b_n - a_n)$, and by the dual of part 2, $|x - y| \le \bigsqcap_n (b_n - a_n) = 0$. Thus $x = y$. $\square$

Step 2 is the only place where completeness is used. In $\mathbb{Q}$ the theorem fails: the example below gives nested intervals with rational ends whose intersection in $\mathbb{Q}$ is empty.

::: mathlib
`Monotone.ciSup_mem_iInter_Icc_of_antitone` · `Mathlib.Order.ConditionallyCompletePartialOrder.Indexed`

The statement is Steps 1 and 2: for `f` monotone, `g` antitone and `f ≤ g`, the supremum `⨆ n, f n` lies in `⋂ n, Set.Icc (f n) (g n)`. Mathlib states it in more generality than the text. The index type is any directed preorder, not only `ℕ`, since Step 1 only needs a common upper index $k$ for $m$ and $n$. The values are in a `ConditionallyCompletePartialOrderSup`, a class weaker than a lattice that has just enough to state the result.

<?decl Monotone.ciSup_mem_iInter_Icc_of_antitone?>
:::

The third application concerns a monotone map. It gives the two inequalities that hold without continuity.

**Theorem (Monotone image).** Let $P$ be a preorder, $Q$ a conditionally complete lattice and $g : P \to Q$ monotone. Let $S \subseteq P$ and let $B$ be an upper bound of $S$.

1. If $c \in S$, then $g(c) \le \sup g(S)$.
2. If $S$ is nonempty, then $\sup g(S) \le g(B)$.

*Proof.* For $s \in S$, $s \le B$, so $g(s) \le g(B)$. Thus $g(B)$ is an upper bound of $g(S)$, and $g(S)$ is bounded above. Part 1: $g(c) \in g(S)$, so $g(c) \le \sup g(S)$ by the theorem "Upper bound". Part 2: $g(S)$ is nonempty because $S$ is, and $g(B)$ is an upper bound, so $\sup g(S) \le g(B)$ by the theorem "Least". $\square$

When $P$ is also a conditionally complete lattice and $S$ is nonempty and bounded above, part 2 with $B = \sup S$ gives $\sup g(S) \le g(\sup S)$. The equality needs more than monotonicity: a counterexample is below, and the left continuity of $g$ is the missing hypothesis.

::: mathlib
`Monotone.csSup_image_le` · `Mathlib.Order.ConditionallyCompleteLattice.Basic`

This is part 2, with the hypotheses `s.Nonempty` and `B ∈ upperBounds s`. Part 1 is `Monotone.le_csSup_image`, which takes `c ∈ s` and `BddAbove s`. The domain is only a preorder, so the lemmas apply to a monotone function on any ordered type.

<?decl Monotone.csSup_image_le?>
:::

The last theorem uses the group structure of $\mathbb{R}$. For sets $S, T \subseteq \mathbb{R}$ let $S + T = \{ s + t \mid s \in S, t \in T \}$.

**Theorem (Supremum of a sum).** Let $S, T \subseteq \mathbb{R}$ be nonempty and bounded above. Then $S + T$ is nonempty and bounded above, and $\sup (S + T) = \sup S + \sup T$.

*Proof.* Write $u = \sup S$ and $v = \sup T$. For $s \in S$ and $t \in T$, $s \le u$ and $t \le v$, so $s + t \le u + v$. So $u + v$ is an upper bound of $S + T$. The set $S + T$ is nonempty, since $S$ and $T$ are. So $\sup (S + T) \le u + v$.

For the other inequality, let $w = \sup (S + T)$. Fix $t \in T$. For each $s \in S$, $s + t \in S + T$, so $s + t \le w$ and $s \le w - t$. So $w - t$ is an upper bound of $S$ and $u \le w - t$, which is $t \le w - u$. This holds for each $t \in T$, so $w - u$ is an upper bound of $T$ and $v \le w - u$. Thus $u + v \le w$. Antisymmetry gives $w = u + v$. $\square$

The proof uses only that addition keeps the order and that $x \mapsto x - t$ is its inverse. So it holds in every conditionally complete lattice with a group structure whose operation keeps the order on both sides.

::: mathlib
`csSup_add` · `Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice`

The lemma states `sSup (s + t) = sSup s + sSup t` for a conditionally complete lattice with an additive group structure and the classes `AddLeftMono` and `AddRightMono`, which say that addition keeps the order on each side. The hypotheses are the four facts `s.Nonempty`, `BddAbove s`, `t.Nonempty` and `BddAbove t`. The sum `s + t` is the pointwise sum of sets, from the scope `Pointwise`. The multiplicative form is `csSup_mul`.

<?decl csSup_add?>
:::

### Examples

**Example (A computed indexed supremum).** Let $a_n = 1 - 2^{-n}$ for $n \in \mathbb{N}$. The sequence is increasing and bounded above by $1$. Its supremum is $1$. Indeed $1$ is an upper bound, and for $w < 1$ there is $n$ with $2^{-n} < 1 - w$, since $2^n \ge n + 1$ for each $n$ and the Archimedean property gives $n + 1 > 1/(1 - w)$. Then $w < a_n$. So the characterization of the previous section gives $\bigsqcup_n a_n = 1$. With $\varepsilon = 1/1000$, the theorem on monotone sequences gives $N = 10$, since $2^{-10} = 1/1024 < 1/1000$. Every $a_n$ with $n \ge 10$ lies in $(1 - 1/1000, 1]$.

**Example (Nested intervals for the square root of two).** Take the decimal approximations $a_0 = 1$, $a_1 = 1.4$, $a_2 = 1.41$, $a_3 = 1.414$, $a_4 = 1.4142$, and $b_n = a_n + 10^{-n}$: $b_0 = 2$, $b_1 = 1.5$, $b_2 = 1.42$, $b_3 = 1.415$, $b_4 = 1.4143$. In general $a_n$ is the largest multiple of $10^{-n}$ whose square is below $2$. Then $a_n^2 < 2 < b_n^2$. For instance $1.4142^2 = 1.99996164$ and $1.4143^2 = 2.00024449$. The $a_n$ increase and the $b_n$ decrease, and $b_n - a_n = 10^{-n}$ has infimum $0$. By the nested interval theorem the intersection of the $[a_n, b_n]$ is one point $c = \bigsqcup_n a_n$. Since $\sqrt{2}$ is in each interval, $c = \sqrt{2}$. In $\mathbb{Q}$ the same intervals have an empty intersection, since a common rational point would be a rational square root of $2$. So the nested interval theorem fails in $\mathbb{Q}$.

**Counterexample (A monotone map that does not preserve the supremum).** Let $g : \mathbb{R} \to \mathbb{R}$ be $g(x) = 0$ for $x < 1$ and $g(x) = 1$ for $x \ge 1$. It is monotone. Let $S = (0, 1)$, with $\sup S = 1$. Then $g(S) = \{0\}$, so $\sup g(S) = 0$, while $g(\sup S) = g(1) = 1$. The inequality $\sup g(S) \le g(\sup S)$ of the theorem "Monotone image" is strict.

**Counterexample (The hypotheses of the indexed lemmas).** In $\mathbb{R}$, let $f(n) = n$. The family is not bounded above, so $\bigsqcup_n f(n) = 0$ in Mathlib (`Real.iSup_of_not_bddAbove`), and $f(1) = 1 \le 0$ is false. So `le_ciSup` needs the bound. For the empty index type, Mathlib gives `⨆ i, f i = 0` (`Real.iSup_of_isEmpty`). Each $f(i) \le -1$ holds, since there is no $i$, but $0 \le -1$ is false. So `ciSup_le` needs `Nonempty ι`. In $\mathbb{R}_{\ge 0}$ the second problem disappears, since $\sup \emptyset = 0 = \bot$.

### The library around it

The file `Mathlib.Order.ConditionallyCompleteLattice.Indexed` repeats the lemmas for `sSup` in the indexed form, with the prefix `ci`: `le_ciSup`, `ciSup_le`, `ciSup_le_iff`, `ciSup_mono`, `isLUB_ciSup`, and the duals `ciInf_le` and `le_ciInf`. The constant family is `ciSup_const`. For a finite index type, `Set.finite_range` and `Set.Finite.bddAbove` give the bound of the range. The indexed form of the sum is `ciSup_add`. On `ℝ≥0∞` and `EReal`, which are complete lattices, all hypotheses disappear, so a proof with many side conditions on `ℝ` is often shorter there.

### Exercises

1. (A) Compute $\bigsqcup_{n \ge 1} (1 - 1/n)$ and $\bigsqcap_{n \ge 1} (1 + 1/n)$ in $\mathbb{R}$.
2. (A) Give the value of `⨆ n : ℕ, (n : ℝ)` in Mathlib, and of `⨆ n : ℕ, n` in `ℕ`. *Hint:* both families are unbounded.
3. (A) Show that $\bigsqcup_i a = a$ for a constant family with a nonempty index set, and say what fails for an empty index set in $\mathbb{R}$.
4. (B) Let $(a_n)$ be decreasing and bounded below in $\mathbb{R}$. State and prove the analogue of the theorem on monotone sequences for $\bigsqcap_n a_n$.
5. (B) Let $f, g : I \to \mathbb{R}$ be bounded above with $I$ nonempty. Show that $\bigsqcup_i (f(i) + g(i)) \le \bigsqcup_i f(i) + \bigsqcup_i g(i)$, and give an example where the inequality is strict. *Hint:* $f(i) = i$ and $g(i) = -i$ on $I = \{0, 1\}$.
6. (B) Let $S \subseteq \mathbb{R}$ be nonempty and bounded above, and let $c > 0$. Show that $\sup (cS) = c \sup S$, where $cS = \{ cs \mid s \in S \}$. What happens for $c < 0$?
7. (B) Show that the intersection of the intervals $(0, 1/n)$ for $n \ge 1$ is empty. Explain why this does not contradict the nested interval theorem.
8. (C) Let $g : \mathbb{R} \to \mathbb{R}$ be monotone. Show that $\sup g((-\infty, x)) \le g(x)$ for each $x$, and that the set of the points $x$ where the inequality is strict is countable. *Hint:* the intervals $(\sup g((-\infty, x)), g(x))$ are disjoint, and each contains a rational.
9. (C) Use the nested interval theorem to prove that $\mathbb{R}$ is uncountable. *Hint:* given a sequence $(x_n)$, choose closed intervals $I_{n+1} \subseteq I_n$ of positive length with $x_n \notin I_n$.

### Notes and history

The nested interval theorem is in the work of Bolzano and Cauchy on roots of equations by bisection. Cantor used nested intervals in 1874 in his first proof that the reals are uncountable, which is Exercise 9. Abbott, *Understanding analysis*, Theorem 1.4.1, is the nested interval property. In Mathlib, the class `ConditionallyCompletePartialOrderSup` is a recent generalization that lets the nested interval statement hold for orders that are not lattices.

### Reference

<?reference?>
