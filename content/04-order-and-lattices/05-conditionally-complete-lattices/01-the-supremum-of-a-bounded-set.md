---
title: The supremum of a bounded set
kind: theory
modules:
  - Mathlib.Order.ConditionallyCompleteLattice.Basic
  - Mathlib.Order.Bounds.Defs
explains:
  E3: [ConditionallyCompleteLattice, IsLUB]
  E2: [BddAbove, le_csSup, csSup_le, isLUB_csSup, exists_lt_of_lt_csSup]
  E1: [BddBelow, upperBounds, ConditionallyCompleteLinearOrder, csSup_le_iff, le_csSup_iff, csSup_le_csSup, csInf_le, csSup_singleton, csSup_Icc, bddAbove_Icc, Real.sSup_empty, Real.sSup_univ, Real.sSup_of_not_bddAbove]
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

The completeness axiom of the real numbers says that a nonempty set that is bounded above has a least upper bound. The reals are not a complete lattice, because the set `ℝ` itself has no upper bound. Mathlib uses the class `ConditionallyCompleteLattice` for this case. The function `sSup` is still total, so `sSup s` has a value for each set $s$. The lemmas about `sSup` have the hypotheses that $s$ is nonempty or bounded above, and the names of the lemmas start with `c`, for conditional. This section shows the predicates of bounds, the class, the main lemmas, and the junk values of `sSup` on `ℝ`.

### Definitions

**Definition (Upper bounds).** For a set $s$ in a preorder, `upperBounds s` is the set of the elements $b$ with $a \le b$ for each $a \in s$. The set $s$ is `BddAbove` if `upperBounds s` is nonempty. The predicates `lowerBounds` and `BddBelow` are dual.

**Definition (Least upper bound).** The proposition `IsLUB s a` says that $a$ is the least element of `upperBounds s`. So $a$ is an upper bound of $s$, and $a \le b$ for each upper bound $b$.

**Definition (Conditionally complete lattice).** A `ConditionallyCompleteLattice` is a lattice with operations `sSup` and `sInf`, such that `sSup s` is the least upper bound of $s$ when $s$ is nonempty and bounded above, and `sInf s` is the greatest lower bound of $s$ when $s$ is nonempty and bounded below.

### Theorems and proofs

**Theorem (Upper bound).** If $s$ is bounded above and $a \in s$, then $a \le \operatorname{sSup} s$.

*Proof.* The set $s$ is nonempty because $a \in s$. So `sSup s` is the least upper bound of $s$, and in particular an upper bound. $\square$

**Theorem (Least).** If $s$ is nonempty and $b$ is an upper bound of $s$, then $\operatorname{sSup} s \le b$.

*Proof.* The element $b$ shows that $s$ is bounded above. So `sSup s` is the least upper bound, and it is below the upper bound $b$. $\square$

**Theorem (Approximation).** If $s$ is nonempty and $b < \operatorname{sSup} s$ in a linear order, then there is $a \in s$ with $b < a$.

*Proof.* Suppose not. Then $a \le b$ for each $a \in s$, so $b$ is an upper bound of $s$. By the previous theorem, $\operatorname{sSup} s \le b$, and this contradicts $b < \operatorname{sSup} s$. $\square$

::: mathlib
`ConditionallyCompleteLattice` · `Mathlib.Order.ConditionallyCompleteLattice.Defs`

The class extends `Lattice`, `SupSet` and `InfSet`, with the two axioms `isLUB_csSup` and `isGLB_csInf`. The lemmas `le_csSup` and `csSup_le` follow from them. The instance for `ℝ` is `Real.instConditionallyCompleteLinearOrder`, in `Mathlib.Algebra.Order.Archimedean.Real.Basic`.

<?decl ConditionallyCompleteLattice?>
:::

::: mathlib
`le_csSup` · `Mathlib.Order.ConditionallyCompleteLattice.Basic`

The lemma takes a proof of `BddAbove s` and a proof of `a ∈ s`. Compare it with `le_sSup` of a complete lattice, which needs only the second proof.

<?decl le_csSup?>
:::

::: mathlib
`csSup_le` · `Mathlib.Order.ConditionallyCompleteLattice.Basic`

The lemma takes a proof of `s.Nonempty` and a proof that $b$ is an upper bound. The lemma `csSup_le_iff` is the equivalence, with both hypotheses.

<?decl csSup_le?>
:::

::: mathlib
`IsLUB` · `Mathlib.Order.Bounds.Defs`

The predicate does not use `sSup`, so it is the right tool when a type has no `SupSet` instance. The lemma `isLUB_csSup` gives `IsLUB s (sSup s)` in a conditionally complete lattice.

<?decl IsLUB?>
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

**Example (A closed interval).** The lemma `csSup_Icc` needs only the hypothesis $a \le b$.

<?lean MathlibHandbook/V04/C05/Examples.lean#icc?>

**Example (Junk values).** In `ℝ`, the supremum of the empty set is `0`, and the supremum of a set that is not bounded above is `0`.

<?lean MathlibHandbook/V04/C05/Examples.lean#junk?>

**Counterexample (A false lemma).** The statement `∀ s : Set ℝ, ∀ a ∈ s, a ≤ sSup s` is false. For $s = \mathbb{N} \subseteq \mathbb{R}$ and $a = 1$, the value of `sSup s` is `0`, and $1 \le 0$ is false. So `le_csSup` needs the hypothesis `BddAbove s`.

### The library around it

The lemmas of a conditionally complete lattice have a `c` in front of the name of the lemma of a complete lattice: `le_csSup` for `le_sSup`, `csSup_le` for `sSup_le` and `csInf_le` for `sInf_le`. The lemma `bddAbove_Icc` and the lemmas in `Mathlib.Order.Bounds.Basic` give the hypothesis `BddAbove` for the usual sets. The class `ConditionallyCompleteLinearOrder` adds a linear order, and the approximation lemma `exists_lt_of_lt_csSup` needs it. For the reals, the definition `Real.sSup_def` gives the value, and `Real.sSup_of_not_bddAbove` states the junk value. The types `ℝ≥0∞` and `EReal` are complete lattices, so their lemmas need no hypothesis. A proof that works with an unbounded set can move to one of these types.

### Exercises

1. (A) Give the value of `sSup (Set.Ioi (0 : ℝ))` in Mathlib.
2. (A) Explain why `le_csSup` needs `BddAbove s` and `csSup_le` needs `s.Nonempty`.
3. (B) Show that $\operatorname{sSup} \{a\} = a$ in a conditionally complete lattice.
4. (B) Show that $\operatorname{sSup} (0, 1) = 1$ in `ℝ`.
5. (B) Show that $\operatorname{sSup} s \le \operatorname{sSup} t$ when $s \subseteq t$, $s$ is nonempty and $t$ is bounded above.
6. (L) Prove that $2 \le \operatorname{sSup} [0, 2]$. The solution is `le_csSup_two_example`.
7. (L) Prove that a nonempty set of reals with the upper bound $1$ has a supremum at most $1$. The solution is `csSup_le_one_example`.
8. (L) Prove that the supremum of the empty set of reals is $0$. The solution is `sSup_empty_real_example`.

### Notes and history

Dedekind gave the completeness of the reals in 1872 with his cuts. Mathlib builds the reals as a quotient of Cauchy sequences and proves the completeness axiom as a theorem. The junk value `0` follows the convention of the other junk values of Mathlib, and it makes `sSup` a total function.

### Reference

<?reference?>
