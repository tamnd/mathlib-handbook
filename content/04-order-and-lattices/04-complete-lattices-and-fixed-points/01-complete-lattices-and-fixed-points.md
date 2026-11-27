---
title: Complete lattices and fixed points
kind: theory
modules:
  - Mathlib.Order.CompleteLattice.Defs
  - Mathlib.Order.FixedPoints
explains:
  E3: [CompleteLattice, OrderHom.lfp]
  E2: [sSup_le_iff, le_sInf_iff, OrderHom.map_lfp, OrderHom.lfp_le, OrderHom.gfp]
  E1: [le_sSup, sSup_le, sInf_le, le_sInf, le_iSup, iSup_le, sSup_empty, OrderHom.map_gfp, OrderHom.le_gfp, OrderHom.isLeast_lfp, OrderHom.lfp_le_gfp]
families: []
requires: [V04.C02, V04.C03]
reads_with: ["MIL"]
lean:
  - MathlibHandbook/V04/C04/Examples.lean
  - MathlibHandbook/V04/C04/Exercises.lean
  - MathlibHandbook/V04/C04/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Complete lattices and fixed points

### Overview

In a lattice, two elements have a supremum. In a complete lattice, each set of elements has a supremum and an infimum, also the empty set and the infinite sets. Mathlib writes the supremum of a set $s$ as `sSup s` and the supremum of a family $f : \iota \to \alpha$ as `⨆ i, f i`. The sets of a type, the propositions and the extended reals are complete lattices. The main theorem of the section is the theorem of Knaster and Tarski: a monotone map on a complete lattice has a least fixed point and a greatest fixed point. Mathlib names them `OrderHom.lfp` and `OrderHom.gfp`.

### Definitions

**Definition (Complete lattice).** A `CompleteLattice` is a lattice with a top and a bottom element and two operations `sSup` and `sInf` on sets. For each set $s$, `sSup s` is an upper bound of $s$ and is below each upper bound of $s$. Also, `sInf s` is a lower bound of $s$ and is above each lower bound of $s$.

**Definition (Indexed supremum).** For a family $f : \iota \to \alpha$, the supremum `⨆ i, f i` is `sSup (Set.range f)`. The infimum `⨅ i, f i` is `sInf (Set.range f)`.

**Definition (Least fixed point).** For a monotone map $f : \alpha \to \alpha$ on a complete lattice, `OrderHom.lfp f` is `sInf {a | f a ≤ a}`. The greatest fixed point `OrderHom.gfp f` is `sSup {a | a ≤ f a}`.

### Theorems and proofs

**Theorem (Universal property).** In a complete lattice, $\operatorname{sSup} s \le a \iff \forall b \in s,\ b \le a$.

*Proof.* If $\operatorname{sSup} s \le a$ and $b \in s$, then $b \le \operatorname{sSup} s \le a$. Conversely, if each $b \in s$ is below $a$, then $a$ is an upper bound of $s$, so $\operatorname{sSup} s \le a$. $\square$

**Theorem (Empty set).** $\operatorname{sSup} \emptyset = \bot$ and $\operatorname{sInf} \emptyset = \top$.

*Proof.* Each element is an upper bound of the empty set, so $\operatorname{sSup} \emptyset \le \bot$. Then $\operatorname{sSup} \emptyset = \bot$ by antisymmetry. The proof for $\operatorname{sInf}$ is dual. $\square$

**Theorem (Knaster and Tarski).** Let $f$ be a monotone map on a complete lattice, and let $S = \{a \mid f(a) \le a\}$ and $m = \operatorname{sInf} S$. Then $f(m) = m$, and $m \le x$ for each fixed point $x$.

*Proof.* Let $a \in S$. Then $m \le a$, so $f(m) \le f(a) \le a$. Thus $f(m)$ is a lower bound of $S$, and $f(m) \le m$. Then $f(f(m)) \le f(m)$ because $f$ is monotone, so $f(m) \in S$ and $m \le f(m)$. By antisymmetry, $f(m) = m$. A fixed point $x$ is in $S$, so $m \le x$. $\square$

::: mathlib
`CompleteLattice` · `Mathlib.Order.CompleteLattice.Defs`

The class extends `Lattice`, `CompleteSemilatticeSup`, `CompleteSemilatticeInf` and `BoundedOrder`. The lemmas `le_sSup` and `sSup_le` state the two axioms of the supremum, and `sSup_le_iff` and `le_sInf_iff` state the universal properties.

<?decl CompleteLattice?>
:::

::: mathlib
`OrderHom.lfp` · `Mathlib.Order.FixedPoints`

The least fixed point is a bundled monotone map `(α →o α) →o α`, so it takes a term of `α →o α` and not a plain function. The lemma `OrderHom.map_lfp` states that it is a fixed point, and `OrderHom.lfp_le` states that it is below each $a$ with $f(a) \le a$.

<?decl OrderHom.lfp?>
:::

::: mathlib
`OrderHom.gfp` · `Mathlib.Order.FixedPoints`

The greatest fixed point is the dual of `OrderHom.lfp`. The lemmas `OrderHom.map_gfp` and `OrderHom.le_gfp` are the duals of the lemmas for `lfp`.

<?decl OrderHom.gfp?>
:::

### Examples

**Example (The supremum is below each upper bound).**

<?lean MathlibHandbook/V04/C04/Examples.lean#sSup_le?>

**Example (Each element is below the supremum).**

<?lean MathlibHandbook/V04/C04/Examples.lean#le_sSup?>

**Example (The lattice of sets).** The supremum of a set of sets is its union, by definition.

<?lean MathlibHandbook/V04/C04/Examples.lean#set?>

**Example (The lattice of propositions).** In `Prop`, the order is the implication, and the sup is the disjunction.

<?lean MathlibHandbook/V04/C04/Examples.lean#prop?>

**Example (A fixed point).**

<?lean MathlibHandbook/V04/C04/Examples.lean#lfp?>

**Example (The least fixed point is least).** This lemma is the usual tool to prove a property of `lfp f`: find an element $a$ with the property and with $f(a) \le a$.

<?lean MathlibHandbook/V04/C04/Examples.lean#lfp_le?>

**Counterexample (A lattice that is not complete).** The type `ℕ` is a lattice with a bottom element, but the set of all natural numbers has no supremum. So `ℕ` has no `CompleteLattice` instance. The type `ℕ∞` adds a top element, and it is a complete lattice.

### The library around it

The general lemmas are in `Mathlib.Order.CompleteLattice.Basic`, for example `le_iSup` and `iSup_le` for the indexed supremum. For sets, the supremum is the union `⋃₀`, and the indexed supremum is `⋃ i`. A complete lattice is a bounded order, and the instance `CompleteLattice.toBoundedOrder` gives the bounds. The class `CompleteLinearOrder` combines a complete lattice and a linear order. The file `Mathlib.Order.FixedPoints` also has the induction principle `OrderHom.lfp_induction`, which proves a property of the least fixed point from a property that $f$ keeps. In logic and in computer science, `lfp` gives inductive definitions, and `gfp` gives coinductive definitions.

### Exercises

1. (A) Give `sSup` and `sInf` of the empty set in the lattice of the sets of `ℕ`.
2. (A) Explain why `ℝ` has no `CompleteLattice` instance.
3. (B) Show that $\operatorname{sSup} s \le \operatorname{sSup} t$ when $s \subseteq t$.
4. (B) Show that $\operatorname{sInf} s \le \operatorname{sSup} s$ for a nonempty set $s$, and give a counterexample for the empty set.
5. (B) Find the least and the greatest fixed points of the map $X \mapsto X \cup \{0\}$ on the sets of `ℕ`.
6. (L) Prove that `sSup ∅ = ⊥`. The solution is `sSup_empty_example`.
7. (L) Prove that the least fixed point is below the greatest fixed point. The solution is `lfp_le_gfp_example`.
8. (L) Prove that $a \le \operatorname{sSup} \{a, b\}$. The solution is `le_sSup_pair_example`.

### Notes and history

Knaster and Tarski proved the theorem for the lattice of sets in 1928, and Tarski proved the general form in 1955. The theorem is the base of the semantics of recursive definitions. Lean has inductive types, so the kernel does not need it. Mathlib uses `OrderHom.lfp` in its proof of the theorem of Schröder and Bernstein, and the file `Mathlib.SetTheory.Ordinal.FixedPointApproximants` builds the least fixed point with ordinals.

### Reference

<?reference?>
