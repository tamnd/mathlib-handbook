---
title: Complete lattices
kind: theory
modules:
  - Mathlib.Order.CompleteLattice.Defs
  - Mathlib.Order.CompleteLattice.Basic
explains:
  E3: [CompleteLattice, CompleteLinearOrder, completeLatticeOfSup]
  E2: [sSup_le_iff, le_sInf_iff, le_iSup, iSup_le_iff, sSup_le_sSup, completeLatticeOfInf]
  E1: [le_sSup, sSup_le, sInf_le, le_sInf, iSup_le, sSup_empty, sInf_empty, sSup_univ, sInf_univ, isLUB_sSup, isGLB_sInf, le_iInf_iff, le_iSup_iff, sInf_le_sInf, sSup_insert, sSup_union, sSup_pair, sSup_image, sSup_range, iSup_range, iSup_mono, iSup_const, sInf_le_sSup, sSup_Prop_eq, Prop.instCompleteLattice, Pi.instCompleteLattice, OrderDual.instCompleteLattice, CompleteLattice.toBoundedOrder, CompleteSemilatticeSup, CompleteSemilatticeInf, Monotone.le_map_sSup]
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

## Complete lattices

### Overview

In a lattice, each pair of elements has a least upper bound, and so each finite nonempty set has one. Many arguments need more. The union of an infinite family of sets, the intersection of all subgroups that contain a given set, and the closure of a set in a topological space are suprema and infima of infinite families. A complete lattice is a partial order in which every set has a least upper bound and a greatest lower bound. The empty set and the infinite sets are included.

This section gives the definition, the universal properties of `sSup` and `sInf`, and the indexed forms `⨆ i, f i` and `⨅ i, f i`. The main theorem says that half of the axioms is enough: a partial order in which every set has a supremum is a complete lattice. The next section uses complete lattices for the fixed point theorem of Knaster and Tarski.

### Definitions

Let $(P, \le)$ be a partial order and let $S \subseteq P$. An element $u$ is an *upper bound* of $S$ if $s \le u$ for each $s \in S$. It is a *least upper bound*, or *supremum*, of $S$ if also $u \le v$ for each upper bound $v$ of $S$. By antisymmetry, the supremum is unique when it exists. The *infimum*, or greatest lower bound, is the dual notion.

**Definition (Complete lattice).** A *complete lattice* is a partial order $P$ in which every subset $S \subseteq P$ has a supremum $\sup S$ and an infimum $\inf S$.

A complete lattice has a least element $\bot = \sup \emptyset = \inf P$ and a greatest element $\top = \inf \emptyset = \sup P$. It is a lattice, with $a \sqcup b = \sup \{a, b\}$ and $a \sqcap b = \inf \{a, b\}$. The empty set gives the bounds: in the integers each nonempty bounded set has a supremum, but there is no bottom.

**Definition (Indexed supremum).** Let $f : I \to P$ be a family of elements of a complete lattice. Its supremum is $\bigsqcup_{i \in I} f(i) = \sup \{ f(i) \mid i \in I \}$, the supremum of the range of $f$. Its infimum $\bigsqcap_{i \in I} f(i)$ is $\inf$ of the range.

A set $S$ is the range of the inclusion $S \to P$, so $\sup S = \bigsqcup_{s \in S} s$. The union $\bigcup_n A_n$ of a sequence of sets is an indexed supremum.

**Definition (Complete linear order).** A *complete linear order* is a complete lattice whose order is linear.

The closed interval $[0,1]$ of real numbers, the extended reals $[-\infty, +\infty]$ and the extended natural numbers $\mathbb{N} \cup \{\infty\}$ are complete linear orders. The lattice of the subsets of a set with two or more elements is complete but not linear.

::: mathlib
`CompleteLattice` · `Mathlib.Order.CompleteLattice.Defs`

The class `CompleteLattice α` carries the operations as data: `sSup : Set α → α` and `sInf : Set α → α`, together with `⊔`, `⊓`, `⊤` and `⊥`. The axioms say that `sSup s` is an upper bound of `s` (`le_sSup`) and is below each upper bound (`sSup_le`), and dually for `sInf`. With the operations as data, the supremum for `Set α` is the union by definition. The class extends `Lattice` and `BoundedOrder`, among others.

<?decl CompleteLattice?>
:::

::: mathlib
`le_iSup` · `Mathlib.Order.CompleteLattice.Basic`

The notation `⨆ i, f i` stands for `iSup f`, defined as `sSup (Set.range f)`. The index type is a `Sort`, so it can be a proposition, which gives the bounded form `⨆ i ∈ s, f i`. The lemma `le_iSup f i` gives `f i ≤ ⨆ i, f i`, and `iSup_le` takes a bound for each `f i`.

<?decl le_iSup?>
:::

::: mathlib
`CompleteLinearOrder` · `Mathlib.Order.CompleteLattice.Defs`

The class combines `CompleteLattice` and `LinearOrder`, and it also extends `BiheytingAlgebra`, because a complete linear order has a Heyting implication and a co-Heyting difference. Instances are `ENat`, `EReal`, `ENNReal` and `Prop`.

<?decl CompleteLinearOrder?>
:::

### Theorems and proofs

The first two theorems are the working form of the definition. A proof about a supremum almost always reduces to one of them.

**Theorem (Universal property of the supremum).** In a complete lattice, $\sup S \le a$ if and only if $s \le a$ for each $s \in S$. Dually, $a \le \inf S$ if and only if $a \le s$ for each $s \in S$.

*Proof.* Assume $\sup S \le a$ and let $s \in S$. Since $\sup S$ is an upper bound of $S$, $s \le \sup S$. Transitivity gives $s \le a$. Conversely, assume $s \le a$ for each $s \in S$. Then $a$ is an upper bound of $S$. The supremum is below each upper bound, so $\sup S \le a$. The statement for the infimum is the same statement in the dual order, where $\le$ is reversed and $\sup$ becomes $\inf$. $\square$

**Theorem (Monotonicity in the set).** Let $S \subseteq T$ in a complete lattice. Then $\sup S \le \sup T$ and $\inf T \le \inf S$.

*Proof.* By the universal property it suffices to show $s \le \sup T$ for each $s \in S$. Each $s \in S$ is in $T$, and $\sup T$ is an upper bound of $T$, so $s \le \sup T$. The claim for the infimum is the dual. $\square$

So a larger set has a larger supremum and a smaller infimum. For $\sup \emptyset$: each element is an upper bound of $\emptyset$, so $\sup \emptyset \le \bot$, and $\sup \emptyset = \bot$. Dually $\inf \emptyset = \top$, not $\bot$, because every element is a lower bound of $\emptyset$.

**Theorem (Supremum of a union).** In a complete lattice, $\sup (S \cup T) = \sup S \sqcup \sup T$. In particular $\sup (\{a\} \cup S) = a \sqcup \sup S$.

*Proof.* Let $u = \sup (S \cup T)$ and $v = \sup S \sqcup \sup T$. Each element of $S$ is in $S \cup T$, so $S \subseteq S \cup T$ and $\sup S \le u$ by monotonicity. In the same way $\sup T \le u$. So $u$ is an upper bound of $\{\sup S, \sup T\}$ and $v \le u$. For the other inequality, let $x \in S \cup T$. If $x \in S$, then $x \le \sup S \le v$. If $x \in T$, then $x \le \sup T \le v$. So $v$ is an upper bound of $S \cup T$, and $u \le v$. Antisymmetry gives $u = v$. The second claim is the case $S = \{a\}$, with $\sup \{a\} = a$. $\square$

The main theorem of the section shows that the definition asks for more than it needs.

**Theorem (Suprema give infima).** Let $P$ be a partial order in which every subset has a supremum. Then every subset of $P$ has an infimum, and $\inf S = \sup L(S)$, where $L(S) = \{ x \in P \mid x \le s \text{ for each } s \in S \}$ is the set of the lower bounds of $S$. So $P$ is a complete lattice.

*Proof.* Let $S \subseteq P$ and let $m = \sup L(S)$. Two facts have to be shown: $m$ is a lower bound of $S$, and $m$ is above each lower bound of $S$.

First, let $s \in S$. Each $x \in L(S)$ satisfies $x \le s$ by the definition of $L(S)$. So $s$ is an upper bound of the set $L(S)$. The supremum $m$ of $L(S)$ is below each upper bound of $L(S)$, so $m \le s$. This holds for each $s \in S$, so $m \in L(S)$: $m$ is a lower bound of $S$.

Second, let $x$ be a lower bound of $S$. Then $x \in L(S)$, and $m$ is an upper bound of $L(S)$, so $x \le m$.

The two facts say that $m$ is the greatest lower bound of $S$. $\square$

The proof does not use any infimum. For $S = \emptyset$, every element is a lower bound, so $L(\emptyset) = P$ and $\inf \emptyset = \sup P = \top$. Dually, a partial order in which every subset has an infimum is a complete lattice, with $\sup S = \inf U(S)$ for the set $U(S)$ of the upper bounds.

The theorem is the reason why many complete lattices appear with only one operation. The subgroups of a group have an obvious infimum, the intersection, and the theorem gives the supremum for free.

::: mathlib
`completeLatticeOfSup` · `Mathlib.Order.CompleteLattice.Defs`

The definition takes a partial order with an operation `sSup` and a proof of `∀ s, IsLUB s (sSup s)`, and it builds a `CompleteLattice` instance with the infimum of the proof above. The dual construction is `completeLatticeOfInf`. When the infimum has a better definition, such as the intersection, Mathlib replaces the generated field with `CompleteLattice.copy`.

<?decl completeLatticeOfSup?>
:::

::: mathlib
`sSup_le_iff` · `Mathlib.Order.CompleteLattice.Defs`

This is the universal property of the supremum. Its dual is `le_sInf_iff`, and the indexed forms are `iSup_le_iff` and `le_iInf_iff`. The monotonicity in the set is `sSup_le_sSup`, and the union is `sSup_union`.

<?decl sSup_le_iff?>
:::

### Examples

**Example (The supremum is below each upper bound).** This is the axiom `sSup_le`.

<?lean MathlibHandbook/V04/C04/Examples.lean#sSup_le?>

**Example (Each element is below the supremum).** This is the axiom `le_sSup`.

<?lean MathlibHandbook/V04/C04/Examples.lean#le_sSup?>

**Example (The lattice of sets).** Let $X$ be a set and order its subsets by inclusion. For a family $\mathcal{A}$ of subsets, the union $\bigcup \mathcal{A}$ contains each member of $\mathcal{A}$, and each set $B$ that contains each member of $\mathcal{A}$ contains the union. So $\sup \mathcal{A} = \bigcup \mathcal{A}$. In the same way $\inf \mathcal{A} = \bigcap \mathcal{A}$, with the convention $\bigcap \emptyset = X$. For a computation, take $X = \mathbb{N}$ and $A_n = \{0, 1, \dots, n\}$. Then $\bigsqcup_n A_n = \mathbb{N}$ and $\bigsqcap_n A_n = \{0\}$. In Mathlib the supremum of a set of sets is `⋃₀` by definition.

<?lean MathlibHandbook/V04/C04/Examples.lean#set?>

**Example (The lattice of propositions).** Order the propositions by implication: $p \le q$ means $p \to q$. The bottom is `False` and the top is `True`. The supremum of a set $S$ of propositions is the proposition "some member of $S$ is true", and the infimum is "each member of $S$ is true". Indeed, $\exists p \in S, p$ implies $q$ if and only if each $p \in S$ implies $q$. So $\sup$ is an existential quantifier and $\inf$ is a universal quantifier. The lemma `sSup_Prop_eq` states the first fact. For two propositions, `⊔` is `∨`.

<?lean MathlibHandbook/V04/C04/Examples.lean#prop?>

**Example (The closed interval).** Let $P = [0,1] \subseteq \mathbb{R}$ with the usual order. Let $S \subseteq [0,1]$. If $S$ is nonempty, it is bounded above by $1$, and the completeness of $\mathbb{R}$ gives a real supremum $u$. It satisfies $0 \le s \le u \le 1$ for any $s \in S$, so $u \in [0,1]$, and it is the supremum in $[0,1]$ as well. If $S$ is empty, its supremum in $[0,1]$ is the least element $0$. For example, $S = \{1 - 1/n \mid n \ge 1\}$ has supremum $1$ and infimum $0$, and $\sup \emptyset = 0$, $\inf \emptyset = 1$. So $[0,1]$ is a complete linear order. The whole line $\mathbb{R}$ is not: the set $\mathbb{N} \subseteq \mathbb{R}$ has no upper bound. Chapter 5 treats $\mathbb{R}$.

**Example (Extended numbers).** The type $\mathbb{N}_\infty = \mathbb{N} \cup \{\infty\}$ is a complete linear order. A set $S \subseteq \mathbb{N}_\infty$ with a finite upper bound in $\mathbb{N}$ has its largest element as supremum. Each other set has supremum $\infty$. So $\sup \mathbb{N} = \infty$, while $\mathbb{N}$ itself has no supremum in $\mathbb{N}$. In the same way the extended reals $[-\infty, +\infty]$ are a complete linear order, with $\sup \emptyset = -\infty$ and $\sup \mathbb{R} = +\infty$.

**Example (Subgroups).** Let $G$ be a group and order its subgroups by inclusion. The intersection of any family of subgroups is a subgroup, so every family has an infimum, the intersection. By the theorem "Suprema give infima", applied to the dual order, the subgroups form a complete lattice. The supremum of a family is the intersection of all subgroups that contain each member, that is, the subgroup generated by the union. In $G = \mathbb{Z}$, take $4\mathbb{Z}$ and $6\mathbb{Z}$. Their infimum is $4\mathbb{Z} \cap 6\mathbb{Z} = 12\mathbb{Z}$, since an integer is a multiple of $4$ and of $6$ exactly when it is a multiple of $\operatorname{lcm}(4,6) = 12$. Their supremum is the subgroup generated by $4$ and $6$. It is $4\mathbb{Z} + 6\mathbb{Z} = 2\mathbb{Z}$, since $2 = 6 - 4$ and both generators are even. The union $4\mathbb{Z} \cup 6\mathbb{Z}$ is not a subgroup: it contains $4$ and $6$ but not $10$. So the supremum in a lattice of subobjects is often larger than the union. In Mathlib, `Subgroup.closure_le` says that the generated subgroup is below `K` if and only if the set is in `K`.

**Counterexample (A lattice that is not complete).** The type `ℕ` is a lattice with a bottom element, but the set of all natural numbers has no upper bound, so it has no supremum. The rationals in $[0,1]$ are a bounded lattice, but the set $\{x \in \mathbb{Q} \mid 0 \le x,\ x^2 < 1/2\}$ has no supremum in $\mathbb{Q} \cap [0, 1]$, since its supremum in $\mathbb{R}$ is the irrational number $1/\sqrt{2}$. So boundedness does not give completeness. Neither type has a `CompleteLattice` instance in Mathlib.

### The library around it

The lemmas come in pairs for `sSup` and `sInf`, and again for `iSup` and `iInf`: `le_sSup` and `sSup_le` are the axioms, `sSup_le_iff` is the universal property, `sSup_le_sSup` and `iSup_mono` are the monotonicity. The special values are `sSup_empty`, `sInf_empty`, `sSup_univ` and `sInf_univ`. The dual order and the function types `ι → α` have `CompleteLattice` instances.

For sets, the supremum and the union are the same term, but the simp normal form is the union: `Set.sSup_eq_sUnion` and `Set.iSup_eq_iUnion` rewrite `sSup` to `⋃₀` and `⨆` to `⋃`. Lemmas about unions live in `Mathlib.Data.Set.Lattice`. A monotone map does not preserve suprema in general, but it satisfies one inequality: `Monotone.le_map_sSup` gives `⨆ a ∈ s, f a ≤ f (sSup s)`. The maps that preserve all suprema are the lower adjoints of Galois connections (Chapter 6).

### Exercises

1. (A) Give `sSup` and `sInf` of the empty set in the lattice of the subsets of `ℕ`. *Hint:* the infimum of the empty family is the top element.
2. (A) Explain why `ℝ` has no `CompleteLattice` instance, and give a complete lattice that contains `ℝ`.
3. (A) In the lattice of subgroups of $\mathbb{Z}$, compute $6\mathbb{Z} \sqcup 10\mathbb{Z}$, $6\mathbb{Z} \sqcap 10\mathbb{Z}$ and $\bigsqcap_{n \ge 1} n\mathbb{Z}$. *Hint:* the gcd and the lcm.
4. (B) Show that $\inf S \le \sup S$ for a nonempty set $S$, and give a counterexample for the empty set in a lattice with two or more elements.
5. (B) Show that $\bigsqcup_i (f(i) \sqcup g(i)) = (\bigsqcup_i f(i)) \sqcup (\bigsqcup_i g(i))$. *Hint:* prove two inequalities with the universal property.
6. (B) Let $P$ be a complete lattice and $a \in P$. Show that the interval $\{x \mid a \le x\}$ is a complete lattice with the order of $P$. Compute its supremum of the empty set. *Hint:* the supremum of a nonempty subset is the same as in $P$.
7. (B) Show that a finite lattice is a complete lattice. *Hint:* a finite nonempty set has a supremum by induction on its size, and a finite lattice has a bottom.
8. (C) Show that $\mathbb{Q}$ with the usual order has a subset that is nonempty and bounded above, with no supremum in $\mathbb{Q}$. Then show that the Dedekind cuts of $\mathbb{Q}$, ordered by inclusion, together with $\emptyset$ and $\mathbb{Q}$, form a complete lattice. *Hint:* a union of cuts is a cut or all of $\mathbb{Q}$.
9. (L) Prove that `sSup ∅ = ⊥`. The solution is `sSup_empty_example`.
10. (L) Prove that $a \le \sup \{a, b\}$. The solution is `le_sSup_pair_example`.

### Notes and history

Complete lattices appear in the work of Dedekind on ideals, and Birkhoff made lattice theory a subject in the 1930s with his book *Lattice theory* (1940). Davey and Priestley, *Introduction to lattices and order* (2002), Chapter 2, is a good first text. The completion of a partial order by cuts is due to MacNeille (1937). Mathlib has it as `DedekindCut`.

In Mathlib the file `Mathlib.Order.CompleteLattice.Defs` has the classes, and `Mathlib.Order.CompleteLattice.Basic` has the general lemmas.

### Reference

<?reference?>
