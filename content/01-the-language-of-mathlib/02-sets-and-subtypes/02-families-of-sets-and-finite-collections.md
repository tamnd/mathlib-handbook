---
title: Families of sets and finite collections
kind: theory
modules: []
explains:
  E1: [Set.mem_iUnion, Set.mem_iInter, Set.compl_iUnion, Set.compl_iInter, Set.inter_iUnion, Set.iUnion_const, Finset.card_powerset, Finset.card_range, Finset.coe_range, Set.ncard, Fintype.card, Set.Finite]
families: []
requires: [V01.C01]
reads_with: ["MIL"]
lean:
  - MathlibHandbook/V01/C02/Examples.lean
  - MathlibHandbook/V01/C02/Exercises.lean
  - MathlibHandbook/V01/C02/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Families of sets and finite collections

### Overview

The previous section treated one or two sets at a time. Analysis and topology need many sets at once: the open intervals $(-1/n, 1/n)$ for all $n \geq 1$, or the balls of every radius around a point. A *family* of sets is a function from an index type to sets. Its union and intersection extend the operations of the previous section, and the laws of the previous section extend to families.

The second topic is the power set, the set of all subsets. The section proves that the power set of a set with $n$ elements has $2^n$ elements.

The third topic is finiteness. A finite collection in Mathlib can have four forms: a `Finset`, a finite type with a `Fintype` instance, a subtype, or a set with a cardinality. The forms have different lemmas, and a proof often passes from one form to another. The section shows one count in all four forms.

### Definitions

**Definition (Indexed family).** Let $\iota$ and $\alpha$ be types. An *indexed family of sets* is a function $A : \iota \to \texttt{Set}\ \alpha$. The set $A(i)$ is often written $A_i$.

**Definition (Union and intersection of a family).** For a family $A : \iota \to \texttt{Set}\ \alpha$:
$$\bigcup_i A_i = \{x \mid \exists i,\ x \in A_i\}, \qquad \bigcap_i A_i = \{x \mid \forall i,\ x \in A_i\}.$$

For a set $S$ of sets, a term of `Set (Set α)`, the union and intersection are $\bigcup S = \{x \mid \exists t \in S,\ x \in t\}$ and $\bigcap S = \{x \mid \forall t \in S,\ x \in t\}$. These are the same as the indexed forms for the family $t \mapsto t$ on the subtype of $S$.

::: mathlib
`Set.mem_iUnion` · `Mathlib.Order.SetNotation`

Mathlib writes the union of a family as `⋃ i, A i` and calls it `Set.iUnion`, for "indexed union". The membership lemma is `x ∈ ⋃ i, A i ↔ ∃ i, x ∈ A i`. The intersection is `⋂ i, A i`, `Set.iInter`, with `Set.mem_iInter`. The union of a set of sets is `⋃₀ S`, `Set.sUnion`, with the lemma `Set.mem_sUnion`.

<?decl Set.mem_iUnion?>
:::

**Definition (Power set).** For a set $s$ in `Set α`, the *power set* $\mathcal{P}(s)$ is the set $\{t \mid t \subseteq s\}$, a term of `Set (Set α)`.

**Definition (Finite collections).** Mathlib has four forms of a finite collection.

1. A `Finset α` is a finite set of elements of $\alpha$. It is a list without repetition, up to order. It has a cardinality `Finset.card`, a natural number.
2. A `Fintype α` instance states that the type $\alpha$ is finite, and it gives a `Finset` of all its elements. The type has a cardinality `Fintype.card α`.
3. A finset $s$ gives a subtype $\{x : \alpha \mid x \in s\}$ of $\alpha$, which has a `Fintype` instance.
4. A set $s$ in `Set α` has a cardinality `Set.ncard s`, a natural number. It is $0$ when $s$ is infinite.

### Theorems and proofs

**Theorem (Union and intersection are bounds).** Let $A : \iota \to \texttt{Set}\ \alpha$ and let $t$ be a set. Then:

1. $A_j \subseteq \bigcup_i A_i$ and $\bigcap_i A_i \subseteq A_j$ for every $j$;
2. $\bigcup_i A_i \subseteq t$ if and only if $A_i \subseteq t$ for every $i$;
3. $t \subseteq \bigcap_i A_i$ if and only if $t \subseteq A_i$ for every $i$.

*Proof.* 1. If $x \in A_j$, then $j$ is a witness for $\exists i,\ x \in A_i$. If $x \in \bigcap_i A_i$, then $x \in A_i$ for each $i$, in particular for $j$.

2. If $\bigcup_i A_i \subseteq t$, then $A_i \subseteq \bigcup_i A_i \subseteq t$ by part 1 and transitivity. Conversely, let $x \in \bigcup_i A_i$. There is $i$ with $x \in A_i$, and the hypothesis for $i$ gives $x \in t$. The goal $x \in t$ does not depend on $i$, so the use of the existential is allowed.

3. If $t \subseteq \bigcap_i A_i$, then $t \subseteq A_i$ by part 1. Conversely, let $x \in t$ and fix $i$. The hypothesis for $i$ gives $x \in A_i$. So $x \in \bigcap_i A_i$. $\square$

Part 2 says that $\bigcup_i A_i$ is the smallest set that contains every $A_i$. Part 3 says that $\bigcap_i A_i$ is the largest set contained in every $A_i$. Volume 4 states these facts as "supremum" and "infimum" in a complete lattice.

**Theorem (De Morgan laws for families).** For $A : \iota \to \texttt{Set}\ \alpha$:
$$\Bigl(\bigcup_i A_i\Bigr)^{c} = \bigcap_i A_i^{c}, \qquad \Bigl(\bigcap_i A_i\Bigr)^{c} = \bigcup_i A_i^{c}.$$

*Proof.* Fix $x$. The first equation is $\lnot(\exists i,\ x \in A_i) \leftrightarrow \forall i,\ x \notin A_i$, the constructive law for quantifiers of Section 2 of Chapter 1. The second equation is $\lnot(\forall i,\ x \in A_i) \leftrightarrow \exists i,\ x \notin A_i$, the classical law for quantifiers of the same section. Extensionality turns each equivalence into an equation of sets. $\square$

::: mathlib
`Set.compl_iUnion` · `Mathlib.Data.Set.Lattice.Indexed`

The two laws are `Set.compl_iUnion` and `Set.compl_iInter`. The module also has the distributive laws `Set.inter_iUnion : s ∩ ⋃ i, t i = ⋃ i, s ∩ t i` and `Set.union_iInter`, and the bounds `Set.subset_iUnion`, `Set.iInter_subset` and `Set.iUnion_subset`.

<?decl Set.compl_iUnion?>
:::

**Theorem (Distributive law for families).** For a set $s$ and a family $A$:
$$s \cap \bigcup_i A_i = \bigcup_i (s \cap A_i).$$

*Proof.* Fix $x$. The left side is $x \in s \land \exists i,\ x \in A_i$. The right side is $\exists i,\ x \in s \land x \in A_i$. From left to right, take the witness $i$ of the second conjunct; the pair $\langle x \in s, x \in A_i\rangle$ is a proof for $i$. From right to left, a witness $i$ gives $x \in s$ and the witness $i$ for $\exists i,\ x \in A_i$. $\square$

**Theorem (Size of the power set).** Let $s$ be a finite set with $n$ elements. Then $\mathcal{P}(s)$ has $2^n$ elements.

*Proof.* Induction on $n$. If $n = 0$, then $s = \emptyset$, and the only subset of $\emptyset$ is $\emptyset$. So $\mathcal{P}(s)$ has $1 = 2^0$ element.

Assume the claim for sets with $n$ elements, and let $s$ have $n + 1$ elements. Choose $a \in s$ and let $s' = s \setminus \{a\}$, a set with $n$ elements. Each subset $t \subseteq s$ either does not contain $a$, and then $t \subseteq s'$, or contains $a$, and then $t = t' \cup \{a\}$ with $t' = t \setminus \{a\} \subseteq s'$. The two kinds are disjoint. The map $t' \mapsto t' \cup \{a\}$ is a bijection from $\mathcal{P}(s')$ to the subsets of the second kind, with inverse $t \mapsto t \setminus \{a\}$. So the number of subsets of $s$ is $2^n + 2^n = 2^{n + 1}$. $\square$

::: mathlib
`Finset.card_powerset` · `Mathlib.Data.Finset.Powerset`

For a finset, `Finset.powerset s` is the finset of all subfinsets, and the theorem is `(Finset.powerset s).card = 2 ^ s.card`. The proof in Mathlib follows the induction above, with `Finset.induction_on`.

<?decl Finset.card_powerset?>
:::

### Examples

**Example (Shrinking intervals).** For $n : \mathbb{N}$, let $A_n = \{x : \mathbb{R} \mid |x| < 1/(n + 1)\}$. Then $\bigcap_n A_n = \{0\}$. Clearly $|0| = 0 < 1/(n + 1)$ for each $n$. Conversely, let $x \neq 0$. Then $|x| > 0$, and by the Archimedean property there is $n$ with $1/(n + 1) < |x|$. So $x \notin A_n$, and $x$ is not in the intersection. The union $\bigcup_n A_n$ is $A_0 = (-1, 1)$, since $A_n \subseteq A_0$ for every $n$.

**Example (Four forms of one count).** The numbers below $3$ are three, and Mathlib can say this in four ways: the finset `Finset.range 3` has card $3$; the type `Fin 3` has `Fintype.card` $3$; the subtype of the elements of `Finset.range 3` has `Fintype.card` $3$; and the set `Set.Iio 3` has `ncard` $3$. Each form has its own lemma. The last form needs a rewrite from the set to the finset, by `Finset.coe_range`.

<?lean MathlibHandbook/V01/C02/Examples.lean#four_forms?>

**Counterexample (Closure and infinite unions).** The equation $\bigcap_i (s \cup A_i) = s \cup \bigcap_i A_i$ holds, but the analogue $\bigcup_n \overline{A_n} = \overline{\bigcup_n A_n}$ for closures in $\mathbb{R}$ fails. Take $A_n = \{1/(n + 1)\}$. Each $A_n$ is closed, so the left side is $\{1/(n + 1) \mid n\}$. The closure of the union also contains $0$. Laws of sets hold for all families. Laws that mix sets with a topology can fail for infinite families, and this is why topology distinguishes finite and infinite unions.

### The library around it

The notation `⋃ i, A i` and `⋂ i, A i` comes from `Mathlib.Order.SetNotation`, which also defines `⋃₀` and `⋂₀`. The lemmas are in `Mathlib.Data.Set.Lattice.Indexed` and `Mathlib.Data.Set.Lattice`. The notation `⋃ i ∈ s, A i` is a double union, first over $i$ and then over proofs of $i \in s$, and its membership lemma is `Set.mem_iUnion₂`.

For finite collections, the rule is as follows. Use a `Finset` when a proof sums or counts over the collection. Use a type with `Fintype` when the collection is a type, such as `Fin n` or `Bool`. Use a set with `Set.Finite` when the collection is a set and finiteness is a property to prove. The lemmas `Finset.coe_range`, `Finset.mem_coe`, `Set.toFinset` and `Set.ncard_coe_finset` pass between the forms. Volume 3 treats finite sets in detail.

#### Common errors

1. A learner writes `⋃ i, A i` with `A : ℕ → Set ℕ` and `simp` gives a goal with `∃ i`. This is correct: the union is an existential.
2. A learner applies `Set.iUnion_const` without the hypothesis that the index type is nonempty.
3. A learner uses `Set.ncard` for an infinite set and gets $0$. The value $0$ is a junk value, as Chapter 5 explains. Use `Set.encard` for a value in $\mathbb{N} \cup \{\infty\}$.

### Exercises

1. (A) Compute $\bigcup_{n \geq 1} [1/n, 1]$ and $\bigcap_{n \geq 1} (0, 1/n)$ in $\mathbb{R}$.
2. (A) Prove $s \cup \bigcap_i A_i = \bigcap_i (s \cup A_i)$.
3. (B) Prove that $\bigcup_i (A_i \cap B_i) \subseteq (\bigcup_i A_i) \cap (\bigcup_i B_i)$, and give an example where the inclusion is strict.
4. (B) Prove that $s \subseteq t$ if and only if $\mathcal{P}(s) \subseteq \mathcal{P}(t)$.
5. (B) Prove that $\mathcal{P}(s \cap t) = \mathcal{P}(s) \cap \mathcal{P}(t)$. Show that $\mathcal{P}(s \cup t) = \mathcal{P}(s) \cup \mathcal{P}(t)$ fails for $s = \{0\}$ and $t = \{1\}$.
6. (C) For a family $A : \mathbb{N} \to \texttt{Set}\ \alpha$, define $\limsup A = \bigcap_n \bigcup_{k \geq n} A_k$. Prove that $x \in \limsup A$ if and only if $x \in A_k$ for infinitely many $k$.
7. (L) Prove that `Finset.range 5` has five elements. The solution is `card_range_five` in `Solutions.lean`.

### Notes and history

Unions and intersections of infinite families appear in the work of Cantor on point sets (1879 to 1884) and of Borel on measure (1898). The limit superior of Exercise 6 is the basis of the lemma of Borel and Cantelli in probability.

### Reference

<?reference?>
