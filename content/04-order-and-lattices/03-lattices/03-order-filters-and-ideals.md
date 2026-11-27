---
title: Order filters and ideals
kind: theory
modules:
  - Mathlib.Order.Ideal
  - Mathlib.Order.PFilter
  - Mathlib.Order.PrimeIdeal
  - Mathlib.Order.PrimeSeparator
explains:
  E3: [Order.Ideal, Order.PFilter, Order.Ideal.IsPrime]
  E2: [Order.IsIdeal, Order.IsPFilter, Order.Ideal.principal, Order.PFilter.principal, Order.Ideal.mem_principal, Order.PFilter.mem_principal, Order.Ideal.IsProper, Order.Ideal.IsMaximal, Order.Ideal.IsProper.exists_le_maximal, Order.PFilter.IsPrime, Order.Ideal.isPrime_iff_mem_or_mem, Order.Ideal.IsMaximal.isPrime, Order.Ideal.sup_mem, Order.PFilter.inf_mem, DistribLattice.prime_ideal_of_disjoint_filter_ideal]
  E1: auto
families: []
requires: [V04.C01]
reads_with: ["MIL"]
lean:
  - MathlibHandbook/V04/C03/Examples.lean
  - MathlibHandbook/V04/C03/Exercises.lean
  - MathlibHandbook/V04/C03/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Order filters and ideals

### Overview

An ideal of a lattice is a set that is closed under $\sqcup$ and that contains each element below one of its elements. A filter is the dual notion. A filter on a type $X$ is a filter in the Boolean algebra of the subsets of $X$: a family of "large" sets that contains $X$ and is closed under finite intersections and supersets. Filters carry the theory of limits in Mathlib.

The main theorem is the ultrafilter lemma, proved with Zorn's lemma. The section ends with the type `Filter α` of Mathlib, its reversed order and its lattice structure. Volume 13 uses these filters for limits and topology.

### Definitions

Let $P$ be a partial order. A set $S \subseteq P$ is a *lower set* if $x \in S$ and $y \le x$ give $y \in S$. It is an *upper set* if $x \in S$ and $x \le y$ give $y \in S$. It is *directed* if any two elements of $S$ have a common upper bound in $S$, and *codirected* if any two have a common lower bound in $S$.

**Definition (Ideal).** An ideal of a partial order $P$ is a nonempty, directed lower set $I \subseteq P$. It is *proper* if $I \ne P$. The principal ideal of $a \in P$ is ${\downarrow} a = \{x \in P \mid x \le a\}$.

**Definition (Order filter).** A filter of a partial order $P$ is a nonempty, codirected upper set $F \subseteq P$. It is *proper* if $F \ne P$. The principal filter of $a$ is ${\uparrow} a = \{x \in P \mid a \le x\}$.

*Remarks.* A filter of $P$ is an ideal of the order dual of $P$, so each theorem about ideals gives a theorem about filters. If $P$ has a top element, an ideal $I$ is proper if and only if $\top \notin I$; dually, a filter is proper if and only if $\bot \notin F$.

**Definition (Prime and maximal).** Let $L$ be a lattice. A proper ideal $I$ is *prime* if $x \sqcap y \in I$ gives $x \in I$ or $y \in I$. A proper filter $F$ is *prime* if $x \sqcup y \in F$ gives $x \in F$ or $y \in F$. A proper ideal or filter is *maximal* if no proper ideal or filter strictly contains it. A maximal proper filter is also called an *ultrafilter*.

::: mathlib
`Order.Ideal` · `Mathlib.Order.Ideal`

The structure `Order.Ideal P` extends `LowerSet P` with the fields `nonempty'` and `directed'`, and it needs only `LE P`. Mathlib asks for directed sets and not for closure under `⊔`, because `P` need not have `⊔`. The predicate on sets is `Order.IsIdeal`.

<?decl Order.Ideal?>
:::

::: mathlib
`Order.PFilter` · `Mathlib.Order.PFilter`

The structure `Order.PFilter P` has one field `dual : Order.Ideal Pᵒᵈ`, so a filter is an ideal of the dual order. The name avoids a clash with `Filter`. The lemma `Order.PFilter.mem_principal` states `x ∈ principal y ↔ y ≤ x`.

<?decl Order.PFilter?>
:::

::: mathlib
`Order.Ideal.IsPrime` · `Mathlib.Order.PrimeIdeal`

The class has the fields of `IsProper` and `compl_filter : IsPFilter (I : Set P)ᶜ`, so a prime ideal is a proper ideal whose complement is a filter. In a meet semilattice, `Order.Ideal.isPrime_iff_mem_or_mem` gives the form above; the next theorem proves this.

<?decl Order.Ideal.IsPrime?>
:::

### Theorems and proofs

**Theorem (Ideals and filters of a lattice).** Let $L$ be a lattice and let $I \subseteq L$ be a nonempty lower set. Then $I$ is an ideal if and only if $x, y \in I$ give $x \sqcup y \in I$. Dually, a nonempty upper set $F$ is a filter if and only if $x, y \in F$ give $x \sqcap y \in F$.

*Proof.* Suppose $I$ is closed under $\sqcup$. For $x, y \in I$, the element $x \sqcup y$ is in $I$ and is an upper bound of $x$ and $y$, so $I$ is directed. Conversely, suppose $I$ is directed, and let $x, y \in I$. There is $z \in I$ with $x \le z$ and $y \le z$. By the universal property $x \sqcup y \le z$, and $I$ is a lower set, so $x \sqcup y \in I$. The statement for filters is the dual statement. $\square$

**Theorem (Prime ideals and prime filters).** Let $L$ be a lattice and let $I$ be a proper ideal. Then $I$ is prime if and only if its complement $F = L \setminus I$ is a filter. In this case $F$ is a prime filter.

*Proof.* Suppose $I$ is prime. The set $F$ is nonempty, because $I \ne L$. It is an upper set: let $x \in F$ and $x \le y$; if $y \in I$, then $x \in I$ because $I$ is a lower set, a contradiction, so $y \in F$. It is closed under $\sqcap$: let $x, y \in F$; if $x \sqcap y \in I$, then $x \in I$ or $y \in I$ because $I$ is prime, a contradiction. By the previous theorem $F$ is a filter. It is proper because $I$ is nonempty. It is prime: if $x \notin F$ and $y \notin F$, then $x, y \in I$, so $x \sqcup y \in I$ by the previous theorem, and $x \sqcup y \notin F$.

Conversely, suppose $F$ is a filter, and let $x \sqcap y \in I$. If $x \notin I$ and $y \notin I$, then $x, y \in F$, so $x \sqcap y \in F$, a contradiction. So $x \in I$ or $y \in I$. $\square$

**Theorem (Maximal filters of a Boolean algebra).** Let $B$ be a Boolean algebra and let $F$ be a proper filter of $B$. The following are equivalent:

1. $F$ is a maximal proper filter;
2. for each $a \in B$, $a \in F$ or $a^c \in F$;
3. $F$ is prime.

Under these conditions, exactly one of $a$ and $a^c$ is in $F$.

*Proof.* First, $a$ and $a^c$ are never both in $F$: otherwise $a \sqcap a^c = \bot \in F$, and $F$ is not proper. This gives the last statement once 2 holds.

1 gives 2. Let $F$ be maximal, and suppose $a \notin F$ and $a^c \notin F$. Let
$$G = \{x \in B \mid f \sqcap a \le x \text{ for some } f \in F\}.$$
The set $G$ is an upper set by transitivity. It is closed under $\sqcap$: if $f_1 \sqcap a \le x$ and $f_2 \sqcap a \le y$, then $(f_1 \sqcap f_2) \sqcap a \le x \sqcap y$, and $f_1 \sqcap f_2 \in F$. The filter $F$ is nonempty and an upper set, so $\top \in F$, and $\top \sqcap a = a$ gives $a \in G$. Each $f \in F$ is in $G$, since $f \sqcap a \le f$. So $G$ is a filter with $F \subseteq G$, and $G \ne F$ because $a \in G$. The filter $G$ is proper. Indeed, suppose $\bot \in G$, so $f \sqcap a = \bot$ for some $f \in F$. Then
$$f = f \sqcap (a \sqcup a^c) = (f \sqcap a) \sqcup (f \sqcap a^c) = f \sqcap a^c \le a^c,$$
so $a^c \in F$, a contradiction. Thus $G$ is a proper filter that strictly contains $F$, and $F$ is not maximal. This contradiction proves 2.

2 gives 3. Let $x \sqcup y \in F$ and $x \notin F$. By 2, $x^c \in F$. Then $x^c \sqcap (x \sqcup y) \in F$. By distributivity, $x^c \sqcap (x \sqcup y) = (x^c \sqcap x) \sqcup (x^c \sqcap y) = x^c \sqcap y \le y$. So $y \in F$.

3 gives 1. Let $F$ be prime, and let $G$ be a proper filter with $F \subseteq G$. Let $b \in G$. The element $b \sqcup b^c = \top$ is in $F$, so $b \in F$ or $b^c \in F$. If $b^c \in F$, then $b^c \in G$, and $b \sqcap b^c = \bot \in G$, which is false. So $b \in F$. Thus $G = F$, and $F$ is maximal. $\square$

The last theorem uses Zorn's lemma in the form for families of sets from Section 4 of Chapter 1 (`zorn_subset_nonempty`): if $\mathcal{S}$ is a family of subsets of a set and each nonempty chain in $\mathcal{S}$ has an upper bound in $\mathcal{S}$ for $\subseteq$, then each $S_0 \in \mathcal{S}$ is contained in a maximal member of $\mathcal{S}$. Here the union of the chain is the upper bound.

**Theorem (Ultrafilter lemma).** Let $L$ be a bounded lattice and let $F_0$ be a proper filter of $L$. There is a maximal proper filter $M$ with $F_0 \subseteq M$.

*Proof.* Let $\mathcal{S}$ be the family of the proper filters of $L$ that contain $F_0$. It contains $F_0$. Let $\mathcal{C} \subseteq \mathcal{S}$ be a nonempty chain, and let $U = \bigcup \mathcal{C}$. Show that $U \in \mathcal{S}$.

*$U$ is nonempty and contains $F_0$*, because $\mathcal{C}$ has a member and each member contains $F_0$.

*$U$ is an upper set.* Let $x \in U$ and $x \le y$. Then $x \in G$ for some $G \in \mathcal{C}$, so $y \in G \subseteq U$.

*$U$ is closed under $\sqcap$.* Let $x, y \in U$, with $x \in G_1$ and $y \in G_2$ for $G_1, G_2 \in \mathcal{C}$. The family $\mathcal{C}$ is a chain, so $G_1 \subseteq G_2$ or $G_2 \subseteq G_1$. Say $G_1 \subseteq G_2$. Then $x, y \in G_2$, so $x \sqcap y \in G_2 \subseteq U$.

*$U$ is proper.* No member of $\mathcal{C}$ contains $\bot$, so $\bot \notin U$.

By the first theorem, $U$ is a filter, and so $U \in \mathcal{S}$. Zorn's lemma gives a maximal member $M$ of $\mathcal{S}$ with $F_0 \subseteq M$. Let $G$ be a proper filter with $M \subseteq G$. Then $F_0 \subseteq G$, so $G \in \mathcal{S}$, and $G = M$ by the maximality of $M$ in $\mathcal{S}$. So $M$ is a maximal proper filter. $\square$

The bound $\bot$ is used in the step "$U$ is proper". In $(\mathbb{Z}, \le)$, which has no $\bot$, a proper filter is bounded below, so it is ${\uparrow} n$ for its least element $n$, and ${\uparrow} n \subsetneq {\uparrow} (n - 1)$: there is no maximal proper filter.

::: mathlib
`Order.Ideal.IsProper.exists_le_maximal` · `Mathlib.Order.Ideal`

This is the dual form, for ideals: in an order with `⊤`, each proper ideal is below a maximal ideal. For filters of sets the lemma is `Ultrafilter.exists_le`. In a distributive lattice, `DistribLattice.prime_ideal_of_disjoint_filter_ideal` separates a filter from a disjoint ideal by a prime ideal.

<?decl Order.Ideal.IsProper.exists_le_maximal?>
:::

#### Filters of sets

Let $X$ be a set. A filter of the Boolean algebra of the subsets of $X$ is a family $\mathcal{F}$ of subsets with $X \in \mathcal{F}$ that is closed under supersets and under $\cap$. It is proper if and only if $\emptyset \notin \mathcal{F}$. Mathlib calls the type of these families `Filter X`, and it allows the improper filter of all sets.

The order on `Filter X` is the reverse of inclusion: $f \le g$ means that each member of $g$ is a member of $f$. For the principal filters $\mathcal{P}(s) = \{t \mid s \subseteq t\}$ this gives $\mathcal{P}(s) \le \mathcal{P}(t)$ if and only if $s \subseteq t$, so a filter is a "generalized set". The bottom filter is the family of all sets, and the top filter is $\{X\}$.

**Theorem (The lattice of filters).** The filters on $X$ form a lattice. The sup of $f$ and $g$ is the filter $f \cap g$ of the sets that are in both, and the inf is
$$f \sqcap g = \{s \mid s \supseteq t_1 \cap t_2 \text{ for some } t_1 \in f,\ t_2 \in g\}.$$
More generally, the intersection of any family of filters is a filter, and it is the sup of the family.

*Proof.* Let $(f_i)_{i \in I}$ be a family of filters and let $h = \bigcap_i f_i$. Each $f_i$ satisfies the three axioms, so $h$ does. In the reversed order, $f_i \le h$ because $h \subseteq f_i$. If $f_i \le k$ for each $i$, then $k \subseteq f_i$ for each $i$, so $k \subseteq h$, that is $h \le k$. So $h$ is the least upper bound, and for $I = \{1, 2\}$ the sup is $f \cap g$.

For the inf, let $m$ be the family in the statement. It contains $X$ and it is an upper set. If $s \supseteq t_1 \cap t_2$ and $s' \supseteq t_1' \cap t_2'$, then $s \cap s' \supseteq (t_1 \cap t_1') \cap (t_2 \cap t_2')$, so $m$ is a filter. Each $t_1 \in f$ is in $m$, because $X \in g$, so $f \subseteq m$, that is $m \le f$; similarly $m \le g$. If $k \le f$ and $k \le g$, then $f, g \subseteq k$, so $k$ contains each $t_1 \cap t_2$ and its supersets, and $k \le m$. $\square$

Since each family has a sup, the filters on $X$ form a complete lattice, by the theorem of Chapter 4.

::: mathlib
`Filter` · `Mathlib.Order.Filter.Defs`

The structure `Filter α` has the field `sets : Set (Set α)` and the three axioms. The order is reversed by definition: `Filter.le_def` states `f ≤ g ↔ ∀ x ∈ g, x ∈ f`. The principal filter is `𝓟 s`, and `Filter.le_principal_iff` states `f ≤ 𝓟 s ↔ s ∈ f`. Volume 13 is the home of the theory.

<?decl Filter?>
:::

### Examples

**Example (A prime ideal of a finite lattice).** In the lattice $D_{12}$ of the divisors of $12$, with $\sqcap = \gcd$ and $\sqcup = \operatorname{lcm}$, the ideal ${\downarrow} 6 = \{1, 2, 3, 6\}$ is prime: its complement $\{4, 12\}$ is the filter ${\uparrow} 4$. The ideal ${\downarrow} 2 = \{1, 2\}$ is not prime: $\gcd(3, 4) = 1 \in {\downarrow} 2$, but $3, 4 \notin {\downarrow} 2$.

**Example (The ideal of finite sets).** In the subsets of $\mathbb{N}$, the finite sets form a proper ideal, and it is not principal: if it were ${\downarrow} s$, then the finite set $s$ would contain each $\{n\}$. Their complements form the cofinite filter, by the law of De Morgan. In Mathlib this is `Filter.cofinite`.

**Example (The filter at infinity).** On $\mathbb{Z}$, the sets that contain all $b \ge a$ for some $a$ form a filter; for two such sets, take $a$ above both thresholds. This is `Filter.atTop`. It differs from the cofinite filter: $\mathbb{N} \in$ `atTop`, but its complement is infinite. Each cofinite set of integers contains all large integers, so `atTop ≤ cofinite` on $\mathbb{Z}$. On $\mathbb{N}$ the two filters are equal.

**Example (Principal ultrafilters).** Let $a \in X$. The filter $U_a = \mathcal{P}(\{a\})$ is proper, and for each $s$, $a \in s$ or $a \in X \setminus s$. By the theorem on Boolean algebras, $U_a$ is an ultrafilter.

**Example (A non-principal ultrafilter).** The cofinite filter on $\mathbb{N}$ is proper, so by the ultrafilter lemma an ultrafilter $U$ contains it. No finite set $s$ is in $U$, because its complement is in $U$. So $\{a\} \notin U$ for each $a$, and $U$ is not principal. The proof gives no description of $U$: without some form of the axiom of choice, a non-principal ultrafilter on $\mathbb{N}$ cannot be proved to exist.

### The library around it

The API of `Order.Ideal` has `Order.Ideal.principal`, `Order.Ideal.mem_principal` and `Order.Ideal.sup_mem`; `Order.Ideal.IsProper` and `Order.Ideal.IsMaximal` are classes. The API of `Order.PFilter` is the dual one, with `Order.PFilter.inf_mem`. The lemma `Order.Ideal.IsMaximal.isPrime` states that a maximal ideal of a distributive lattice is prime.

### Exercises

1. (A) List the ideals of the lattice $D_{12}$ of the divisors of $12$, and say which of them are prime. *Hint:* in a finite lattice each ideal is principal, because the sup of its elements is in it.
2. (A) Show that the intersection of two ideals of a lattice is an ideal, if it is nonempty. *Hint:* check the lower set property and the closure under $\sqcup$.
3. (B) Let $f$ be a filter on $X$ and $\varphi : X \to Y$ a function. Show that $\{t \subseteq Y \mid \varphi^{-1}(t) \in f\}$ is a filter on $Y$. This is `Filter.map φ f`. *Hint:* the preimage keeps intersections and inclusions.
4. (B) Show that an ultrafilter $U$ on $X$ is prime in the sense of sets: $s \cup t \in U$ gives $s \in U$ or $t \in U$. Give a filter that is not an ultrafilter and for which this fails. *Hint:* for the second part, use $\mathcal{P}(\{0, 1\})$ on $\mathbb{N}$.
5. (B) Prove that in a distributive lattice each maximal proper ideal is prime. *Hint:* if $x \sqcap y \in I$ and $x, y \notin I$, look at the ideal generated by $I$ and $x$, which is $\{z \mid z \le i \sqcup x \text{ for some } i \in I\}$.
6. (C) Show that the lattice $M_3$ has a maximal proper ideal that is not prime, so the hypothesis "distributive" in Exercise 5 is needed. *Hint:* try ${\downarrow} x$.

### Notes and history

Cartan introduced filters in 1937, and Bourbaki made them the base of convergence. Tarski proved the ultrafilter lemma for sets in 1930. Stone used prime ideals in his representation theorems of 1936 and 1937. A reference is Davey and Priestley, *Introduction to Lattices and Order*, Chapter 10.

In Mathlib, the filters of sets came first, after the work of Hölzl, Immler and Huffman in Isabelle; the order ideals came later.

### Reference

<?reference?>
