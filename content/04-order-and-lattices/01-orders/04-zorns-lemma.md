---
title: Zorn's lemma
kind: theory
modules:
  - Mathlib.Order.Zorn
  - Mathlib.Order.Preorder.Chain
  - Mathlib.Order.TeichmullerTukey
  - Mathlib.Order.ZornAtoms
  - Mathlib.Order.Extension.Linear
  - Mathlib.Order.CompleteLattice.Chain
  - Mathlib.Order.BourbakiWitt
explains:
  E3: [zorn_le_nonempty, IsChain]
  E2: [zorn_le, zorn_le₀, zorn_le_nonempty₀, zorn_subset, zorn_subset_nonempty, exists_maximal_of_chains_bounded, IsMaxChain, IsChain.total]
  E1: auto
families: []
requires: [V01]
reads_with: ["MIL", "TPIL"]
lean:
  - MathlibHandbook/V04/C01/Examples.lean
  - MathlibHandbook/V04/C01/Exercises.lean
  - MathlibHandbook/V04/C01/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Zorn's lemma

### Overview

Some objects of algebra exist, but no explicit construction gives them: a basis of $\mathbb{R}$ as a vector space over $\mathbb{Q}$, an algebraic closure of a field. Zorn's lemma is the tool that proves their existence. It says that a partial order in which each chain has an upper bound has a maximal element.

This section defines chains, proves the fixed point theorem of Bourbaki and Witt, and deduces Zorn's lemma from it and the axiom of choice. Two applications follow, also with full proofs: each proper ideal of a commutative ring lies in a maximal ideal, and each vector space has a basis.

### Definitions

**Definition (Chain).** Let $\alpha$ be a preorder. A subset $C \subseteq \alpha$ is a chain if any two elements of $C$ are comparable: for $x, y \in C$, $x \le y$ or $y \le x$. A chain is maximal if no chain strictly contains it.

The empty set is a chain, and each subset with one element is a chain. In a linear order each subset is a chain. In the subsets of $\mathbb{N}$ with $\subseteq$, the family $\{\{0\}, \{0,1\}, \{0,1,2\}, \dots\}$ is a chain, and $\{\{0\}, \{1\}\}$ is not.

::: mathlib
`IsChain` · `Mathlib.Order.Preorder.Chain`

`IsChain r s` is defined for any relation `r`, as `s.Pairwise fun x y => r x y ∨ r y x`. The pairwise condition is only for distinct elements, so the relation need not be reflexive. The lemma `IsChain.total` gives the comparison of two elements of a chain for a reflexive relation. `IsMaxChain r s` says that `s` is a chain and that each chain that contains `s` is equal to `s`.

<?decl IsChain?>
:::


### Theorems and proofs

**Theorem (Bourbaki-Witt).** Let $X$ be a partial order in which each chain, the empty chain included, has a least upper bound. Let $g : X \to X$ satisfy $x \le g(x)$ for each $x$. Then $g$ has a fixed point: there is $s \in X$ with $g(s) = s$.

*Proof.* The plan: build the smallest subset $M$ that is closed under $g$ and under suprema of chains, show that $M$ is a chain, and take its supremum. Write $\sup K$ for the least upper bound of a chain $K$, and $\bot = \sup \emptyset$. Each element is an upper bound of $\emptyset$, so $\bot \le x$ for each $x$.

*Step 1.* Call a subset $T \subseteq X$ a tower if $\bot \in T$, if $x \in T$ gives $g(x) \in T$, and if $\sup K \in T$ for each chain $K \subseteq T$. The set $X$ is a tower. Let $M$ be the intersection of all towers. Then $M$ is a tower: $\bot$ is in each tower; if $x \in M$, then $x$ is in each tower $T$, so $g(x) \in T$ for each $T$; if $K \subseteq M$ is a chain, then $K \subseteq T$ for each tower $T$, so $\sup K \in T$. Each tower contains $M$. So a tower $T \subseteq M$ is equal to $M$.

*Step 2.* Call $c \in M$ extreme if each $x \in M$ with $x < c$ satisfies $g(x) \le c$. For an extreme $c$, let $M_c = \{x \in M : x \le c \text{ or } g(c) \le x\}$. The claim is that $M_c$ is a tower. First, $\bot \le c$, so $\bot \in M_c$. Next, let $x \in M_c$. There are three cases. If $x < c$, then $g(x) \le c$ because $c$ is extreme. If $x = c$, then $g(c) \le g(x)$. If $g(c) \le x$, then $g(c) \le x \le g(x)$. In each case $g(x) \in M_c$, and $g(x) \in M$ since $M$ is a tower. Last, let $K \subseteq M_c$ be a chain and $s = \sup K$. Then $s \in M$. If each $k \in K$ satisfies $k \le c$, then $c$ is an upper bound of $K$ and $s \le c$. Otherwise there is $k \in K$ with $g(c) \le k$, and then $g(c) \le k \le s$. In both cases $s \in M_c$. So $M_c$ is a tower contained in $M$, and $M_c = M$ by Step 1.

So, for each extreme $c$ and each $x \in M$: $x \le c$ or $g(c) \le x$. $(\ast)$

*Step 3.* Let $E$ be the set of extreme elements of $M$. The claim is that $E$ is a tower. First, $\bot \in E$, because no $x$ satisfies $x < \bot$.

Next, let $c \in E$, and let $x \in M$ with $x < g(c)$. By $(\ast)$, $x \le c$ or $g(c) \le x$. The second is false, because $x < g(c)$. So $x \le c$. If $x < c$, then $g(x) \le c \le g(c)$. If $x = c$, then $g(x) = g(c)$. In both cases $g(x) \le g(c)$, so $g(c) \in E$.

Last, let $K \subseteq E$ be a chain, $s = \sup K$, and $x \in M$ with $x < s$. By $(\ast)$ for each $k \in K$, $x \le k$ or $g(k) \le x$. If $g(k) \le x$ for each $k \in K$, then $k \le g(k) \le x$ for each $k$, so $x$ is an upper bound of $K$ and $s \le x$. This contradicts $x < s$. So there is $k \in K$ with $x \le k$. If $x < k$, then $g(x) \le k \le s$, since $k$ is extreme. If $x = k$, then $k < s$, so $k$ is not an upper bound of $K$, and there is $k' \in K$ with $k' \not\le k$. The chain $K$ gives $k \le k'$, and $k \ne k'$, so $k < k'$. Since $k'$ is extreme, $g(k) \le k' \le s$. In each case $g(x) \le s$, so $s \in E$.

So $E$ is a tower, and $E = M$. Each element of $M$ is extreme. Now let $x, y \in M$. By $(\ast)$ for $c = y$, $x \le y$ or $g(y) \le x$, and the second gives $y \le g(y) \le x$. So $x$ and $y$ are comparable, and $M$ is a chain.

*Step 4.* Let $s = \sup M$. Since $M$ is a chain contained in the tower $M$, $s \in M$. Then $g(s) \in M$, so $g(s) \le s$. Also $s \le g(s)$ by the hypothesis on $g$. Antisymmetry gives $g(s) = s$. $\square$

The proof does not use the axiom of choice. Choice enters in the next proof, to choose the map $g$.

**Theorem (Zorn's lemma).** Let $P$ be a partial order in which each chain has an upper bound. Then $P$ has a maximal element.

*Proof.* Let $\mathcal{C}$ be the set of chains of $P$, ordered by inclusion. It is a partial order. Each chain $\mathcal{K}$ of $\mathcal{C}$ has a least upper bound in $\mathcal{C}$, namely the union $U = \bigcup \mathcal{K}$. Indeed, $U$ is a chain of $P$: let $x, y \in U$, with $x \in C_1$ and $y \in C_2$ for $C_1, C_2 \in \mathcal{K}$. The sets $C_1$ and $C_2$ are comparable, so both $x$ and $y$ lie in the larger one, which is a chain, and $x$ and $y$ are comparable. The union is an upper bound of $\mathcal{K}$, and it is contained in each upper bound. For the empty family, $U = \emptyset$, which is a chain.

Suppose that $P$ has no maximal element. Let $C \in \mathcal{C}$. By hypothesis $C$ has an upper bound $u$. The element $u$ is not maximal, so there is $v \in P$ with $u < v$. Then $x \le u < v$ for each $x \in C$, so $x < v$ for each $x \in C$, and $v \notin C$. By the axiom of choice, there is a function $f$ on $\mathcal{C}$ such that $f(C)$ is such an element $v$ for each chain $C$. Put $g(C) = C \cup \{f(C)\}$. It is a chain, since $f(C)$ is above each element of $C$. So $g : \mathcal{C} \to \mathcal{C}$, $C \subseteq g(C)$, and $C \ne g(C)$ because $f(C) \notin C$. This contradicts the theorem of Bourbaki and Witt applied to $\mathcal{C}$ and $g$. So $P$ has a maximal element. $\square$

The hypothesis includes the empty chain. An upper bound of the empty chain is any element of $P$, so the hypothesis says in particular that $P$ is nonempty. In practice the empty chain is treated apart, and the usual form is: if $P$ is nonempty and each nonempty chain has an upper bound, then $P$ has a maximal element.

::: mathlib
`zorn_le_nonempty` · `Mathlib.Order.Zorn`

The base form is `exists_maximal_of_chains_bounded`, for any transitive relation `r`. Mathlib proves it from the Hausdorff maximality principle: an upper bound of a maximal chain is a maximal element. The variants have names by a pattern: `zorn_le` for `≤` on a type, `zorn_subset` for `⊆` on a family of sets, the suffix `₀` for a subset of the type, and the suffix `_nonempty` to treat only nonempty chains. So `zorn_le_nonempty` asks for `[Nonempty α]` and bounds for nonempty chains, and gives `∃ m, IsMax m`. The statements need only a `Preorder`.

<?decl zorn_le_nonempty?>
:::

**Theorem (Zorn's lemma for families of sets).** Let $X$ be a set, let $S$ be a family of subsets of $X$, and let $A \in S$. Assume that the union of each nonempty chain of $S$ is in $S$. Then there is a maximal element $M$ of $S$ with $A \subseteq M$.

*Proof.* Order $S$ by inclusion. Let $T = \{B \in S : A \subseteq B\}$. It is nonempty, since $A \in T$. Let $\mathcal{K} \subseteq T$ be a nonempty chain. Its union $U$ is in $S$ by hypothesis, and $A \subseteq K \subseteq U$ for each $K \in \mathcal{K}$, so $U \in T$ is an upper bound of $\mathcal{K}$. By the nonempty form of Zorn's lemma, $T$ has a maximal element $M$. Let $B \in S$ with $M \subseteq B$. Then $A \subseteq B$, so $B \in T$, and $B = M$. So $M$ is maximal in $S$. $\square$

::: mathlib
`zorn_subset_nonempty` · `Mathlib.Order.Zorn`

This is the form for a family `S : Set (Set α)` ordered by inclusion. The hypothesis is that each nonempty chain `c ⊆ S` has an upper bound in `S`, and the result gives, for each `x ∈ S`, a maximal `m ∈ S` with `x ⊆ m`. A proof starts with `obtain ⟨m, hxm, hm⟩ := zorn_subset_nonempty S ?_ x hx`, and the goal `?_` is the bound for chains.

<?decl zorn_subset_nonempty?>
:::

**Theorem (Krull).** Let $R$ be a commutative ring and let $I \subsetneq R$ be a proper ideal. Then there is a maximal ideal $M$ with $I \subseteq M$.

*Proof.* Let $S$ be the set of ideals $J$ of $R$ with $1 \notin J$. An ideal $J$ satisfies $1 \notin J$ if and only if $J \ne R$, because $1 \in J$ gives $r = r \cdot 1 \in J$ for each $r$. So $I \in S$. Let $\mathcal{K} \subseteq S$ be a nonempty chain and $U = \bigcup \mathcal{K}$. The set $U$ is an ideal. It contains $0$, because $\mathcal{K}$ has an element. Let $x, y \in U$, with $x \in J_1$ and $y \in J_2$, for $J_1, J_2 \in \mathcal{K}$. The ideals are comparable, so $x, y \in J$ for the larger one $J$. Then $x + y \in J \subseteq U$, and $ax \in J_1 \subseteq U$ for each $a \in R$. Also $1 \notin U$ because $1$ is in no member of $\mathcal{K}$. So $U \in S$. By Zorn's lemma for families of sets, there is a maximal element $M$ of $S$ with $I \subseteq M$. It remains to see that $M$ is a maximal ideal. Let $J$ be an ideal with $M \subseteq J \subsetneq R$. Then $1 \notin J$, so $J \in S$, and maximality in $S$ gives $J = M$. $\square$

::: mathlib
`Ideal.exists_le_maximal` · `Mathlib.RingTheory.Ideal.Maximal`

The theorem is stated for a `Semiring`, with the hypothesis `I ≠ ⊤`, and gives `∃ M, M.IsMaximal ∧ I ≤ M`. Mathlib deduces it from the fact that the lattice of ideals is coatomic (`IsCoatomic`): each element other than `⊤` lies below a maximal element of the elements other than `⊤`.

<?decl Ideal.exists_le_maximal?>
:::

**Theorem (Existence of a basis).** Each vector space $V$ over a field $K$ has a basis.

*Proof.* Let $\mathcal{L}$ be the set of linearly independent subsets of $V$. The empty set is linearly independent, so $\emptyset \in \mathcal{L}$. Let $\mathcal{K} \subseteq \mathcal{L}$ be a nonempty chain and $U = \bigcup \mathcal{K}$. The claim is that $U$ is linearly independent. Let $v_1, \dots, v_n \in U$ be distinct and $c_1 v_1 + \dots + c_n v_n = 0$ with $c_i \in K$. Each $v_i$ lies in some $L_i \in \mathcal{K}$. The sets $L_1, \dots, L_n$ are pairwise comparable, so one of them, say $L_j$, contains the others. Then $v_1, \dots, v_n \in L_j$, which is linearly independent, so each $c_i = 0$. So $U \in \mathcal{L}$.

By Zorn's lemma for families of sets, with $A = \emptyset$, $\mathcal{L}$ has a maximal element $B$. It is linearly independent, and it remains to show that it spans $V$. Let $v \in V$, and suppose that $v$ is not in the span of $B$. Then $v \notin B$. The set $B \cup \{v\}$ is linearly independent: let $c v + c_1 b_1 + \dots + c_n b_n = 0$ with distinct $b_i \in B$. If $c \ne 0$, then $v = -c^{-1}(c_1 b_1 + \dots + c_n b_n)$ is in the span of $B$, a contradiction. So $c = 0$, and then each $c_i = 0$ by the independence of $B$. So $B \cup \{v\}$ is an element of $\mathcal{L}$ that strictly contains $B$, which contradicts the maximality of $B$. So $B$ spans $V$, and $B$ is a basis. $\square$

The same proof shows more: each linearly independent set $L$ is contained in a basis. Take $A = L$ in place of $A = \emptyset$.

::: mathlib
`exists_linearIndependent` · `Mathlib.LinearAlgebra.LinearIndependent.Lemmas`

This lemma states that each subset `t` of a vector space over a division ring contains a linearly independent subset `b` with the same span. Applied to `t = Set.univ`, it gives a basis. The volume on linear algebra builds the basis `Module.Basis.ofVectorSpace` from it.

<?decl exists_linearIndependent?>
:::


### Examples

**Counterexample (The hypothesis of Zorn's lemma is needed).** In the finite subsets of $\mathbb{N}$ with $\subseteq$, the chain $\{0\} \subseteq \{0,1\} \subseteq \{0,1,2\} \subseteq \dots$ has no upper bound, because its union $\mathbb{N}$ is infinite, and a finite subset $F$ is not maximal, since $F \cup \{\max F + 1\}$ is larger. Each finite chain is bounded, and the conclusion fails. So it is not enough to bound the finite chains.

**Example (Maximal ideals of the integers).** Apply the theorem of Krull to $I = 12\mathbb{Z}$ in $\mathbb{Z}$. Each ideal of $\mathbb{Z}$ is $n\mathbb{Z}$ for some $n \ge 0$, and $12\mathbb{Z} \subseteq n\mathbb{Z}$ if and only if $n \mid 12$. So the proper ideals that contain $12\mathbb{Z}$ are $n\mathbb{Z}$ for $n \in \{2, 3, 4, 6, 12\}$, since $n = 1$ gives $\mathbb{Z}$. With inclusion, $12\mathbb{Z} \subseteq 4\mathbb{Z} \subseteq 2\mathbb{Z}$, $12\mathbb{Z} \subseteq 6\mathbb{Z} \subseteq 2\mathbb{Z}$ and $6\mathbb{Z} \subseteq 3\mathbb{Z}$. The maximal elements of this family are $2\mathbb{Z}$ and $3\mathbb{Z}$, the ideals of the prime divisors of $12$.

### The library around it

For Zorn's lemma, `Mathlib.Order.Zorn` has the variants listed in the boxes, with `zorn_superset` for the reversed inclusion. The file `Mathlib.Order.Preorder.Chain` has the API of chains: `IsChain.mono` for a subset of a chain, and the structure `Flag α` of a maximal chain.

The module `Mathlib.Order.TeichmullerTukey` proves a form of Zorn's lemma for families of sets. A family $F$ of subsets of $\alpha$ is of finite character, `Order.IsOfFiniteCharacter F`, if a set $X$ lies in $F$ exactly when each finite subset of $X$ lies in $F$. The lemma `Order.IsOfFiniteCharacter.exists_maximal` is the lemma of Teichmüller and Tukey: each member $x$ of such a family lies below a maximal member $m$, with $x \subseteq m$ and `Maximal (· ∈ F) m`. The proof applies `zorn_subset_nonempty`: the union of a chain in $F$ is in $F$, because a finite subset of the union lies in one member of the chain.

The module `Mathlib.Order.ZornAtoms` gives the form of Zorn's lemma for atoms and coatoms. The lemma `IsCoatomic.of_isChain_bounded` says: if each nonempty chain that does not contain $\top$ has an upper bound other than $\top$, then the order is coatomic, so each element other than $\top$ lies below a coatom. The dual `IsAtomic.of_isChain_bounded` uses lower bounds other than $\bot$. The proof applies `zorn_le_nonempty₀` to the interval from $x$ to $\top$, without $\top$. The order ideals of Chapter 3 use the coatomic form.

The module `Mathlib.Order.Extension.Linear` applies Zorn's lemma to extend a partial order to a linear order. The lemma `extend_partialOrder` says: for a partial order $r$ on $\alpha$, there is a linear order $s$ with $r \le s$. The proof applies Zorn's lemma to the set of partial orders that contain $r$. A maximal partial order $s$ is linear, because if $a$ and $b$ are not comparable, the relation $s$ together with the pairs $(x, y)$ with $s(x, a)$ and $s(b, y)$ is a larger partial order. The type synonym `LinearExtension α` carries such a linear order, and `toLinearExtension` is the monotone map from $\alpha$ to it.

The module `Mathlib.Order.CompleteLattice.Chain` gives a maximal chain without a choice of upper bounds. The set `maxChain r` is the union of the chains that `ChainClosure` makes from the empty set by successor steps and unions, and `maxChain_spec` says `IsMaxChain r (maxChain r)`. This is the maximality principle of Hausdorff. The lemma `ChainClosure.total` says that two members of the closure are comparable under inclusion, and `ChainClosure.isChain` says that each member is a chain.

The module `Mathlib.Order.BourbakiWitt` has the class `ChainCompletePartialOrder`: a partial order in which each nonempty chain, of type `NonemptyChain α`, has a supremum `ChainCompletePartialOrder.cSup`, with `ChainCompletePartialOrder.le_cSup` and `ChainCompletePartialOrder.cSup_le`. The theorem of Bourbaki and Witt is `ChainCompletePartialOrder.nonempty_fixedPoints_of_inflationary`: an inflationary map $f$, with $x \le f(x)$ for each $x$, on a nonempty chain-complete partial order has a fixed point. Each complete lattice is chain-complete by `ChainCompletePartialOrder.instOfCompleteLattice`.

### Exercises

1. (A) Count the maximal chains in the subsets of $\{1, \dots, n\}$ with $\subseteq$. *Hint:* a maximal chain adds one element at each step.
2. (A) Find the maximal ideals of $\mathbb{Z}$ that contain $30\mathbb{Z}$, and of $\mathbb{Z}/36\mathbb{Z}$.
3. (B) Use Zorn's lemma to show that each partial order contains a maximal chain. *Hint:* order the chains by inclusion, as in the proof of Zorn's lemma.
4. (B) Show that the fixed point in the theorem of Bourbaki and Witt need not be unique, and that $g$ need not be monotone. *Hint:* on $X = \{0, 1, 2\}$ with the usual order, take the map $0 \mapsto 2$, $1 \mapsto 1$, $2 \mapsto 2$.
5. (C) Use Zorn's lemma to show that each subgroup $H$ of $\mathbb{Q}$ with $1 \notin H$ is contained in a subgroup maximal with the property $1 \notin H$. Then show that $\mathbb{Q}$ has no maximal proper subgroup. *Hint:* for the second part, a maximal proper subgroup $M$ gives a simple quotient $\mathbb{Q}/M$, and a divisible simple abelian group does not exist.
6. (C) Show that each partial order $\le$ on a set $\alpha$ is contained in a linear order. *Hint:* apply Zorn's lemma to the partial orders that contain $\le$, ordered by inclusion of relations; for a maximal order with two incomparable elements $a$ and $b$, add all pairs $(x, y)$ with $x \le a$ and $b \le y$.

### Notes and history

Zermelo proved the well-ordering theorem from the axiom of choice in 1904. Hausdorff stated the maximality principle for chains in 1914, and Zorn stated the lemma in 1935 in a paper on algebra. The fixed point theorem is due to Bourbaki (1949) and to Witt (1951), and the proof above follows Lang, *Algebra*, Appendix 2, Section 2. Krull proved the existence of maximal ideals in 1929. Blass proved in 1984 that the existence of a basis of each vector space implies the axiom of choice. The existence of a maximal ideal of each nonzero ring is equivalent to the axiom of choice, by a theorem of Hodges (1979).

### Reference

<?reference?>
