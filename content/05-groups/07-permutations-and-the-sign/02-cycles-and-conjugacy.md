---
title: Cycles, cycle types and conjugacy in the symmetric group
kind: theory
modules:
  - Mathlib.GroupTheory.Perm.Cycle.Basic
  - Mathlib.GroupTheory.Perm.Cycle.Type
explains:
  E3: [Equiv.Perm.isConj_iff_cycleType_eq]
  E2: [Equiv.Perm.IsCycle, Equiv.Perm.support, Equiv.Perm.Disjoint, Equiv.Perm.Disjoint.commute, Equiv.Perm.cycleType, Equiv.Perm.cycleFactorsFinset, Equiv.Perm.lcm_cycleType, Equiv.Perm.IsCycle.sign, Equiv.Perm.cycleType_conj, Equiv.Perm.closure_three_cycles_eq_alternating]
  E1: auto
families: []
requires: [V05.C06]
reads_with: ["MIL"]
lean:
  - MathlibHandbook/V05/C07/Examples.lean
  - MathlibHandbook/V05/C07/Exercises.lean
  - MathlibHandbook/V05/C07/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Cycles, cycle types and conjugacy in the symmetric group

### Overview

Transpositions generate $S_n$, but a product of transpositions hides the structure of a permutation. The cycle decomposition shows it. Each permutation is a product of disjoint cycles, in one way up to the order of the factors. The lengths of the cycles form the cycle type. The cycle type gives the order, the lcm of the lengths, and the sign. It also solves the conjugacy problem in $S_n$: two permutations are conjugate if and only if they have the same cycle type.

The section computes the conjugacy classes of $S_4$, and it proves that the $3$-cycles generate $A_n$. That fact is the first step in the proof that $A_n$ is simple for $n \ge 5$.

### Definitions

**Definition (Support and disjointness).** The support of $\sigma \in \operatorname{Sym}(X)$ is the set of the points that $\sigma$ moves. Two permutations are disjoint if their supports are disjoint.

::: mathlib
`Equiv.Perm.support` · `Mathlib.GroupTheory.Perm.Support`

The support as a `Finset α`, for a finite type with decidable equality. The lemma `Equiv.Perm.mem_support` says `x ∈ σ.support ↔ σ x ≠ x`.

<?decl Equiv.Perm.support?>
:::

::: mathlib
`Equiv.Perm.Disjoint` · `Mathlib.GroupTheory.Perm.Support`

The relation `σ.Disjoint τ`: for each `x`, `σ x = x` or `τ x = x`. It needs no finiteness.

<?decl Equiv.Perm.Disjoint?>
:::

**Definition (Cycle).** Let $k \ge 2$ and let $a_1, \ldots, a_k$ be distinct points. The $k$-cycle $(a_1\,a_2\,\cdots\,a_k)$ sends $a_i \mapsto a_{i+1}$ for $i < k$ and $a_k \mapsto a_1$, and fixes the other points. A $2$-cycle is a transposition.

::: mathlib
`Equiv.Perm.IsCycle` · `Mathlib.GroupTheory.Perm.Cycle.Basic`

The predicate `σ.IsCycle`: there is a point `x` with `σ x ≠ x`, and each point that `σ` moves is `(σ ^ k) x` for some `k : ℤ`. So the support is one orbit of the group `⟨σ⟩`. A `k`-cycle has `σ.support.card = k`, and its order is `k` by `Equiv.Perm.IsCycle.orderOf`.

<?decl Equiv.Perm.IsCycle?>
:::

**Definition (Cycle type).** The cycle type of $\sigma$ is the multiset of the lengths of the cycles in its decomposition, by the theorem below. Points fixed by $\sigma$ are not listed.

::: mathlib
`Equiv.Perm.cycleType` · `Mathlib.GroupTheory.Perm.Cycle.Type`

The cycle type as a `Multiset ℕ`. Each entry is at least `2`. The sum of the entries is the size of the support, by `Equiv.Perm.sum_cycleType`.

<?decl Equiv.Perm.cycleType?>
:::

### Theorems and proofs

**Theorem (Disjoint permutations commute).** If $\sigma$ and $\tau$ are disjoint, then $\sigma \tau = \tau \sigma$.

*Proof.* Let $x \in X$. If $\sigma$ and $\tau$ both fix $x$, both products fix $x$. Let $\sigma(x) \ne x$, so $\tau(x) = x$. The point $\sigma(x)$ is moved by $\sigma$: if $\sigma(\sigma(x)) = \sigma(x)$, then $\sigma(x) = x$ by injectivity. So $\tau$ fixes $\sigma(x)$. Then $\sigma \tau (x) = \sigma(x)$ and $\tau \sigma(x) = \sigma(x)$. The case $\tau(x) \ne x$ is the same with the roles exchanged. $\square$

::: mathlib
`Equiv.Perm.Disjoint.commute` · `Mathlib.GroupTheory.Perm.Support`

The theorem `σ.Disjoint τ → Commute σ τ`.

<?decl Equiv.Perm.Disjoint.commute?>
:::

**Theorem (Cycle decomposition).** Let $X$ be finite and $\sigma \in \operatorname{Sym}(X)$. Then $\sigma$ is a product of pairwise disjoint cycles. The set of these cycles is unique.

*Proof.* Existence. The cyclic group $\langle \sigma \rangle$ acts on $X$, and its orbits partition $X$. Let $O$ be an orbit with more than one point and $x \in O$. Then $O = \{\sigma^i(x) : i \in \mathbb{Z}\}$. Let $k$ be the least $k \ge 1$ with $\sigma^k(x) = x$; it exists since $X$ is finite. The points $x, \sigma(x), \ldots, \sigma^{k - 1}(x)$ are distinct, by the minimal choice of $k$, and $O$ is the set of them, by division of $i$ by $k$. Let $c_O$ be the $k$-cycle $(x\,\sigma(x)\,\cdots\,\sigma^{k - 1}(x))$. It agrees with $\sigma$ on $O$ and fixes the points outside $O$. The cycles $c_O$ for different orbits are disjoint. Their product agrees with $\sigma$ at each point: at a point of $O$ only $c_O$ moves it, and at a fixed point of $\sigma$ no $c_O$ moves it. So $\sigma = \prod_O c_O$.

Uniqueness. Let $\sigma = c_1 \cdots c_m$ with disjoint cycles $c_j$. On the support of $c_j$ the other factors act as the identity, so $\sigma$ agrees with $c_j$ there. The support of $c_j$ is closed under $\sigma$ and is one orbit of $\langle c_j \rangle$, so it is an orbit $O$ of $\langle \sigma \rangle$, and $c_j = c_O$. Each orbit with more than one point is the support of some $c_j$, since $\sigma$ moves its points. So $\{c_1, \ldots, c_m\}$ is the set of the $c_O$. $\square$

::: mathlib
`Equiv.Perm.cycleFactorsFinset` · `Mathlib.GroupTheory.Perm.Cycle.Factors`

The set of the cycles of the decomposition, as a `Finset (Perm α)`. The cycles commute pairwise, so their product does not depend on an order, and `Equiv.Perm.cycleFactorsFinset_noncommProd` says it is `σ`. The cycle through one point is `Equiv.Perm.cycleOf`. For proofs by induction, `Equiv.Perm.cycle_induction_on` splits a permutation into a cycle and a disjoint rest.

<?decl Equiv.Perm.cycleFactorsFinset?>
:::

**Theorem (Order and sign from the cycle type).** Let $\sigma$ have cycle type $(k_1, \ldots, k_m)$. Then $\operatorname{ord}(\sigma) = \operatorname{lcm}(k_1, \ldots, k_m)$ and $\operatorname{sgn}(\sigma) = \prod_j (-1)^{k_j - 1}$.

*Proof.* Write $\sigma = c_1 \cdots c_m$ with disjoint cycles. They commute, so $\sigma^n = c_1^n \cdots c_m^n$. The factors $c_j^n$ have disjoint supports, so $\sigma^n = 1$ if and only if $c_j^n = 1$ for each $j$. A $k$-cycle has order $k$: its $i$th power sends $a_1$ to $a_{1 + i}$ for $i < k$. So $\sigma^n = 1$ if and only if $k_j \mid n$ for each $j$, and the least such $n \ge 1$ is the lcm. For the sign, a $k$-cycle is a product of $k - 1$ transpositions,
$$(a_1\,a_2\,\cdots\,a_k) = (a_1\,a_k)(a_1\,a_{k-1}) \cdots (a_1\,a_2),$$
as one checks at each $a_i$: the factors from the right move $a_i$ to $a_1$ at the step $(a_1\,a_i)$ and then $a_1$ to $a_{i+1}$ at the next step. The sign is a homomorphism, so the claim follows. $\square$

::: mathlib
`Equiv.Perm.lcm_cycleType` · `Mathlib.GroupTheory.Perm.Cycle.Type`

The equation `σ.cycleType.lcm = orderOf σ`. The sign has `Equiv.Perm.sign_of_cycleType`.

<?decl Equiv.Perm.lcm_cycleType?>
:::

::: mathlib
`Equiv.Perm.IsCycle.sign` · `Mathlib.GroupTheory.Perm.Cycle.Basic`

The sign of a cycle: `sign σ = -(-1) ^ σ.support.card`. For a $k$-cycle the right side is $(-1)^{k + 1} = (-1)^{k - 1}$.

<?decl Equiv.Perm.IsCycle.sign?>
:::

**Theorem (Conjugation of a cycle).** For $\tau \in \operatorname{Sym}(X)$,
$$\tau (a_1\,a_2\,\cdots\,a_k) \tau^{-1} = (\tau(a_1)\,\tau(a_2)\,\cdots\,\tau(a_k)).$$

*Proof.* Let $c$ be the cycle on the left side. The left side sends $\tau(a_i)$ to $\tau(c(a_i)) = \tau(a_{i+1})$, with indices modulo $k$. A point $y$ not of the form $\tau(a_i)$ has $\tau^{-1}(y) \notin \{a_1, \ldots, a_k\}$, so it is fixed by $c$, and the left side fixes $y$. The right side does the same. $\square$

::: mathlib
`Equiv.Perm.cycleType_conj` · `Mathlib.GroupTheory.Perm.Cycle.Type`

The consequence `(τ * σ * τ⁻¹).cycleType = σ.cycleType`.

<?decl Equiv.Perm.cycleType_conj?>
:::

**Theorem (Conjugacy in $S_n$).** Two permutations of a finite set are conjugate if and only if they have the same cycle type.

*Proof.* If $\sigma = c_1 \cdots c_m$, then $\tau \sigma \tau^{-1} = (\tau c_1 \tau^{-1}) \cdots (\tau c_m \tau^{-1})$, and the factors are disjoint cycles of the same lengths, by the last theorem. So conjugates have the same cycle type. Conversely, let $\sigma$ and $\sigma'$ have the same cycle type. Write their cycles as $(a_1\,\cdots\,a_k)$, one below the other: each cycle of $\sigma$ above a cycle of $\sigma'$ of the same length. The fixed points of $\sigma$ and of $\sigma'$ are equal in number, since both are $|X|$ minus the sum of the lengths. Put them in the two lines too. Let $\tau$ send each point of the upper line to the point below it. This is a bijection of $X$, since each line lists each point once. By the last theorem, $\tau \sigma \tau^{-1}$ has the cycles of $\sigma'$, so it is $\sigma'$. $\square$

::: mathlib
`Equiv.Perm.isConj_iff_cycleType_eq` · `Mathlib.GroupTheory.Perm.Cycle.Type`

The theorem `IsConj σ τ ↔ σ.cycleType = τ.cycleType`. For two cycles of the same length there is the special case `Equiv.Perm.IsCycle.isConj`.

<?decl Equiv.Perm.isConj_iff_cycleType_eq?>
:::

**Theorem ($3$-cycles generate $A_n$).** For $n \ge 3$, $A_n$ is generated by the $3$-cycles.

*Proof.* A $3$-cycle is even, being a product of two transpositions, so the $3$-cycles generate a subgroup of $A_n$. Conversely, an even permutation is a product of an even number of transpositions, so it is a product of pairs $(a\,b)(c\,d)$. Each pair is a product of $3$-cycles. If $\{a, b\} = \{c, d\}$, the pair is $e$. If the pairs share one point, write them $(a\,b)(a\,c)$; this sends $a \mapsto c$, $c \mapsto b$, $b \mapsto a$, so it is $(a\,c\,b)$. If $a, b, c, d$ are distinct, then $(a\,b)(c\,d) = (a\,b)(b\,c) \cdot (b\,c)(c\,d)$, a product of two pairs of the second kind. $\square$

::: mathlib
`Equiv.Perm.closure_three_cycles_eq_alternating` · `Mathlib.GroupTheory.SpecificGroups.Alternating`

The theorem as `closure {σ | σ.IsThreeCycle} = alternatingGroup α`.

<?decl Equiv.Perm.closure_three_cycles_eq_alternating?>
:::

### Examples

**Example (A decomposition).** Let $\sigma \in S_8$ be $3\,8\,5\,7\,1\,6\,4\,2$ in one-line form, so $\sigma(1) = 3$, $\sigma(2) = 8$, and so on. Follow $1$: $1 \mapsto 3 \mapsto 5 \mapsto 1$. Follow $2$: $2 \mapsto 8 \mapsto 2$. Follow $4$: $4 \mapsto 7 \mapsto 4$. The point $6$ is fixed. So $\sigma = (1\,3\,5)(2\,8)(4\,7)$, with cycle type $(3, 2, 2)$. Its order is $\operatorname{lcm}(3, 2, 2) = 6$ and its sign is $(+1)(-1)(-1) = 1$.

**Example (Conjugacy classes of $S_4$).** The cycle types in $S_4$ and the sizes of the classes are: the identity, $1$; transpositions $(a\,b)$, $\binom{4}{2} = 6$; products $(a\,b)(c\,d)$, $3$; $3$-cycles, $4 \cdot 2 = 8$; $4$-cycles, $3! = 6$. The class equation is $24 = 1 + 6 + 3 + 8 + 6$, and the center is trivial. The even classes are $1 + 3 + 8 = 12 = |A_4|$. By orbit-stabilizer, the centralizer of a $4$-cycle has $24/6 = 4$ elements, so it is the cyclic group that the cycle generates.

**Counterexample (Conjugate in $S_4$, not in $A_4$).** The $3$-cycles $(1\,2\,3)$ and $(1\,3\,2)$ are conjugate in $S_4$, by the theorem. They are not conjugate in $A_4$. The centralizer of $c = (1\,2\,3)$ in $S_4$ has $24/8 = 3$ elements, so it is $\langle c \rangle \le A_4$. So the centralizer in $A_4$ has $3$ elements too, and the class of $c$ in $A_4$ has $12/3 = 4$ elements, not $8$. The eight $3$-cycles split into two classes of $A_4$, of $4$ elements each. So the theorem on conjugacy is special to the symmetric group.

**Example (Orders in $S_5$).** The cycle types of $S_5$ are the partitions of $5$ with parts at least $2$, plus fixed points. The possible orders are $1, 2, 3, 4, 5$ and $6 = \operatorname{lcm}(2, 3)$, from $(1\,2)(3\,4\,5)$. No element of $S_5$ has order $10$ or $15$, although these divide $120$.

### The library around it

The theory of cycles is spread over `Mathlib.GroupTheory.Perm.Cycle.Basic`, `.Factors`, `.Type` and `.Concrete`. The last one gives the notation `c[1, 2, 3]` for a cycle, and `decide` computes with it. The predicate `Equiv.Perm.IsThreeCycle` is the cycle type `{3}`. The theorem of Cauchy, `exists_prime_orderOf_dvd_card`, is in the same file as the cycle type, because its proof uses a permutation of tuples. The lemma `alternatingGroup.isConj_of` gives conditions for conjugacy in the alternating group.

Common errors of a learner:

- The cycle type does not list the fixed points. The identity has the empty cycle type, and `(1 2)` in `Perm (Fin 4)` has type `{2}`, not `{2, 1, 1}`.
- A cycle in Mathlib is a permutation, not a list of points. The list form is the type `Cycle α`, a different object.
- `Equiv.Perm.support` needs `Fintype α`. For an infinite type, use the set `{x | σ x ≠ x}`, or `Function.support`-style statements.

### Exercises

1. (A) Decompose $\sigma = 4\,6\,1\,3\,2\,5$ in $S_6$ into disjoint cycles and find its order and sign.
2. (A) Find a $\tau$ with $\tau (1\,2\,3)(4\,5) \tau^{-1} = (2\,5\,4)(1\,3)$.
3. (B) Count the elements of each cycle type in $S_5$ and write the class equation.
4. (B) Show that $S_n$ is generated by $(1\,2)$ and $(1\,2\,\cdots\,n)$. Hint: conjugate $(1\,2)$ by powers of the $n$-cycle to get the adjacent transpositions.
5. (B) Show that $V = \{e, (1\,2)(3\,4), (1\,3)(2\,4), (1\,4)(2\,3)\}$ is a union of conjugacy classes of $S_4$, and deduce again that it is normal.
6. (C) Show that for $n \ge 5$ all the $3$-cycles are conjugate in $A_n$. Hint: if $\tau$ is odd, multiply it by a transposition disjoint from the cycle.

### Notes and history

Cauchy introduced the notation of cycles in 1815 and proved the cycle decomposition, in his long memoir on the number of values of a function. He also computed the number of permutations of each cycle type. The result on conjugacy is implicit in his work and explicit in Jordan's Traité of 1870. That the $3$-cycles generate $A_n$ was known to Cauchy and to Jordan, and it is the starting point of the proofs of the simplicity of $A_n$ for $n \ge 5$, due to Jordan in his Traité.

In Mathlib the cycle type is a multiset, so the order of the cycles is not part of the data, and theorems like `Equiv.Perm.isConj_iff_cycleType_eq` are equations of multisets.

### Reference

<?reference?>
