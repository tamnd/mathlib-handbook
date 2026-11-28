---
title: Centralizers, generators and maximal subgroups of the symmetric and alternating groups
kind: api
modules:
  - Mathlib.GroupTheory.Perm.Centralizer
  - Mathlib.GroupTheory.Perm.DomMulAct
  - Mathlib.GroupTheory.Perm.Closure
  - Mathlib.GroupTheory.Perm.ClosureSwap
  - Mathlib.GroupTheory.Perm.MaximalSubgroups
  - Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer
  - Mathlib.GroupTheory.SpecificGroups.Alternating.KleinFour
  - Mathlib.GroupTheory.SpecificGroups.Alternating.MaximalSubgroups
  - Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
explains:
  E2: [Equiv.Perm.nat_card_centralizer, Equiv.Perm.card_isConj_eq, DomMulAct.stabilizer_card, Equiv.Perm.centralizer_le_alternating_iff, closure_of_isSwap_of_isPretransitive, Equiv.Perm.closure_prime_cycle_swap, Equiv.Perm.isCoatom_stabilizer, commutator_alternatingGroup_eq_top, alternatingGroup.normal_kleinFour, alternatingGroup.isSimpleGroup]
  E1: auto
families: []
requires: [V05.C03, V05.C05, V05.C06]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Centralizers, generators and maximal subgroups of the symmetric and alternating groups

### Overview

The theory of Section 2 gives the conjugacy classes of $S_n$ by the cycle type. These modules go further. They compute the order of the centralizer of a permutation and so the size of each conjugacy class, they decide when a class of $S_n$ splits in $A_n$, they give small sets of generators of $S_n$, they find a family of maximal subgroups, and they prove that $A_n$ is simple for $n \ge 5$. The Klein four-group in $A_4$ gets its own module, because it is the exception in the small cases.

The modules use the centralizer and the commutator subgroup from Chapters 3 and 5, and orbits, stabilizers, primitive actions and the Iwasawa criterion from Chapter 6. The statements are for a finite type $\alpha$ with $n = \lvert\alpha\rvert$, and `Equiv.Perm α` plays the part of $S_n$.

### The library around it

#### The centralizer of a permutation

Let $g$ have cycle type $m$, a multiset of lengths at least $2$. The theorem `Equiv.Perm.nat_card_centralizer` states
$$\lvert C(g) \rvert = (n - \textstyle\sum m)! \cdot \prod_{\ell \in m} \ell \cdot \prod_{k} c_k!,$$
where $c_k$ is the number of cycles of length $k$. Here $n - \sum m$ is the number of fixed points.

The proof in `Mathlib.GroupTheory.Perm.Centralizer` has two parts. First, an element $k$ of $C(g)$ conjugates each cycle factor of $g$ to a cycle factor of $g$. This gives an action of $C(g)$ on the set `Equiv.Perm.cycleFactorsFinset` $g$, and a homomorphism `Equiv.Perm.OnCycleFactors.toPermHom` to the permutations of the cycles. Its image is the group of permutations of the cycles that keep the lengths (`Equiv.Perm.OnCycleFactors.mem_range_toPermHom_iff`), of order $\prod_k c_k!$ (`Equiv.Perm.OnCycleFactors.nat_card_range_toPermHom`). To show that each such permutation lifts, the module chooses one point in each cycle: this is the structure `Equiv.Perm.Basis`, and `Equiv.Perm.Basis.toCentralizer` is the lift. Second, the kernel is the set of $k$ that keep each cycle. Such a $k$ is a permutation of the fixed points times a power of each cycle, by `Equiv.Perm.commute_iff_of_mem_cycleFactorsFinset` from Section 3. The map `Equiv.Perm.OnCycleFactors.kerParam` parametrizes the kernel, and its range has order $(n - \sum m)! \cdot \prod_{\ell} \ell$ (`Equiv.Perm.OnCycleFactors.kerParam_range_card`). The product of the two orders is the formula.

The orbit of $g$ under conjugation is its conjugacy class, and the stabilizer is $C(g)$. So the orbit-stabilizer theorem gives `Equiv.Perm.card_isConj_eq`:
$$\lvert \{h \mid h \sim g\} \rvert = \frac{n!}{(n - \sum m)! \cdot \prod_{\ell \in m} \ell \cdot \prod_k c_k!}.$$
The form without division is `Equiv.Perm.card_isConj_mul_eq`. The number of permutations with a given cycle type $m$ is `Equiv.Perm.card_of_cycleType`: the same quotient when $\sum m \le n$ and each entry is at least $2$, and $0$ otherwise. For example, $S_5$ has $5!/(2 \cdot 3) = 20$ elements of type $\{2, 3\}$ and $5!/(1! \cdot 2 \cdot 2 \cdot 2!) = 15$ elements of type $\{2, 2\}$.

#### Stabilizers of a function

A related count is in `Mathlib.GroupTheory.Perm.DomMulAct`. A permutation $g$ of $\alpha$ acts on functions $f : \alpha \to \iota$ by composition on the right, through `DomMulAct`. The stabilizer of $f$ is the set of $g$ with $f \circ g = f$, that is, the permutations that keep each fiber $f^{-1}(i)$. So it is the product of the symmetric groups of the fibers. This is the isomorphism `DomMulAct.stabilizerMulEquiv`, and the count is `DomMulAct.stabilizer_card`: the number of $g$ with $f \circ g = f$ is $\prod_i \lvert f^{-1}(i) \rvert!$. The version `DomMulAct.stabilizer_ncard` uses `Set.ncard` and only needs `Finite α`.

#### Centralizers in the alternating group

The conjugacy class of $g$ in $S_n$ is one class of $A_n$, or it splits into two classes of the same size. It splits exactly when $C(g) \le A_n$, because then $C_{A_n}(g) = C(g)$ has index $1$ in $C(g)$ instead of index $2$. The theorem `Equiv.Perm.centralizer_le_alternating_iff` decides this: $C(g) \le A_n$ if and only if the cycle lengths are odd, they are pairwise different, and $g$ has at most one fixed point. Proof of one direction: if $g$ has a cycle $c$ of even length, then $c$ commutes with $g$ and is odd. If two cycles have the same length $\ell$, a product of $\ell$ transpositions exchanges them and commutes with $g$; it is odd when $\ell$ is odd. If $g$ has two fixed points, their transposition commutes with $g$. The other direction uses `Equiv.Perm.OnCycleFactors.kerParam_range_eq_centralizer_of_count_le_one`: with distinct lengths, $C(g)$ is generated by the cycles of $g$ and the permutations of the fixed points.

The counts in $A_n$ are `AlternatingGroup.card_of_cycleType` and `AlternatingGroup.card_of_cycleType_mul_eq`, with the extra condition that $\sum m + \lvert m \rvert$ is even, that is, the sign is $1$. For example, the $24$ elements of type $\{5\}$ in $A_5$ form two classes of $12$, since $\{5\}$ has odd distinct lengths and no fixed point.

#### Commutators

The module `Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer` also computes commutator subgroups. The commutator subgroup of $S_n$ is in $A_n$ (`alternatingGroup.commutator_perm_le`), since $A_n$ is the kernel of the sign and the sign has a commutative target. For $n \ge 5$ it is equal (`alternatingGroup.commutator_perm_eq`), and `commutator_alternatingGroup_eq_top` says that $A_n$ is perfect. Proof: for $n \ge 5$, each $3$-cycle $\sigma$ is a commutator in $A_n$ (`Equiv.Perm.IsThreeCycle.mem_commutatorSet_alternatingGroup`). Indeed $\sigma^2$ is also a $3$-cycle, and for $n \ge 5$ all $3$-cycles are conjugate in $A_n$, because two points outside the support give a transposition that corrects the sign. So $k \sigma k^{-1} = \sigma^2$ for some $k \in A_n$, and then $[k, \sigma] = k \sigma k^{-1} \sigma^{-1} = \sigma^2 \sigma^{-1} = \sigma$. Since the $3$-cycles generate $A_n$ (`Equiv.Perm.closure_three_cycles_eq_alternating`), the commutator subgroup is all of $A_n$.

#### The Klein four-group in $A_4$

The subgroup `alternatingGroup.kleinFour` $\alpha$ of $A(\alpha)$ is defined for every finite $\alpha$, but its lemmas need $\lvert\alpha\rvert = 4$. Then it is the set of $1$ and the three double transpositions (`alternatingGroup.coe_kleinFour_of_card_eq_four`), it has order $4$ and exponent $2$, and it satisfies `IsKleinFour` (`alternatingGroup.kleinFour_isKleinFour`). It is normal (`alternatingGroup.normal_kleinFour`): conjugation keeps the cycle type, and the double transpositions are all the elements of type $\{2, 2\}$. It is characteristic, it is the commutator subgroup of $A_4$ (`alternatingGroup.kleinFour_eq_commutator`), and it is the only Sylow $2$-subgroup (`alternatingGroup.two_sylow_eq_kleinFour_of_card_eq_four`), since $\lvert A_4 \rvert = 12$ (`alternatingGroup.card_of_card_eq_four`) and a normal Sylow subgroup is unique. With these facts, `alternatingGroup.isSolvable` and `Equiv.Perm.isSolvable` say that $A_n$ and $S_n$ are solvable for $n \le 4$.

#### Generators of $S_n$

The module `Mathlib.GroupTheory.Perm.Closure` gives small generating sets. The cycles generate (`Equiv.Perm.closure_isCycle`). If $\sigma$ is an $n$-cycle, then $\sigma$ and the transposition $(x\ \sigma x)$ generate $S_n$ (`Equiv.Perm.closure_cycle_adjacent_swap`), and the same holds for $(x\ \sigma^k x)$ when $k$ is coprime to $n$ (`Equiv.Perm.closure_cycle_coprime_swap`). For $n = p$ prime, `Equiv.Perm.closure_prime_cycle_swap` says that a $p$-cycle and any transposition generate $S_p$. Proof: let the transposition be $(a\ b)$. Since $\sigma$ is a $p$-cycle, $b = \sigma^k(a)$ for some $0 < k < p$, and $k$ is coprime to $p$. The power $\sigma^k$ is again a $p$-cycle, and $(a\ \sigma^k a)$ is an adjacent transposition for it. So the previous result applies to $\sigma^k$. This lemma is the group theory behind the proof that a polynomial of prime degree $p$ with exactly two nonreal roots has Galois group $S_p$.

The module `Mathlib.GroupTheory.Perm.ClosureSwap` works with sets of transpositions on any type. The subgroup generated by all transpositions is the set of permutations with finite support (`mem_closure_isSwap'`). For a set $S$ of transpositions, `swap_mem_closure_isSwap` says that $(x\ y)$ is in the subgroup generated by $S$ if and only if $x$ is in the orbit of $y$ under that subgroup. The main consequence is `closure_of_isSwap_of_isPretransitive`: on a finite type, a set of transpositions that generates a transitive subgroup generates all of $S_n$. Proof: by transitivity each $x$ is in the orbit of each $y$, so each transposition $(x\ y)$ is in the subgroup, and the transpositions generate $S_n$ (`Equiv.Perm.closure_isSwap`). The lemma `surjective_of_isSwap_of_isPretransitive` is the same statement for a transitive action of a group $G$ that is generated by elements acting as transpositions.

#### Maximal subgroups

The module `Mathlib.GroupTheory.Perm.MaximalSubgroups` proves the intransitive case of the classification of the maximal subgroups. Let $s$ be a subset with $s$ and its complement nonempty. Its stabilizer is $S_s \times S_{s^c}$. The theorem `Equiv.Perm.isCoatom_stabilizer` says that it is a maximal subgroup when $n \neq 2\lvert s \rvert$. When $n = 2\lvert s\rvert$, a permutation that exchanges $s$ and $s^c$ gives a larger proper subgroup, so the hypothesis is needed. Proof sketch: let $G$ be a subgroup that strictly contains the stabilizer. Then $G$ contains a transposition (`Equiv.Perm.has_swap_mem_of_lt_stabilizer`), and $G$ is transitive (`MulAction.IsPretransitive.of_partition`), because the stabilizer is transitive on $s$ and on $s^c$ and an element of $G$ outside it moves a point of $s$ to $s^c$. The block lemmas, such as `MulAction.IsBlock.subsingleton_of_ssubset_of_stabilizer_Perm_le`, show that $G$ is primitive when $\lvert s \rvert \ne \lvert s^c \rvert$. A primitive group that contains a transposition is the whole symmetric group, by the Jordan theorems of Chapter 6.

The module `Mathlib.GroupTheory.SpecificGroups.Alternating.MaximalSubgroups` has the same results for $A_n$: `alternatingGroup.isCoatom_stabilizer`, and `alternatingGroup.isCoatom_stabilizer_singleton`, which says that the stabilizer of a point is maximal in $A_n$ for $n \ge 3$. It also has `Equiv.Perm.alternatingGroup_le_of_isPreprimitive`: for $n > 4$, a primitive subgroup that contains $A_n \cap \operatorname{Stab}(s)$ contains $A_n$.

#### The simplicity of $A_n$

The module `Mathlib.GroupTheory.SpecificGroups.Alternating.Simple` proves `alternatingGroup.isSimpleGroup`: $A_n$ is simple for $n \ge 5$. The proof uses the Iwasawa criterion of Chapter 6 with the action of $A_n$ on the $k$-element subsets. For $k = 3$, the subgroups $T(s)$ are the copies of $A_3$, cyclic of order $3$ (`alternatingGroup.iwasawaStructure_three`). For $k = 4$, they are the copies of the Klein four-group on $s$ (`alternatingGroup.iwasawaStructure_four`). In both cases $T(s)$ is commutative, the subgroups are conjugate as $s$ moves, and they generate $A_n$, because they contain the $3$-cycles or the double transpositions. The action on $k$-subsets is primitive when $n \neq 2k$, by the maximality of the stabilizers above. So for $n \ne 6$ the action on $3$-subsets works, and for $n = 6$ the action on $4$-subsets works. With the perfectness of $A_n$, the criterion gives `alternatingGroup.normal_subgroup_eq_bot_or_eq_top`. The same idea with `Equiv.Perm.iwasawaStructure_two`, on pairs, gives `Equiv.Perm.alternatingGroup_le_of_normal`: for $n \ge 5$, each nontrivial normal subgroup of $S_n$ contains $A_n$.

#### Common errors

1. The counting theorems use `Nat.card` and the cycle type, which does not list fixed points. The factor $(n - \sum m)!$ in `Equiv.Perm.nat_card_centralizer` is the factorial of the number of fixed points, and forgetting it gives a wrong count for the identity and for each $g$ with two or more fixed points.
2. `alternatingGroup.kleinFour` is a subgroup of `alternatingGroup α`, not of `Equiv.Perm α`. To use it in $S_4$, map it with the subtype homomorphism of `alternatingGroup α`.
3. `Equiv.Perm.isCoatom_stabilizer` is about the stabilizer of a set $s$ under the action on sets, `MulAction.stabilizer (Equiv.Perm α) s`, not about the pointwise stabilizer. The pointwise stabilizer of $s$ is the smaller group $S_{s^c}$, and it is not maximal when $\lvert s \rvert \ge 2$.

### Exercises

1. (A) Use `Equiv.Perm.card_isConj_eq` to list the sizes of the conjugacy classes of $S_5$, and check that they add up to $120$.
2. (A) Find the order of the centralizer of $(1\ 2)(3\ 4)$ in $S_6$ with `Equiv.Perm.nat_card_centralizer`, and describe the centralizer as a group.
3. (B) Use `Equiv.Perm.centralizer_le_alternating_iff` to find the cycle types of $S_7$ whose class splits in $A_7$.
4. (B) Show that $(1\ 2)$ and $(1\ 2\ 3\ 4)$ generate $S_4$, but $(1\ 3)$ and $(1\ 2\ 3\ 4)$ do not. Which hypothesis of `Equiv.Perm.closure_cycle_coprime_swap` fails in the second case?
5. (B) Show that the stabilizer of a $2$-element subset of $\{1, 2, 3, 4\}$ is not maximal in $S_4$, and find a proper subgroup that strictly contains it.
6. (C) Prove that $A_n$ has no subgroup of index $k$ with $1 < k < n$ for $n \ge 5$. Hint: let $A_n$ act on the cosets, and use the simplicity of $A_n$.

### Reference

<?reference?>
