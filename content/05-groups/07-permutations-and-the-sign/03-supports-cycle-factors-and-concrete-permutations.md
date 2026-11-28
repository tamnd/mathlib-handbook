---
title: Supports, cycle factors and concrete permutations
kind: api
modules:
  - Mathlib.GroupTheory.Perm.Support
  - Mathlib.GroupTheory.Perm.Cycle.Factors
  - Mathlib.GroupTheory.Perm.Cycle.Concrete
  - Mathlib.GroupTheory.Perm.List
  - Mathlib.GroupTheory.Perm.Finite
  - Mathlib.GroupTheory.Perm.Fin
  - Mathlib.GroupTheory.Perm.Option
  - Mathlib.GroupTheory.Perm.ViaEmbedding
explains:
  E2: [Equiv.Perm.Disjoint.card_support_mul, Equiv.Perm.support_swap_mul_eq, List.formPerm_cons_cons, List.formPerm_eq_formPerm_iff, Equiv.Perm.formPerm_toList, Equiv.Perm.mem_cycleFactorsFinset_iff, Equiv.Perm.Disjoint.orderOf, Fin.sign_cycleRange, Equiv.Perm.decomposeFin.symm_sign]
  E1: auto
families: []
requires: [V05.C03, V05.C04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Supports, cycle factors and concrete permutations

### Overview

Section 2 states the cycle decomposition and the theory of the cycle type. This section describes the library under that theory. The modules hold the support of a permutation and the calculus of disjoint permutations, the cycle through a point and the finite set of cycle factors, the cycle of a list and the list of a cycle, and some concrete permutations of `Fin n` and of `Option α`. A reader who proves a statement about a specific permutation, or who does an induction on the size of a finite type, uses these files more than the abstract theorems.

The modules need subgroups and closures from Chapter 3 and the order of an element from Chapter 4. All the permutations here are elements of `Equiv.Perm α`, with the product $(\sigma \tau)(x) = \sigma(\tau(x))$.

### The library around it

#### Supports and disjointness

For a finite type $\alpha$ with decidable equality, `Equiv.Perm.support` is the `Finset` of the points $x$ with $\sigma(x) \neq x$. The membership lemmas are `Equiv.Perm.mem_support` and `Equiv.Perm.notMem_support`, and `Equiv.Perm.coe_support_eq_set_support` identifies the coercion with the set $\{x \mid \sigma(x) \neq x\}$. For an infinite type the library uses this set directly, with lemmas such as `Equiv.Perm.set_support_mul_subset` and `Equiv.Perm.set_support_zpow_subset`.

The support is invariant under $\sigma$: `Equiv.Perm.apply_mem_support`, `Equiv.Perm.pow_apply_mem_support` and `Equiv.Perm.zpow_apply_mem_support` say that $\sigma^n(x)$ is in the support if and only if $x$ is. The basic bounds are these.

| Lean name | Statement |
| --- | --- |
| `Equiv.Perm.support_eq_empty_iff` | $\operatorname{supp} \sigma = \emptyset \iff \sigma = 1$ |
| `Equiv.Perm.card_support_ne_one` | $\lvert \operatorname{supp} \sigma \rvert \neq 1$ |
| `Equiv.Perm.two_le_card_support_of_ne_one` | $\sigma \neq 1 \Rightarrow 2 \le \lvert \operatorname{supp} \sigma \rvert$ |
| `Equiv.Perm.card_support_eq_two` | $\lvert \operatorname{supp} \sigma \rvert = 2 \iff \sigma$ is a transposition |
| `Equiv.Perm.support_mul_le` | $\operatorname{supp}(\sigma\tau) \subseteq \operatorname{supp}\sigma \cup \operatorname{supp}\tau$ |
| `Equiv.Perm.support_inv` | $\operatorname{supp}\sigma^{-1} = \operatorname{supp}\sigma$ |
| `Equiv.Perm.support_pow_le` | $\operatorname{supp}\sigma^n \subseteq \operatorname{supp}\sigma$ |
| `Equiv.Perm.support_conj` | $\operatorname{supp}(\sigma\tau\sigma^{-1}) = \sigma(\operatorname{supp}\tau)$ |
| `Equiv.Perm.support_swap` | $x \neq y \Rightarrow \operatorname{supp}(x\ y) = \{x, y\}$ |

The relation `Equiv.Perm.Disjoint` says that for each $x$, $\sigma(x) = x$ or $\tau(x) = x$ (`Equiv.Perm.disjoint_iff_eq_or_eq`). It does not need a finite type. For a finite type it is equivalent to the disjointness of the supports, by `Equiv.Perm.disjoint_iff_disjoint_support`. The relation is symmetric (`Equiv.Perm.Disjoint.symm`), it is stable under inverses and powers (`Equiv.Perm.Disjoint.inv_left`, `Equiv.Perm.Disjoint.zpow_disjoint_zpow`), under products (`Equiv.Perm.Disjoint.mul_left`, `Equiv.Perm.Disjoint.mul_right`, `Equiv.Perm.disjoint_prod_right`) and under conjugation (`Equiv.Perm.Disjoint.conj`).

For disjoint $\sigma$ and $\tau$ the support of the product is the union, `Equiv.Perm.Disjoint.support_mul`, so $\lvert\operatorname{supp}(\sigma\tau)\rvert = \lvert\operatorname{supp}\sigma\rvert + \lvert\operatorname{supp}\tau\rvert$ (`Equiv.Perm.Disjoint.card_support_mul`). Proof: a point of $\operatorname{supp}\sigma$ is fixed by $\tau$, so $\sigma\tau$ moves it, and the same holds for a point of $\operatorname{supp}\tau$. A point outside both supports is fixed by both. So the support of $\sigma\tau$ is the disjoint union of the two supports. For a list of pairwise disjoint permutations, `Equiv.Perm.support_prod_of_pairwise_disjoint` and `Equiv.Perm.card_support_prod_list_of_pairwise_disjoint` give the same results, and `Equiv.Perm.disjoint_prod_perm` says that the product does not depend on the order of the list.

The inductive proofs of the cycle decomposition and of the sign formula remove one point at a time with a transposition. The key lemma is `Equiv.Perm.support_swap_mul_eq`: if $\sigma(\sigma(x)) \neq x$, then $\operatorname{supp}((x\ \sigma x)\,\sigma) = \operatorname{supp}\sigma \setminus \{x\}$. Proof: $(x\ \sigma x)\sigma$ sends $x$ to $x$, sends $\sigma^{-1}(x)$ to $\sigma x$ because $\sigma^{-1}(x) \neq \sigma(x)$ by the hypothesis, and agrees with $\sigma$ at all other points. The weaker `Equiv.Perm.card_support_swap_mul` only says that the support gets smaller when $\sigma(x) \neq x$.

#### Permutations of a finite part

The module `Mathlib.GroupTheory.Perm.Finite` collects facts that need a finiteness hypothesis on a part of the type. If $s$ is a finite set and $\sigma$ maps $s$ into $s$, then $\sigma^{-1}$ also maps $s$ into $s$ (`Equiv.Perm.perm_symm_mapsTo_of_mapsTo`), since an injective map from a finite set to itself is onto. So $\sigma$ restricts to a permutation `Equiv.Perm.subtypePermOfFintype` of $s$. A permutation of $m \oplus n$ that maps the left summand into itself comes from a pair of permutations, by `Equiv.Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl`.

The same module has two results on the order and on conjugacy. For disjoint $\sigma$ and $\tau$, `Equiv.Perm.Disjoint.orderOf` gives $\operatorname{ord}(\sigma\tau) = \operatorname{lcm}(\operatorname{ord}\sigma, \operatorname{ord}\tau)$. Proof: $\sigma$ and $\tau$ commute, so $(\sigma\tau)^n = \sigma^n\tau^n$, and $\sigma^n$ and $\tau^n$ are disjoint. By `Equiv.Perm.Disjoint.mul_eq_one_iff`, $\sigma^n\tau^n = 1$ if and only if $\sigma^n = 1$ and $\tau^n = 1$, that is, if and only if both orders divide $n$. The lemma `Equiv.Perm.Disjoint.isConj_mul` says that a product of disjoint permutations is conjugate to the product of disjoint conjugates of the factors. The lemma `Equiv.Perm.isConj_of_support_equiv` builds a conjugacy from a bijection of the supports that commutes with the two permutations. Last, `Equiv.Perm.support_pow_coprime` says that $\sigma^n$ has the same support as $\sigma$ when $n$ is coprime to the order of $\sigma$.

#### The cycle through a point and the cycle factors

For a permutation $f$ and a point $x$, `Equiv.Perm.cycleOf` is the permutation that acts as $f$ on the points in the cycle of $x$ and fixes all other points: `Equiv.Perm.cycleOf_apply` states $(f.\mathrm{cycleOf}\ x)(y) = f(y)$ if $y$ is in the same cycle as $x$ (`Equiv.Perm.SameCycle`), and $y$ otherwise. It is a cycle exactly when $f(x) \neq x$ (`Equiv.Perm.isCycle_cycleOf_iff`). The lemma `Equiv.Perm.SameCycle.exists_pow_eq` bounds the exponent: if $y$ is in the cycle of $x$, then $y = f^i(x)$ with $0 < i \le \lvert\operatorname{supp}(f.\mathrm{cycleOf}\ x)\rvert + 1$. The lemma `Equiv.Perm.pow_mod_card_support_cycleOf_self_apply` reduces the exponent modulo the length of the cycle.

The cycle factors come in three forms. `Equiv.Perm.cycleFactors` is a list of disjoint cycles with product $f$; it needs a `LinearOrder` on $\alpha$ to choose an order. `Equiv.Perm.truncCycleFactors` gives the same list inside `Trunc`, so it only needs `DecidableEq`. `Equiv.Perm.cycleFactorsFinset` is the `Finset` of the cycles, with no choice at all, and it is the form for theorems. Its characterization is `Equiv.Perm.mem_cycleFactorsFinset_iff`: $p$ is a cycle factor of $f$ if and only if $p$ is a cycle and $p(a) = f(a)$ for each $a$ in the support of $p$. Proof sketch: a cycle factor $f.\mathrm{cycleOf}\ x$ has these properties by `Equiv.Perm.cycleOf_apply`. Conversely, a cycle $p$ that agrees with $f$ on its support has as support one cycle of $f$, so it is $f.\mathrm{cycleOf}\ x$ for any $x$ in its support.

Other lemmas of the family: `Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff` ($f.\mathrm{cycleOf}\ x$ is a factor if and only if $x$ is in the support), `Equiv.Perm.cycleFactorsFinset_eq_empty_iff` (the set is empty if and only if $f = 1$), `Equiv.Perm.Disjoint.cycleFactorsFinset_mul_eq_union` (the factors of a product of disjoint permutations), `Equiv.Perm.cycleFactorsFinset_injective` (a permutation is determined by its factors) and `Equiv.Perm.list_cycles_perm_list_cycles` (two lists of disjoint cycles with the same product are permutations of each other). The induction principle `Equiv.Perm.cycle_induction_on` proves a property for all permutations of a finite type from the identity, the cycles, and products of a cycle with a disjoint permutation. The lemma `Equiv.Perm.commute_iff_of_mem_cycleFactorsFinset` says that $k$ commutes with a factor $c$ of $g$ if and only if $k$ preserves the support of $c$ and acts on it as a power of $c$.

#### The cycle of a list

The module `Mathlib.GroupTheory.Perm.List` defines `List.formPerm`. For a list $[x_1, \dots, x_n]$ it sends $x_i$ to $x_{i+1}$ and $x_n$ to $x_1$ when the entries are distinct. The definition is a product of transpositions, by `List.formPerm_cons_cons`: $\mathrm{formPerm}(x :: y :: l) = (x\ y) \cdot \mathrm{formPerm}(y :: l)$. Unfold the recursion once for $[a, b, c]$: $(a\ b)(b\ c)$ sends $a \mapsto b$, $b \mapsto c$ and $c \mapsto a$, which is the $3$-cycle $(a\ b\ c)$. For a list with no duplicates, `List.formPerm_apply_mem_eq_next` says that the permutation sends each entry to the next entry, in the sense of `List.next`, `List.support_formPerm_of_nodup` gives the support, and `List.formPerm_pow_length_eq_one_of_nodup` says that the $n$-th power is $1$.

The permutation does not change under a rotation of the list (`List.formPerm_rotate`), and reversal gives the inverse (`List.formPerm_reverse`). For lists with no duplicates, `List.formPerm_eq_formPerm_iff` says that two lists give the same permutation if and only if one is a rotation of the other or both have length at most $1$. So the cycle depends only on the class of the list under rotation, and `Mathlib.GroupTheory.Perm.Cycle.Concrete` uses this to define `Cycle.formPerm` on the type `Cycle α` of lists up to rotation. For a list of length at least $2$ with no duplicates the result is a cycle, by `List.isCycle_formPerm` and `Cycle.isCycle_formPerm`.

#### From a cycle to a list

The other direction is `Equiv.Perm.toList`: for $p$ and $x$, it is the list $[x, p(x), p^2(x), \dots]$ of the points of the cycle of $x$, and it is empty if $p(x) = x$ (`Equiv.Perm.toList_eq_nil_iff`). Its length is the size of the support of $p.\mathrm{cycleOf}\ x$ (`Equiv.Perm.length_toList`), and its cycle is the cycle of $x$: `Equiv.Perm.formPerm_toList` states $\mathrm{formPerm}(p.\mathrm{toList}\ x) = p.\mathrm{cycleOf}\ x$. Proof: the entries of the list are distinct, and `List.formPerm_apply_mem_eq_next` shows that the cycle of the list sends $p^i(x)$ to $p^{i+1}(x)$, as $p$ does. Both permutations fix all other points.

A cycle $f$ gives an element `Equiv.Perm.toCycle` of `Cycle α`, and `Equiv.Perm.isoCycle` is the bijection between the cycles of $\alpha$ and the nontrivial cycles of `Cycle α` with no duplicates. The uniqueness statement is `Equiv.Perm.IsCycle.existsUnique_cycle`. The module also defines the notation `c[1, 2, 3]` for the cycle of a list and a `Repr` instance, so `#eval` prints a permutation of a finite type as a product of cycles.

#### Concrete permutations of `Fin n` and of `Option α`

The module `Mathlib.GroupTheory.Perm.Option` splits a permutation of `Option α` into the image of `none` and a permutation of $\alpha$. The equivalence is `Equiv.Perm.decomposeOption`, and `Equiv.Perm.decomposeOption_symm_apply` gives its inverse: $(a, e) \mapsto (\mathrm{none}\ a) \cdot \mathrm{optionCongr}(e)$. The extension `Equiv.optionCongr` keeps the sign (`Equiv.optionCongr_sign`). The lemma `Finset.univ_perm_option` writes the set of all permutations of `Option α` as the image of this map, and it is the induction step of the formula $\lvert S_n \rvert = n!$.

The module `Mathlib.GroupTheory.Perm.Fin` does the same for `Fin (n + 1)`. The equivalence is `Equiv.Perm.decomposeFin`, from `Equiv.Perm (Fin (n + 1))` to `Fin (n + 1) × Equiv.Perm (Fin n)`. By `Equiv.Perm.decomposeFin.symm_sign`, the permutation built from $(p, e)$ has sign $\operatorname{sign} e$ if $p = 0$ and $-\operatorname{sign} e$ otherwise, because it is $e$ followed by the transposition $(0\ p)$. The rotation `finRotate` is a cycle of length $n$ for $n \ge 2$ (`isCycle_finRotate`, `cycleType_finRotate`), with sign $(-1)^{n-1}$ (`sign_finRotate`).

The cycle `Fin.cycleRange` $i$ is the cycle $(0\ 1\ \cdots\ i)$: it sends $j \mapsto j + 1$ for $j < i$, sends $i \mapsto 0$, and fixes the points above $i$ (`Fin.cycleRange_of_le`, `Fin.cycleRange_of_gt`). Its sign is $(-1)^i$ (`Fin.sign_cycleRange`), since it is a cycle of length $i + 1$ for $i \neq 0$ (`Fin.cycleType_cycleRange`) and a cycle of length $k$ has sign $(-1)^{k-1}$. In particular `Fin.isThreeCycle_cycleRange_two` gives a $3$-cycle in each `Fin n`. The more general `Fin.cycleIcc` $i$ $j$ is the cycle on the interval $[i, j]$, with cycle type $\{j - i + 1\}$ for $i < j$ (`Fin.cycleType_cycleIcc_of_lt`). The sign of a permutation of `Fin n` also has a formula as a product over pairs, `Equiv.Perm.sign_eq_prod_prod_Iio`.

Last, `Mathlib.GroupTheory.Perm.ViaEmbedding` extends a permutation of $\alpha$ along an embedding $\iota : \alpha \hookrightarrow \beta$ by the identity outside the range. This is `Equiv.Perm.viaEmbedding`, with `Equiv.Perm.viaEmbedding_apply` and `Equiv.Perm.viaEmbedding_apply_of_notMem`. The map is an injective group homomorphism `Equiv.Perm.viaEmbeddingHom` (`Equiv.Perm.viaEmbeddingHom_injective`), so $S_n$ is a subgroup of $S_m$ for $n \le m$.

#### Common errors

1. `Equiv.Perm.support` needs `Fintype α` and `DecidableEq α`, while `Equiv.Perm.Disjoint` does not. A lemma about `Equiv.Perm.Disjoint` on an infinite type is stated with `Equiv.Perm.disjoint_iff_eq_or_eq`, not with supports.
2. `List.formPerm` is defined for every list, but most of its lemmas need `List.Nodup`. For the list $[a, b, a]$ the permutation is $(a\ b)(b\ a) = 1$, not a cycle of length $3$.
3. The product of `Equiv.Perm` applies the right factor first. So `Fin.cycleRange` $i$ times a transposition is not the same as the transposition times `Fin.cycleRange` $i$, and `List.formPerm_cons_cons` puts the transposition on the left.

### Exercises

1. (A) Compute `List.formPerm` of the list $[1, 2, 3, 4]$ in `Fin 5` with `List.formPerm_cons_cons`, and check that it is the $4$-cycle $(1\ 2\ 3\ 4)$.
2. (A) Use `Equiv.Perm.Disjoint.orderOf` to find the order of $(1\ 2)(3\ 4\ 5)(6\ 7\ 8\ 9)$ in $S_9$.
3. (B) Show that if $\sigma \neq 1$, then $\sigma$ has at most $\lvert\alpha\rvert - 2$ fixed points, and deduce `Equiv.Perm.two_le_card_support_of_ne_one` from `Equiv.Perm.card_support_ne_one`.
4. (B) Prove that the sign of $\mathrm{formPerm}(l)$ is $(-1)^{n-1}$ for a list $l$ of length $n \ge 1$ with no duplicates, by induction with `List.formPerm_cons_cons`.
5. (B) Show that two permutations of $\alpha$ that commute and have disjoint supports generate a subgroup isomorphic to $\langle\sigma\rangle \times \langle\tau\rangle$.
6. (C) Use `Equiv.Perm.decomposeFin` to prove that the number of permutations of `Fin n` with sign $1$ is $n!/2$ for $n \ge 2$, by induction on $n$.

### Reference

<?reference?>
