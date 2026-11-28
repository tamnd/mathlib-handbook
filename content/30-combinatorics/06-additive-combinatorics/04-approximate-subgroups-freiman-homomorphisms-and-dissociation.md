---
title: Approximate subgroups, Freiman homomorphisms and dissociation
kind: api
modules:
  - Mathlib.Combinatorics.Additive.ApproximateSubgroup
  - Mathlib.Combinatorics.Additive.Convolution
  - Mathlib.Combinatorics.Additive.CovBySMul
  - Mathlib.Combinatorics.Additive.Dissociation
  - Mathlib.Combinatorics.Additive.FreimanHom
  - Mathlib.Combinatorics.Additive.Randomisation
  - Mathlib.Combinatorics.Additive.SmallTripling
  - Mathlib.Combinatorics.Additive.SubsetSum
  - Mathlib.Combinatorics.Additive.VerySmallDoubling
  - Mathlib.Combinatorics.Schnirelmann
  - Mathlib.Combinatorics.Nullstellensatz
explains:
  E2: [IsApproximateSubgroup, IsApproximateSubgroup.card_pow_le, IsApproximateSubgroup.of_small_tripling, CovBySMul.trans, Finset.exists_subset_mulSpan_card_le_of_forall_mulDissociated, IsMulFreimanHom.mono, Finset.card_succ_choose_two_lt_card_subsetSum_of_pos, Finset.doubling_lt_three_halves, add_eq_univ_of_one_le_schirelmannDensity_add_schnirelmannDensity, MvPolynomial.combinatorial_nullstellensatz_exists_eval_ne_zero]
  E1: auto
families: []
requires: [V03.C03, V03.C06, V05.C04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Approximate subgroups, Freiman homomorphisms and dissociation

### Overview

Section 2 studied finite sets $A$ with small doubling, $|A + A| \le K|A|$, in abelian groups. This section collects the other tools of additive combinatorics in Mathlib. Most of them work in arbitrary groups, where the doubling alone controls less, and the tripling $|A^3| \le K|A|$ takes its place.

An approximate subgroup is a set that is closed under products up to a bounded number of translates. A $K$-approximate subgroup $A$ of a group $G$ contains $1$, is symmetric ($A^{-1} = A$), and $A^2$ is covered by at most $K$ left translates $x A$. A $1$-approximate subgroup is the same as a subgroup. Approximate subgroups have small powers, and a symmetric set with small tripling becomes one after squaring.

A Freiman homomorphism of order $n$ is a map that keeps the equalities between products of $n$ elements. A dissociated set is a set whose subset products are all different, like the powers $1, 2, 4, \dots$ of $2$ in the integers. The section also covers the subset sums of a set of positive elements, the sets of very small doubling, the Schnirelmann density of a set of natural numbers, and the Combinatorial Nullstellensatz for polynomials that vanish on a grid.

Most modules state the multiplicative form, and the attribute `to_additive` makes the additive form. So `IsMulFreimanHom` has the twin `IsAddFreimanHom`, and `MulDissociated` has the twin `AddDissociated`.

### The library around it

#### Coverings by translates

The module `Mathlib.Combinatorics.Additive.CovBySMul` has one definition. For a monoid $M$ that acts on $X$, `CovBySMul M K A B` states that there is a finset `F : Finset M` with at most $K$ elements and `A ⊆ F • B`. So $A$ is covered by at most $K$ translates of $B$. Coverings compose: `CovBySMul.trans` gives `CovBySMul N (K * L) A C` from a covering of $A$ by $K$ translates of $B$ and a covering of $B$ by $L$ translates of $C$. The lemma `CovBySMul.mono` makes $K$ larger.

#### Approximate subgroups

The module `Mathlib.Combinatorics.Additive.ApproximateSubgroup` defines `IsApproximateSubgroup K A` for a set `A : Set G` as a structure with three fields: `one_mem`, `inv_eq_self` and `sq_covBySMul : CovBySMul G K (A ^ 2) A`. The constant is at least $1$ (`IsApproximateSubgroup.one_le`), and the set is not empty (`IsApproximateSubgroup.nonempty`). A subgroup is a $1$-approximate subgroup (`IsApproximateSubgroup.subgroup`), and `isApproximateSubgroup_one` gives the converse: a $1$-approximate subgroup is the carrier of a subgroup.

The image of a $K$-approximate subgroup by a group homomorphism is a $K$-approximate subgroup (`IsApproximateSubgroup.image`). The intersection of two approximate subgroups is not an approximate subgroup in general, but the intersection of powers is: `IsApproximateSubgroup.pow_inter_pow` makes $A^m \cap B^n$ an approximate subgroup with constant $K^{2m-1} L^{2n-1}$ when $m, n \ge 2$.

**Theorem.** If $A$ is a finite $K$-approximate subgroup and $n \ge 1$, then $|A^n| \le K^{n-1}|A|$.

*Proof.* Let $F$ be a finset with $|F| \le K$ and $A^2 \subseteq F A$. By induction, $A^n \subseteq F^{n-1} A$. For the step, put the new factor on the left. In a non-abelian group the order of the factors matters, so write $A^{n+1} = A^2 A^{n-1} \subseteq F A\, A^{n-1} = F A^n \subseteq F F^{n-1} A$. Then $|A^n| \le |F|^{n-1} |A| \le K^{n-1}|A|$. $\square$

This is `IsApproximateSubgroup.card_pow_le`. The case $n = 2$ is the doubling bound `IsApproximateSubgroup.card_mul_self_le`. In the other direction, `IsApproximateSubgroup.of_small_tripling` states that a finset $A$ with $1 \in A$, $A^{-1} = A$ and $|A^3| \le K|A|$ has a square $A^2$ that is a $K^3$-approximate subgroup.

#### Small tripling and small powers

The module `Mathlib.Combinatorics.Additive.SmallTripling` proves that small tripling gives small powers in any group. In an abelian group the Plünnecke-Ruzsa inequality of Section 2 gets the same result from the doubling alone, but in a non-abelian group a set can have small doubling and large tripling. The lemma `Finset.small_pow_of_small_tripling` states that $|A^m| \le K^{m-2}|A|$ for $m \ge 3$, when $A^{-1} = A$ and $|A^3| \le K|A|$. For a set that is not symmetric, `Finset.small_alternating_pow_of_small_tripling` bounds every product $A^{\varepsilon_0} A^{\varepsilon_1} \cdots A^{\varepsilon_{m-1}}$ with signs $\varepsilon_i = \pm 1$ by $K^{3(m-2)}|A|$.

#### Convolutions

The module `Mathlib.Combinatorics.Additive.Convolution` defines `Finset.convolution A B x` as the number of representations of $x$ as a product $a b$. The lemma `Finset.card_mul_eq` states this as the cardinality of `{ab ∈ A ×ˢ B | ab.1 * ab.2 = x}`, and `Finset.card_mul_inv_eq_convolution_inv` counts the representations $x = a b^{-1}$ by `A.convolution B⁻¹ x`. A representation is fixed by its first factor, so `Finset.convolution_le_card_left` gives $A * B(x) \le |A|$.

#### Dissociated sets

The module `Mathlib.Combinatorics.Additive.Dissociation` works in a commutative group $\alpha$. The definition `MulDissociated s` states that the map $t \mapsto \prod_{x \in t} x$ is injective on the finsets $t \subseteq s$. The lemma `mulDissociated_iff_sum_eq_subsingleton` restates this: for each $a$ there is at most one finset $t \subseteq s$ with product $a$. The negation has a useful form. By `not_mulDissociated_iff_exists_disjoint`, a set is not dissociated exactly when it has two different disjoint finite subsets with equal products.

In a finite group, `Finset.mulSpan s` is the set of the products $\prod_{a \in s} a^{\varepsilon(a)}$ with $\varepsilon(a) \in \{-1, 0, 1\}$. The membership lemma is `Finset.mem_mulSpan`, and `Finset.subset_mulSpan` states $s \subseteq$ `s.mulSpan`.

**Theorem.** Let $s$ be a finset in a finite commutative group. If each dissociated subset of $s$ has at most $d$ elements, then there is $s' \subseteq s$ with $|s'| \le d$ and $s \subseteq$ `s'.mulSpan`.

*Proof.* Let $s'$ be a dissociated subset of $s$ that is maximal for inclusion. Then $|s'| \le d$. Let $a \in s \setminus s'$. The set $s' \cup \{a\}$ is not dissociated, so it has two different disjoint subsets $t$ and $u$ with equal products. If $a$ is in neither of them, they are subsets of $s'$ and $s'$ is not dissociated, which is false. So $a$ is in exactly one of them, say in $t$. Then $a = \prod_{x \in u} x \cdot \prod_{x \in t \setminus \{a\}} x^{-1}$, and the elements of $u$ and of $t \setminus \{a\}$ are different elements of $s'$. So $a$ is in the span of $s'$. $\square$

This is `Finset.exists_subset_mulSpan_card_le_of_forall_mulDissociated`.

The module `Mathlib.Combinatorics.Additive.Randomisation` has one lemma, `AddDissociated.randomisation`. It works in a finite abelian group $G$ with two functions $c$ and $d$ on the characters $\psi$ of $G$. When the support of $d$ is dissociated, the average over $a \in G$ of $\prod_\psi (c(\psi) + \operatorname{Re}(d(\psi)\psi(a)))$ is $\prod_\psi c(\psi)$.

#### Freiman homomorphisms

The module `Mathlib.Combinatorics.Additive.FreimanHom` defines `IsMulFreimanHom n A B f` for `f : α → β` between commutative monoids. It has two fields. The field `mapsTo` states that $f$ maps $A$ to $B$. The field `map_prod_eq_map_prod` states that for multisets $s$ and $t$ of $n$ elements of $A$ with equal products, the images have equal products. The definition `IsMulFreimanIso n A B f` asks for `Set.BijOn f A B` and for the equivalence of the two equalities, so the inverse map is also a Freiman homomorphism. The lemma `IsMulFreimanIso.isMulFreimanHom` forgets the inverse, and `IsMulFreimanHom.comp` and `IsMulFreimanIso.comp` compose.

The small orders have direct forms. A homomorphism of order $1$ is any map from $A$ to $B$ (`isMulFreimanHom_one_iff`). A homomorphism of order $2$ keeps the equalities $a b = c d$ (`isMulFreimanHom_two` and `IsMulFreimanHom.mul_eq_mul`).

**Theorem.** If $\beta$ is cancellative and $m \le n$, then a Freiman homomorphism of order $n$ is a Freiman homomorphism of order $m$.

*Proof.* If $A$ is empty, there is nothing to prove. Otherwise fix $a \in A$. Let $s$ and $t$ be multisets of $m$ elements of $A$ with equal products. Add $n - m$ copies of $a$ to each. The new multisets have $n$ elements and equal products, so their images have equal products. These images are the images of $s$ and $t$ multiplied by $f(a)^{n-m}$. Cancel this factor in $\beta$. $\square$

This is `IsMulFreimanHom.mono`, and `IsMulFreimanIso.mono` is the form for isomorphisms. A standard example is `Fin.isAddFreimanIso_Iio`. For $m \ne 0$ and $m k \le n$, the map `Fin.val` is an additive Freiman isomorphism of order $m$ from the elements of `Fin n` below $k$ to the natural numbers below $k$.

#### Subset sums

The module `Mathlib.Combinatorics.Additive.SubsetSum` defines `Finset.subsetSum A` as the finset of the sums $\sum_{b \in B} b$ over the subsets $B \subseteq A$ (`Finset.mem_subsetSum_iff`).

**Theorem.** If $A$ is a finset of $k$ positive elements of a linearly ordered cancellative commutative monoid, then $\binom{k+1}{2} < |\Sigma(A)|$, where $\Sigma(A)$ is the set of subset sums.

*Proof.* Induction on $k$. For $k = 0$, $\Sigma(\emptyset) = \{0\}$ has $1 > 0$ elements. For the step, let $a$ be the largest element of $A$, let $A' = A \setminus \{a\}$ and let $\sigma$ be the sum of $A'$. Each element of $\Sigma(A')$ is at most $\sigma$. The $k$ sums $\sigma + a$ and $\sigma + a - b$ for $b \in A'$ are in $\Sigma(A)$, they are different, and each is larger than $\sigma$ because $a > b$. So $|\Sigma(A)| \ge |\Sigma(A')| + k > \binom{k}{2} + k = \binom{k+1}{2}$. $\square$

This is `Finset.card_succ_choose_two_lt_card_subsetSum_of_pos`. The set $\{1, \dots, k\}$ shows that the bound is sharp. For nonnegative elements, `Finset.card_choose_two_lt_card_subsetSum_of_nonneg` gives $\binom{k}{2}$ in place of $\binom{k+1}{2}$, because $0$ can be one of the elements.

#### Very small doubling

The module `Mathlib.Combinatorics.Additive.VerySmallDoubling` describes the finsets $A$ of a group whose doubling $|A A|/|A|$ is very small. If $|A A| \le |A|$, then $A$ is a left coset of its stabilizer: `Finset.smul_stabilizer_of_no_doubling` gives `a • stabilizer G A = A` for each $a \in A$. If $|A A| < \tfrac32 |A|$, then `Finset.invMulSubgroup A h` is a subgroup with carrier $A^{-1} A$ (`Finset.invMulSubgroup_eq_inv_mul`), equal to $A A^{-1}$ (`Finset.invMulSubgroup_eq_mul_inv`). The theorem `Finset.doubling_lt_three_halves` then gives a subgroup $H$ with $|H| < \tfrac32 |A|$ such that $A \subseteq a H$ and $a H = H a$ for each $a \in A$. Two further theorems treat larger doublings. `Finset.doubling_lt_golden_ratio` treats a doubling below the golden ratio `Real.goldenRatio`, and `Finset.doubling_lt_two` treats a doubling at most $2 - \varepsilon$. Each gives a finite subgroup $H$ and a bounded number of cosets of $H$ that cover the set.

#### Schnirelmann density

The module `Mathlib.Combinatorics.Schnirelmann` defines the Schnirelmann density of a set $A \subseteq \mathbb{N}$:
$$\sigma(A) = \inf_{n \ge 1} \frac{|A \cap \{1, \dots, n\}|}{n}.$$
The definition `schnirelmannDensity A` needs a `DecidablePred (· ∈ A)` instance. The value is in $[0, 1]$ (`schnirelmannDensity_nonneg`, `schnirelmannDensity_le_one`), and `le_schnirelmannDensity_iff` unfolds a lower bound. The density ignores $0$ (`schnirelmannDensity_sdiff_singleton_zero`), but it is very sensitive to small elements: if $1 \notin A$ then $\sigma(A) = 0$ (`schnirelmannDensity_eq_zero_of_one_notMem`), and if $k \notin A$ then $\sigma(A) \le 1 - 1/k$ (`schnirelmannDensity_le_of_notMem`). The density is $1$ exactly when $A$ contains all positive integers (`schnirelmannDensity_eq_one_iff`). The primes have density $0$ (`schnirelmannDensity_setOfPred_prime`), because $1$ is not a prime, and the odd numbers have density $\tfrac12$ (`schnirelmannDensity_setOfPred_Odd`).

**Theorem.** If $0 \in A$, $0 \in B$ and $\sigma(A) + \sigma(B) \ge 1$, then $A + B = \mathbb{N}$.

*Proof.* Let $n \ge 1$. If $n \in A$ or $n \in B$, then $n = n + 0$ or $n = 0 + n$. Otherwise $A$ has at least $\sigma(A) n$ elements in $\{1, \dots, n - 1\}$, and $B$ has at least $\sigma(B) n$ elements there. So the two sets $A \cap \{1, \dots, n-1\}$ and $\{n - b : b \in B,\ 1 \le b \le n - 1\}$ have together at least $n$ elements in a set of $n - 1$ elements. They meet, and a common element gives $n = a + b$. $\square$

This is `add_eq_univ_of_one_le_schirelmannDensity_add_schnirelmannDensity`. The name has the spelling "schirelmann" in its first part.

#### The Combinatorial Nullstellensatz

The module `Mathlib.Combinatorics.Nullstellensatz` works with multivariate polynomials `MvPolynomial σ R` over an integral domain $R$, with a finite type $\sigma$ of variables. Let $S_i$ be a finset of $R$ for each variable $i$. The first theorem, `MvPolynomial.combinatorial_nullstellensatz_exists_linearCombination`, states that a polynomial $f$ that vanishes on the grid $\prod_i S_i$ is a combination $\sum_i h_i \prod_{r \in S_i}(X_i - r)$, with $\deg(h_i \prod_{r \in S_i}(X_i - r)) \le \deg f$ for each $i$.

The second theorem, `MvPolynomial.combinatorial_nullstellensatz_exists_eval_ne_zero`, is the form for applications. Let $t$ be a multi-index with $\sum_i t_i = \deg f$ and a nonzero coefficient of $X^t$ in $f$. If $|S_i| > t_i$ for each $i$, then $f$ does not vanish at some point of the grid. The old name `MvPolynomial.combinatorial_nullstellensatz_exists_eval_nonzero` is a deprecated alias.

#### Common errors

1. Using `IsApproximateSubgroup K A` with a finset. The predicate is on `Set G`, so a finset `A` must be coerced to `(A : Set G)`. The cardinality lemmas such as `IsApproximateSubgroup.card_pow_le` take `A : Finset G` and the hypothesis on its coercion.
2. Expecting `Finset.mulSpan` in an infinite group. It needs `[Fintype α]`, because it is the image of the finite set of sign functions on all of $\alpha$. The predicate `MulDissociated` needs no finiteness.
3. Expecting a set of density $0$ to be small. The Schnirelmann density is $0$ for each set without $1$, so the even numbers have density $0$. The theorem on $A + B$ needs the density of both sets, with $0$ in both.

### Exercises

1. (A) Compute $\Sigma(\{1, 2, \dots, k\})$ and show that it has $\binom{k+1}{2} + 1$ elements. Deduce that the bound of `Finset.card_succ_choose_two_lt_card_subsetSum_of_pos` is sharp.
2. (A) Show that the set $\{1, 2, 4, \dots, 2^{k-1}\}$ is `AddDissociated` in $\mathbb{Z}$, and that $\{1, 2, 3\}$ is not. Give the two disjoint subsets that `not_mulDissociated_iff_exists_disjoint` asks for in the second case.
3. (A) Show that the odd numbers have Schnirelmann density $\tfrac12$. Find the value of $n$ where the infimum is attained.
4. (B) Prove that a subgroup $H$ is a $1$-approximate subgroup, and that a $1$-approximate subgroup $A$ is closed under products. Use `CovBySMul G 1 (A ^ 2) A` and the fact $1 \in A$ to show first that the single translate $x A$ has $x \in A$ and is equal to $A^2$.
5. (B) Let $f$ be an additive Freiman homomorphism of order $2$ from a set $A \subseteq \mathbb{Z}$ to $\mathbb{Z}$. Show that $f$ maps an arithmetic progression in $A$ of length $3$ to an arithmetic progression of length $3$, possibly with common difference $0$. State the result in Lean with `isMulFreimanHom_two` in its additive form.
6. (C) Prove the theorem of Cauchy and Davenport of Section 1 with the Combinatorial Nullstellensatz. For $A, B \subseteq \mathbb{Z}/p\mathbb{Z}$ with $|A| + |B| \le p + 1$, suppose that $C = A + B$ has at most $|A| + |B| - 2$ elements. Add elements to $C$ until $|C| = |A| + |B| - 2$, and apply `MvPolynomial.combinatorial_nullstellensatz_exists_eval_ne_zero` to $f(x, y) = \prod_{c \in C}(x + y - c)$ with $t = (|A| - 1, |B| - 1)$.

### Reference

<?reference?>
