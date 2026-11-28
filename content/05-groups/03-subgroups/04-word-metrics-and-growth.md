---
title: Word length, word metrics and growth
kind: api
modules:
  - Mathlib.Geometry.Group.WordProd
  - Mathlib.Geometry.Group.WordMetric
  - Mathlib.Geometry.Group.Growth.LinearLowerBound
  - Mathlib.Geometry.Group.Growth.QuotientInter
explains:
  E2: [Group.Generators.wordProd, Group.Generators.wordLength, Group.Generators.wordLength_le_iff, Group.Generators.wordLength_mul_le, Group.Generators.normedGroup, Finset.add_one_le_card_pow, Finset.card_pow_quotient_mul_pow_inter_subgroup_le]
  E1: auto
families: []
requires: [V05.C01, V05.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Word length, word metrics and growth

### Overview

Section 1 builds the subgroup that a set generates: its elements are the products of elements of the set and their inverses. This section measures such products. Fix a generating family of a group $G$. The word length $|g|$ of an element $g$ is the length of a shortest word in the generators and their inverses whose product is $g$. The word length makes $G$ a metric space, with $d(g, h) = |g^{-1} h|$. This metric is the start of geometric group theory, which studies a group through the geometry of this metric.

A second measure of growth uses a finite set $X$ and its powers $X^n = \{x_1 \cdots x_n : x_i \in X\}$. The growth of $X$ is the function $n \mapsto |X^n|$. The modules of this section prove two first facts: the growth of a set that generates an infinite group is at least linear, and the growth of a set splits into a part in a normal subgroup and a part in the quotient.

### The library around it

#### Generating families and words

A generating family of $G$ indexed by a type $\iota$ is a structure `Group.Generators G ι`. It holds a function `Group.Generators.val` from $\iota$ to $G$ and a proof `Group.Generators.closure_eq_top` that the closure of its range is all of $G$. Each set $S$ with closure $G$ gives a family indexed by $S$, by `Group.Generators.ofSet`. A family gives a homomorphism `Group.Generators.lift` from the free group on $\iota$ to $G$, and this homomorphism is surjective.

A word is a list of pairs $(i, b)$ with $i \in \iota$ and $b$ a boolean. The pair $(i, \mathrm{true})$ stands for the generator $s_i$, and $(i, \mathrm{false})$ stands for $s_i^{-1}$. This is the form that `FreeGroup.mk` takes. The module `Mathlib.Geometry.Group.WordProd` defines the evaluation `Group.Generators.wordProd`, which sends a word to the product of its letters in $G$. Its API follows the word API of Coxeter groups, `CoxeterSystem.wordProd`.

| Lean name | Statement |
|---|---|
| `Group.Generators.wordProd_nil` | the empty word evaluates to $1$ |
| `Group.Generators.wordProd_singleton` | the word $(i, b)$ evaluates to $s_i$ or $s_i^{-1}$ |
| `Group.Generators.wordProd_cons` | the evaluation of $(i, b) :: l$ is the letter times the evaluation of $l$ |
| `Group.Generators.wordProd_append` | the evaluation of $l_1 \mathbin{+\!\!+} l_2$ is the product of the evaluations |
| `Group.Generators.wordProd_invRev` | the reversed word with inverted letters evaluates to the inverse |
| `Group.Generators.wordProd_surjective` | each element of $G$ is the evaluation of some word |

The reversed word with inverted letters is `FreeGroup.invRev`. The surjectivity is the definition of a generating family: the free group maps onto $G$, and each element of the free group is the class of a word.

#### Word length

The word length `Group.Generators.wordLength` of $g$ is the infimum of the lengths of the words that evaluate to $g$. The set of these lengths is not empty, by the surjectivity above, so the infimum is a minimum. A word is geodesic, `Group.Generators.IsGeodesic`, when its length is the word length of its evaluation. Each element has a geodesic word, by `Group.Generators.exists_isGeodesic`.

The definition uses an infimum and has no useful computation. Use the characterisation `Group.Generators.wordLength_le_iff` instead:

$$|g| \le n \iff \text{there is a word } l \text{ of length at most } n \text{ with } \mathrm{wordProd}(l) = g.$$

*Proof.* If $|g| \le n$, take a geodesic word for $g$: its length is $|g|$. Conversely, a word $l$ with product $g$ gives $|g| \le \mathrm{length}(l)$ by `Group.Generators.wordLength_wordProd_le`. $\square$

The word length has the three properties of a norm on a group.

1. $|g| = 0$ if and only if $g = 1$ (`Group.Generators.wordLength_eq_zero_iff`). Only the empty word has length $0$, and it evaluates to $1$.
2. $|g^{-1}| = |g|$ (`Group.Generators.wordLength_inv`). Reverse a geodesic word for $g$ and invert its letters: this gives a word for $g^{-1}$ of the same length, so $|g^{-1}| \le |g|$. Apply the same argument to $g^{-1}$.
3. $|gh| \le |g| + |h|$ (`Group.Generators.wordLength_mul_le`). Concatenate geodesic words for $g$ and $h$, and use `Group.Generators.wordProd_append`.

The additive forms have their own names: for an additive group, `AddGroup.Generators.wordSum` evaluates a word and `AddGroup.Generators.wordLength` is its length.

#### The word metric

The three properties above say that the word length is a group norm. The definition `Group.Generators.groupNorm` packs it as a `GroupNorm G`, and `Group.Generators.normedGroup` turns this norm into a `NormedGroup G` structure. The distance of this structure is

$$d(g, h) = |g^{-1} h|.$$

This is the word metric. It is invariant under left multiplication: $d(kg, kh) = |g^{-1} k^{-1} k h| = d(g, h)$. Two elements are at distance $1$ when they differ by one generator on the right, so the word metric is the path metric of the Cayley graph. The library does not yet prove this last statement.

The structure `Group.Generators.normedGroup` is a definition, not an instance, because it depends on the choice of the generators. Two generating families give two different metrics on the same group. When both families are finite, the two metrics are bi-Lipschitz equivalent, but this is not in these modules. For an additive group the definition is `AddGroup.Generators.normedAddGroup`.

#### Linear lower bound on growth

Now let $X$ be a finite set in $G$ with $1 \in X$. Then $X^n \subseteq X^{n+1}$, because $x = x \cdot 1$. The sets $X^n$ increase, and their union is the submonoid that $X$ generates.

**Theorem.** Let $X$ be a finite subset of $G$ with $1 \in X$, and assume that the subgroup that $X$ generates is infinite. Then $|X^n| \ge n + 1$ for each $n$. This is `Finset.add_one_le_card_pow`.

*Proof.* First the chain $X^0 \subseteq X^1 \subseteq \cdots$ is strict. Suppose that $X^n = X^{n+1}$ for some $n$. Then $X^{n+k} = X^n$ for each $k$, by induction on $k$, so the union of all powers of $X$ is the finite set $X^n$. This union is a submonoid of $G$, and a finite submonoid of a group is a subgroup. So $X^n$ is a subgroup. It contains $X$, because $X = X^1 \subseteq X^n$ for $n \ge 1$, and for $n = 0$ the equality $X^0 = X^1$ gives $X = \{1\}$. So $X^n$ contains the subgroup generated by $X$. That subgroup is infinite and $X^n$ is finite, a contradiction. A strictly increasing chain of finite sets with $|X^0| = 1$ has $|X^n| \ge n + 1$. $\square$

The library proves the strict increase in two steps. The lemma `Finset.pow_ssubset_pow_succ_of_pow_ne_closure` says $X^n \subsetneq X^{n+1}$ when $X$ is nontrivial and $X^n$ is not the subgroup that $X$ generates. Then `Finset.pow_right_strictMonoOn` and `Finset.pow_right_strictMono` give the strict monotonicity of $n \mapsto X^n$. The bound is sharp: in $\mathbb{Z}$ with $X = \{0, 1\}$, the set $nX$ is $\{0, \ldots, n\}$, with $n + 1$ elements.

#### Growth in a quotient and in a subgroup

Let $H$ be a normal subgroup of $G$, let $\pi : G \to G/H$ be the quotient map of Chapter 5, and let $A$ be a finite subset of $G$. The module `Mathlib.Geometry.Group.Growth.QuotientInter` compares the growth of $A$ with the growth of its image in $G/H$ and of its trace in $H$.

**Theorem.** For each $m$ and $n$,

$$|\pi(A^m)| \cdot |A^n \cap H| \le |A^{m+n}|.$$

This is `Finset.card_pow_quotient_mul_pow_inter_subgroup_le`.

*Proof.* For each $q \in \pi(A^m)$, choose $\varphi(q) \in A^m$ with $\pi(\varphi(q)) = q$. Consider the map $(q, h) \mapsto \varphi(q) h$ on $\pi(A^m) \times (A^n \cap H)$. Its values lie in $A^m A^n = A^{m+n}$. It is injective: if $\varphi(q) h = \varphi(q') h'$, apply $\pi$ to get $q = q'$, because $\pi(h) = \pi(h') = 1$, and then cancel to get $h = h'$. $\square$

**Theorem.** If $A$ is symmetric, that is $A^{-1} = A$, then

$$|A| \le |\pi(A)| \cdot |A^2 \cap H|.$$

This is `Finset.le_card_quotient_mul_sq_inter_subgroup`.

*Proof.* Split $A$ into the fibres $F_q = \{a \in A : \pi(a) = q\}$ for $q \in \pi(A)$. Fix $a \in F_q$. The map $x \mapsto a^{-1} x$ sends $F_q$ injectively into $F_q^{-1} F_q$. This set lies in $A^{-1} A = A^2$ and in $H$, because $\pi(a^{-1} x) = q^{-1} q = 1$. So each fibre has at most $|A^2 \cap H|$ elements, and there are $|\pi(A)|$ fibres. $\square$

The additive forms are `Finset.card_nsmul_quotient_add_nsmul_inter_addSubgroup_le` and `Finset.le_card_quotient_add_sq_inter_addSubgroup`. These inequalities appear in additive combinatorics, where a proof often passes to a quotient to make a set smaller.

#### Common errors

1. The word length depends on the generating family. A lemma about `Group.Generators.wordLength` always takes the family as an argument, and the norm of `Group.Generators.normedGroup` is not an instance. Give it with the tactic *letI* when a proof needs the metric.
2. The theorem `Finset.add_one_le_card_pow` needs $1 \in X$. Without it the sets $X^n$ need not increase: in $\mathbb{Z}/2$ with $X = \{1\}$, written additively, the sets $nX$ alternate between $\{0\}$ and $\{1\}$.
3. A word is a `List (ι × Bool)`, not an element of the free group. Two different words can have the same evaluation, and only some of them are geodesic.

### Exercises

1. (A) Compute the word length of each element of $S_3$ for the generating family of the two transpositions $(1\,2)$ and $(2\,3)$.
2. (A) Prove with `Group.Generators.wordLength_mul_le` and `Group.Generators.wordLength_inv` that $\bigl||g| - |h|\bigr| \le |g^{-1} h|$.
3. (B) Show that the word metric on $\mathbb{Z}$ for the generating family $\{1\}$ is $d(m, n) = |m - n|$, and for the family $\{2, 3\}$ it is a different metric.
4. (B) Let $X$ be a finite set with $1 \in X$ that generates a finite group $G$. Show that $X^n = G$ for each $n \ge |G| - 1$.
5. (B) In $\mathbb{Z}^2$ with $X = \{0, \pm e_1, \pm e_2\}$, compute $|nX|$ and show that the growth is quadratic.
6. (C) Prove that the word metrics of two finite generating families of the same group are bi-Lipschitz equivalent.

### Reference

<?reference?>
