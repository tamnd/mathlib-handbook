---
title: Well-founded sets and well-quasi-orders
kind: api
modules:
  - Mathlib.Order.WellFoundedSet
  - Mathlib.Order.WellQuasiOrder
  - Mathlib.Order.OrderIsoNat
  - Mathlib.Order.KonigLemma
  - Mathlib.Order.Northcott
explains:
  E2: [WellQuasiOrdered.wellFounded, IsAntichain.finite_of_wellQuasiOrdered, WellQuasiOrdered.prod, wellQuasiOrderedLE_iff, Set.IsWF.isPWO, wellFoundedGT_iff_monotone_chain_condition, Northcott.exists_min_image, exists_seq_covby_of_forall_covby_finite]
  E1: auto
families: []
requires: [V01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Well-founded sets and well-quasi-orders

### Overview

The section on well-founded orders treats a well-founded relation on a whole type. Many proofs need the same property for a subset only. A set of exponents of a power series, the support of a Hahn series and a set of monomials in a polynomial ring are examples. The module `Mathlib.Order.WellFoundedSet` gives the relative forms: a relation is well-founded on a set, and a set is partially well-ordered. The module `Mathlib.Order.WellQuasiOrder` gives the absolute notion of a well-quasi-order, both for a relation and as a class for `≤`.

A well-quasi-order is stronger than a well-founded order. It forbids infinite strictly decreasing sequences, and it also forbids infinite antichains. This second condition is what makes products work: the product of two well-quasi-orders is again a well-quasi-order, while the product of two well-founded orders is well-founded but can have infinite antichains. Dickson's lemma and Higman's lemma are the two standard results of this kind, and both are in the library.

The section also covers three smaller modules. The module `Mathlib.Order.OrderIsoNat` turns sequences into order embeddings of `ℕ` and gives the chain conditions. The module `Mathlib.Order.KonigLemma` proves Kőnig's infinity lemma in the language of covering relations. The module `Mathlib.Order.Northcott` defines functions with finite sublevel sets.

### The library around it

#### Well-founded on a set

Let $r$ be a relation on $\alpha$ and let $s \subseteq \alpha$. The predicate `Set.WellFoundedOn s r` says that the restriction of $r$ to $s$ is well-founded. The definition is `WellFounded (Subrel r (· ∈ s))`, and `Set.wellFoundedOn_iff` restates it as the well-foundedness of the relation $r\,a\,b \wedge a \in s \wedge b \in s$ on all of $\alpha$. For `<` the library has the short name `Set.IsWF s`, which is `s.WellFoundedOn (· < ·)`. The two forms agree with the absolute notion on the whole type: `Set.wellFoundedOn_univ` and `Set.isWF_univ_iff` say that `Set.univ` is well-founded for $r$ exactly when $r$ is well-founded.

The closure properties have the standard names. A subset of a well-founded set is well-founded (`Set.WellFoundedOn.subset`, `Set.IsWF.mono`). Finite sets, singletons and the empty set are well-founded for a strict order (`Set.Finite.wellFoundedOn`, `Set.Finite.isWF`, `Set.isWF_singleton`, `Set.isWF_empty`). A union of two well-founded sets is well-founded, and the simp lemmas `Set.isWF_union` and `Set.wellFoundedOn_union` state the equivalence. The lemmas `Set.isWF_insert` and `Set.wellFoundedOn_sdiff_singleton` say that one point does not change the property. The finite forms over a `Finset` index are `Finset.isWF_sup` and `Finset.isWF_bUnion`. In a locally finite order, a set that is bounded below is well-founded for `<`, by `BddBelow.isWF`.

The test by sequences is `Set.isWF_iff_no_descending_seq`: a set $s$ is well-founded if and only if no strictly decreasing sequence $f : \mathbb{N} \to \alpha$ has all its terms in $s$. A nonempty well-founded set has a minimal element (`Set.WellFoundedOn.exists_minimal`), and induction works inside the set (`Set.WellFoundedOn.induction`). In a linear order the minimal element is a minimum, and the library chooses it as `Set.IsWF.min hs hn`, where `hs` proves `s.IsWF` and `hn` proves `s.Nonempty`. The lemmas `Set.IsWF.min_mem`, `Set.IsWF.min_le` and `Set.IsWF.not_lt_min` give its properties, and `Set.IsWF.min_union` computes the minimum of a union as the smaller of the two minima.

For lexicographic orders, `WellFounded.prod_lex_of_wellFoundedOn_fiber` and `Set.WellFoundedOn.prod_lex_of_wellFoundedOn_fiber` prove well-foundedness from the base and from each fiber. The forms `WellFounded.sigma_lex_of_wellFoundedOn_fiber` do the same for a sigma type.

#### Well-quasi-orders

**Definition.** A relation $r$ on $\alpha$ is a *well-quasi-order* if for each sequence $f : \mathbb{N} \to \alpha$ there are $m < n$ with $r\,(f\,m)\,(f\,n)$.

In Lean this is `WellQuasiOrdered r`, and the definition is literally the formula above. The definition does not ask $r$ to be reflexive or transitive, but most theorems assume `IsPreorder α r`. A sequence with no such pair is a *bad sequence*. So a well-quasi-order is a relation with no bad sequence, and `Set.PartiallyWellOrderedOn.IsBadSeq` names the bad sequences inside a set. For a type with `≤`, the class `WellQuasiOrderedLE α` says that `≤` is a well-quasi-order, and `wellQuasiOrdered_le` extracts the property from the instance.

**Proposition.** Let $r$ be a preorder on $\alpha$ that is a well-quasi-order. Then the strict relation $r\,a\,b \wedge \lnot r\,b\,a$ is well-founded (`WellQuasiOrdered.wellFounded`), and each antichain of $r$ is finite (`IsAntichain.finite_of_wellQuasiOrdered`).

*Proof.* Suppose that $f$ is a strictly decreasing sequence for the strict relation. The definition gives $m < n$ with $r\,(f\,m)\,(f\,n)$. But $f\,n$ is strictly below $f\,m$ by transitivity, so $\lnot r\,(f\,m)\,(f\,n)$. This is a contradiction, and a relation with no infinite descending sequence is well-founded. For the second claim, an infinite antichain contains an injective sequence $f$. Then $r\,(f\,m)\,(f\,n)$ with $m < n$ is false, because $f\,m \ne f\,n$ are two different elements of the antichain. So the antichain is finite. $\square$

For a preorder the converse also holds. The theorem `wellQuasiOrderedLE_iff` says that `WellQuasiOrderedLE α` is equivalent to `WellFoundedLT α` together with the finiteness of each antichain. In a linear order each antichain has at most one element, so `wellQuasiOrderedLE_iff_wellFoundedLT` reduces the class to well-foundedness, and the instance `instWellQuasiOrderedLEOfWellFoundedLT` applies to `ℕ`, to ordinals and to each well-ordered type.

The second test uses subsequences. The theorem `wellQuasiOrdered_iff_exists_monotone_subseq` says that a preorder $r$ is a well-quasi-order if and only if each sequence has a monotone subsequence: there is $g : \mathbb{N} \hookrightarrow \mathbb{N}$, strictly increasing, with $r\,(f\,(g\,m))\,(f\,(g\,n))$ for all $m \le n$. A proof uses the Ramsey type statement `exists_increasing_or_nonincreasing_subseq` of `Mathlib.Order.OrderIsoNat`: for a transitive relation, each sequence has a subsequence on which $r$ holds for all pairs $m < n$, or on which $r$ fails for all pairs $m < n$. In a well-quasi-order the second case is impossible.

**Proposition (Dickson).** If $r$ on $\alpha$ and $s$ on $\beta$ are well-quasi-orders and $r$ is a preorder, then the relation $r\,a_1\,b_1 \wedge s\,a_2\,b_2$ on $\alpha \times \beta$ is a well-quasi-order (`WellQuasiOrdered.prod`).

*Proof.* Let $f = (f_1, f_2)$ be a sequence in $\alpha \times \beta$. Take a monotone subsequence $f_1 \circ g$ for $r$. The sequence $f_2 \circ g$ has $m < n$ with $s\,(f_2(g\,m))\,(f_2(g\,n))$. Since $g\,m < g\,n$ and $r\,(f_1(g\,m))\,(f_1(g\,n))$, the pair $g\,m < g\,n$ is good for $f$. $\square$

By induction on a finite index type, `WellQuasiOrdered.pi` gives the same result for a finite product with the pointwise relation, and `Pi.wellQuasiOrderedLE` is the instance. For $\mathbb{N}^k$ this is Dickson's lemma: each set of monomials in $k$ variables has finitely many minimal elements for divisibility. Other ways to build a well-quasi-order are a finite type (`Finite.to_wellQuasiOrderedLE`), the image under a monotone surjection (`Monotone.wellQuasiOrderedLE_of_wellQuasiOrderedLE_of_surjective`) and an order isomorphism (`OrderIso.wellQuasiOrderedLE_iff`).

#### Partially well-ordered sets

The relative form of a well-quasi-order is `Set.PartiallyWellOrderedOn s r`: the restriction of $r$ to $s$ is a well-quasi-order. Its unfolded form is `Set.partiallyWellOrderedOn_iff_exists_lt`: each sequence with values in $s$ has $m < n$ with $r\,(f\,m)\,(f\,n)$. For `≤` the short name is `Set.IsPWO s`. The two notions match the absolute ones by `Set.partiallyWellOrderedOn_univ_iff` and `Set.isPWO_univ_iff`.

The API follows the pattern of the well-founded sets. There are the lemmas `Set.IsPWO.mono`, `Set.isPWO_union`, `Set.isPWO_insert`, `Set.Finite.isPWO`, `Set.isPWO_singleton` and `Finset.isPWO_sup`. A partially well-ordered set is well-founded (`Set.IsPWO.isWF`). In a linear order the converse holds, because each antichain has at most one point.

**Proposition.** In a linear order, a well-founded set is partially well-ordered (`Set.IsWF.isPWO`), so `Set.isPWO_iff_isWF` holds.

*Proof.* Let $f$ be a sequence in $s$. If $f\,m \le f\,n$ for some $m < n$, the pair is good. Otherwise $f\,n < f\,m$ for all $m < n$, because the order is linear. Then $f$ is strictly decreasing in $s$, which contradicts `Set.isWF_iff_no_descending_seq`. $\square$

The library proves the main closure results for partially well-ordered sets. The image under a monotone map is partially well-ordered (`Set.IsPWO.image_of_monotone`). The product of two partially well-ordered sets is partially well-ordered (`Set.IsPWO.prod`), and so is a finite product (`Set.IsPWO.pi`). A partially well-ordered set has a minimal element below each of its elements (`Set.IsPWO.exists_le_minimal`).

Higman's lemma is `Set.PartiallyWellOrderedOn.partiallyWellOrderedOn_sublistForall₂`. It says: if $r$ is a preorder that is partially well-ordered on $s$, then the set of lists with entries in $s$ is partially well-ordered for the relation `List.SublistForall₂ r`. A list $l_1$ is in this relation with $l_2$ when $l_2$ has a sublist of the same length as $l_1$ whose entries dominate the entries of $l_1$ one by one. The proof is the minimal bad sequence argument. The library gives it in a general form: `Set.PartiallyWellOrderedOn.exists_min_bad_of_exists_bad` takes a rank function $\mathrm{rk} : \alpha \to \mathbb{N}$ and turns a bad sequence into a bad sequence that is minimal for the rank at each index, with the predicate `Set.PartiallyWellOrderedOn.IsMinBadSeq`.

Hahn series use these sets. The support of a Hahn series is partially well-ordered, and the product of two Hahn series is defined because each exponent has only finitely many ways to be a sum of two exponents from the supports.

#### Sequences and chain conditions

The module `Mathlib.Order.OrderIsoNat` connects sequences in an order with embeddings of $\mathbb{N}$. For a strict order $r$ and a sequence $f$ with $r\,(f\,n)\,(f\,(n+1))$ for each $n$, the map `RelEmbedding.natLT f H` is $f$ as a relation embedding of $(\mathbb{N}, <)$ into $(\alpha, r)$. The map `RelEmbedding.natGT` is the same for a decreasing sequence. So `RelEmbedding.not_wellFounded` says that a relation with an embedding of $(\mathbb{N}, >)$ is not well-founded. For an infinite set $s \subseteq \mathbb{N}$, the map `Nat.orderEmbeddingOfSet s` enumerates $s$ in increasing order, and `Nat.Subtype.orderIsoOfNat s` is the order isomorphism $\mathbb{N} \cong s$.

**Proposition (ascending chain condition).** A partial order satisfies `WellFoundedGT α` if and only if each increasing sequence $a_0 \le a_1 \le \cdots$ is eventually constant (`wellFoundedGT_iff_monotone_chain_condition`).

*Proof.* If an increasing sequence is not eventually constant, it has a strictly increasing subsequence, and this is an infinite descending sequence for `>`. Conversely, if `>` is not well-founded, there is a strictly increasing sequence, and it is never constant. $\square$

This is the Noetherian condition of commutative algebra, for the lattice of ideals. For a sequence `a : ℕ →o α` in such an order, `monotonicSequenceLimit a` is the final value and `monotonicSequenceLimitIndex a` is an index where the sequence becomes constant. In a complete lattice, `WellFoundedGT.iSup_eq_monotonicSequenceLimit` says that the supremum of the sequence is this final value. The dual form for decreasing sequences is `WellFoundedLT.antitone_chain_condition`.

The module has two finiteness results. The theorem `Infinite.exists_strictMono_or_strictAnti` says that each infinite linear order contains a strictly increasing or a strictly decreasing sequence. So a linear order that is well-founded in both directions is finite, which is `Finite.of_wellFoundedLT_of_wellFoundedGT`. The form for chains in a preorder is `IsChain.finite_of_wellFoundedLT_of_wellFoundedGT`.

#### Kőnig's lemma

Kőnig's infinity lemma says that an infinite tree in which each vertex has finitely many children has an infinite branch. The module `Mathlib.Order.KonigLemma` states it for an order. A partial order is strongly atomic (`IsStronglyAtomic`) when for $a < b$ there is a $c$ with $a \lessdot c \le b$, where $a \lessdot c$ is the covering relation `CovBy`.

**Theorem.** Let $\alpha$ be a strongly atomic partial order in which each element has finitely many covers, and let $b \in \alpha$ have infinitely many elements above it. Then there is a sequence $f$ with $f\,0 = b$ and $f\,i \lessdot f\,(i+1)$ for each $i$ (`exists_seq_covby_of_forall_covby_finite`).

*Proof sketch.* Each $x > b$ lies above some cover $c$ of $b$, because the order is strongly atomic. So $\{x \mid b \le x\}$ is the union of $\{b\}$ and of the finitely many sets $\{x \mid c \le x\}$ for the covers $c$ of $b$. One of these sets is infinite. Choose such a cover as $f\,1$ and repeat the argument from $f\,1$. $\square$

The variant `exists_orderEmbedding_covby_of_forall_covby_finite` gives the sequence as an order embedding of `ℕ`. The form `exists_seq_forall_proj_of_forall_finite` is the version for an inverse system: if $(\alpha_i)_{i \in \mathbb{N}}$ is a family of nonempty finite sets with compatible maps $\alpha_j \to \alpha_i$ for $i \le j$, then there is a compatible choice of one element in each $\alpha_i$.

#### Northcott functions

In number theory, a height function $h$ has the property that the sets $\{a \mid h\,a \le b\}$ are finite. The class `Northcott h` records this property for a function $h : \alpha \to \beta$ into an order, with `Northcott.finite_le` as its field. The lemma `northcott_iff_tendsto` says that for a linear order with no maximum, the property is equivalent to $h\,a \to \infty$ along the cofinite filter.

**Proposition.** If $h : \alpha \to \beta$ is Northcott and $\beta$ is a linear order, then $h$ attains a minimum on each nonempty set $s$ (`Northcott.exists_min_image`).

*Proof.* Choose $a_0 \in s$. The set $t = \{a \in s \mid h\,a \le h\,a_0\}$ is finite, because it lies in a sublevel set, and it contains $a_0$. A finite nonempty set has an element $a$ where $h$ is minimal on $t$. Each $a' \in s \setminus t$ has $h\,a' > h\,a_0 \ge h\,a$. So $h\,a$ is the minimum of $h$ on $s$. $\square$

The lemmas `Northcott.comp_of_bddAbove` and `Northcott.comp_of_finite_fibers` give the property for a composite function.

#### Common errors

1. `Set.IsPWO` and `Set.IsWF` are about `≤` and `<` of the type, not about a relation of your choice. For another relation, use `Set.PartiallyWellOrderedOn s r` and `Set.WellFoundedOn s r`. The relation in `Set.WellFoundedOn` is a strict relation, as in `WellFounded`, while the relation in `Set.PartiallyWellOrderedOn` is a reflexive one, as `≤`.
2. `Set.IsWF.min` needs the two proofs `hs : s.IsWF` and `hn : s.Nonempty` as arguments, and it is defined in a preorder. But the lemmas `Set.IsWF.min_le` and `Set.IsWF.le_min_iff` need a linear order. In a preorder the only comparison is `Set.IsWF.not_lt_min`: no element of $s$ is strictly below the chosen element.
3. A well-founded partial order need not be a well-quasi-order. The type `ℕ` with the discrete order (only $a \le a$) is well-founded, but `ℕ` itself is an infinite antichain. Use `wellQuasiOrderedLE_iff` to see which condition fails.

### Exercises

1. (A) Prove that a finite set $s$ in a preorder satisfies `s.IsPWO`, by the pigeonhole principle on a sequence in $s$.
2. (A) Use `Set.isWF_iff_no_descending_seq` to prove that $\{1/n \mid n \ge 1\} \subseteq \mathbb{Q}$ is not well-founded for `<`.
3. (B) Prove `WellQuasiOrdered.prod` from `WellQuasiOrdered.exists_monotone_subseq` and the definition.
4. (B) Deduce from Dickson's lemma that each set of monomials $x_1^{e_1} \cdots x_k^{e_k}$ has finitely many minimal elements for divisibility.
5. (B) Prove that the identity map $\mathbb{N} \to \mathbb{N}$ is Northcott, and that a constant map from an infinite type is not.
6. (C) Prove Kőnig's lemma for a rooted tree in which each vertex has finitely many children, from `exists_seq_covby_of_forall_covby_finite`, by an order on the vertices where $u \le v$ when $u$ lies on the path from the root to $v$.

### Reference

<?reference?>
