---
title: Binary images, sups and slices of finsets
kind: api
modules:
  - Mathlib.Data.Finset.NAry
  - Mathlib.Data.Finset.Sups
  - Mathlib.Data.Finset.Slice
  - Mathlib.Data.Finset.Grade
  - Mathlib.Data.Finset.Interval
  - Mathlib.Data.Finset.Sym
explains:
  E2: [Finset.image₂, Finset.card_image₂_le, Finset.compls_sups, Set.Sized.card_le, Finset.sum_card_slice, Finset.card_Icc_finset, Finset.covBy_iff_card_sdiff_eq_one, Finset.card_sym2]
  E1: auto
families: []
requires: [V03.C01, V03.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Binary images, sups and slices of finsets

### Overview

Section 1 of this chapter gave the image of a finset under a function of one variable. Many constructions take two finsets and a function of two variables: the sums $s + t = \{a + b : a \in s, b \in t\}$ of additive combinatorics, the unions $\{A \cup B : A \in \mathcal{A}, B \in \mathcal{B}\}$ of extremal set theory, and the pairs $\{a, b\}$ of elements of one finset. The modules of this section give the common tool, the binary image `Finset.image₂`, and the operations on families of sets that the combinatorics of finite sets uses.

The section also treats the order on `Finset α` itself. A finset of finsets is a *set family*. Its members of a fixed size form a *slice*. The inclusion order on `Finset α` is graded by the card, so a finset covers another one exactly when it has one more element, and the intervals $[s, t]$ of this order are finite with $2^{|t| - |s|}$ elements. The last module builds the finsets of unordered pairs and of multisets of a fixed size with elements in a given finset. The subsets of a given size of Section 2 are the model for all these counts.

### The library around it

#### Binary images

For $f : \alpha \to \beta \to \gamma$ and finsets $s$ of $\alpha$ and $t$ of $\beta$, the binary image is $$f(s, t) = \{f(a, b) : a \in s,\ b \in t\}.$$ The module `Mathlib.Data.Finset.NAry` defines it as `Finset.image₂ f s t`. It needs `DecidableEq γ`, because it removes the repeated values. The definition is the image of the product: `Finset.image_uncurry_product` states that the image of `s ×ˢ t` under `Function.uncurry f` is `Finset.image₂ f s t`. The membership rule `Finset.mem_image₂` says $c \in f(s, t) \iff \exists a \in s, \exists b \in t, f(a, b) = c$, and `Finset.coe_image₂` sends the binary image to `Set.image2` of the coercions. So each statement can move to the sets of Chapter 1.

**Theorem (Card of a binary image).** $|f(s, t)| \le |s| \cdot |t|$. Equality holds exactly when $(a, b) \mapsto f(a, b)$ is injective on $s \times t$.

*Proof.* The binary image is the image of $s \times t$ under the map $(a, b) \mapsto f(a, b)$. The image of a finset under a map has at most as many elements as the finset, with equality exactly when the map is injective on it. The product has $|s| \cdot |t|$ elements. $\square$

The Lean forms are `Finset.card_image₂_le` and `Finset.card_image₂_iff`. For a map with `Function.Injective2 f`, which is injective in each variable on the whole types, `Finset.card_image₂` gives the equality with no condition on $s$ and $t$. The lower bounds `Finset.card_le_card_image₂_left` and `Finset.card_le_card_image₂_right` say that $|t| \le |f(s, t)|$ when some $a \in s$ makes $f(a, \cdot)$ injective. The lemma `Finset.card_dvd_card_image₂_right` gives a divisibility: if the fibers $f(a, t)$ for $a \in s$ are pairwise disjoint or equal and each $f(a, \cdot)$ is injective, then $|t|$ divides $|f(s, t)|$.

The other lemmas of the module follow the lemmas of `Finset.image`. The names use the suffixes `_left` and `_right` for the argument that changes.

| Lean name | Statement |
|---|---|
| `Finset.image₂_empty_left` | $f(\emptyset, t) = \emptyset$ |
| `Finset.image₂_eq_empty_iff` | $f(s, t) = \emptyset \iff s = \emptyset \lor t = \emptyset$ |
| `Finset.image₂_singleton` | $f(\{a\}, \{b\}) = \{f(a, b)\}$ |
| `Finset.image₂_insert_left` | $f(\{a\} \cup s, t) = f(a, t) \cup f(s, t)$ |
| `Finset.image₂_union_left` | $f(s \cup s', t) = f(s, t) \cup f(s', t)$ |
| `Finset.image₂_inter_subset_left` | $f(s \cap s', t) \subseteq f(s, t) \cap f(s', t)$ |
| `Finset.image₂_subset` | $s \subseteq s'$ and $t \subseteq t'$ give $f(s, t) \subseteq f(s', t')$ |
| `Finset.image₂_swap` | $f(s, t) = g(t, s)$ for $g(b, a) = f(a, b)$ |
| `Finset.image₂_assoc` | an associative law for two binary images |
| `Finset.biUnion_image_left` | $f(s, t) = \bigcup_{a \in s} f(a, t)$ |

The inclusion for an intersection can be strict. For $f(a, b) = a + b$ on $\mathbb{N}$, $s = \{0\}$, $s' = \{1\}$ and $t = \{0, 1\}$, the left side is empty and the right side is $\{1\}$. With `Function.Injective2 f`, the lemma `Finset.image₂_inter_left` gives the equality. The pointwise sum and product of finsets in the volume on groups are binary images, so all these lemmas apply to them.

#### Operations on set families

Let $\alpha$ be a lattice. The module `Mathlib.Data.Finset.Sups` defines five operations on finsets of $\alpha$. The case of interest is $\alpha = \mathrm{Finset}\ \beta$, where $\sqcup$ is the union and $\sqcap$ is the intersection, so a finset of $\alpha$ is a set family.

| Notation | Elements | Membership lemma |
|---|---|---|
| $s \mathbin{\underline{\vee}} t$ | $a \sqcup b$ with $a \in s$, $b \in t$ | `Finset.mem_sups` |
| $s \mathbin{\overline{\wedge}} t$ | $a \sqcap b$ with $a \in s$, $b \in t$ | `Finset.mem_infs` |
| `s.disjSups t` or `s ○ t` | $a \sqcup b$ with $a \in s$, $b \in t$ and $a$, $b$ disjoint | `Finset.mem_disjSups` |
| `s.diffs t` | $a \setminus b$ with $a \in s$, $b \in t$ | `Finset.mem_diffs` |
| `s.compls` or `sᶜˢ` | $a^c$ with $a \in s$ | `Finset.mem_compls` |

The first two are instances of the classes `HasSups` and `HasInfs`, given by `Finset.hasSups` and `Finset.hasInfs`. They are binary images of $\sqcup$ and $\sqcap$, so the card bounds `Finset.card_sups_le` and `Finset.card_infs_le` come from the theorem above. The operations are commutative and associative: `Finset.sups_comm`, `Finset.sups_assoc`, `Finset.infs_comm` and `Finset.infs_assoc`, with `Finset.disjSups_comm` and `Finset.disjSups_assoc` for the disjoint sups in a distributive lattice. A family is closed under unions exactly when $s \mathbin{\underline{\vee}} s = s$, by `Finset.sups_eq_self`, and the power set is such a family: `Finset.powerset_sups_powerset_self`. For two lower sets, the infs is the intersection, by `Finset.infs_eq_inter`. The concrete forms for families of finsets are `Finset.union_mem_sups` and `Finset.inter_mem_infs`.

The complements turn sups into infs.

**Theorem (De Morgan for families).** In a Boolean algebra, $(s \mathbin{\underline{\vee}} t)^{c\mathrm{s}} = s^{c\mathrm{s}} \mathbin{\overline{\wedge}} t^{c\mathrm{s}}$.

*Proof.* An element $c$ is in the left side when $c^c \in s \mathbin{\underline{\vee}} t$, that is, when $c^c = a \sqcup b$ for some $a \in s$ and $b \in t$. Take complements: this is $c = a^c \sqcap b^c$. Since $a^c$ runs over $s^{c\mathrm{s}}$ and $b^c$ runs over $t^{c\mathrm{s}}$, this is the condition $c \in s^{c\mathrm{s}} \mathbin{\overline{\wedge}} t^{c\mathrm{s}}$. $\square$

This is `Finset.compls_sups`. The map $a \mapsto a^c$ is injective, so `Finset.compls` is a `Finset.map` with no repeated values, and `Finset.card_compls` gives $|s^{c\mathrm{s}}| = |s|$. The lemma `Finset.infs_compls_eq_diffs` writes the differences as an infs: $s \mathbin{\overline{\wedge}} t^{c\mathrm{s}}$ is `s.diffs t`.

#### Slices and families of a given size

A family $\mathcal{A}$ of finsets is *$r$-sized* when each member has $r$ elements. The module `Mathlib.Data.Finset.Slice` writes this as `Set.Sized r A` for a set `A` of finsets. The *slice* `Finset.slice 𝒜 r`, with the notation `𝒜 # r` in the scope `Finset`, is the family of the members of $\mathcal{A}$ with $r$ elements: `Finset.mem_slice` says $A \in \mathcal{A}_r \iff A \in \mathcal{A} \land |A| = r$, and `Finset.sized_slice` says that the slice is $r$-sized.

**Theorem (Bounds for sized families).** Let $\alpha$ be finite with $n$ elements. An $r$-sized family has at most $\binom{n}{r}$ members, and it is an antichain for $\subseteq$. Each family $\mathcal{A}$ satisfies $|\mathcal{A}| = \sum_{r \le n} |\mathcal{A}_r|$.

*Proof.* An $r$-sized family is a subset of the family of all $r$-subsets of $\alpha$. That family is `Finset.powersetCard r univ`, with $\binom{n}{r}$ members by Section 2. If $A \subseteq B$ and $|A| = |B| = r$, then $A = B$, so no two distinct members are comparable. For the sum, the slices for different $r$ are disjoint, and each member $A$ of $\mathcal{A}$ is in the slice $r = |A|$ with $|A| \le n$. So $\mathcal{A}$ is the disjoint union of its slices, and the sum rule of Section 3 gives the formula. $\square$

The three parts are `Set.Sized.card_le`, `Set.Sized.isAntichain` and `Finset.sum_card_slice`. The disjointness of the slices is `Finset.pairwiseDisjoint_slice`, and the equivalence with a subfamily of the $r$-subsets is `Finset.subset_powersetCard_univ_iff`. The family `Finset.powersetCard r s` is $r$-sized by `Set.sized_powersetCard`. The rules `Set.sized_union` and `Set.sized_iUnion` say that a union of families is $r$-sized when each family is.

#### The grade and the covering relation

In a partial order, $t$ *covers* $s$, written $s ⋖ t$, when $s < t$ and no element lies strictly between them. The module `Mathlib.Data.Finset.Grade` describes this relation `CovBy` on finsets.

**Theorem (Covers of a finset).** For finsets $s$ and $t$, $t ⋖ s$ holds exactly when $t \subseteq s$ and $|s \setminus t| = 1$.

*Proof.* If $t \subseteq s$ and $s \setminus t = \{a\}$, then a finset $u$ with $t \subsetneq u \subseteq s$ contains an element of $s \setminus t$, so it contains $a$ and equals $s$. Conversely, let $t ⋖ s$. Then $t \subsetneq s$, so $s \setminus t$ has an element $a$. The finset $t \cup \{a\}$ satisfies $t < t \cup \{a\} \le s$, so it is $s$ by the covering, and $s \setminus t = \{a\}$. $\square$

This is `Finset.covBy_iff_card_sdiff_eq_one`. The forms `Finset.covBy_iff_exists_insert` and `Finset.covBy_iff_exists_erase` say that a cover adds one element, and `Finset.covBy_insert` and `Finset.erase_covBy` give the covers of a finset. The atoms are the singletons (`Finset.isAtom_iff`), and in a finite type the coatoms are the complements of singletons (`Finset.isCoatom_iff`). So the card is a grade function: the instance `Finset.instGradeMinOrder_nat` makes `Finset α` a graded order over $\mathbb{N}$, with `Finset.grade_eq` stating that the grade of $s$ is $|s|$. The multisets have the same structure, with `Multiset.covBy_iff`, `Multiset.grade_eq` and the instance `Multiset.instGradeMinOrder`.

#### Intervals of finsets

The module `Mathlib.Data.Finset.Interval` gives the instance `Finset.instLocallyFiniteOrder`. So the intervals `Finset.Icc s t`, `Finset.Ico s t` and the others are finsets of finsets. By `Finset.Icc_eq_filter_powerset`, `Finset.Icc s t` is the family of the $u \subseteq t$ with $s \subseteq u$, and `Finset.Iic_eq_powerset` says that `Finset.Iic s` is the power set of $s$.

**Theorem (Card of an interval of finsets).** If $s \subseteq t$, then $|[s, t]| = 2^{|t| - |s|}$.

*Proof.* The map $u \mapsto s \cup u$ sends the subsets of $t \setminus s$ to $[s, t]$. It is a bijection, with inverse $v \mapsto v \setminus s$: for $u \subseteq t \setminus s$, $(s \cup u) \setminus s = u$, and for $s \subseteq v \subseteq t$, $s \cup (v \setminus s) = v$. The finset $t \setminus s$ has $|t| - |s|$ elements, so it has $2^{|t| - |s|}$ subsets. $\square$

This is `Finset.card_Icc_finset`, and the map of the proof is `Finset.Icc_eq_image_powerset`. The open and half open intervals lose one or two endpoints: `Finset.card_Ico_finset`, `Finset.card_Ioc_finset` and `Finset.card_Ioo_finset` give $2^{|t| - |s|} - 1$ and $2^{|t| - |s|} - 2$, with the truncated subtraction of $\mathbb{N}$. The module also gives tests for monotone maps out of `Finset α`: by `Finset.monotone_iff_forall_le_insert`, a map $f$ is monotone exactly when $f(s) \le f(\{a\} \cup s)$ for each $s$ and $a \notin s$. The strict and antitone forms are `Finset.strictMono_iff_forall_lt_insert` and `Finset.antitone_iff_forall_insert_le`.

#### Symmetric powers of a finset

The module `Mathlib.Data.Finset.Sym` lifts the symmetric powers `Sym2 α` and `Sym α n` of the volume on combinatorics to finsets. For a finset $s$, `Finset.sym2 s` is the finset of the unordered pairs $\{a, b\}$ with $a, b \in s$, the pair $\{a, a\}$ included. Its membership rule is `Finset.mk_mem_sym2_iff`, and `Finset.sym2_eq_image` describes it as the image of $s \times s$.

**Theorem (Unordered pairs).** If $|s| = n$, then $s$ has $\binom{n + 1}{2}$ unordered pairs with repetition.

*Proof.* The pairs $\{a, a\}$ give $n$ elements. The pairs $\{a, b\}$ with $a \ne b$ come from the $n(n - 1)$ ordered pairs off the diagonal, and each unordered pair comes from exactly two of them, so there are $n(n - 1)/2$ such pairs. The total is $n + n(n - 1)/2 = n(n + 1)/2 = \binom{n + 1}{2}$. $\square$

This is `Finset.card_sym2`, and `Finset.image_diag_union_image_offDiag` is the split of the proof into the diagonal `Finset.diag` and the rest `Finset.offDiag`. The finset `Finset.sym s n` has the multisets of size $n$ with elements in $s$: `Finset.mem_sym_iff` is its membership rule, `Finset.sym_zero` gives $\{\emptyset\}$, and `Finset.sym_succ` builds the size $n + 1$ from the size $n$ by the addition of one element. The equivalence `Finset.symInsertEquiv` splits a multiset of size $n$ over $\{a\} \cup s$ by the number $i$ of copies of $a$, and this gives the recursion of the count. The count itself, $\binom{|s| + n - 1}{n}$, is `Sym.card_sym_eq_multichoose` for a finite type, in the volume on combinatorics.

#### Common errors

1. The notations for the sups and the infs, `○`, `\\` and `ᶜˢ` are scoped. Without `open scoped FinsetFamily`, Lean does not find the instance `Finset.hasSups`, and the sups $s \mathbin{\underline{\vee}} t$ fail to elaborate.
2. The lemma `Finset.card_image₂` needs `Function.Injective2 f` on the whole types. The map $(a, b) \mapsto a + b$ on $\mathbb{N}$ is injective in each variable, but it is not injective on pairs, so it gives no card formula for $s + t$. Use `Finset.card_image₂_iff` with the injectivity on $s \times t$.
3. The intervals of finsets need the order of `Finset α`. `Finset.Icc s t` is empty when $s \not\subseteq t$, and then the formula $2^{|t| - |s|}$ is false, so `Finset.card_Icc_finset` has the hypothesis $s \subseteq t$.

### Exercises

1. (A) Compute `Finset.image₂ (· + ·) {0, 1, 2} {0, 10}` and check the bound of `Finset.card_image₂_le`. Give $s, t \subseteq \mathbb{N}$ with $|s| = |t| = 3$ and $|s + t| = 5$.
2. (A) For $\beta = \{1, 2, 3\}$, list `Finset.Icc {1} {1, 2, 3}` and check `Finset.card_Icc_finset`.
3. (B) Prove that for nonempty $s, t \subseteq \mathbb{Z}$, $|s + t| \ge |s| + |t| - 1$. Hint: list $s$ and $t$ in increasing order and find $|s| + |t| - 1$ distinct sums.
4. (B) Let $\mathcal{A}$ be a family of subsets of an $n$-set that is closed under unions and contains $\emptyset$. Prove that $\mathcal{A} \mathbin{\underline{\vee}} \mathcal{A} = \mathcal{A}$, and give such a family that is not the power set of a set.
5. (B) Prove that a chain $s_0 ⋖ s_1 ⋖ \cdots ⋖ s_k$ of finsets has $|s_k| = |s_0| + k$, and deduce that each maximal chain in the power set of an $n$-set has $n + 1$ members.
6. (C) Prove $|\mathrm{sym}(s, n)| = \binom{|s| + n - 1}{n}$ by induction on $s$ with `Finset.symInsertEquiv` and the hockey stick identity for binomial coefficients.

### Reference

<?reference?>
