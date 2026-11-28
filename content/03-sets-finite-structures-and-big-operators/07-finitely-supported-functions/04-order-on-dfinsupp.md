---
title: Order, intervals and well-foundedness of DFinsupp
kind: api
modules:
  - Mathlib.Data.DFinsupp.Order
  - Mathlib.Data.DFinsupp.Lex
  - Mathlib.Data.DFinsupp.WellFounded
  - Mathlib.Data.DFinsupp.Interval
  - Mathlib.Data.DFinsupp.Multiset
  - Mathlib.Data.DFinsupp.NeLocus
explains:
  E2: [DFinsupp.le_def, DFinsupp.single_le_iff, DFinsupp.lex_lt_of_lt, DFinsupp.Lex.wellFounded, DFinsupp.wellFoundedLT, Finset.mem_dfinsupp_iff, DFinsupp.card_Icc, DFinsupp.toMultiset_toDFinsupp, DFinsupp.mem_neLocus, DFinsupp.neLocus_eq_support_sub]
  E1: auto
families: []
requires: [V03.C03, V03.C06]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Order, intervals and well-foundedness of DFinsupp

### Overview

The previous section describes the type $\Pi_0\, i,\ \alpha\, i$ of dependent functions with finite support. When each $\alpha\, i$ carries an order, the type carries two orders. The *pointwise order* says $f \leq g$ when $f\,i \leq g\,i$ for each $i$. It is a partial order, and it is the order of multisets when each $\alpha\, i$ is $\mathbb{N}$. The *lexicographic order* compares $f$ and $g$ at the first index where they differ. It is a linear order when $\iota$ and each $\alpha\, i$ are linear orders.

Both orders appear in algebra. The pointwise order on $\Pi_0\, i,\ \mathbb{N}$ is the divisibility order on monomials, and its intervals are finite. The lexicographic order is a monomial order, and its well-foundedness gives the termination of division algorithms. This section lists the API in six modules: the pointwise order, the lexicographic order, well-foundedness, finite intervals, the link with multisets, and the set of points where two functions differ.

### The library around it

#### The pointwise order

The module `Mathlib.Data.DFinsupp.Order` gives the instances. The order is defined pointwise, and `DFinsupp.le_def` states $f \leq g \leftrightarrow \forall i,\ f\,i \leq g\,i$. The lemma `DFinsupp.coe_le_coe` states the same with the coercions to functions, and `DFinsupp.orderEmbeddingToFun` is the order embedding into $\prod_i \alpha\, i$. The coercion is monotone (`DFinsupp.coe_mono`) and strictly monotone (`DFinsupp.coe_strictMono`). The lattice operations are pointwise too: `DFinsupp.sup_apply` and `DFinsupp.inf_apply` give $(f \sqcup g)\,i = f\,i \sqcup g\,i$ and $(f \sqcap g)\,i = f\,i \sqcap g\,i$, and `DFinsupp.lattice` is the lattice instance.

Most of the module assumes that each $\alpha\, i$ is a canonically ordered additive monoid, such as $\mathbb{N}$. In this case $0$ is the least element, and the support controls the order.

| Lean name | Statement |
|---|---|
| `DFinsupp.le_iff` | $f \leq g$ if and only if $f\,i \leq g\,i$ for each $i \in \mathrm{supp}\, f$ |
| `DFinsupp.single_le_iff` | $(\mathtt{fun_0} \mid i \Rightarrow a) \leq f \leftrightarrow a \leq f\,i$ |
| `DFinsupp.support_mono` | $f \leq g$ implies $\mathrm{supp}\, f \subseteq \mathrm{supp}\, g$ |
| `bot_eq_zero` | the least element is $0$ |
| `DFinsupp.add_eq_zero_iff` | $f + g = 0 \leftrightarrow f = 0 \wedge g = 0$ |
| `DFinsupp.tsub_apply` | the truncated difference is pointwise |
| `DFinsupp.support_tsub` | $\mathrm{supp}(f - g) \subseteq \mathrm{supp}\, f$ |
| `DFinsupp.support_inf` | for linear orders, $\mathrm{supp}(f \sqcap g) = \mathrm{supp}\, f \cap \mathrm{supp}\, g$ |
| `DFinsupp.support_sup` | for linear orders, $\mathrm{supp}(f \sqcup g) = \mathrm{supp}\, f \cup \mathrm{supp}\, g$ |
| `DFinsupp.disjoint_iff` | $f$ and $g$ are disjoint if and only if their supports are disjoint |

The lemma `DFinsupp.le_iff` reduces the order to a finite check, and `DFinsupp.decidableLE` uses it to decide $f \leq g$. The truncated subtraction `DFinsupp.tsub` makes the type an ordered subtraction monoid, and the type is again canonically ordered.

#### The lexicographic order

The relation `DFinsupp.Lex r s f g` takes a relation $r$ on the indices and a relation $s\,i$ on each $\alpha\, i$. By `DFinsupp.lex_def`, it holds if there is an index $j$ such that $f$ and $g$ agree at each $d$ with $r\,d\,j$, and $s\,j\,(f\,j)\,(g\,j)$ holds. The lemma `Pi.lex_eq_dfinsupp_lex` identifies it with `Pi.Lex` on the underlying functions.

The type synonym `Lex` carries the order instances. For a linear order on $\iota$ and partial orders on each $\alpha\, i$, the order on `Lex (Π₀ i, α i)` is `DFinsupp.Lex.partialOrder`, and `DFinsupp.Lex.lt_iff` states
$$a < b \iff \exists i,\ (\forall j < i,\ a\,j = b\,j) \wedge a\,i < b\,i.$$
When each $\alpha\, i$ is a linear order, `DFinsupp.Lex.linearOrder` makes it a linear order, and `DFinsupp.Lex.decidableLT` decides it. The type synonym `Colex` compares at the last differing index instead, and `DFinsupp.Colex.lt_iff` and `DFinsupp.Colex.linearOrder` are the matching names. Addition is strictly monotone for both orders (`DFinsupp.Lex.addLeftStrictMono`). When each $\alpha\, i$ is an ordered cancellative monoid, `DFinsupp.Lex.isOrderedCancelAddMonoid` makes `Lex` one too.

The pointwise order is contained in the lexicographic order. The lemma `DFinsupp.lex_lt_of_lt` says that $x < y$ in the pointwise order implies `Pi.Lex r (· < ·) x y` for each strict order $r$ on the indices. The lemmas `DFinsupp.toLex_monotone` and `DFinsupp.toColex_monotone` state the same for the maps into `Lex` and `Colex`.

#### Well-foundedness

The module `Mathlib.Data.DFinsupp.WellFounded` proves that the lexicographic order is well founded under natural conditions. The main theorem is `DFinsupp.Lex.wellFounded`. It asks for three hypotheses:

1. no $a$ satisfies $s\,i\,a\,0$, so $0$ is minimal in each $\alpha\, i$;
2. each relation $s\,i$ is well founded;
3. the relation $r^c \sqcap (\neq)$ on the indices is well founded.

For $r = (<)$ on a linear order, the third relation is $(>)$. So the index type must have no infinite ascending chain. The reason is that the order compares at the first differing index, and the single functions $e_0 > e_1 > e_2 > \cdots$ at the indices of $\mathbb{N}$ form a descending chain in `Lex`. The variant `DFinsupp.Lex.wellFounded'` replaces the third hypothesis by well-foundedness of the reverse of $r$ for a trichotomous $r$. The instance `DFinsupp.Lex.wellFoundedLT` packages this for `Lex`, with `WellFoundedGT ι`. The instance `DFinsupp.Colex.wellFoundedLT` asks for `WellFoundedLT ι` instead, so the colexicographic order on $\Pi_0\, (n : \mathbb{N}),\ \mathbb{N}$ is well founded. For a finite index type, `DFinsupp.Lex.wellFounded_of_finite` needs no condition on $r$ beyond a strict total order, and `Pi.Lex.wellFounded` gives the same result for ordinary functions.

The proof works on single functions. The lemma `DFinsupp.Lex.acc_single` shows that each single function is accessible, `DFinsupp.Lex.acc_of_single` shows that a function is accessible if each of its single parts is, and `DFinsupp.Lex.acc` combines them. The lemma `DFinsupp.lex_fibration` is the step that splits a function into two pieces.

The same module also proves well-foundedness of the pointwise order. The theorem `DFinsupp.wellFoundedLT` says: if each $\alpha\, i$ is a preorder with no infinite descending chain and no $a < 0$, then the pointwise strict order on $\Pi_0\, i,\ \alpha\, i$ has no infinite descending chain. The index type can be arbitrary. The instance `DFinsupp.wellFoundedLT'` applies it when $0$ is the bottom element, and `DFinsupp.wellFoundedLT_of_finite` removes the condition on $0$ for a finite index type.

#### Finite intervals

The module `Mathlib.Data.DFinsupp.Interval` builds a `LocallyFiniteOrder` instance, `DFinsupp.instLocallyFiniteOrder`. The tool is `Finset.dfinsupp`: for a finite set $s$ of indices and a finite set $t\,i$ for each index, it is the finite set of functions with support in $s$ and values in $t\,i$. The lemma `Finset.mem_dfinsupp_iff` states this membership, and `Finset.card_dfinsupp` gives its size, $\prod_{i \in s} |t\,i|$.

The function `DFinsupp.rangeIcc f g` sends $i$ to the interval $[f\,i, g\,i]$, and `DFinsupp.rangeIcc_apply` states this. The interval $[f, g]$ is then `Finset.dfinsupp` over the union of the two supports, by `DFinsupp.Icc_eq`. The size follows.

| Lean name | Statement |
|---|---|
| `DFinsupp.card_Icc` | $|[f, g]| = \prod_{i \in \mathrm{supp}\, f \cup \mathrm{supp}\, g} |[f\,i, g\,i]|$ |
| `DFinsupp.card_Ico` | the same product minus $1$ |
| `DFinsupp.card_Ioc` | the same product minus $1$ |
| `DFinsupp.card_Ioo` | the same product minus $2$ |
| `DFinsupp.card_Iic` | $|(-\infty, f]| = \prod_{i \in \mathrm{supp}\, f} |(-\infty, f\,i]|$, for a canonical order |
| `DFinsupp.card_uIcc` | the size of $[f \sqcap g, f \sqcup g]$, for lattices |

For $\alpha\, i = \mathbb{N}$, `DFinsupp.card_Iic` says that $f$ has $\prod_{i \in \mathrm{supp}\, f} (f\,i + 1)$ functions below it. This is the count of divisors of a number from the exponents of its factorization.

#### Multisets

The module `Mathlib.Data.DFinsupp.Multiset` compares $\Pi_0\, (a : \alpha),\ \mathbb{N}$ with `Multiset α`. The map `DFinsupp.toMultiset` takes $f$ to the multiset with $f\,a$ copies of $a$. The map `Multiset.toDFinsupp` takes a multiset to its count function, by `Multiset.toDFinsupp_apply`. Both are additive homomorphisms. They are inverse to each other by `DFinsupp.toMultiset_toDFinsupp` and `Multiset.toDFinsupp_toMultiset`, and `Multiset.equivDFinsupp` is the additive equivalence.

The equivalence respects the order and the lattice operations. The lemmas `DFinsupp.toMultiset_le_toMultiset` and `Multiset.toDFinsupp_le_toDFinsupp` state that it respects $\leq$. The lemmas `DFinsupp.toMultiset_sup` and `DFinsupp.toMultiset_inf` send $\sqcup$ and $\sqcap$ to union and intersection. On single functions, `DFinsupp.toMultiset_single` gives `Multiset.replicate n a`, and `Multiset.toDFinsupp_support` gives the support of a count function as the set of elements of the multiset.

#### The locus where two functions differ

The finite set `DFinsupp.neLocus f g` is the set of indices where $f$ and $g$ differ. It needs decidable equality on each $\alpha\, i$. The lemma `DFinsupp.mem_neLocus` states $a \in \mathrm{neLocus}\, f\, g \leftrightarrow f\,a \neq g\,a$, and `DFinsupp.coe_neLocus` states the same as a set. The lemma `DFinsupp.neLocus_eq_empty` says that the locus is empty if and only if $f = g$, and `DFinsupp.neLocus_comm` says that it is symmetric. With $0$ on one side, `DFinsupp.neLocus_zero_left` gives the support of $f$.

In groups, `DFinsupp.neLocus_eq_support_sub` gives $\mathrm{neLocus}\, f\, g = \mathrm{supp}(f - g)$. The lemmas `DFinsupp.neLocus_add_left`, `DFinsupp.neLocus_sub_left` and `DFinsupp.neLocus_neg_neg` say that the locus does not change when the same element is added to both sides, or when both sides are negated. For a map, `DFinsupp.mapRange_neLocus_eq` keeps the locus if each component map is injective, and `DFinsupp.subset_mapRange_neLocus` gives an inclusion in general.

#### Common errors

1. The lexicographic order compares at the least differing index. On $\Pi_0\, (n : \mathbb{N}),\ \mathbb{N}$ it is not well founded, because the index type has an infinite ascending chain. Use `Colex` there, or reverse the order of the indices.
2. Most lemmas of `Mathlib.Data.DFinsupp.Order` assume a canonically ordered monoid in each component. For integer values, $0$ is not the least element, and `DFinsupp.le_iff` and `DFinsupp.single_le_iff` do not apply. Use `DFinsupp.le_def` in this case.
3. The lemma `DFinsupp.card_Icc` takes the product over the union of the two supports, not over all indices. For indices outside the union the factor is $|[0, 0]| = 1$, so the full product over a finite index type gives the same value, but a rewrite gives the union form.

### Exercises

1. (A) Prove that $f \leq g$ in $\Pi_0\, i,\ \mathbb{N}$ implies $\mathrm{supp}\, f \subseteq \mathrm{supp}\, g$, with `DFinsupp.le_def` and `DFinsupp.mem_support_iff`. Compare with `DFinsupp.support_mono`.
2. (A) Use `DFinsupp.mem_neLocus` to prove that $\mathrm{neLocus}\, f\, h \subseteq \mathrm{neLocus}\, f\, g \cup \mathrm{neLocus}\, g\, h$.
3. (B) Let $f = (\mathtt{fun_0} \mid 0 \Rightarrow 2) + (\mathtt{fun_0} \mid 1 \Rightarrow 3)$ in $\Pi_0\, (n : \mathbb{N}),\ \mathbb{N}$. Compute the number of functions below $f$ with `DFinsupp.card_Iic`, and relate the answer to the number of divisors of $2^2 \cdot 3^3$.
4. (B) Show with `DFinsupp.toMultiset_toDFinsupp` and `DFinsupp.toMultiset_le_toMultiset` that a multiset $s$ is below $t$ if and only if the count of each element in $s$ is at most its count in $t$.
5. (B) In `Lex (Π₀ n : ℕ, ℕ)`, show that the single functions $e_n = (\mathtt{fun_0} \mid n \Rightarrow 1)$ satisfy $e_{n+1} < e_n$ for each $n$, with `DFinsupp.Lex.lt_iff`. Conclude that this order is not well founded.
6. (C) Prove that the pointwise order on $\Pi_0\, (n : \mathbb{N}),\ \mathbb{N}$ is well founded, with `DFinsupp.wellFoundedLT`, and derive that each set of monomials in countably many variables has a minimal element for divisibility.

### Reference

<?reference?>
