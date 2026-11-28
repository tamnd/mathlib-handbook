---
title: The span rank, maps of finite range and the index
kind: api
modules:
  - Mathlib.Algebra.Module.SpanRank
  - Mathlib.Algebra.Module.SpanRankOperations
  - Mathlib.Algebra.Module.MinimalGenerators
  - Mathlib.Algebra.Module.LinearMap.FiniteRange
  - Mathlib.Algebra.Module.LinearMap.Index
explains:
  E2: [Submodule.spanRank, Submodule.spanFinrank, Submodule.spanRank_finite_iff_fg, Submodule.spanRank_sup_le_sum_spanRank, IsLocalRing.spanFinrank_eq_finrank_quotient, LinearMap.HasFiniteRange, LinearMap.HasNoetherianRange, LinearMap.IsQuasiInverse, LinearMap.index, LinearMap.index_comp]
  E1: auto
families: []
requires: [V05, V06]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The span rank, maps of finite range and the index

### Overview

A finitely generated module has generating sets of many sizes. The least size is a measure of the module: for a vector space it is the dimension, and for an ideal of a local ring it is the number of generators that Nakayama's lemma computes. Mathlib calls it the span rank. This section covers the span rank of a submodule as a cardinal and as a natural number, its behaviour under maps and sums, and its value over a local ring. It then treats two notions for linear maps that are "small" or "almost invertible": maps with a finitely generated range, the relation of two maps that differ by such a map, and the index $\dim \ker f - \dim \operatorname{coker} f$ of a linear map between vector spaces.

### The library around it

#### The span rank

For a submodule $p \le M$, `Submodule.spanRank p` is the least cardinal of a set $s$ with $\operatorname{span}(s) = p$. Such a set exists, since $p$ spans itself, and a set of the least size exists by the well order of the cardinals: `Submodule.exists_span_set_card_eq_spanRank`. A choice of such a set is `Submodule.generators p`, with `Submodule.span_generators` and `Submodule.generators_card`. The variant `Submodule.spanFinrank p` is a natural number: it is the span rank when $p$ is finitely generated, and it is $0$ otherwise (`Submodule.spanFinrank_of_not_fg`). The two agree on finitely generated submodules (`Submodule.FG.spanRank_eq_spanFinrank`).

**Theorem.** The span rank of $p$ is finite if and only if $p$ is finitely generated.

*Proof.* If $p$ is the span of a finite set $s$, then the span rank is at most $|s|$. If the span rank is finite, a generating set of that size is finite. $\square$

This is `Submodule.spanRank_finite_iff_fg`, stated as `p.spanRank < Cardinal.aleph0 ↔ p.FG`. For a finitely generated $p$, `Submodule.FG.exists_span_finset_card_eq_spanFinrank` gives a finite set of generators of the least size.

The basic values are $0$ for $\bot$ (`Submodule.spanRank_bot`, and `Submodule.spanRank_eq_zero_iff_eq_bot`), and $1$ for a nonzero principal submodule (`Submodule.spanFinrank_singleton`, `Submodule.spanFinrank_eq_one_iff`). The span of a set $s$ has span rank at most $|s|$ (`Submodule.spanRank_span_le_card`), with equality for a linearly independent set (`Submodule.spanRank_span_of_linearIndepOn`). For a free module, the span rank of $\top$ is the rank (`Submodule.rank_eq_spanRank_of_free`), and in general the rank is at most the span rank (`Submodule.rank_le_spanRank`).

#### Maps and sums

A linear map does not increase the span rank: the image of a generating set generates the image. This is `Submodule.spanRank_map_le`, and for an injective map the span rank is kept (`Submodule.spanRank_map_eq_of_injective`). For ideals the same holds along ring maps (`Ideal.spanRank_map_le`).

**Theorem.** For submodules $p$ and $q$, the span rank of $p \sqcup q$ is at most the sum of the span ranks of $p$ and $q$.

*Proof.* Let $s$ and $t$ be generating sets of $p$ and $q$ of the least size. The set $s \cup t$ generates $p \sqcup q$, and its cardinal is at most $|s| + |t|$. $\square$

This is `Submodule.spanRank_sup_le_sum_spanRank`. Base change does not increase the span rank (`Submodule.spanRank_baseChange_le`), and for a surjective map of rings $R \to S$ the span rank of an $S$-submodule is the same over $R$ (`Submodule.spanRank_restrictScalars_eq`).

#### Local rings and minimal generators

Over a local ring $R$ with maximal ideal $\mathfrak{m}$ and residue field $k = R / \mathfrak{m}$, Nakayama's lemma computes the span rank.

**Theorem.** Let $N$ be a finitely generated module over a local ring. Then the least number of generators of $N$ is $\dim_k N / \mathfrak{m} N$.

*Proof.* The images of a generating set of $N$ span $N / \mathfrak{m} N$ over $k$, so the number of generators is at least the dimension. Conversely, lift a basis of $N / \mathfrak{m} N$ to elements $x_1, \ldots, x_d$ of $N$, and let $N'$ be their span. Then $N' + \mathfrak{m} N = N$, so $N' = N$ by Nakayama's lemma. $\square$

This is `IsLocalRing.spanFinrank_eq_finrank_quotient`. For the maximal ideal, the vector space $\mathfrak{m} / \mathfrak{m}^2$ is the cotangent space, and `IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace` states that the least number of generators of $\mathfrak{m}$ is its dimension. The span rank is then the rank over the residue field: $\operatorname{spanFinrank}(N) = \operatorname{spanFinrank}(k \otimes N)$ (`TensorProduct.spanFinrank_top_eq_of_residueField`).

The file `Mathlib.Algebra.Module.MinimalGenerators` uses this to compare minimal presentations. Let $F_1 \to M$ and $F_2 \to M$ be surjections from free modules whose rank is the span rank of $M$. Then each map $h : F_1 \to F_2$ over $M$ is bijective (`LinearMap.bijective_of_surjective_of_rank_eq_of_of_comp_eq`). Two lists of generators of an ideal, both of the least length, differ by a linear automorphism of $R^n$ (`LinearEquiv.exists_of_length_eq_spanRank`).

#### Maps of finite range

A linear map has finite range, `LinearMap.HasFiniteRange f`, if its range is finitely generated. It has Noetherian range, `LinearMap.HasNoetherianRange f`, if its range is a Noetherian module. The second condition is stronger, and the two agree over a Noetherian ring (`LinearMap.HasFiniteRange.hasNoetherianRange`). The second condition is better behaved: the sum of two maps of Noetherian range has Noetherian range (`LinearMap.HasNoetherianRange.add`), since the range of $f + g$ is in the range of $f$ plus the range of $g$. For maps of finite range, `LinearMap.HasFiniteRange.add` needs a Noetherian ring. Both conditions are kept by composition on either side.

The maps of Noetherian range form the submodule `LinearMap.finiteRange K V V₂` of the module of linear maps. The quotient relation is `LinearMap.FiniteRangeSetoid.setoid`, written $u \approx v$ after `open LinearMap.FiniteRangeSetoid`: two maps are equivalent if their difference has Noetherian range (`LinearMap.FiniteRangeSetoid.equiv_iff_hasNoetherianRange`). Over a Noetherian ring, $u \approx v$ if and only if $u$ and $v$ agree on a submodule of finite codimension (`LinearMap.FiniteRangeSetoid.equiv_iff_eqLocus_coFG`).

Two maps $u : V_2 \to V_3$ and $v : V_3 \to V_2$ are quasi-inverses, `LinearMap.IsQuasiInverse u v`, if $u \circ v \approx \mathrm{id}$ and $v \circ u \approx \mathrm{id}$. This is the algebraic form of a Fredholm operator: a map with a quasi-inverse is invertible up to maps of finite rank. The relation is symmetric (`LinearMap.IsQuasiInverse.symm`) and is kept by composition and by $\approx$ (`LinearMap.isQuasiInverse_congr`). A linear equivalence and its inverse are quasi-inverses (`LinearEquiv.isQuasiInverse`). For a decomposition $V = S \oplus T$, the inclusion of $S$ and the projection onto $S$ are quasi-inverses if and only if $T$ is Noetherian (`LinearMap.isQuasiInverse_subtype_projectionOnto_iff`).

#### The index

For a linear map $f : M \to N$, `LinearMap.index f` is the integer $\dim \ker f - \dim (N / \operatorname{range} f)$ (`LinearMap.index_eq_finrank_sub`). The value is only meaningful when both dimensions are finite; otherwise a dimension counts as $0$. A bijective map has index $0$ (`LinearMap.index_of_bijective`), an injective map has index $-\dim \operatorname{coker} f$ (`LinearMap.index_of_injective`), and a map between finite-dimensional spaces has index $\dim M - \dim N$ (`LinearMap.index_eq_of_finiteDimensional`).

**Theorem.** Let $f : M \to N$ and $g : N \to P$ be linear maps between vector spaces with finite-dimensional kernels and cokernels. Then the index of $g \circ f$ is the sum of the indices of $g$ and $f$.

*Proof.* There is an exact sequence
$$0 \to \ker f \to \ker (g f) \to \ker g \to \operatorname{coker} f \to \operatorname{coker} (g f) \to \operatorname{coker} g \to 0.$$
The maps are the inclusion, $f$, the projection to the cokernel, $g$, and the projection. All six spaces are finite-dimensional, so the alternating sum of their dimensions is $0$. This gives $\dim \ker (g f) - \dim \operatorname{coker} (g f) = (\dim \ker f - \dim \operatorname{coker} f) + (\dim \ker g - \dim \operatorname{coker} g)$. $\square$

This is `LinearMap.index_comp`, over a division ring. The index of a projection onto a complement $S$ of $T$ is $\dim T$ (`LinearMap.index_projectionOnto`), and the index of the quotient map $M \to M / S$ is $\dim S$ (`LinearMap.index_mkQ`).

#### Common errors

1. Reading `Submodule.spanFinrank p = 0` as $p = \bot$. It is also $0$ when $p$ is not finitely generated; `Submodule.spanFinrank_eq_zero_iff_eq_bot` needs the hypothesis that $p$ is finitely generated.
2. Using `LinearMap.HasFiniteRange` where sums are needed over a ring that is not Noetherian. Use `LinearMap.HasNoetherianRange`, which is closed under sums over each ring.
3. Using `LinearMap.index` without finiteness. When the kernel or the cokernel is infinite-dimensional, the value is not the index; `LinearMap.index_comp` needs the four finiteness instances.

### Exercises

1. (A) Compute the span rank of the ideal $(2, x)$ of $\mathbb{Z}[x]$.
2. (A) Show that the span rank of $\mathbb{Z}/2 \oplus \mathbb{Z}/3$ over $\mathbb{Z}$ is $1$, while the span rank of $\mathbb{Z}/2 \oplus \mathbb{Z}/2$ is $2$.
3. (B) Show that the span rank of the maximal ideal of $k[x, y]_{(x, y)}$ is $2$, with `IsLocalRing.spanFinrank_eq_finrank_quotient`.
4. (B) Find two linear maps of finite range over a ring whose sum does not have finite range, and explain why the ring cannot be Noetherian.
5. (B) Compute the index of the shift map $(a_0, a_1, \ldots) \mapsto (0, a_0, a_1, \ldots)$ on the space of sequences, and of the shift in the other direction.
6. (C) Show that if $u$ and $v$ are quasi-inverses between vector spaces and $u$ has finite-dimensional kernel and cokernel, then the index of $v$ is minus the index of $u$.

### Reference

<?reference?>
