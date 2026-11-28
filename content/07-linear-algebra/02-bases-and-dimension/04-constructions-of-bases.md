---
title: Constructions of bases and linear independence
kind: api
modules:
  - Mathlib.LinearAlgebra.LinearIndependent.Basic
  - Mathlib.LinearAlgebra.LinearIndependent.BaseChange
  - Mathlib.LinearAlgebra.Basis.Prod
  - Mathlib.LinearAlgebra.Basis.Fin
  - Mathlib.LinearAlgebra.Basis.SMul
  - Mathlib.LinearAlgebra.Basis.MulOpposite
  - Mathlib.LinearAlgebra.Basis.Submodule
  - Mathlib.LinearAlgebra.Basis.Exact
  - Mathlib.LinearAlgebra.Basis.Flag
  - Mathlib.LinearAlgebra.Basis.Cardinality
  - Mathlib.LinearAlgebra.Unimodular
explains:
  E2: [LinearIndependent.map, linearIndependent_sum, linearIndepOn_union_iff, LinearIndependent.restrict_scalars, Module.Basis.prod, Module.Basis.mkFinCons, Module.Basis.unitsSMul, Module.Basis.flag, Module.Basis.ofSplitExact, Module.IsUnimodular]
  E1: auto
families: []
requires: [V01, V03, V04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Constructions of bases and linear independence

### Overview

Section 1 defines linear independence and bases, and Section 2 proves that a vector space has a basis. In practice a proof seldom builds a basis from nothing. It starts from known bases and makes new ones: a basis of a product from bases of the factors, a basis of $R^{n+1}$ from a basis of $R^n$ and one more vector, a basis with each vector multiplied by a unit, a basis of a quotient from a basis of a larger module. This section describes the files that do these constructions, and the tests of linear independence that their proofs need.

The tests are in `Mathlib.LinearAlgebra.LinearIndependent.Basic`: images under linear maps, families indexed by a sum type, unions of sets, change of the ring of scalars. The constructions of bases are in six small files of the folder `Mathlib/LinearAlgebra/Basis`, named Prod, Fin, SMul, MulOpposite, Submodule and Exact. The module `Mathlib.LinearAlgebra.Basis.Flag` turns a basis indexed by `Fin n` into a full flag of subspaces. Two files go in the other direction and draw conclusions from a basis: `Mathlib.LinearAlgebra.Basis.Cardinality` compares the size of a basis with spanning sets and independent sets, and `Mathlib.LinearAlgebra.Unimodular` asks which vectors can be the first vector of a basis.

### The library around it

#### Tests for linear independence

A linear map keeps independence when it is injective on the span of the family.

**Proposition (`LinearIndependent.map`).** Let $v$ be linearly independent in $M$ and let $f : M \to M'$ be linear with $\operatorname{span}(v) \cap \ker f = 0$. Then $f \circ v$ is linearly independent.

*Proof.* Let $\sum_i c_i f(v_i) = 0$. Then $f(\sum_i c_i v_i) = 0$, so $\sum_i c_i v_i$ lies in the span and in the kernel. It is $0$, and independence gives $c_i = 0$ for all $i$. $\square$

The variant `LinearIndependent.map'` takes the hypothesis $\ker f = 0$, and `LinearIndependent.map_injOn` asks only that $f$ be injective on the span. The lemma `LinearMap.linearIndependent_iff` gives the equivalence for an injective $f$, and `Submodule.range_ker_disjoint` is the converse of the proposition: if $f \circ v$ is independent, then the span of $v$ meets the kernel only in $0$. The lemmas `LinearIndependent.codRestrict` and `linearIndependent_span` restrict the target of the family to a submodule that contains it.

Two independent families combine when their spans are disjoint.

**Proposition (`linearIndependent_sum`).** A family $v : \iota \oplus \iota' \to M$ is linearly independent if and only if its two parts are independent and their spans meet only in $0$.

The direction used to build families is `LinearIndependent.sum_type`. For sets of vectors, or for a family on a subset of its index type, Mathlib uses the predicate `LinearIndepOn R v s`, independence of $v$ restricted to $s$. The lemma `linearIndepOn_union_iff` is the form of the proposition for disjoint sets $s$ and $t$, and `LinearIndepOn.union` and `LinearIndepOn.id_union` are its constructors. In the other direction, `LinearIndependent.disjoint_span_image` says that disjoint sets of indices have spans that meet only in $0$, and `LinearIndependent.notMem_span_image` says that $v_x$ is not in the span of the other vectors. Two more tests are of everyday use: `linearIndepOn_singleton_iff` says that one vector is independent if and only if it is nonzero, and `linearIndepOn_of_finite` reduces independence of an infinite set to its finite subsets.

The lemmas `LinearIndependent.finCons'` and `LinearIndependent.finSnoc'` add one vector $x$ to a family indexed by `Fin n`. The hypothesis is that $c \cdot x + y = 0$ with $y$ in the span of the family forces $c = 0$. Over a field this says that $x$ is not in the span.

Independence also depends on the ring of scalars.

**Proposition (`LinearIndependent.restrict_scalars`).** Let $R \to K$ be an injective map of rings, with $K$ acting on $M$ compatibly. A family that is independent over $K$ is independent over $R$.

For example, a family of complex vectors that is independent over $\mathbb{C}$ is independent over $\mathbb{R}$. The lemma `LinearIndependent.restrict_scalars'` states the same with instances in place of the injectivity hypothesis. The module `Mathlib.LinearAlgebra.LinearIndependent.BaseChange` has one lemma, `linearIndependent_algebraMap_comp_iff`, which compares independence of a family of functions with values in $R$ and of its image in an algebra $S$. The general maps `LinearIndependent.map_of_injective_injective` and `LinearIndependent.map_of_surjective_injective` change ring and module at the same time.

Rescaling keeps independence. The lemmas `LinearIndependent.units_smul` and `LinearIndependent.units_smul_iff` multiply each vector by a unit, `LinearIndependent.group_smul` by an element of a group that acts, and `LinearIndependent.smul_of_isRightRegular` by an element that is not a zero divisor on the right.

#### New bases from old

The module `Mathlib.LinearAlgebra.Basis.Prod` makes the basis of a product.

**Definition (`Module.Basis.prod`).** For bases $b$ of $M$ indexed by $\iota$ and $b'$ of $M'$ indexed by $\iota'$, `b.prod b'` is the basis of $M \times M'$ indexed by $\iota \oplus \iota'$ with vectors $(b_i, 0)$ and $(0, b'_j)$.

The coordinates of $(x, y)$ are the coordinates of $x$ followed by those of $y$ (`Module.Basis.prod_repr_inl` and `Module.Basis.prod_repr_inr`), and the instance `Module.Free.prod` follows. The basis `Module.Basis.finTwoProd R` of $R \times R$ has the two vectors $(1, 0)$ and $(0, 1)$ (`Module.Basis.finTwoProd_zero` and `Module.Basis.finTwoProd_one`).

The module `Mathlib.LinearAlgebra.Basis.Fin` builds a basis indexed by `Fin (n + 1)` from a basis of a submodule and one vector.

**Definition (`Module.Basis.mkFinCons`).** Let $N$ be a submodule with a basis $b$ indexed by `Fin n`, and let $y \in M$. Assume that $c \cdot y + x = 0$ with $x \in N$ forces $c = 0$, and that for each $z$ some $z + c \cdot y$ lies in $N$. Then `Module.Basis.mkFinCons y b hli hsp` is a basis of $M$ with $y$ first and the vectors of $b$ after it.

The lemma `Module.Basis.coe_mkFinCons` states the vectors. The variant `Module.Basis.mkFinSnoc` puts $y$ last, and `Module.Basis.mkFinConsOfLE` and `Module.Basis.mkFinSnocOfLE` work inside a larger submodule $O$ in place of $M$. These are the steps of an induction on the rank; `Submodule.inductionOnRankAux` packages such an induction for the proof that submodules of free modules over a principal ideal domain are free, in Chapter 7.

The module `Mathlib.LinearAlgebra.Basis.SMul` rescales a basis. For units $w_i$, `Module.Basis.unitsSMul b w` is the basis with vectors $w_i \cdot b_i$, and its coordinates are divided by $w_i$ (`Module.Basis.repr_unitsSMul`). The basis `Module.Basis.isUnitSMul` takes elements with a proof that they are units. A group $G$ that acts on $M$ and commutes with $R$ acts on the bases of $M$ by `Module.Basis.instMulAction`, with `Module.Basis.smul_eq_map`; the basis `Module.Basis.groupSMul` multiplies each vector by its own element of $G$.

Three more constructions change the module.

| Lean name | Input | Output |
|---|---|---|
| `Module.Basis.mulOpposite b` | a basis of $H$ | the same basis of $H^{\mathrm{mop}}$ |
| `Module.Basis.restrictScalars b` | a basis over $S$ | a basis over $R$ of its $R$-span |
| `Module.Basis.addSubgroupOfClosure` | a basis and the subgroup it generates | a $\mathbb{Z}$-basis of that subgroup |

The first gives the instances `MulOpposite.instFree` and `MulOpposite.instFiniteDimensional` and the equation `MulOpposite.finrank`. The second is used for lattices: the $\mathbb{Z}$-span of a basis of $\mathbb{R}^n$ is a free abelian group with the same basis. The lemma `Module.Basis.mem_span_iff_repr_mem` says that a vector lies in this span if and only if its coordinates lie in the image of $R$.

The module `Mathlib.LinearAlgebra.Basis.Exact` makes a basis of a quotient. Let $0 \to K \xrightarrow{f} M \xrightarrow{g} P \to 0$ be exact with a retraction $s$ of $f$. Take a basis $v$ of $M$ and two maps $a : \kappa \to \iota$ and $b : \sigma \to \iota$ whose ranges cover $\iota$. If $s(v_{a(i)}) = 0$ for each $i$ and the vectors $s(v_{b(j)})$ are independent, then `Module.Basis.ofSplitExact` is the basis $g(v_{a(i)})$ of $P$. The two halves of the proof are the separate lemmas `LinearIndependent.linearIndependent_of_exact_of_retraction` and `Submodule.top_le_span_of_exact_of_retraction`.

#### Flags

Let $b$ be a basis of $M$ indexed by `Fin n`. The flag of $b$ is the chain of the spans of its first vectors.

**Definition (`Module.Basis.flag`).** For $k \le n$, `b.flag k` is the span of $b_0, \dots, b_{k-1}$.

The flag starts at $0$ (`Module.Basis.flag_zero`), ends at $M$ (`Module.Basis.flag_last`), and grows by one line at each step (`Module.Basis.flag_succ`). A vector lies in `b.flag k` if and only if its coordinates from $k$ on vanish (`Module.Basis.mem_flag_iff_repr_eq_zero`). Over a nontrivial ring the flag is strictly monotone (`Module.Basis.flag_strictMono`). Over a division ring each step is a covering relation (`Module.Basis.flag_covBy`), the range is a maximal chain of subspaces (`Module.Basis.isMaxChain_range_flag`), and `Module.Basis.toFlag` bundles it as a term of type `Flag (Submodule K V)`. The lemma `Module.Basis.flag_le_ker_dual` relates the flag to the dual basis of Chapter 6. Triangular matrices are the matrices of the endomorphisms that preserve the flag of the standard basis.

#### Size of a basis and unimodular vectors

The module `Mathlib.LinearAlgebra.Basis.Cardinality` compares a basis with other families. The lemma `basis_finite_of_finite_spans` says that a module spanned by a finite set has only finite bases, over any nontrivial ring. The lemma `infinite_basis_le_maximal_linearIndependent` says that an infinite basis has at most the cardinality of each maximal independent family. Its proof uses `union_support_maximal_linearIndependent_eq_range_basis`: the supports of the coordinates of a maximal independent family cover the index set of the basis.

The module `Mathlib.LinearAlgebra.Unimodular` defines unimodular vectors.

**Definition (`Module.IsUnimodular`).** A vector $v$ of an $R$-module is unimodular when some linear functional $f$ has $f(v) = 1$ (`Module.isUnimodular_iff`).

In a free module, $v$ is unimodular if and only if its coordinates in a basis generate the unit ideal (`Module.Basis.isUnimodular_iff_span_repr_eq_top`). In $\mathbb{Z}^n$ this means that the greatest common divisor of the coordinates is $1$. Each vector of a basis is unimodular, since its coordinate functional takes the value $1$. In rank $2$ the converse holds: `Module.IsUnimodular.exists_basis_zero_eq` gives a basis whose first vector is $v$. The proof builds the second vector from a relation $a v_1 + b v_2 = 1$.

#### Common errors

1. `LinearIndependent.map` needs the disjointness of the span and the kernel, not of the family and the kernel. Each vector $v_i$ can be outside $\ker f$ while a combination of them lies in it.
2. The constructions in `Mathlib.LinearAlgebra.Basis.Fin` need the hypotheses in the form with $c \cdot y + x = 0$. Over a field, derive them from $y \notin N$; over a ring, $y \notin N$ is not enough, as $y = 2$ and $N = 0$ in $\mathbb{Z}$ show.
3. `Module.Basis.flag` is indexed by `Fin (n + 1)`, with `b.flag 0 = ⊥`. The index $k$ counts the vectors in the span, so `b.flag k` does not contain $b_k$.

### Exercises

1. (A) Show that the family $(1, 0), (1, 1)$ in $\mathbb{Q} \times \mathbb{Q}$ is linearly independent with `linearIndependent_sum`, splitting it as two families of one vector.
2. (A) Describe the vectors of `(Module.Basis.finTwoProd ℚ).prod (Module.Basis.finTwoProd ℚ)` as elements of $(\mathbb{Q} \times \mathbb{Q}) \times (\mathbb{Q} \times \mathbb{Q})$.
3. (B) Let $f : \mathbb{Q}^3 \to \mathbb{Q}$ be the sum of the coordinates. Find two independent vectors whose images under $f$ are dependent, and check that `LinearIndependent.map` does not apply.
4. (B) Prove that $(2, 3)$ is a unimodular vector of $\mathbb{Z}^2$ and complete it to a basis.
5. (B) For the standard basis $e$ of $\mathbb{Q}^3$, list the subspaces `e.flag k` for $k = 0, 1, 2, 3$, and show that $(1, 2, 0) \in$ `e.flag 2`.
6. (C) Prove that $(2, 0)$ is not unimodular in $\mathbb{Z}^2$, and that no basis of $\mathbb{Z}^2$ contains it.

### Reference

<?reference?>
