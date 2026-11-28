---
title: Submodules, vanishing and finite generation in tensor products
kind: api
modules:
  - Mathlib.LinearAlgebra.TensorProduct.Submodule
  - Mathlib.LinearAlgebra.TensorProduct.Subalgebra
  - Mathlib.LinearAlgebra.TensorProduct.Vanishing
  - Mathlib.LinearAlgebra.TensorProduct.DirectLimit
  - Mathlib.LinearAlgebra.TensorProduct.Decomposition
  - Mathlib.RingTheory.TensorProduct.DirectLimitFG
  - Mathlib.RingTheory.TensorProduct.Finite
explains:
  E2: [TensorProduct.sum_tmul_eq_zero_of_vanishesTrivially, TensorProduct.vanishesTrivially_iff_sum_tmul_eq_zero, Submodule.mulMap_range, TensorProduct.directLimitLeft, TensorProduct.exists_of_fg, DirectSum.subtype_rTensor_injective, Module.Finite.tensorProduct]
  E1: auto
families: []
requires: [V08.C01, V07.C02, V06.C08]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Submodules, vanishing and finite generation in tensor products

### Overview

An element of $M \otimes N$ is a finite sum $\sum_i m_i \otimes n_i$. Section 1 proves this, but it does not say when such a sum is zero. The relations of the construction give the answer only in an implicit form. This section collects the parts of the library that make the answer explicit and that reduce questions about $M \otimes N$ to small pieces: finitely generated submodules, direct limits and the summands of a direct sum decomposition.

A second theme is multiplication. When $M$ and $N$ are submodules of one algebra $S$, the product in $S$ gives a linear map $M \otimes N \to S$. Its image is the product submodule $M N$. Its kernel measures how far $M$ and $N$ are from being independent, and this is the start of the notion of linear disjointness. The same maps exist for subalgebras.

The section uses the functoriality of Section 2 (the maps `LinearMap.rTensor` and `LinearMap.lTensor`, and right exactness), the finite sums of Section 3, the direct sums and decompositions of Chapter 3, and the direct limits of modules. A reader who knows Sections 1 to 3 can read it at once.

### The library around it

#### Multiplication maps for submodules and subalgebras

Fix a commutative ring $R$ and an $R$-algebra $S$, not necessarily commutative. For two $R$-submodules $M, N \subseteq S$, the module `Mathlib.LinearAlgebra.TensorProduct.Submodule` defines the $R$-linear map `Submodule.mulMap M N : M ⊗[R] N →ₗ[R] S` with `Submodule.mulMap_tmul`: $m \otimes n \mapsto m n$. The lemma `Submodule.mulMap_eq_mul'_comp_mapIncl` writes it as the composite of `TensorProduct.mapIncl` with the multiplication `LinearMap.mul'` of $S$.

**Theorem.** The range of $\mu : M \otimes N \to S$, $m \otimes n \mapsto m n$, is the product submodule $M N$.

*Proof.* The submodule $M N$ is the span of the products $m n$ with $m \in M$ and $n \in N$. Each product is the image of a pure tensor, so $M N \subseteq \operatorname{range} \mu$. Pure tensors span $M \otimes N$, so their images span $\operatorname{range} \mu$, and these images lie in $M N$. $\square$

This is `Submodule.mulMap_range`. The map with the codomain restricted to $M N$ is `Submodule.mulMap'`, and `Submodule.mulMap'_surjective` restates the theorem. The other lemmas of the module describe how `Submodule.mulMap` changes with its arguments:

| Lean name | Statement |
|---|---|
| `Submodule.mulMap_comm` | for commutative $S$, `N.mulMap M` is `M.mulMap N` after the swap $n \otimes m \mapsto m \otimes n$ |
| `Submodule.mulMap_comm_of_commute` | the same when all elements of $M$ commute with all elements of $N$ |
| `Submodule.mulMap_comp_map_inclusion` | for $M' \le M$ and $N' \le N$, the map of $M' \otimes N'$ is the restriction |
| `Submodule.mulMap_map_comp_eq` | an algebra map $f : S \to T$ carries `M.mulMap N` to `(M.map f).mulMap (N.map f)` |
| `Submodule.mulMap_one_left_eq` | with $M = R \cdot 1$, the map is the isomorphism `Submodule.lTensorOne` followed by the inclusion |
| `Submodule.mulLeftMap_eq_mulMap_comp` | the map `Submodule.mulLeftMap` of a family in $M$ factors through `Submodule.mulMap` |

The isomorphisms `Submodule.lTensorOne : ↥⊥ ⊗[R] N ≃ₗ[R] N` and `Submodule.rTensorOne` are the unit laws of the tensor product, written for the submodule $\bot$ of $S$, which is the image of $R$ (as a subalgebra, turned into a submodule). They send $1 \otimes n$ to $n$ (`Submodule.lTensorOne_one_tmul`) and $r \otimes n$ to $r \cdot n$ (`Submodule.lTensorOne_tmul`). The primed versions `Submodule.lTensorOne'` and `Submodule.rTensorOne'` are the underlying linear maps. The ring $R$ can be larger than its image in $S$, so the inverse needs a proof and is not a mere unit law.

The module `Mathlib.LinearAlgebra.TensorProduct.Subalgebra` repeats the pattern for two subalgebras $A, B$ of a commutative algebra $S$. The map `Subalgebra.mulMap A B : A ⊗[R] B →ₐ[R] S` is now an algebra map, and `Subalgebra.mulMap_toLinearMap` says that its linear map is `Submodule.mulMap` of the two submodules. Its range is the subalgebra $A \sqcup B$ generated by $A$ and $B$ (`Subalgebra.mulMap_range`), because the products $a b$ span this subalgebra. The unit laws are `Subalgebra.lTensorBot` and `Subalgebra.rTensorBot`, now algebra equivalences. Finally `Algebra.TensorProduct.algEquivIncludeRange` identifies $S \otimes_R T$ with the tensor product of the ranges of the two inclusions `Algebra.TensorProduct.includeLeft` and `Algebra.TensorProduct.includeRight`. The injectivity of `Submodule.mulMap` is the definition of `Submodule.LinearDisjoint`, and `Subalgebra.LinearDisjoint` is the same notion for subalgebras.

#### When a sum of pure tensors vanishes

Let $R$ be a commutative ring and let $\sum_{i \in I} m_i \otimes n_i$ be a finite sum in $M \otimes N$. The sum *vanishes trivially* if there are finitely many $y_1, \dots, y_k \in N$ and scalars $a_{i j} \in R$ with

$$n_i = \sum_j a_{i j} y_j \quad \text{for each } i, \qquad \sum_i a_{i j} m_i = 0 \quad \text{for each } j.$$

This is `TensorProduct.VanishesTrivially R m n`, for families `m : ι → M` and `n : ι → N` over a finite type. The definition uses `Fin k` for the index of the $y_j$, and `TensorProduct.VanishesTrivially.of_fintype` accepts any finite index type. The condition is not symmetric in $M$ and $N$.

**Theorem.** A sum that vanishes trivially is zero.

*Proof.* Substitute $n_i = \sum_j a_{i j} y_j$ and move the scalars across the tensor sign:

$$\sum_i m_i \otimes n_i = \sum_i \sum_j a_{i j} m_i \otimes y_j = \sum_j \Big(\sum_i a_{i j} m_i\Big) \otimes y_j = \sum_j 0 \otimes y_j = 0. \qquad \square$$

This is `TensorProduct.sum_tmul_eq_zero_of_vanishesTrivially`. The converse is the equational criterion for vanishing.

**Theorem (Equational criterion).** If the $m_i$ generate $M$, then $\sum_i m_i \otimes n_i = 0$ if and only if the sum vanishes trivially.

*Proof sketch.* Let $G : R^I \to M$ send the basis vector $e_i$ to $m_i$. It is surjective, so its kernel $K$ gives an exact sequence $K \to R^I \to M \to 0$. By right exactness, $K \otimes N \to R^I \otimes N \to M \otimes N \to 0$ is exact. The element $\sum_i e_i \otimes n_i$ of $R^I \otimes N \cong N^I$ maps to $\sum_i m_i \otimes n_i = 0$. So it is the image of an element $\sum_j \kappa_j \otimes y_j$ of $K \otimes N$, a finite sum. Write $\kappa_j = \sum_i a_{i j} e_i$. Then $\kappa_j \in K$ says $\sum_i a_{i j} m_i = 0$, and the equality in $N^I$ says $n_i = \sum_j a_{i j} y_j$. $\square$

This is `TensorProduct.vanishesTrivially_iff_sum_tmul_eq_zero`, with the hypothesis `Submodule.span R (Set.range m) = ⊤`. The variant `TensorProduct.vanishesTrivially_iff_sum_tmul_eq_zero_of_rTensor_injective` replaces this hypothesis with the injectivity of $M' \otimes N \to M \otimes N$, where $M'$ is the span of the $m_i$. For $M = R$ it is the equational criterion for flatness, `Module.Flat.iff_forall_isTrivialRelation`. Conversely, `TensorProduct.rTensor_injective_of_forall_vanishesTrivially` says: if every vanishing sum vanishes trivially, then $M' \otimes N \to M \otimes N$ is injective for every submodule $M'$. The two directions combine to `TensorProduct.forall_vanishesTrivially_iff_forall_rTensor_injective`, and `TensorProduct.rTensor_injective_of_forall_fg_rTensor_injective` reduces the injectivity to finitely generated $M'$.

#### Direct limits

The tensor product commutes with direct limits. Let $(G_i, f_{i j})$ be a directed system of $R$-modules over a preorder, with the direct limit $\varinjlim G_i$ (`Module.DirectLimit G f`). Apply $- \otimes M$ to the system: the maps are `LinearMap.rTensor M (f i j h)`, and the instance of the module says that this is again a directed system.

**Theorem.** $(\varinjlim G_i) \otimes M \cong \varinjlim (G_i \otimes M)$, by $\iota_i(g) \otimes m \mapsto \iota_i(g \otimes m)$.

*Proof sketch.* The maps $\iota_i \otimes \mathrm{id} : G_i \otimes M \to (\varinjlim G_i) \otimes M$ are compatible with the system, so they induce `TensorProduct.fromDirectLimit` by the universal property of the limit. In the other direction, for fixed $m$ the maps $g \mapsto \iota_i(g \otimes m)$ are compatible, so they induce a map on $\varinjlim G_i$. It is linear in $m$, so the universal property of the tensor product gives `TensorProduct.toDirectLimit`. Both composites are the identity on generators of the form $\iota_i(g \otimes m)$ and $\iota_i(g) \otimes m$. $\square$

This is `TensorProduct.directLimitLeft`, with `TensorProduct.directLimitLeft_tmul_of` for the value on generators. The right version $M \otimes \varinjlim G_i \cong \varinjlim (M \otimes G_i)$ is `TensorProduct.directLimitRight`. Conceptually, $- \otimes M$ is a left adjoint, and left adjoints preserve colimits.

#### Reduction to finitely generated submodules

The module `Mathlib.RingTheory.TensorProduct.DirectLimitFG` applies this to the system of finitely generated submodules. The finitely generated submodules of $M$, ordered by inclusion, form a directed system (`Submodule.FG.directedSystem`), and $M$ is its direct limit (`Submodule.FG.directLimit`). The lemma `DirectedSystem.rTensor` tensors a directed system with $N$, and `Submodule.FG.rTensor.directLimit` gives

$$\varinjlim_{P \subseteq M,\ P \text{ f.g.}} P \otimes N \;\cong\; M \otimes N,$$

with `Submodule.FG.lTensor.directLimit` for the other side. The first consequence needs no direct limit at all.

**Theorem.** Each $u \in M \otimes N$ is in the image of $P \otimes N \to M \otimes N$ for some finitely generated submodule $P \subseteq M$.

*Proof.* Write $u = \sum_{i=1}^k m_i \otimes n_i$, and let $P$ be the span of $m_1, \dots, m_k$. Then $u$ is the image of $\sum_i m_i \otimes n_i \in P \otimes N$. $\square$

This is `TensorProduct.exists_of_fg`. The direct limit gives more: if $u \in P \otimes N$ maps to zero in $M \otimes N$, then $u$ already maps to zero in $Q \otimes N$ for some finitely generated $Q \supseteq P$. The map $P \otimes N \to M \otimes N$ need not be injective, so this is a real statement. The version for algebras is `TensorProduct.Algebra.exists_of_fg`: an element of $S \otimes N$ comes from $A \otimes N$ for a finitely generated subalgebra $A \subseteq S$. The lemma `Submodule.exists_fg_of_baseChange_eq_zero` says that an element killed by a base change $f_S$ is already killed by $f_A$ for such an $A$. These results let a proof about an arbitrary algebra assume that the algebra is finitely generated.

The module `Mathlib.RingTheory.TensorProduct.Finite` has the same reduction in a form with subtypes: `Submodule.exists_fg_le_eq_rTensor_subtype` and, for a finite set of elements at once, `Submodule.exists_fg_le_subset_range_rTensor_subtype`. It also proves that finiteness passes to tensor products.

**Theorem.** If $M$ and $N$ are finitely generated $R$-modules, then so is $M \otimes N$.

*Proof.* Let $m_1, \dots, m_a$ generate $M$ and $n_1, \dots, n_b$ generate $N$. Each $m \otimes n$ is a combination $\sum_{i, j} r_i s_j \, m_i \otimes n_j$ by bilinearity. Pure tensors span $M \otimes N$, so the $a b$ elements $m_i \otimes n_j$ generate it. $\square$

This is the instance `Module.Finite.tensorProduct`. The instance `Module.Finite.base_change` says that $A \otimes M$ is a finite $A$-module when $M$ is a finite $R$-module. The lemma `Subalgebra.finite_sup` says that $E_1 \sqcup E_2$ is finite when the subalgebras $E_1$ and $E_2$ are finite: it is the image of $E_1 \otimes E_2$ by the multiplication map. The lemma `RingHom.Finite.tensorProductMap` says that $f \otimes g$ is a finite ring map when $f$ and $g$ are finite. The file also proves that a nonzero finitely generated module $M$ has a surjection onto some $R/I$ with $I \ne R$ (`Module.exists_surjective_quotient_of_finite`). As a consequence $M \otimes M$ is nonzero, because $M \otimes M$ maps onto $R/I \otimes R/I \cong R/I$.

#### Decompositions

Let $M = \bigoplus_i M_i$ be a decomposition of $M$ into submodules, as in Chapter 3. The module `Mathlib.LinearAlgebra.TensorProduct.Decomposition` transports it along $- \otimes N$ and along base change.

**Theorem.** For each $i$, the map $M_i \otimes N \to M \otimes N$ induced by the inclusion is injective.

*Proof.* Let $\pi_i : M \to M_i$ be the projection given by the decomposition. Then $\pi_i \circ \mathrm{incl}_i = \mathrm{id}$, so $(\pi_i \otimes \mathrm{id}) \circ (\mathrm{incl}_i \otimes \mathrm{id}) = \mathrm{id}$ by functoriality. A map with a left inverse is injective. $\square$

This is `DirectSum.subtype_rTensor_injective`. The image of $M_i \otimes N$ is the submodule `DirectSum.decomposeTensor ℳ N i` of $M \otimes N$, and `DirectSum.decomposeTensorEquiv` is the isomorphism of $M_i \otimes N$ with it. These submodules again form a decomposition, `DirectSum.tensorDecomposition`, by the isomorphism `TensorProduct.directSumLeft` of Section 2. For an $R$-algebra $S$, the instance `DirectSum.Decomposition.baseChange` decomposes $S \otimes M$ into the submodules `Submodule.baseChange S (ℳ i)`, and `DirectSum.toBaseChange_bijective` says that `Submodule.toBaseChange` is an isomorphism $S \otimes M_i \cong (M_i)_S$ for a decomposition. The lemma `DirectSum.IsInternal.baseChange` gives the same for an internal direct sum, the predicate `DirectSum.IsInternal`. A graded algebra therefore stays graded after a change of scalars.

#### Common errors

1. Reading `Submodule.mulMap M N` as injective. Its range is $M N$, but its kernel can be large. For $S = \mathbb{Q}(\sqrt 2)$ and $M = N = S$ over $\mathbb{Q}$, the kernel has dimension $2$. Injectivity is the definition of linear disjointness, a hypothesis to prove.
2. Assuming that $P \otimes N \to M \otimes N$ is injective for a submodule $P \subseteq M$. This holds when $N$ is flat, not in general: $2\mathbb{Z} \otimes \mathbb{Z}/2 \to \mathbb{Z} \otimes \mathbb{Z}/2$ is zero on a nonzero module. Use the direct limit results to pass to a larger finitely generated submodule instead.
3. Swapping the roles of $M$ and $N$ in `TensorProduct.VanishesTrivially`. The scalars $a_{i j}$ express the $n_i$ through the $y_j$ and kill combinations of the $m_i$. The equational criterion needs the hypothesis on the $m_i$, the left factor.

### Exercises

1. (A) Show that $2 \otimes 1 \in 2\mathbb{Z} \otimes \mathbb{Z}/2$ is nonzero, and that its image in $\mathbb{Z} \otimes \mathbb{Z}/2$ is zero. Write the image as a sum that vanishes trivially.
2. (A) Let $S = R[x]$ and let $M = N$ be the span of $1$ and $x$. Compute the range of `Submodule.mulMap M N` and find a nonzero element of its kernel.
3. (B) Show that $\mathbb{Q} \otimes_{\mathbb{Z}} N \cong \varinjlim_n N$, where the system is $N \xrightarrow{2} N \xrightarrow{3} N \xrightarrow{4} \cdots$. Hint: $\mathbb{Q}$ is the direct limit of the modules $\frac{1}{n!}\mathbb{Z}$.
4. (B) Use the equational criterion with $M = R$ to show: if $\sum_i r_i \otimes n_i = 0$ in $R \otimes N$ and the $r_i$ generate $R$, then the family $(n_i)$ satisfies a trivial relation. Explain why this case is easy directly.
5. (B) Let $M = M_0 \oplus M_1$ and let $S$ be an $R$-algebra. Show that $S \otimes M_0 \to S \otimes M$ is injective with no flatness hypothesis on $S$.
6. (C) Let $M$ be a nonzero finitely generated module over a commutative ring. Show that $M \otimes M \ne 0$, and give a module $M$, not finitely generated, with $M \ne 0$ and $M \otimes M = 0$.

### Reference

<?reference?>
