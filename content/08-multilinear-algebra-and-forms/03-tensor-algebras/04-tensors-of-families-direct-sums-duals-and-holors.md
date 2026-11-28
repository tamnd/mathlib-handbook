---
title: Tensors of families, direct sums, duals and holors
kind: api
modules:
  - Mathlib.LinearAlgebra.PiTensorProduct
  - Mathlib.LinearAlgebra.PiTensorProduct.Generators
  - Mathlib.LinearAlgebra.PiTensorProduct.Finite
  - Mathlib.LinearAlgebra.Multilinear.DirectSum
  - Mathlib.LinearAlgebra.Multilinear.DFinsupp
  - Mathlib.LinearAlgebra.Multilinear.Finsupp
  - Mathlib.LinearAlgebra.PiTensorProduct.DirectSum
  - Mathlib.LinearAlgebra.PiTensorProduct.DFinsupp
  - Mathlib.LinearAlgebra.PiTensorProduct.Finsupp
  - Mathlib.LinearAlgebra.Multilinear.TensorProduct
  - Mathlib.LinearAlgebra.PiTensorProduct.Dual
  - Mathlib.LinearAlgebra.TensorPower.Pairing
  - Mathlib.LinearAlgebra.TensorPower.Symmetric
  - Mathlib.Data.Holor
explains:
  E2: [PiTensorProduct.submodule_span_eq_top, MultilinearMap.fromDirectSumEquiv, PiTensorProduct.ofDirectSumEquiv, PiTensorProduct.dualDistribEquiv, SymmetricPower.tprod_equiv, Holor.cprankMax_upper_bound]
  E1: auto
families: []
requires: [V08.C01, V08.C02, V07.C06]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Tensors of families, direct sums, duals and holors

### Overview

Section 1 of this chapter builds the tensor product $\bigotimes_i M_i$ of a finite family of modules and proves that the pure tensors of basis vectors form a basis. This section collects the rest of the library on this tensor product. It answers four questions. Which pure tensors span $\bigotimes_i M_i$? How does $\bigotimes_i$ act on direct sums, and on multilinear maps out of direct sums? What is the dual of $\bigotimes_i M_i$? What is the quotient of $M^{\otimes n}$ by the permutations of the factors?

The last part treats `Holor`, a concrete model of tensors as arrays of numbers. A holor of shape $(d_1, \dots, d_k)$ is a function of $k$ indices with $i_m < d_m$. The library uses it for the rank of a tensor, in the sense of the least number of rank one terms.

The section uses multilinear maps from Chapter 1, the tensor product of two modules from Chapter 2, and the dual space and dual basis from Volume 7, Chapter 6. The module `Mathlib.LinearAlgebra.PiTensorProduct` has no declarations of its own: it is a deprecated alias that imports `Mathlib.LinearAlgebra.PiTensorProduct.Basic`.

### The library around it

#### Generators

**Theorem.** Let $g_i : \gamma_i \to M_i$ be families whose images span the modules $M_i$. Then the pure tensors $\bigotimes_i g_i(j_i)$, for all choices $j \in \prod_i \gamma_i$, span $\bigotimes_i M_i$.

*Proof.* The pure tensors $\bigotimes_i m_i$ span $\bigotimes_i M_i$ by construction. Write each $m_i$ as a finite combination $\sum_k c_{i k} \, g_i(k)$. The map $\operatorname{tprod}$ is multilinear, so $\bigotimes_i m_i$ expands to a finite combination of the tensors $\bigotimes_i g_i(j_i)$. $\square$

This is `PiTensorProduct.submodule_span_eq_top`, in `Mathlib.LinearAlgebra.PiTensorProduct.Generators`. Its two consequences are extensionality lemmas. `PiTensorProduct.ext_of_span_eq_top` says that two linear maps out of $\bigotimes_i M_i$ agree when they agree on the tensors of generators, and `MultilinearMap.ext_of_span_eq_top` is the same rule for multilinear maps on $\prod_i M_i$. The same file splits off one factor: `PiTensorProduct.equivPiTensorComplSingletonTensor R M i₀` is the isomorphism
$$\bigotimes_{i} M_i \cong \Big(\bigotimes_{i \ne i_0} M_i\Big) \otimes M_{i_0},$$
with `PiTensorProduct.equivPiTensorComplSingletonTensor_tprod` on pure tensors. The inverse puts the factor $i_0$ back with `Function.subtypeNeLift`. The theorem also gives the instance `PiTensorProduct.finite` in `Mathlib.LinearAlgebra.PiTensorProduct.Finite`: a tensor product of finitely many finite modules is finite, since finite generating sets give finitely many tensors of generators.

#### Multilinear maps out of direct sums

A linear map out of $\bigoplus_j N_j$ is a family of linear maps out of the $N_j$. A multilinear map out of a product of direct sums is a family indexed by choices of one summand in each factor.

**Theorem.** Let $\iota$ be finite and let $M_i = \bigoplus_{j \in \kappa_i} M_{i j}$. Multilinear maps $\prod_i M_i \to N$ correspond to families $(f_p)$, indexed by $p \in \prod_i \kappa_i$, of multilinear maps $f_p : \prod_i M_{i, p(i)} \to N$. The map of the family is
$$f(x) = \sum_{p} f_p\big(x_{1, p(1)}, \dots, x_{n, p(n)}\big).$$

*Proof.* Given $f$, restrict it to the summands: $f_p = f \circ \prod_i \operatorname{of}_{p(i)}$. Conversely, for a family $(f_p)$ the sum is finite, because $x_{i, p(i)} = 0$ outside the finite set $\prod_i \operatorname{supp}(x_i)$, and it is multilinear because each term is. The two constructions are inverse: by multilinearity, $f(x) = f\big(\sum_{j} \operatorname{of}_j(x_{1 j}), \dots\big)$ expands into the sum over $p$, and the restriction of the sum to the summand $p$ is $f_p$, since the other terms vanish there. $\square$

This is `MultilinearMap.fromDirectSumEquiv` in `Mathlib.LinearAlgebra.Multilinear.DirectSum`, with `MultilinearMap.fromDirectSumEquiv_apply` for the formula and `MultilinearMap.fromDirectSumEquiv_symm_apply` for the restriction by `MultilinearMap.compLinearMap`. The extensionality rule `MultilinearMap.directSum_ext` checks equality on each family of summands. The module `Mathlib.LinearAlgebra.Multilinear.DFinsupp` has the same results for the type `Π₀ j, M i j` of finitely supported functions: `MultilinearMap.fromDFinsuppEquiv` and `MultilinearMap.dfinsupp_ext`, with `DFinsupp.lsingle` in the place of `DirectSum.lof`. It also has `MultilinearMap.dfinsuppFamily`, which turns a family of multilinear maps $f_p$ with values in $N_p$ into one multilinear map with values in `Π₀ p, N p`, by $x \mapsto (f_p(x_{\cdot, p(\cdot)}))_p$.

For free modules this gives coordinates. `MultilinearMap.freeDFinsuppEquiv` and its form for `Finsupp`, `MultilinearMap.freeFinsuppEquiv` in `Mathlib.LinearAlgebra.Multilinear.Finsupp`, identify multilinear maps $\prod_i R^{(\kappa_i)} \to R^{(\iota')}$ with finitely supported functions on $(\prod_i \kappa_i) \times \iota'$. The coefficient at $(p, k)$ is the coordinate $k$ of the value at the basis vectors $p$. The rule `MultilinearMap.freeFinsuppEquiv_apply` states $f(x) = \sum_p \sum_k c_{p k} \big(\prod_i x_{i, p(i)}\big) e_k$, the formula of a multilinear map in coordinates.

#### Tensor products of direct sums

**Theorem.** For finite $\iota$ there is an isomorphism
$$\bigotimes_i \bigoplus_{j \in \kappa_i} M_{i j} \cong \bigoplus_{p \in \prod_i \kappa_i} \bigotimes_i M_{i, p(i)},$$
which sends $\bigotimes_i \operatorname{of}_{p(i)}(x_i)$ to $\operatorname{of}_p\big(\bigotimes_i x_i\big)$.

*Proof sketch.* Compare the linear maps out of both sides into a module $N$. Out of the left side, they are the multilinear maps on $\prod_i \bigoplus_j M_{i j}$ by the universal property of Section 1. By the last theorem, these are families over $p$ of multilinear maps on $\prod_i M_{i, p(i)}$. By the universal property again, these are families over $p$ of linear maps out of $\bigotimes_i M_{i, p(i)}$, which are the linear maps out of the right side. The correspondence is natural in $N$, so the two modules are isomorphic, and the formula on pure tensors follows from the formula of the correspondence. $\square$

This is `PiTensorProduct.ofDirectSumEquiv`, with `PiTensorProduct.ofDirectSumEquiv_tprod_lof` and `PiTensorProduct.ofDirectSumEquiv_symm_lof_tprod`. The forms for finitely supported functions are `PiTensorProduct.ofDFinsuppEquiv` and `PiTensorProduct.ofFinsuppEquiv`, where the second reads $\bigotimes_i (\kappa_i \to_0 M_i) \cong (\prod_i \kappa_i) \to_0 \bigotimes_i M_i$. The scalar case `PiTensorProduct.ofFinsuppEquiv'` is the basis theorem of Section 1 in coordinates: by `PiTensorProduct.ofFinsuppEquiv'_tprod_single`, the tensor of the functions $r_i \, \delta_{p(i)}$ goes to $\big(\prod_i r_i\big) \delta_p$.

#### Products of multilinear maps

For multilinear maps $a$ on $\iota_1$ copies of $N$ and $b$ on $\iota_2$ copies of $N$, the map `MultilinearMap.domCoprod a b` is the multilinear map on $\iota_1 \sqcup \iota_2$ copies with values in $N_1 \otimes N_2$,
$$v \mapsto a(v|_{\iota_1}) \otimes b(v|_{\iota_2}),$$
as `MultilinearMap.domCoprod_apply` states. It is bilinear in $(a, b)$, and `MultilinearMap.domCoprod'` is the induced linear map out of the tensor product of the two spaces of multilinear maps. The forms `MultilinearMap.domCoprodDep` and `MultilinearMap.domCoprodDep'` allow a different module at each index. The rule `MultilinearMap.domCoprod_domDomCongr_sumCongr` says that the product commutes with a renaming of the indices by `MultilinearMap.domDomCongr`. The product of alternating maps `AlternatingMap.domCoprod` of Chapter 1 is this product followed by a sum over shuffles.

#### Duals

For linear forms $f_i$ on $M_i$, the product $\bigotimes_i m_i \mapsto \prod_i f_i(m_i)$ is a linear form on $\bigotimes_i M_i$. This defines a linear map `PiTensorProduct.dualDistrib` from $\bigotimes_i M_i^*$ to $(\bigotimes_i M_i)^*$, with `PiTensorProduct.dualDistrib_apply`.

**Theorem.** If the $M_i$ are finite free modules over a commutative ring and $\iota$ is finite, the map $\bigotimes_i M_i^* \to \big(\bigotimes_i M_i\big)^*$ is an isomorphism.

*Proof.* Choose bases $(b_{i k})_k$ of the $M_i$ with dual bases $(b^*_{i k})_k$. By Section 1 the tensors $\bigotimes_i b_{i, p(i)}$ form a basis of $\bigotimes_i M_i$ and the tensors $\bigotimes_i b^*_{i, p(i)}$ form a basis of $\bigotimes_i M_i^*$. The image of $\bigotimes_i b^*_{i, p(i)}$ takes the value $\prod_i b^*_{i, p(i)}(b_{i, q(i)})$ at the basis vector $q$, which is $1$ for $q = p$ and $0$ otherwise. So the map sends a basis to the dual basis, and it is bijective. $\square$

The library has the inverse with explicit bases as `PiTensorProduct.dualDistribInvOfBasis`, with the formula `PiTensorProduct.dualDistribInvOfBasis_apply` $f \mapsto \sum_p f\big(\bigotimes_i b_{i, p(i)}\big) \bigotimes_i b^*_{i, p(i)}$, and the isomorphisms `PiTensorProduct.dualDistribEquivOfBasis` and `PiTensorProduct.dualDistribEquiv`. For a tensor power, `Mathlib.LinearAlgebra.TensorPower.Pairing` has the same pairing as `TensorPower.pairingDual R M n` from $(M^*)^{\otimes n}$ to $(M^{\otimes n})^*$, and its multilinear form `TensorPower.multilinearMapToDual`. Both satisfy the rule $\langle f_1 \otimes \dots \otimes f_n, v_1 \otimes \dots \otimes v_n \rangle = \prod_i f_i(v_i)$ (`TensorPower.pairingDual_tprod_tprod`). They need no finiteness, but they are isomorphisms only in the finite free case.

#### Symmetric tensor powers

The module `Mathlib.LinearAlgebra.TensorPower.Symmetric` defines `SymmetricPower R ι M`, with the notation `Sym[R] ι M` and `Sym[R]^n M` for $\iota = \{0, \dots, n - 1\}$. It is the quotient of $\bigotimes_{\iota} M$ by the relation `SymmetricPower.Rel`, which relates $\bigotimes_i f_i$ and $\bigotimes_i f_{e(i)}$ for each permutation $e$. The quotient is taken by the additive congruence `addConGen` generated by the relation, not by a submodule, because $R$ is only a semiring. The lemma `SymmetricPower.smul` checks that scalars respect the congruence, and the instance `SymmetricPower.module` follows.

The quotient map is the linear surjection `SymmetricPower.mk R ι M` (`SymmetricPower.range_mk`), and the composite with $\operatorname{tprod}$ is the multilinear map `SymmetricPower.tprod R`, written `⨂ₛ[R] i, f i`.

**Theorem.** For each permutation $e$ of $\iota$, $\bigotimes^{s}_i f_{e(i)} = \bigotimes^{s}_i f_i$ in $\mathrm{Sym}^\iota M$.

*Proof.* The two tensors $\bigotimes_i f_i$ and $\bigotimes_i f_{e(i)}$ are related by `SymmetricPower.Rel`, so they have the same class in the quotient. $\square$

This is `SymmetricPower.tprod_equiv`, and `SymmetricPower.domDomCongr_tprod` states it as an equality of multilinear maps. By `SymmetricPower.span_tprod_eq_top` the symmetric pure tensors span. The file does not yet state the universal property for symmetric multilinear maps or the product of symmetric powers. Section 2 of this chapter has the symmetric algebra, a second model of the same objects with its product.

#### Holors

The module `Mathlib.Data.Holor` gives tensors in coordinates. For a list of natural numbers $(d_1, \dots, d_k)$, written `ds` in Lean, the type `HolorIndex ds` is the type of lists $t$ of the same length with $t_m < d_m$, and `Holor α ds` is the type of functions `HolorIndex ds → α`. A holor of shape `[d]` is a vector, of shape `[d₁, d₂]` a matrix. The instances make `Holor α ds` an additive group and an `α`-module, pointwise.

The tensor product of holors is `Holor.mul x y : Holor α (ds₁ ++ ds₂)`, with $(x \otimes y)(t) = x(t') \, y(t'')$, where $t'$ and $t''$ are the first and the last indices of $t$ (`HolorIndex.take` and `HolorIndex.drop`). It is bilinear (`Holor.mul_left_distrib`, `Holor.mul_right_distrib`, `Holor.zero_mul`). Its associativity holds only up to the equality of shapes `ds₁ ++ ds₂ ++ ds₃ = ds₁ ++ (ds₂ ++ ds₃)`, so `Holor.mul_assoc` is a heterogeneous equality and `Holor.mul_assoc0` inserts the cast `Holor.assocLeft`. A holor of shape `d :: ds` has slices `Holor.slice x i h : Holor α ds` for $i < d$, and two holors with the same slices are equal (`Holor.slice_eq`). With the unit vectors `Holor.unitVec d j`, the rule `Holor.sum_unitVec_mul_slice` writes a holor as $x = \sum_{i < d} e_i \otimes \operatorname{slice}_i(x)$.

A holor has rank one when it is a product of vectors, the predicate `Holor.CPRankMax1`. The predicate `Holor.CPRankMax n x` says that $x$ is a sum of $n$ holors of rank one, and `Holor.cprank x` is the least such $n$. This is the tensor rank, also called the canonical polyadic rank.

**Theorem.** Each holor of shape $(d_1, \dots, d_k)$ is a sum of $d_1 d_2 \cdots d_k$ holors of rank one. So its rank is at most $\prod_m d_m$.

*Proof.* Induction on the shape. A holor of the empty shape is a scalar and has rank one (`Holor.cprankMax_nil`). For the shape $d :: ds$, write $x = \sum_{i < d} e_i \otimes \operatorname{slice}_i(x)$. By induction each slice is a sum of $\prod ds$ holors of rank one. The product $e_i \otimes y$ of a vector with a rank one holor has rank one, so $e_i \otimes \operatorname{slice}_i(x)$ is again a sum of $\prod ds$ of them (`Holor.cprankMax_mul`). A sum of $d$ such terms is a sum of $d \prod ds$ holors of rank one (`Holor.cprankMax_sum`). $\square$

The statement is `Holor.cprankMax_upper_bound`, and `Holor.cprank_upper_bound` is the bound on `Holor.cprank`. The rank is subadditive by `Holor.cprankMax_add`. Unlike the rank of a matrix, the tensor rank of a holor with three or more indices is hard to compute, and the library has no algorithm for it.

#### Common errors

1. Expecting `PiTensorProduct.ofDirectSumEquiv` for an infinite index type. It needs `Finite ι`, since a pure tensor of infinitely many factors does not expand into a finite sum.
2. Expecting `PiTensorProduct.dualDistrib` to be an isomorphism in general. Only `PiTensorProduct.dualDistribEquiv` is, and it needs finite free factors over a commutative ring.
3. Writing `(x.mul y).mul z = x.mul (y.mul z)` for holors. The two sides have different types, so the statement does not type check. Use `Holor.mul_assoc0` with `Holor.assocLeft`.

### Exercises

1. (A) Write $(e_1 + e_2) \otimes (e_1 - e_2) \otimes e_1$ in the basis of $(\mathbb{Q}^2)^{\otimes 3}$, and give the values of the pairing $\langle e_1^* \otimes e_2^* \otimes e_1^*, \cdot \rangle$ on it.
2. (A) Use the theorem on tensor products of direct sums to show that $(R \oplus R)^{\otimes 2} \cong R^4$, and list the four summands.
3. (B) Show that $\mathrm{Sym}^2(\mathbb{Q}^2)$ is spanned by the three classes of $e_1 \otimes e_1$, $e_1 \otimes e_2$ and $e_2 \otimes e_2$.
4. (B) Show that the holor of shape $(2, 2)$ with entries $x_{00} = x_{11} = 1$ and $x_{01} = x_{10} = 0$ has rank $2$ over $\mathbb{Q}$. Hint: a holor of shape $(d_1, d_2)$ of rank one is a matrix of rank at most one.
5. (B) Show that the map $\bigotimes_i M_i^* \to (\bigotimes_i M_i)^*$ is not surjective for $M_1 = M_2 = \mathbb{Q}^{(\mathbb{N})}$. Hint: compare the dimensions.
6. (C) Let $\iota = \{1, 2\}$ and let $a$, $b$ be linear forms on $N$. Show that the alternating map of Chapter 1 built from $a$ and $b$ by `AlternatingMap.domCoprod` is $v \mapsto a(v_1) b(v_2) - a(v_2) b(v_1)$, up to the identification $R \otimes R = R$.

### Reference

<?reference?>
