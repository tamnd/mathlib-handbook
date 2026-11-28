---
title: Products and pi types of modules
kind: api
modules:
  - Mathlib.LinearAlgebra.Prod
  - Mathlib.LinearAlgebra.Pi
  - Mathlib.LinearAlgebra.Quotient.Pi
  - Mathlib.LinearAlgebra.Goursat
explains:
  E2: [LinearMap.coprod, LinearMap.prod_ext, LinearMap.graph, Submodule.exists_equiv_eq_graph, LinearMap.lsum, LinearMap.pi_ext, Submodule.quotientPi, Submodule.goursat]
  E1: auto
families: []
requires: [V05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Products and pi types of modules

### Overview

The product $M \times N$ of two modules is again a module, with the operations taken in each component. The same holds for a family: the type `(i : ι) → φ i` of dependent functions is the product $\prod_i \varphi_i$. Linear algebra uses these products all the time. A pair of linear maps out of one module is one map into a product, a pair of maps out of two modules is one map out of their product, and the graph of a linear map is a submodule of a product.

This section describes the library of linear maps and submodules built on products. It starts with the binary product $M \times M_2$, then treats the family $\prod_i \varphi_i$, then quotients of products, and it ends with the lemma of Goursat, which describes all the submodules of $M \times N$ that project onto both factors. The section uses the kernels, ranges and quotients of Sections 2 and 3.

### The library around it

#### The binary product

The module `Mathlib.LinearAlgebra.Prod` gives the four structure maps of $M \times M_2$. The projections are `LinearMap.fst R M M₂` and `LinearMap.snd R M M₂`, and the injections are `LinearMap.inl R M M₂`, $x \mapsto (x, 0)$, and `LinearMap.inr R M M₂`, $y \mapsto (0, y)$. The ring and the two modules are explicit arguments, because Lean cannot infer them from a goal of the form `x.1 = ...`. The coercion lemmas `LinearMap.coe_fst`, `LinearMap.coe_inl` and their companions rewrite the maps to `Prod.fst`, `fun x ↦ (x, 0)` and so on.

The two universal properties of the product have two constructors.

1. `LinearMap.prod f g : M →ₗ[R] M₂ × M₃` sends $x$ to $(f x, g x)$. It is the map into the product.
2. `LinearMap.coprod f g : M × M₂ →ₗ[R] M₃` sends $(x, y)$ to $f x + g y$. It is the map out of the product.

The product of modules is at the same time a product and a coproduct, a fact special to additive categories. For two maps $f : M \to M_3$ and $g : M_2 \to M_4$ the map `LinearMap.prodMap f g` acts in each component. The equivalences `LinearMap.prodEquiv` and `LinearMap.coprodEquiv` state the universal properties as linear equivalences: maps into $M_2 \times M_3$ are pairs of maps, and maps out of $M \times M_2$ are pairs of maps. The ring homomorphism `LinearMap.prodMapRingHom` and the algebra homomorphism `LinearMap.prodMapAlgHom` record that `LinearMap.prodMap` respects composition of endomorphisms.

The extensionality lemma is the most useful result of the file.

**Proposition (`LinearMap.prod_ext`).** Two linear maps $f, g : M \times M_2 \to M_3$ are equal if $f \circ \mathrm{inl} = g \circ \mathrm{inl}$ and $f \circ \mathrm{inr} = g \circ \mathrm{inr}$.

*Proof.* Each $(x, y)$ is $\mathrm{inl}\,x + \mathrm{inr}\,y$. So $f(x, y) = f(\mathrm{inl}\,x) + f(\mathrm{inr}\,y) = g(\mathrm{inl}\,x) + g(\mathrm{inr}\,y) = g(x, y)$. $\square$

The lemma has the attribute `ext`, so the tactic `ext` reduces an equation of maps out of a product to two equations. The form `LinearMap.prod_ext_iff` is the equivalence.

The kernels and ranges of the four maps fit together in a table.

| Lean name | Statement |
|---|---|
| `LinearMap.ker_fst` | $\ker \mathrm{fst} = \operatorname{range} \mathrm{inr}$ |
| `LinearMap.range_inl` | $\operatorname{range} \mathrm{inl} = \ker \mathrm{snd}$ |
| `LinearMap.isCompl_range_inl_inr` | the ranges of $\mathrm{inl}$ and $\mathrm{inr}$ are complements |
| `LinearMap.ker_prod` | $\ker (f, g) = \ker f \cap \ker g$ |
| `LinearMap.range_coprod` | $\operatorname{range}(f \oplus g) = \operatorname{range} f + \operatorname{range} g$ |
| `LinearMap.range_prodMap` | $\operatorname{range}(f \times g) = \operatorname{range} f \times \operatorname{range} g$ |
| `LinearMap.range_prod_le` | $\operatorname{range}(f, g) \le \operatorname{range} f \times \operatorname{range} g$ |
| `Submodule.sup_eq_range` | $p + q$ is the range of the coproduct of the two inclusions |

The inequality `LinearMap.range_prod_le` can be strict: the range of $x \mapsto (x, x)$ is the diagonal, not the whole product. The lemma `LinearMap.range_prod_eq` gives equality when $\ker f + \ker g = M$.

For submodules $p \le M$ and $q \le M_2$, the product `p.prod q` is a submodule of $M \times M_2$. The lemmas `LinearMap.prod_eq_inf_comap` and `LinearMap.prod_eq_sup_map` give it as an intersection of preimages and as a sum of images. The order lemmas `Submodule.le_prod_iff` and `Submodule.prod_le_iff` state the two adjunctions with `map` and `comap`. The span of a union of the images of $s$ and $t$ is the product of the spans (`LinearMap.span_inl_union_inr`). The submodules `Submodule.fst R M M₂` and `Submodule.snd R M M₂` are the copies $M \times 0$ and $0 \times M_2$, and `Submodule.isCompl_fst_snd` says that they are complements.

The canonical linear equivalences are `LinearEquiv.prodComm`, `LinearEquiv.prodAssoc`, `LinearEquiv.prodProdProdComm`, `LinearEquiv.prodUnique` and `LinearEquiv.prodCongr`. The equivalence `LinearEquiv.skewProd` builds $(x, y) \mapsto (e_1 x, e_2 y + f x)$ from two equivalences and a map, a triangular change of coordinates. The equivalence `LinearMap.kerComplementEquivRange` identifies a complement of $\ker f$ with the range of $f$.

#### Graphs

The graph of $f : M \to M_2$ is the submodule `LinearMap.graph f` of $M \times M_2$, the set of pairs $(x, f x)$. The lemma `LinearMap.mem_graph_iff` unfolds membership, and `LinearMap.graph_eq_range_prod` says that the graph is the range of $(\mathrm{id}, f)$. Over a ring, `LinearMap.graph_eq_ker_coprod` gives the graph as the kernel of $(x, y) \mapsto f x - y$.

A converse picks out the graphs among all submodules.

**Proposition (`Submodule.exists_equiv_eq_graph`).** Let $G$ be a submodule of $M \times M_2$. If the first projection restricted to $G$ is bijective, then $G$ is the graph of a linear map. If both projections restricted to $G$ are bijective, then $G$ is the graph of a linear equivalence.

*Proof sketch.* Let $\pi_1 : G \to M$ be the bijective projection. The map $f = \pi_2 \circ \pi_1^{-1}$ is linear, and $G$ is its graph, because each $(x, y) \in G$ has $y = \pi_2 (\pi_1^{-1} x)$. When $\pi_2$ is also bijective, $f$ is a composition of two bijections. $\square$

The first half is `Submodule.exists_eq_graph`. The general forms with a semilinear map are `LinearMap.exists_range_eq_graph` and `LinearMap.exists_linearEquiv_eq_graph`.

#### Families of modules

The module `Mathlib.LinearAlgebra.Pi` treats the product $\prod_{i \in \iota} \varphi_i$. The projection onto the factor $i$ is `LinearMap.proj i`, and the injection is `LinearMap.single R φ i`, with `LinearMap.coe_single` as its value `Pi.single i`. A family of maps $f_i : M_2 \to \varphi_i$ gives one map `LinearMap.pi f` into the product, and `LinearEquiv.linearMapPi` states the universal property as an equivalence. A family of maps $f_i : \varphi_i \to \psi_i$ gives `LinearMap.piMap f`.

For a finite index type, the product is also a coproduct.

**Proposition (`LinearMap.lsum`).** Let $\iota$ be finite. The map $(f_i)_i \mapsto \sum_i f_i \circ \mathrm{proj}_i$ is a linear equivalence from $\prod_i \operatorname{Hom}(\varphi_i, M)$ to $\operatorname{Hom}(\prod_i \varphi_i, M)$.

*Proof sketch.* The inverse sends $F$ to the family $F \circ \mathrm{single}_i$. One composite is the identity because $\mathrm{proj}_j \circ \mathrm{single}_i$ is the identity for $i = j$ and $0$ otherwise (`LinearMap.proj_comp_single_same` and `LinearMap.proj_comp_single_ne`). The other is the identity because each $x$ is $\sum_i \mathrm{single}_i (x_i)$ (`LinearMap.sum_single_apply`). $\square$

The lemmas `LinearMap.lsum_apply`, `LinearMap.lsum_symm_apply` and `LinearMap.lsum_piSingle` evaluate the equivalence. The extensionality lemma `LinearMap.pi_ext` says that two maps out of a finite product agree when they agree on each `Pi.single i x`. The form `LinearMap.pi_ext'` compares the compositions with `LinearMap.single`. For maps out of $R^\iota$ itself, `LinearEquiv.piRing` identifies $\operatorname{Hom}(R^\iota, M)$ with $M^\iota$ through the values on the standard vectors, and `LinearMap.pi_apply_eq_sum_univ` writes $f x = \sum_i x_i f(e_i)$.

The submodule `Submodule.pi I p` is the set of $x$ with $x_i \in p_i$ for $i \in I$ (`Submodule.mem_pi`). The lemmas `Submodule.iInf_comap_proj` and `Submodule.iSup_map_single` write it as an intersection of preimages and as a supremum of images. On the side of the maps, `LinearMap.ker_pi` gives $\ker (f_i)_i = \bigcap_i \ker f_i$, and `LinearMap.iSup_range_single` says that the images of the factors span the product. For a finite set $I$ and its complement $J$, `LinearMap.iSup_range_single_eq_iInf_ker_proj` identifies the span of the factors in $I$ with the common kernel of the projections in $J$.

The file also has the linear forms of the standard equivalences of function types. The table lists the main ones.

| Lean name | Statement |
|---|---|
| `LinearEquiv.piCongrRight` | $\prod_i \varphi_i \simeq \prod_i \psi_i$ from a family of equivalences |
| `LinearEquiv.piCongrLeft` | reindexing of a product along a bijection $\iota' \simeq \iota$ |
| `LinearEquiv.piCurry` | $\prod_{(i, j)} \alpha_{i j} \simeq \prod_i \prod_j \alpha_{i j}$ |
| `LinearEquiv.sumArrowLequivProdArrow` | $M^{\alpha \sqcup \beta} \simeq M^\alpha \times M^\beta$ |
| `LinearEquiv.piOptionEquivProd` | a product over `Option ι` splits off the factor at `none` |
| `LinearEquiv.funUnique` | $M^\iota \simeq M$ for a type $\iota$ with one element |
| `LinearEquiv.finTwoArrow` | $M^{\mathrm{Fin}\,2} \simeq M \times M$ |
| `Fin.consLinearEquiv` | $M_0 \times \prod_{i < n} M_{i+1} \simeq \prod_{i < n + 1} M_i$ |

The maps `LinearMap.vecCons` and `LinearMap.vecEmpty` build maps into `Fin n → M₂` entry by entry, in the style of the notation `![a, b, c]`. The map `LinearMap.compLeft` composes each function $\iota \to M_2$ with a fixed $f : M_2 \to M_3$.

#### Quotients of products

The module `Mathlib.LinearAlgebra.Quotient.Pi` proves that a quotient of a finite product is the product of the quotients.

**Proposition (`Submodule.quotientPi`).** For a finite family of submodules $p_i \le M_i$ there is a linear equivalence $\left(\prod_i M_i\right) / \prod_i p_i \simeq \prod_i M_i / p_i$.

*Proof sketch.* The map $x \mapsto (x_i \bmod p_i)_i$ is surjective, and its kernel is $\prod_i p_i$. The first isomorphism theorem of Section 3 gives the equivalence. $\square$

The library builds the two directions by hand: `Submodule.quotientPiLift` lifts a family of maps that kill the $p_i$, and `Submodule.piQuotientLift` goes from the product of the quotients to a quotient of a target module. The lemmas `Submodule.quotientPiLift_mk` and `Submodule.piQuotientLift_single` evaluate them.

#### The lemma of Goursat

The module `Mathlib.LinearAlgebra.Goursat` classifies the submodules of a product that project onto both factors. For a submodule $L \le M \times N$, the submodule `Submodule.goursatFst L` is the set of $x$ with $(x, 0) \in L$, and `Submodule.goursatSnd L` is the set of $y$ with $(0, y) \in L$.

**Theorem (`Submodule.goursat_surjective`).** Let $L \le M \times N$ be a submodule whose projections to $M$ and to $N$ are surjective. Put $M' = \{x : (x, 0) \in L\}$ and $N' = \{y : (0, y) \in L\}$. Then the image of $L$ in $M / M' \times N / N'$ is the graph of a linear equivalence $M / M' \simeq N / N'$.

*Proof sketch.* The image $\bar L$ projects onto both quotients. If $(\bar 0, \bar y) \in \bar L$, then $(x, y) \in L$ for some $x \in M'$, and $(x, 0) \in L$, so $(0, y) \in L$ and $\bar y = 0$. So the second projection of $\bar L$ is injective, and by symmetry the first one is injective too. The criterion for graphs above gives the equivalence. $\square$

The general form `Submodule.goursat` drops the surjectivity: each submodule of $M \times N$ is the image, under inclusions of submodules, of the preimage of the graph of an equivalence between subquotients. The lemma `Submodule.goursatFst_prod_goursatSnd_le` says that $M' \times N' \le L$, and `Submodule.goursatFst_toAddSubgroup` relates the construction to the lemma of Goursat for additive subgroups.

#### Common errors

1. `LinearMap.fst`, `LinearMap.inl` and their companions take the ring and both modules as explicit arguments. Writing `LinearMap.fst` alone in a term often fails to elaborate; write `LinearMap.fst R M M₂`.
2. `LinearMap.lsum` and `LinearMap.pi_ext` need a finite index type. For an infinite family, the product is not a coproduct, and maps out of the product are not determined by the factors. The functions of finite support of Section 9, `DFinsupp` and `Finsupp`, are the right objects there.
3. `p.prod q` is the product of two submodules, a submodule of $M \times M_2$. It is not the pointwise product of submodules of an algebra, which has the notation `p * q`.

### Exercises

1. (A) Show that `(LinearMap.inl R M M₂).coprod (LinearMap.inr R M M₂)` is the identity, and find the lemma that states it.
2. (A) Compute the kernel of `LinearMap.coprod f g` for $f = g = \mathrm{id}_M$, and show that it is the antidiagonal $\{(x, -x)\}$.
3. (B) Prove `LinearMap.range_prod_eq`: if $\ker f + \ker g = M$, then the range of $(f, g)$ is $\operatorname{range} f \times \operatorname{range} g$.
4. (B) Use `Submodule.quotientPi` to compute $\mathbb{Z}^2 / (2\mathbb{Z} \times 3\mathbb{Z})$ as an abelian group.
5. (B) Let $L \le \mathbb{Q}^2$ be the diagonal. Compute `Submodule.goursatFst L` and `Submodule.goursatSnd L`, and describe the equivalence of the lemma of Goursat.
6. (C) Classify the submodules of $(\mathbb{Z}/p)^2$ that project onto both factors, with the lemma of Goursat.

### Reference

<?reference?>
