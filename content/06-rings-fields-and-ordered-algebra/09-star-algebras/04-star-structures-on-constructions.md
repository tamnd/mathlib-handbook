---
title: Star structures on the standard constructions
kind: api
modules:
  - Mathlib.Algebra.Star.Module
  - Mathlib.Algebra.Star.LinearMap
  - Mathlib.Algebra.WithConv
  - Mathlib.Algebra.Star.Pi
  - Mathlib.Algebra.Star.Prod
  - Mathlib.Algebra.Star.Free
  - Mathlib.Algebra.Star.Rat
  - Mathlib.Algebra.Star.TensorProduct
  - Mathlib.Algebra.Star.TransferInstance
  - Mathlib.Algebra.Star.BigOperators
  - Mathlib.Algebra.Star.RingQuot
  - Mathlib.Algebra.Star.Conjneg
  - Mathlib.Algebra.Star.CentroidHom
explains:
  E2: [StarModule.selfAdjointPart_add_skewAdjointPart, StarModule.decomposeProdAdjoint, LinearMap.IntrinsicStar.isSelfAdjoint_iff_map_star, Module.End.mem_eigenspace_intrinsicStar_iff, FreeAlgebra.star_ι, RingQuot.starRing, star_sum, support_conjneg, CentroidHom.starCenterIsoCentroid]
  E1: auto
families: []
requires: [V06.C01, V06.C02, V06.C08]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Star structures on the standard constructions

### Overview

Each construction of algebra has a star when its inputs have one. A product of star rings has the componentwise star, a free algebra has the star that reverses words, a quotient by a relation that respects the star has a star, and a space of linear maps between star modules has the star $f \mapsto (x \mapsto f(x^*)^*)$. This section collects these instances and the lemmas that compute with them.

The thirteen modules fall into four groups. The first group is about modules: the class `StarModule`, the decomposition of a module into self-adjoint and skew-adjoint parts, and the intrinsic star on linear maps, with the type synonym `WithConv` that carries it. The second group puts stars on products, function types, tensor products, free algebras, ring quotients, the rational numbers and types that are equivalent to a star type. The third group gives the star of a finite sum and of a finite product. The fourth group has two special constructions: the conjugate reflection `conjneg` of a function on a group, and the star on the centroid of a ring.

### The library around it

#### Star modules

The class `StarModule R A` says $(r \cdot a)^* = r^* \cdot a^*$. Its one field is `StarModule.star_smul`. For a field of scalars with the trivial star, such as $\mathbb{R}$, it says that the star of $A$ is $\mathbb{R}$-linear. For $\mathbb{C}$ with conjugation, it says that the star is conjugate linear. The module `Mathlib.Algebra.Star.Module` proves the instances for the small scalar rings: each star additive monoid is a star module over $\mathbb{Q}$, by `StarAddMonoid.toStarModuleRat`, and the lemmas `star_natCast_smul`, `star_intCast_smul` and `star_qsmul` give $(n \cdot x)^* = n \cdot x^*$ for a natural number, an integer or a rational number $n$.

The star of a star module is a semilinear equivalence. `starLinearEquiv R : A ≃ₗ⋆[R] A` is the star as a linear equivalence that is semilinear for the star of $R$. The library also uses the star module structure for the algebra map: `algebraMap_star_comm` says $\iota(r^*) = \iota(r)^*$, and `IsSelfAdjoint.algebraMap` says that the image of a self-adjoint scalar is self-adjoint. The converse, `isSelfAdjoint_algebraMap_iff`, needs an injective algebra map. The lemma `IsIdempotentElem.star_iff` says that $a^*$ is idempotent if and only if $a$ is.

#### The self-adjoint and skew-adjoint parts

Let $R$ have the trivial star, and let $2$ be invertible in $R$. Then a star module $A$ over $R$ splits into the self-adjoint part and the skew-adjoint part. The self-adjoint elements form the submodule `selfAdjoint.submodule R A`, and the skew-adjoint elements form `skewAdjoint.submodule R A`. The projections are linear maps.

| Lean name | Statement |
|---|---|
| `selfAdjointPart R` | $x \mapsto \frac{1}{2}(x + x^*)$, a linear map to the self-adjoint elements |
| `skewAdjointPart R` | $x \mapsto \frac{1}{2}(x - x^*)$, a linear map to the skew-adjoint elements |
| `selfAdjointPart_apply_coe` | the value of the self-adjoint part, as an element of $A$ |
| `StarModule.selfAdjointPart_add_skewAdjointPart` | $\frac{1}{2}(x + x^*) + \frac{1}{2}(x - x^*) = x$ |
| `selfAdjointPart_comp_subtype_selfAdjoint` | the self-adjoint part of a self-adjoint element is the element |
| `StarModule.decomposeProdAdjoint` | $A \simeq$ self-adjoint part $\times$ skew-adjoint part, as modules |

The proof of the decomposition is linear algebra. The two projections add to the identity, by `StarModule.selfAdjointPart_add_skewAdjointPart`. A self-adjoint element has skew-adjoint part $\frac{1}{2}(x - x) = 0$, and a skew-adjoint element has self-adjoint part $0$. So the map $x \mapsto (\text{self-adjoint part}, \text{skew-adjoint part})$ is a linear equivalence, with inverse $(a, b) \mapsto a + b$. For complex matrices this is the decomposition into a Hermitian and a skew-Hermitian matrix. The hypothesis on the trivial star is necessary: over $\mathbb{C}$, the self-adjoint matrices do not form a complex subspace, because $i \cdot 1$ is not self-adjoint.

#### The intrinsic star on linear maps

For star modules $E$ and $F$ over $R$, a linear map $f : E \to F$ has the *intrinsic star* $f^\dagger(x) = f(x^*)^*$. This map is again linear: $f^\dagger(r x) = f(r^* x^*)^* = (r^* f(x^*))^* = r f^\dagger(x)$. The definition is the instance `LinearMap.intrinsicStar`, and `LinearMap.intrinsicStar_apply` is its simp lemma.

The instance does not live on `E →ₗ[R] F` itself. The type of linear maps of a Hilbert space to itself already has a star, the adjoint, and the two stars are different. So the library puts the intrinsic star on the type synonym `WithConv (E →ₗ[R] F)`. The structure `WithConv A` has one field: `WithConv.toConv` builds an element from an element of $A$, and `WithConv.ofConv` goes back. The lemmas `WithConv.ofConv_toConv` and `WithConv.toConv_ofConv` say that the two maps are inverse, and `WithConv.ext` says that two elements with the same image under `WithConv.ofConv` are equal. The module `Mathlib.Algebra.WithConv` transfers the additive structure and the scalar action, with simp lemmas such as `WithConv.toConv_add`. It also gives the bundled forms `WithConv.equiv`, `WithConv.addEquiv` and `WithConv.linearEquiv`, and the maps `WithConv.congr` and `WithConv.congrLinearEquiv` between two synonyms. The name of the synonym comes from its second use: the convolution product of linear maps from a coalgebra lives on the same synonym.

| Lean name | Statement |
|---|---|
| `LinearMap.intrinsicStar_id` | $\mathrm{id}^\dagger = \mathrm{id}$ |
| `LinearMap.intrinsicStar_comp` | $(f \circ g)^\dagger = f^\dagger \circ g^\dagger$ |
| `LinearMap.IntrinsicStar.isSelfAdjoint_iff_map_star` | $f^\dagger = f \iff \forall x,\ f(x^*) = f(x)^*$ |
| `LinearMap.toMatrix'_intrinsicStar` | the matrix of $f^\dagger$ is the entrywise star of the matrix of $f$ |
| `LinearMap.IntrinsicStar.isSelfAdjoint_iff_toMatrix'` | $f^\dagger = f$ if and only if each matrix entry is self-adjoint |
| `Module.End.isUnit_intrinsicStar_iff` | $f^\dagger$ is invertible if and only if $f$ is |
| `Module.End.spectrum_intrinsicStar` | $\sigma(f^\dagger) = \sigma(f)^*$ |

The intrinsic star preserves composition in the same order, not the reverse order. So it is not a star for the composition product. The lemma `LinearMap.IntrinsicStar.isSelfAdjoint_iff_map_star` says that the self-adjoint elements are the maps that commute with the star. Proof: $f^\dagger = f$ means $f(x^*)^* = f(x)$ for each $x$, and the star of both sides gives $f(x^*) = f(x)^*$.

The eigenspaces move with the star. `Module.End.mem_eigenspace_intrinsicStar_iff` says that $x$ is an eigenvector of $f^\dagger$ for $\alpha$ if and only if $x^*$ is an eigenvector of $f$ for $\alpha^*$. Proof: $f^\dagger x = \alpha x$ means $f(x^*)^* = \alpha x$, and the star gives $f(x^*) = \alpha^* x^*$. The spectrum statement `Module.End.spectrum_intrinsicStar` follows in the same way from `Module.End.isUnit_intrinsicStar_iff`.

With the convolution product, the intrinsic star makes the linear maps from a coalgebra $C$ to an algebra $A$ a star ring, provided that the comultiplication of $C$ is compatible with the star. The lemma `LinearMap.intrinsicStar_convMul` gives $(f * g)^\dagger = g^\dagger * f^\dagger$ under this hypothesis, and `LinearMap.convIntrinsicStarRing` builds the star ring.

#### Products, functions, tensor products and free algebras

The product $R \times S$ and the function type $\forall i, f(i)$ have the componentwise star. The instances `Prod.instStarRing`, `Prod.instStarModule`, `Pi.instStarRingForall` and `Pi.instStarModuleForall` give the structures, and the trivial star goes along: `Pi.instTrivialStarForall`. The lemmas say that the usual constructions of functions commute with the star.

| Lean name | Statement |
|---|---|
| `Pi.single_star` | $\mathrm{single}_i(a^*) = \mathrm{single}_i(a)^*$ |
| `Function.update_star` | updating $h^*$ at $i$ with $a^*$ gives the star of $h$ updated with $a$ |
| `Pi.conj_apply` | the conjugate of $f$ at $i$ is the conjugate of $f(i)$ |
| `Function.star_sumElim` | $(\mathrm{elim}\ x\ y)^* = \mathrm{elim}\ x^*\ y^*$ |
| `IsStarOrtho.pi_iff` | two functions are star orthogonal if and only if each pair of values is |
| `IsStarOrtho.prod_iff` | two pairs are star orthogonal if and only if each pair of components is |
| `Units.embed_product_star` | the embedding $R^\times \to R \times R^{\mathrm{op}}$ commutes with the star |

The tensor product $A \otimes_R B$ of two star modules has the star with `TensorProduct.star_tmul`: $(x \otimes y)^* = x^* \otimes y^*$. It is a star module, by `TensorProduct.instStarModule`, and `starLinearEquiv_tensor` says that its star equivalence is the tensor product of the two star equivalences.

The free monoid has the star that reverses a word, `FreeMonoid.instStarMul`, and the generators are self-adjoint, by `FreeMonoid.star_of`. The free algebra has the same star: `FreeAlgebra.instStarRing` is the antiautomorphism that fixes each generator. Its definition comes from the universal property. The map $x \mapsto \mathrm{op}(\iota(x))$ into the opposite algebra extends to an algebra map `FreeAlgebra.starHom : FreeAlgebra R X ≃ₐ[R] (FreeAlgebra R X)ᵐᵒᵖ`. The lemma `FreeAlgebra.star_ι` says $\iota(x)^* = \iota(x)$, and `FreeAlgebra.star_algebraMap` says that the star fixes the scalars. So the star is $R$-linear, and it reverses each monomial: $(\iota(x_1) \cdots \iota(x_n))^* = \iota(x_n) \cdots \iota(x_1)$.

A quotient of a star ring has a star when the relation respects the star. `RingQuot.starRing r h` takes a relation $r$ and a proof $h$ that $r(a, b)$ implies $r(a^*, b^*)$. The key lemma is `RingQuot.Rel.star`: the ring congruence that $r$ generates also respects the star. The proof is an induction over the rules that generate the congruence. The rule for products needs the reversal: from $a \sim b$ the rule gives $a c \sim b c$, and the star gives $c^* a^* \sim c^* b^*$, which is again an instance of a rule.

The rational numbers have the trivial star, by `Rat.instStarRing` and `Rat.instTrivialStar`. In each star ring, the casts of rational numbers are self-adjoint: `star_ratCast` says $(q : R)^* = q$, and `star_nnratCast` is the same for nonnegative rationals.

A structure can travel along an equivalence. For $e : R \simeq S$ and a star on $S$, `Equiv.star e` puts the star $r \mapsto e^{-1}(e(r)^*)$ on $R$. The relatives `Equiv.involutiveStar`, `Equiv.starMul`, `Equiv.starAddMonoid`, `Equiv.starRing` and `Equiv.starModule` transfer the axioms. These are definitions, not instances, so a proof activates them with a local instance.

#### Big operators

The star is additive, so it commutes with finite sums: `star_sum` says $\left(\sum_{i \in s} f(i)\right)^* = \sum_{i \in s} f(i)^*$. The proof is an induction over $s$ with `StarAddMonoid.star_add` and `star_zero`. The star reverses products, so the same statement for products, `star_prod`, needs a commutative monoid. A finite sum of self-adjoint elements is self-adjoint, by `isSelfAdjoint_sum`. For sums over a finitely supported function, `star_finsuppSum` gives the same rule.

#### The conjugate reflection

Let $G$ be an additive group and $R$ a commutative star ring. For $f : G \to R$, `conjneg f` is the function $x \mapsto \overline{f(-x)}$, by `conjneg_apply`. In Fourier analysis on a finite abelian group, the Fourier transform of $\overline{f}$ is the conjugate reflection of the transform of $f$, and `conjneg` is the name for this operation. The map is an involution, `conjneg_conjneg`, and a ring homomorphism, `conjnegRingHom`, so `conjneg_mul` gives $\mathrm{conjneg}(f g) = \mathrm{conjneg}(f)\, \mathrm{conjneg}(g)$. The support reflects: `support_conjneg` says that the support of $\mathrm{conjneg}(f)$ is $-\mathrm{supp}(f)$, because $\overline{f(-x)} \neq 0$ if and only if $f(-x) \neq 0$. On a finite group, `sum_conjneg` says $\sum_a \mathrm{conjneg}(f)(a) = \sum_a \overline{f(a)}$, by the change of variables $a \mapsto -a$.

#### The centroid

The centroid of a non-unital ring $\alpha$ is the ring `CentroidHom α` of additive maps $T$ with $T(a b) = a T(b) = T(a) b$. Each central element $z$ gives such a map, $a \mapsto z a$. The centroid has the star $T^*(a) = T(a^*)^*$, by `CentroidHom.star_apply`. This is the intrinsic star of the previous subsection, for maps of $\alpha$ to itself. The map from the centre to the centroid is a star ring homomorphism, `CentroidHom.starCenterToCentroid`, with values `CentroidHom.starCenterToCentroid_apply`.

For a unital ring the map is an equivalence. `CentroidHom.starCenterIsoCentroid` is a star ring equivalence from `StarSubsemiring.center α` to `CentroidHom α`. Proof sketch: the inverse sends $T$ to $T(1)$. This element is central, because $T(1) a = T(a) = a T(1)$. And $T(a) = T(1 \cdot a) = T(1) a$, so $T$ is the multiplication by $T(1)$. When the centroid is commutative, `CentroidHom.starRingOfCommCentroidHom` makes it a star ring.

#### Common errors

1. The intrinsic star of a linear map is on `WithConv (E →ₗ[R] F)`, not on `E →ₗ[R] F`. A proof must wrap the map with `WithConv.toConv` before it applies the star, and unwrap the result with `WithConv.ofConv`.
2. `selfAdjointPart` and `StarModule.decomposeProdAdjoint` need the trivial star on the scalars and an inverse of $2$. Over $\mathbb{C}$, decompose over $\mathbb{R}$ with the restriction of scalars.
3. `star_prod` needs a commutative monoid. In a non-commutative star ring, the star of a product over a list is the product of the stars in the reverse order.

### Exercises

1. (A) Prove `star_sum` by induction over the finite set, with `StarAddMonoid.star_add`.
2. (A) Compute $(\iota(x) \iota(y) + 2 \iota(z))^*$ in `FreeAlgebra ℚ X`, with `FreeAlgebra.star_ι` and `FreeAlgebra.star_algebraMap`.
3. (B) Write the matrix $\begin{pmatrix} 1 & 2 \\ 0 & 3 \end{pmatrix}$ over $\mathbb{R}$ with the transpose as the star as a sum of a symmetric and a skew-symmetric matrix, and compare with `StarModule.decomposeProdAdjoint`.
4. (B) Prove that the intrinsic star of a linear map $f : E \to F$ is linear when $E$ and $F$ are star modules over a commutative star ring.
5. (B) Prove `support_conjneg` and deduce that `conjneg f` has finite support when $f$ has.
6. (C) Prove that the centroid of a unital ring is isomorphic to its centre, and give the star of the centroid in terms of the star of the centre.

### Reference

<?reference?>
