---
title: Convolution and Hopf algebras
kind: api
modules:
  - Mathlib.RingTheory.Coalgebra.Convolution
  - Mathlib.RingTheory.Bialgebra.Convolution
  - Mathlib.RingTheory.HopfAlgebra.Basic
  - Mathlib.RingTheory.HopfAlgebra.Convolution
  - Mathlib.RingTheory.HopfAlgebra.Quotient
  - Mathlib.RingTheory.HopfAlgebra.TensorProduct
explains:
  E2: [LinearMap.algHom_comp_convMul_distrib, LinearMap.convMul_comp_coalgHom_distrib, HopfAlgebra.antipode_one, HopfAlgebra.counit_antipode, HopfAlgebra.antipode_mul_antidistrib, HopfAlgebra.ofAntipodeOfAdjoin, AlgHom.convGroup]
  E1: auto
families: []
requires: [V08.C02, V06.C08, V05.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Convolution and Hopf algebras

### Overview

Let $C$ be a coalgebra and $A$ an algebra over $R$. The linear maps $C \to A$ form an algebra under *convolution*:
$$f * g = \mu_A \circ (f \otimes g) \circ \Delta_C, \qquad (f * g)(c) = \sum f(c_{(1)})\, g(c_{(2)}),$$
with the unit $\eta_A \circ \varepsilon_C$. The dual $C^* = \mathrm{Hom}(C, R)$ of a coalgebra is the case $A = R$. For a bialgebra $A$, the identity map $A \to A$ is an element of the convolution algebra $\mathrm{End}(A)$. A *Hopf algebra* is a bialgebra in which this element is invertible. Its inverse $S$ is the *antipode*, and it satisfies
$$\sum S(a_{(1)})\, a_{(2)} = \varepsilon(a) \cdot 1 = \sum a_{(1)}\, S(a_{(2)}).$$
The group algebra $R[G]$ of a group, with $S(g) = g^{-1}$, is the model example, and Section 4 treats it.

This section treats the convolution product, the convolution monoids of algebra maps and bialgebra maps, the class of Hopf algebras, the main properties of the antipode, and the quotients and tensor products of Hopf algebras. Most proofs in the section are computations in a convolution algebra: an identity between maps follows when both sides are inverses of the same element.

### The library around it

#### The type synonym for convolution

The type `C →ₗ[R] A` already has a multiplication when $C = A$: the composition of `Module.End`. To avoid the clash, the library puts the convolution product on the type synonym `WithConv (C →ₗ[R] A)`. The maps `WithConv.toConv` and `WithConv.ofConv` move between the two types, and `WithConv.ofConv_toConv` and `WithConv.toConv_ofConv` cancel them. In statements, `toConv f * toConv g` is the convolution of $f$ and $g$, and `(f * g).ofConv` is the underlying linear map.

#### The convolution algebra

The definitions and their pointwise forms are:

| Lean name | Statement |
| --- | --- |
| `LinearMap.convMul_def` | $f * g = \mu \circ (f \otimes g) \circ \Delta$ |
| `LinearMap.convMul_apply` | $(f * g)(c) = \mu((f \otimes g)(\Delta c))$ |
| `Coalgebra.Repr.convMul_apply` | $(f * g)(c) = \sum_i f(c_{(1), i})\, g(c_{(2), i})$ for a representation of $\Delta c$ |
| `LinearMap.convOne_def` | $1 = \eta \circ \varepsilon$ |
| `LinearMap.convOne_apply` | $1(c) = \varepsilon(c) \cdot 1$ |

The instance `LinearMap.convSemiring` makes `WithConv (C →ₗ[R] A)` a semiring when $C$ is a coalgebra and $A$ an algebra. Associativity follows from the coassociativity of $\Delta$ and the associativity of $\mu$, and the unit laws follow from the counit axioms. The instances `LinearMap.convRing` and `LinearMap.convAlgebra` add negation and scalars. When $C$ is cocommutative and $A$ is commutative, `LinearMap.convCommSemiring` and `LinearMap.convCommRing` make the product commutative. For a nonunital algebra $A$, the library has the variants `LinearMap.convNonUnitalSemiring` and `LinearMap.convNonUnitalRing`. For $C = R$, convolution is the product of $A$: `LinearMap.toSpanSingleton_convMul_toSpanSingleton` says that the maps $r \mapsto r x$ and $r \mapsto r y$ have the convolution $r \mapsto r x y$.

Convolution is natural in both variables. If $h : A \to B$ is an algebra map, then
$$h \circ (f * g) = (h \circ f) * (h \circ g),$$
the lemma `LinearMap.algHom_comp_convMul_distrib`. Proof: $h \circ \mu_A = \mu_B \circ (h \otimes h)$, and $(h \otimes h) \circ (f \otimes g) = (h \circ f) \otimes (h \circ g)$. If $k : D \to C$ is a coalgebra map, then $(f * g) \circ k = (f \circ k) * (g \circ k)$, the lemma `LinearMap.convMul_comp_coalgHom_distrib`, by the dual argument with $\Delta_C \circ k = (k \otimes k) \circ \Delta_D$. So composition gives algebra maps of convolution algebras, `AlgHom.convPostcomp` and `CoalgHom.convPrecomp`, which are injective for an injective $h$ and a surjective $k$ (`AlgHom.convPostcomp_injective`, `CoalgHom.convPrecomp_injective`). The lemma `CoalgHom.convPrecomp_comp_convPostcomp` states that the two operations commute, and `TensorProduct.map_convMul_map` computes the convolution of two maps of the form $f \otimes g$ on a tensor product of coalgebras.

#### Convolution of algebra maps and bialgebra maps

Let $C$ be a bialgebra and $A$ a commutative algebra. Then the convolution of two algebra maps $C \to A$ is an algebra map, because the multiplication $A \otimes A \to A$ of a commutative algebra is an algebra map. The library puts a monoid structure on `WithConv (C →ₐ[R] A)` with the instance `AlgHom.instMonoidWithConv`, and a commutative monoid structure with `AlgHom.instCommMonoidWithConv` when $C$ is cocommutative. In this form `AlgHom.convMul_apply` writes $f * g$ as `Algebra.TensorProduct.lift` of $f$ and $g$ applied to $\Delta c$, and `AlgHom.toLinearMap_convMul` says that the coercion to linear maps sends this product to the convolution of the previous part.

If $C$ is a cocommutative bialgebra and $A$ a commutative bialgebra, bialgebra maps $C \to A$ also form a commutative monoid, `BialgHom.instCommMonoidWithConv`. The product is the composite
$$C \xrightarrow{\Delta} C \otimes C \xrightarrow{f \otimes g} A \otimes A \xrightarrow{\mu} A$$
of three bialgebra maps, by `BialgHom.convMul_def` with `Bialgebra.comulBialgHom` and `Bialgebra.mulBialgHom` from Section 2.

#### Hopf algebras

The class `HopfAlgebraStruct R A` extends `Bialgebra R A` with one linear map, the field `HopfAlgebraStruct.antipode`, which code writes as `antipode R`. The class `HopfAlgebra R A` adds the two axioms `HopfAlgebra.mul_antipode_rTensor_comul` and `HopfAlgebra.mul_antipode_lTensor_comul`:
$$\mu \circ (S \otimes \mathrm{id}) \circ \Delta = \eta \circ \varepsilon = \mu \circ (\mathrm{id} \otimes S) \circ \Delta.$$
The Sweedler forms are `HopfAlgebra.sum_antipode_mul_eq_algebraMap_counit` and `HopfAlgebra.sum_mul_antipode_eq_algebraMap_counit`, with the variants `HopfAlgebra.sum_antipode_mul_eq_smul` and `HopfAlgebra.sum_mul_antipode_eq_smul` that write $\varepsilon(a) \cdot 1$ as a scalar product. In the convolution algebra, the axioms read $S * \mathrm{id} = 1 = \mathrm{id} * S$: these are `LinearMap.antipode_mul_id` and `LinearMap.id_mul_antipode`. Since an inverse in a monoid is unique, a bialgebra has at most one antipode, and a Hopf algebra structure is a property of the bialgebra.

Two constructors build an instance from this point of view. `HopfAlgebra.ofConvInverse` takes a linear map and the two equations in the convolution algebra. `HopfAlgebra.ofAlgHom` takes an algebra map $S$ of a commutative bialgebra and the two equations as equalities of algebra maps. The ring $R$ is a Hopf algebra by `CommSemiring.toHopfAlgebra`, with the identity as antipode (`CommSemiring.antipode_eq_id`).

#### Properties of the antipode

The first two properties follow at once from the axioms. Since $\Delta(1) = 1 \otimes 1$, the axiom gives $S(1) \cdot 1 = \varepsilon(1) \cdot 1 = 1$, so $S(1) = 1$ (`HopfAlgebra.antipode_one`). Apply $\varepsilon$ to $\sum S(a_{(1)})\, a_{(2)} = \varepsilon(a) \cdot 1$. The counit is multiplicative, so
$$\varepsilon(a) = \sum \varepsilon(S(a_{(1)}))\, \varepsilon(a_{(2)}) = \varepsilon\Big(S\big(\sum a_{(1)}\, \varepsilon(a_{(2)})\big)\Big) = \varepsilon(S(a)).$$
This is `HopfAlgebra.counit_antipode`, and `HopfAlgebra.counit_comp_antipode` is the same equation of maps.

The antipode reverses products: $S(ab) = S(b)\, S(a)$, the theorem `HopfAlgebra.antipode_mul_antidistrib`. Proof: work in the convolution algebra of linear maps $A \otimes A \to A$, where $A \otimes A$ has the coalgebra structure of Section 1. Let $F(a \otimes b) = S(ab)$ and $G(a \otimes b) = S(b) S(a)$. Then
$$(F * \mu)(a \otimes b) = \sum S(a_{(1)} b_{(1)})\, a_{(2)} b_{(2)} = \sum S((ab)_{(1)})\, (ab)_{(2)} = \varepsilon(ab) \cdot 1,$$
because $\Delta(ab) = \Delta(a)\Delta(b)$. So $F$ is a left inverse of $\mu$. In the same way
$$(\mu * G)(a \otimes b) = \sum a_{(1)} b_{(1)} S(b_{(2)}) S(a_{(2)}) = \varepsilon(b) \sum a_{(1)} S(a_{(2)}) = \varepsilon(a)\varepsilon(b) \cdot 1,$$
so $G$ is a right inverse of $\mu$. A left inverse and a right inverse in a monoid are equal, so $F = G$. The same theorem in the language of maps is `HopfAlgebra.antipode_comp_mul_comp_comm`. So $S$ is an algebra map $A \to A^{\mathrm{mop}}$, bundled as `HopfAlgebra.antipodeAlgHomOp`. For a commutative $A$ the antipode is an algebra map $A \to A$, `HopfAlgebra.antipodeAlgHom`, with `HopfAlgebra.antipode_mul_distrib`. The dual statement for the comultiplication is `LinearMap.comul_right_inv`: in the convolution algebra of maps $A \to A \otimes A$, the map $\Delta \circ S$ is a right inverse of $\Delta$.

#### Constructing antipodes from generators

To check that an algebra map $S : A \to A^{\mathrm{mop}}$ is an antipode, it is enough to check the two axioms on a set $X$ that generates $A$ as an algebra. This is `HopfAlgebra.ofAntipodeOfAdjoin`, with the steps `HopfAlgebra.convMul_id_eq_one_of_adjoin_eq_top` and `HopfAlgebra.id_convMul_eq_one_of_adjoin_eq_top`. Proof: the set of $a$ with $\sum S(a_{(1)})\, a_{(2)} = \varepsilon(a) \cdot 1$ is a submodule that contains $1$. It is closed under products, because $S$ reverses products and $\Delta$ is multiplicative:
$$\sum S(a_{(1)} b_{(1)})\, a_{(2)} b_{(2)} = \sum S(b_{(1)})\, \big(\sum S(a_{(1)})\, a_{(2)}\big)\, b_{(2)} = \varepsilon(a) \sum S(b_{(1)})\, b_{(2)} = \varepsilon(a)\varepsilon(b) \cdot 1.$$
So it is a subalgebra that contains $X$, and it is all of $A$. The constructor `HopfAlgebra.ofSurjective` transfers an antipode along a surjective bialgebra map $f : A \to B$ that commutes with given maps $S_A$ and $S_B$.

#### The group of points

Let $A$ be a commutative Hopf algebra and $C$ a commutative algebra. The algebra maps $A \to C$ form a group under convolution, `AlgHom.convGroup`, with the inverse $f^{-1} = f \circ S$ (`AlgHom.convInv`). Proof: $f \circ S$ is an algebra map because $S$ is one. By the naturality of convolution,
$$(f \circ S) * f = f \circ (S * \mathrm{id}) = f \circ \eta \circ \varepsilon = \eta_C \circ \varepsilon,$$
the unit, and in the same way $f * (f \circ S)$ is the unit. The lemmas `AlgHom.antipode_id_cancel` and `AlgHom.id_antipode_cancel` are the case $f = \mathrm{id}$, and `AlgHom.counitAlgHom_comp_antipodeAlgHom` is the property $\varepsilon \circ S = \varepsilon$ as algebra maps. If $A$ is also cocommutative, the group is commutative (`AlgHom.instCommGroupWithConvOfIsCocomm`). This is the algebraic form of an affine group scheme: $A$ is its ring of functions, and $C \mapsto \mathrm{Hom}(A, C)$ gives the points with values in $C$.

#### Quotients and tensor products

A *Hopf ideal* is a biideal $I$ with $S(I) \subseteq I$. The class is `Ideal.IsHopfIdeal R I`, with the field `Ideal.IsHopfIdeal.antipode_mem` and the criterion `Ideal.isHopfIdeal_iff`. With `I.IsTwoSided`, the quotient $A/I$ is a Hopf algebra (`HopfAlgebra.Quotient.instQuotientIdeal`). The proof is `HopfAlgebra.ofSurjective` for the projection, and `HopfAlgebra.Quotient.antipode_mk` gives $S([a]) = [S(a)]$.

The tensor product of two Hopf algebras is a Hopf algebra, `TensorProduct.instHopfAlgebra`, with $S(a \otimes b) = S(a) \otimes S(b)$ (`TensorProduct.antipode_def`). As in Sections 1 and 2, one factor may be a Hopf algebra over an $R$-algebra $S$, which covers base change.

#### Common errors

1. A learner writes `f * g` for two maps of type `A →ₗ[R] A` and gets the composition. Convolution lives on `WithConv`. Write `toConv f * toConv g`.
2. A learner looks for the antipode as a declaration in the namespace `HopfAlgebra` and does not find it. The field is `HopfAlgebraStruct.antipode`, and code writes it as `antipode R`. The lemma for products is `HopfAlgebra.antipode_mul_antidistrib`, and `HopfAlgebra.antipode_mul_distrib` is the commutative version.
3. A learner expects `AlgHom.convGroup` for a noncommutative target $C$. The convolution of two algebra maps is an algebra map only when the target is commutative, so the group needs `CommSemiring C`.

### Exercises

1. (A) Prove that the convolution product on `WithConv (C →ₗ[R] A)` is associative, from `Coalgebra.coassoc` and the associativity of $A$.
2. (A) Prove $S(a^n) = S(a)^n$ for all $n$ in a Hopf algebra, from `HopfAlgebra.antipode_mul_antidistrib` and `HopfAlgebra.antipode_one`.
3. (B) Prove that $S \circ S = \mathrm{id}$ in a commutative Hopf algebra. Show that $S \circ S$ is a convolution inverse of $S$ in the convolution algebra $\mathrm{End}(A)$, and use the uniqueness of inverses.
4. (B) Let $f : A \to B$ be a bialgebra map between Hopf algebras. Prove that $f \circ S_A = S_B \circ f$ by showing that both are convolution inverses of $f$ in `WithConv (A →ₗ[R] B)`.
5. (B) Let $A = R[X]$ with $\Delta X = X \otimes 1 + 1 \otimes X$, $\varepsilon(X) = 0$ and $S(X) = -X$. Prove that the group of algebra maps $A \to C$ under convolution, as in `AlgHom.convGroup`, is isomorphic to the additive group of $C$.
6. (C) Prove that a bialgebra $A$ is a Hopf algebra if $A$ is generated by a set $X$ of elements $x$ with $\Delta x = x \otimes 1 + 1 \otimes x$, using `HopfAlgebra.ofAntipodeOfAdjoin`. Assume that $A$ is commutative and that an algebra map $S$ with $S(x) = -x$ on $X$ exists.

### Reference

<?reference?>
