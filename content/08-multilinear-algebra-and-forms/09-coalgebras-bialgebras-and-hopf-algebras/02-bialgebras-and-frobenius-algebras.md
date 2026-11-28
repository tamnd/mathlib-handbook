---
title: Bialgebras and Frobenius algebras
kind: api
modules:
  - Mathlib.RingTheory.Bialgebra.Basic
  - Mathlib.RingTheory.Bialgebra.Hom
  - Mathlib.RingTheory.Bialgebra.Equiv
  - Mathlib.RingTheory.Bialgebra.TensorProduct
  - Mathlib.RingTheory.Bialgebra.Quotient
  - Mathlib.RingTheory.Bialgebra.SymmetricAlgebra
  - Mathlib.RingTheory.Coalgebra.IsFrobenius
explains:
  E2: [Bialgebra.algebraMap_injective, Bialgebra.counit_surjective, Bialgebra.ext_to_ring, SymmetricAlgebra.comul_ι, Coalgebra.IsFrobenius.forall_counit_mul_left_eq_zero_iff, Bialgebra.comul_apply_eq_of_isFrobenius, Bialgebra.algebraMap_bijective_of_isFrobenius]
  E1: auto
families: []
requires: [V08.C02, V08.C03, V06.C08]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Bialgebras and Frobenius algebras

### Overview

A bialgebra is a module that is an algebra and a coalgebra at the same time, with a compatibility condition: the comultiplication and the counit are algebra maps. The condition is symmetric. It holds if and only if the multiplication $A \otimes A \to A$ and the unit $R \to A$ are coalgebra maps. The monoid algebra $R[M]$ of a monoid, with $\Delta(m) = m \otimes m$, and the symmetric algebra $S(M)$ of a module, with $\Delta(x) = x \otimes 1 + 1 \otimes x$, are the two basic examples.

This section treats the class of bialgebras, its morphisms and equivalences, its tensor products and quotients, and the bialgebra structure on the symmetric algebra of Chapter 3. It ends with a different combination of the two structures. A Frobenius algebra also has a multiplication and a comultiplication, but the compatibility condition is the Frobenius law $\Delta \circ \mu = (\mu \otimes \mathrm{id}) \circ (\mathrm{id} \otimes \Delta)$. The library proves that a bialgebra satisfies both conditions only when it is the ring $R$ itself.

### The library around it

#### The class

The class `Bialgebra R A` extends `Algebra R A` and `Coalgebra R A`. Its four axioms are stated as equalities of linear and bilinear maps, with the names `Bialgebra.counit_one`, `Bialgebra.mul_compr₂_counit`, `Bialgebra.comul_one` and `Bialgebra.mul_compr₂_comul`. The pointwise forms are the lemmas that a proof uses:

| Lean name | Statement |
| --- | --- |
| `Bialgebra.counit_one` | $\varepsilon(1) = 1$ |
| `Bialgebra.counit_mul` | $\varepsilon(ab) = \varepsilon(a)\varepsilon(b)$ |
| `Bialgebra.comul_one` | $\Delta(1) = 1 \otimes 1$ |
| `Bialgebra.comul_mul` | $\Delta(ab) = \Delta(a)\Delta(b)$ |
| `Bialgebra.counit_algebraMap` | $\varepsilon(r \cdot 1) = r$ |
| `Bialgebra.comul_algebraMap` | $\Delta(r \cdot 1) = r \cdot 1 \otimes 1$ |
| `Bialgebra.counit_pow`, `Bialgebra.comul_pow` | the same for $a^n$ |

The product $\Delta(a)\Delta(b)$ is the product of the algebra $A \otimes_R A$ of Chapter 2. Two constructors avoid the bilinear form of the axioms. `Bialgebra.mk'` takes a `Coalgebra` instance and the four pointwise equations. `Bialgebra.ofAlgHom` takes the comultiplication and the counit as algebra maps, with the coalgebra axioms as equalities of algebra maps. In the other direction, `Bialgebra.comulAlgHom R A : A →ₐ[R] A ⊗[R] A` and `Bialgebra.counitAlgHom R A : A →ₐ[R] R` give the two maps as algebra maps.

The equation $\varepsilon(r \cdot 1) = r$ says that $\varepsilon \circ \eta = \mathrm{id}_R$, where $\eta = $ `algebraMap R A`. So $\eta$ has a left inverse and $\varepsilon$ has a right inverse. This proves `Bialgebra.algebraMap_injective` and `Bialgebra.counit_surjective`. In particular, a bialgebra over a nontrivial ring is nontrivial (`Bialgebra.nontrivial`), and $A = R \cdot 1 \oplus \ker \varepsilon$ as modules. The ring itself is a bialgebra by `CommSemiring.toBialgebra`.

#### Morphisms and equivalences

A bialgebra map is an algebra map that is a coalgebra map. The structure `BialgHom` has the notation `A →ₐc[R] B`, and it extends `CoalgHom` with the multiplicative axioms. The projections `BialgHom.toAlgHom` and `BialgHom.toCoalgHom` give the two underlying maps, and the classes `BialgHomClass` and `BialgEquivClass` follow the pattern of the library. The constructor `BialgHom.ofAlgHom` takes an algebra map $f$ with $\varepsilon \circ f = \varepsilon$ and $(f \otimes f) \circ \Delta = \Delta \circ f$, as equalities of algebra maps.

The unit and the counit are bialgebra maps: `Bialgebra.unitBialgHom R A : R →ₐc[R] A` and `Bialgebra.counitBialgHom R A : A →ₐc[R] R`. Both are unique. `BialgHom.ext_of_ring` holds because an algebra map out of $R$ is fixed, and `Bialgebra.ext_to_ring` holds by the coalgebra fact of Section 1: a coalgebra map to $R$ is the counit. So $R$ is an initial and a terminal object of the category of bialgebras.

The structure `BialgEquiv` has the notation `A ≃ₐc[R] B`. Its constructors are `BialgEquiv.ofBijective` for a bijective bialgebra map, `BialgEquiv.ofAlgEquiv` for an algebra equivalence that respects $\varepsilon$ and $\Delta$, and `BialgEquiv.ofBialgHom` for a map with a two-sided inverse. The projections are `BialgEquiv.toAlgEquiv` and `BialgEquiv.toCoalgEquiv`.

#### Tensor products

If $A$ and $B$ are bialgebras, the algebra $A \otimes_R B$ of Chapter 2 and the coalgebra $A \otimes_R B$ of Section 1 form a bialgebra, `TensorProduct.instBialgebra`. As in Section 1, $A$ may be a bialgebra over an $R$-algebra $S$, which covers base change. The structure maps are bialgebra maps and equivalences: `Bialgebra.TensorProduct.map`, `Bialgebra.TensorProduct.assoc`, `Bialgebra.TensorProduct.lid`, `Bialgebra.TensorProduct.rid`, `Bialgebra.TensorProduct.comm`, `BialgHom.lTensor` and `BialgHom.rTensor`.

Two maps show that the axioms of a bialgebra say "the structure maps are morphisms":

1. `Bialgebra.mulCoalgHom R A : A ⊗[R] A →ₗc[R] A` is the multiplication as a coalgebra map. The equation $\Delta(ab) = \Delta(a)\Delta(b)$ is the statement $\Delta \circ \mu = (\mu \otimes \mu) \circ \Delta_{A \otimes A}$. For a commutative $A$, the multiplication is also an algebra map, and `Bialgebra.mulBialgHom` bundles both.
2. `Bialgebra.comulBialgHom R A : A →ₐc[R] A ⊗[R] A` is the comultiplication as a bialgebra map. It needs `Coalgebra.IsCocomm R A`, as the map `Coalgebra.comulCoalgHom` of Section 1 does.

For computations in Sweedler notation, `Coalgebra.Repr.tmul` builds a representation of $\Delta(a \otimes b)$ from representations of $\Delta a$ and $\Delta b$, indexed by the product of the index types. `Coalgebra.Repr.mul` does the same for $\Delta(ab)$.

#### Quotients by biideals

A *biideal* of a bialgebra $A$ is a two-sided ideal that is also a coideal. In Lean it is an ideal `I : Ideal A` with the instances `I.IsTwoSided` and `(I.restrictScalars R).IsCoideal`. The quotient ring $A/I$ is then a bialgebra (`Bialgebra.Quotient.instQuotientIdeal`), and `Bialgebra.Quotient.mkBialgHom` is the projection. The structure maps of the quotient are `Bialgebra.Quotient.comulAlgHom` and `Bialgebra.Quotient.counitAlgHom`, and `Bialgebra.Quotient.comul_mk` and `Bialgebra.Quotient.counit_mk` compute them on a class $[a]$. The same hypotheses as in Section 1 hold: $R$ must be a `CommRing` and $A$ a `Ring`.

The kernel of the counit is an example. It is a two-sided ideal, and it is a coideal because
$$\Delta(a) - (a \otimes 1 + 1 \otimes a) + \varepsilon(a) \cdot 1 \otimes 1 \in \ker\varepsilon \otimes \ker\varepsilon$$
for all $a$. The quotient $A / \ker\varepsilon$ is isomorphic to $R$.

#### The symmetric algebra

The symmetric algebra $S(M)$ of Chapter 3 is a bialgebra by `SymmetricAlgebra.instBialgebra`, and it is cocommutative by `SymmetricAlgebra.instIsCocomm`. The formulas on the generators are
$$\Delta(\iota x) = \iota x \otimes 1 + 1 \otimes \iota x, \qquad \varepsilon(\iota x) = 0,$$
the lemmas `SymmetricAlgebra.comul_ι` and `SymmetricAlgebra.counit_ι`. Proof: the comultiplication is defined as the algebra map $S(M) \to S(M) \otimes S(M)$ that the universal property of $S(M)$ gives for the linear map $x \mapsto \iota x \otimes 1 + 1 \otimes \iota x$. The target is commutative, so the universal property applies, and the formula is the defining equation of the lift. The counit is the algebra map that sends $\iota x$ to $0$. It is the projection onto degree $0$, which is `SymmetricAlgebra.counitAlgHom_eq`: the counit algebra map equals `SymmetricAlgebra.algebraMapInv`.

For $M = R^n$, the symmetric algebra is the polynomial ring $R[X_1, \dots, X_n]$ and $S(M) \otimes S(M)$ is the polynomial ring in $2n$ variables $X_i, Y_i$. The comultiplication sends $f(X)$ to $f(X + Y)$, and the counit sends $f$ to $f(0)$. Coassociativity is the associativity of addition in $R^n$.

#### Frobenius algebras

The class `Coalgebra.IsFrobenius R A` applies to a module $A$ with a multiplication and a coalgebra structure, and no other compatibility. Its field `Coalgebra.IsFrobenius.left_eq_right` states that two maps $A \otimes A \to A \otimes A$ agree:
$$(\mathrm{id} \otimes \mu) \circ \alpha \circ (\Delta \otimes \mathrm{id}) = (\mu \otimes \mathrm{id}) \circ \alpha^{-1} \circ (\mathrm{id} \otimes \Delta).$$
These maps are `Coalgebra.IsFrobenius.left` and `Coalgebra.IsFrobenius.right`. The lemmas `Coalgebra.IsFrobenius.left_eq_comul_comp_mul'` and `Coalgebra.IsFrobenius.right_eq_comul_comp_mul'` prove that both equal $\Delta \circ \mu$, which is the usual Frobenius law. The ring $R$ is a Frobenius algebra over itself (`Coalgebra.IsFrobenius.of_commSemiring`), and so is the matrix algebra $M_n(R)$ with $\Delta(e_{ij}) = \sum_k e_{ik} \otimes e_{kj}$ and the trace as $\varepsilon$.

The main consequence is that the bilinear form $(a, b) \mapsto \varepsilon(ab)$ is nondegenerate. Write $\Delta(1) = \sum_i x_i \otimes y_i$. The Frobenius law gives
$$\Delta(a) = \Delta(a \cdot 1) = \sum_i a x_i \otimes y_i.$$
Apply $\varepsilon \otimes \mathrm{id}$ and use the counit axiom: $a = \sum_i \varepsilon(a x_i)\, y_i$. If $\varepsilon(ab) = 0$ for all $b$, then $a = 0$. This is `Coalgebra.IsFrobenius.forall_counit_mul_left_eq_zero_iff`, and `Coalgebra.IsFrobenius.forall_counit_mul_right_eq_zero_iff` is the mirror statement. The same formula writes each $a$ as a combination of the finitely many $y_i$, so $A$ is finitely generated (`Coalgebra.IsFrobenius.instFinite`) and projective (`Coalgebra.IsFrobenius.instProjective`). The map $A \to \mathrm{Hom}(A, R)$, $a \mapsto (b \mapsto \varepsilon(ab))$ is bijective (`Coalgebra.IsFrobenius.compr₂_mul_counit_bijective`), and `Coalgebra.IsFrobenius.nondegenerate_compr₂_mul_counit` states the nondegeneracy in the language of Chapter 5. The snake equations of the duality are `Coalgebra.IsFrobenius.lTensor_counit_comp_left_comp_rTensor_algebraLinearMap` and its mirror.

A bialgebra is rarely Frobenius. In a Frobenius bialgebra, the same computation with $\Delta(1) = 1 \otimes 1$ gives $\Delta(a) = a \otimes 1$ for all $a$, the lemma `Bialgebra.comul_apply_eq_of_isFrobenius`. Apply $\varepsilon \otimes \mathrm{id}$: then $1 \otimes a = \varepsilon(a) \otimes 1$, so $a = \varepsilon(a) \cdot 1$. This is `Bialgebra.algebraMap_counit_of_isFrobenius`, and with the injectivity of $\eta$ it gives `Bialgebra.algebraMap_bijective_of_isFrobenius`: the unit $R \to A$ is a bijection, and $A$ is $R$. The lemmas `Bialgebra.counit_bijective_of_isFrobenius` and `Bialgebra.algebraOfId_bijective_of_isFrobenius` restate this.

#### Common errors

1. A learner proves $\Delta(ab) = \Delta(a)\Delta(b)$ and tries to build the instance with the anonymous constructor. The fields of `Bialgebra` are equalities of bilinear maps. Use `Bialgebra.mk'` for the pointwise form.
2. A learner asks for `Bialgebra.mulBialgHom` on a noncommutative bialgebra. The multiplication is an algebra map only for a commutative $A$. Use `Bialgebra.mulCoalgHom` for the coalgebra map.
3. A learner forms the quotient of a bialgebra by an ideal and gets no instance. The quotient needs both instances `I.IsTwoSided` and `(I.restrictScalars R).IsCoideal`, and a coideal for the scalars $R$, not $A$.

### Exercises

1. (A) Prove from `Bialgebra.counit_mul` and `Bialgebra.counit_one` that $\varepsilon(u^{-1}) = \varepsilon(u)^{-1}$ for a unit $u$ of a bialgebra.
2. (A) In the symmetric algebra, compute $\Delta(\iota x\, \iota y)$ and $\Delta((\iota x)^3)$ from `SymmetricAlgebra.comul_ι` and `Bialgebra.comul_mul`.
3. (B) Prove that the kernel of the counit of a bialgebra over a commutative ring is a biideal, and that the quotient is isomorphic to $R$ as a bialgebra.
4. (B) Show that the matrix algebra $M_n(R)$ with $\Delta(e_{ij}) = \sum_k e_{ik} \otimes e_{kj}$ and $\varepsilon(e_{ij}) = [i = j]$ is a coalgebra that satisfies the Frobenius law, and decide whether it is a bialgebra for $n \geq 2$.
5. (B) Let $A = R \times R$ with the product algebra structure. Find a coalgebra structure that makes $A$ a Frobenius algebra, and verify the Frobenius law on the basis.
6. (C) Prove `Bialgebra.comul_apply_eq_of_isFrobenius` in detail from `Coalgebra.IsFrobenius.right_eq_comul_comp_mul'` and `Bialgebra.comul_one`.

### Reference

<?reference?>
