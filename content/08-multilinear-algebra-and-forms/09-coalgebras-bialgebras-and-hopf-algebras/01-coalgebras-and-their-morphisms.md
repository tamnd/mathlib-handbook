---
title: Coalgebras and their morphisms
kind: api
modules:
  - Mathlib.RingTheory.Coalgebra.Basic
  - Mathlib.RingTheory.Coalgebra.Hom
  - Mathlib.RingTheory.Coalgebra.Equiv
  - Mathlib.RingTheory.Coalgebra.CoassocSimps
  - Mathlib.RingTheory.Coalgebra.MulOpposite
  - Mathlib.RingTheory.Coalgebra.Quotient
  - Mathlib.RingTheory.Coalgebra.TensorProduct
explains:
  E2: [Coalgebra.ext_to_ring, Coalgebra.sum_counit_smul, Submodule.isCoideal_iff_comul_mem, TensorProduct.counit_tmul, CoalgEquiv.ofBijective]
  E1: auto
families: []
requires: [V08.C02, V07.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Coalgebras and their morphisms

### Overview

An algebra over a commutative ring $R$ is a module $A$ with a multiplication $A \otimes_R A \to A$ and a unit $R \to A$. A coalgebra reverses the arrows. It is a module $C$ with a *comultiplication* $\Delta : C \to C \otimes_R C$ and a *counit* $\varepsilon : C \to R$, and the axioms of an algebra, written as equalities of linear maps, hold with all arrows reversed. Coalgebras describe how an object splits into two parts. In the coalgebra of a monoid algebra, a monoid element $g$ splits as $g \otimes g$. In the symmetric algebra, a vector $x$ splits as $x \otimes 1 + 1 \otimes x$.

This section treats the coalgebra structure, its examples, the coalgebra maps and equivalences, the quotients by coideals, and the tensor product of two coalgebras. Every construction uses the tensor product of Chapter 2, and most proofs are computations with the maps `LinearMap.rTensor`, `LinearMap.lTensor`, `TensorProduct.map` and `TensorProduct.assoc` of that chapter. The later sections of this chapter add a multiplication (bialgebras) and an antipode (Hopf algebras).

### The library around it

#### The structure

The class `CoalgebraStruct R A` holds the two maps and no axioms. Its fields are `CoalgebraStruct.comul : A →ₗ[R] A ⊗[R] A` and `CoalgebraStruct.counit : A →ₗ[R] R`. After `open RingTheory.LinearMap`, the scoped notations `δ` and `ε` denote them. The class `Coalgebra R A` extends `CoalgebraStruct R A` with three axioms, stated as equalities of linear maps:

| Lean name | Statement |
| --- | --- |
| `Coalgebra.coassoc` | $\alpha \circ (\Delta \otimes \mathrm{id}) \circ \Delta = (\mathrm{id} \otimes \Delta) \circ \Delta$, where $\alpha$ is `TensorProduct.assoc` |
| `Coalgebra.rTensor_counit_comp_comul` | $(\varepsilon \otimes \mathrm{id}) \circ \Delta = (a \mapsto 1 \otimes a)$ |
| `Coalgebra.lTensor_counit_comp_comul` | $(\mathrm{id} \otimes \varepsilon) \circ \Delta = (a \mapsto a \otimes 1)$ |

Each axiom has a pointwise form with the suffix `_apply`, for example `Coalgebra.coassoc_apply`, and `Coalgebra.coassoc_symm_apply` states coassociativity with the inverse associator. The mixin `Coalgebra.IsCocomm R A` adds the axiom `Coalgebra.comm_comp_comul`: the flip $a \otimes b \mapsto b \otimes a$ (the map `TensorProduct.comm`) fixes $\Delta$.

#### Sweedler notation

On paper one writes $\Delta a = \sum a_{(1)} \otimes a_{(2)}$ and forgets the index set. Lean needs a finite index set, and the structure `Coalgebra.Repr R a ι` holds one. Its fields are a finite set `Coalgebra.Repr.index`, two maps `Coalgebra.Repr.left` and `Coalgebra.Repr.right` from $\iota$ to $A$, and the equation `Coalgebra.Repr.eq`:
$$\sum_{i \in \mathrm{index}} \mathrm{left}(i) \otimes \mathrm{right}(i) = \Delta a.$$
Every element has a representation, because every element of a tensor product is a finite sum of pure tensors. The term `Coalgebra.Repr.arbitrary R a` chooses one, with the notation `ℛ R a`. The counit axioms then take the familiar form: `Coalgebra.sum_counit_tmul_eq` and `Coalgebra.sum_tmul_counit_eq` give $\sum \varepsilon(a_{(1)}) \otimes a_{(2)} = 1 \otimes a$ and $\sum a_{(1)} \otimes \varepsilon(a_{(2)}) = a \otimes 1$, and `Coalgebra.sum_counit_smul` gives
$$\sum_i \varepsilon(a_{(1), i}) \cdot a_{(2), i} = a.$$
Proof: apply the linear map $R \otimes A \to A$, $r \otimes b \mapsto r b$, to the first identity. The left side becomes $\sum \varepsilon(a_{(1)}) a_{(2)}$ and the right side becomes $1 \cdot a = a$. The lemma `Coalgebra.sum_tmul_tmul_eq` is the coassociativity axiom in this notation.

#### Examples

The ring $R$ itself is a coalgebra by `CommSemiring.toCoalgebra`, with $\Delta r = 1 \otimes r$ (`CommSemiring.comul_apply`) and $\varepsilon = \mathrm{id}$ (`CommSemiring.counit_apply`). The library builds new coalgebras from old ones:

1. `Prod.instCoalgebra`: on $A \times B$, the comultiplication sends $(a, b)$ to the image of $\Delta a$ under $\mathrm{inl} \otimes \mathrm{inl}$ plus the image of $\Delta b$ under $\mathrm{inr} \otimes \mathrm{inr}$, and $\varepsilon(a, b) = \varepsilon(a) + \varepsilon(b)$ (`Prod.comul_apply`, `Prod.counit_apply`).
2. `Finsupp.instCoalgebra` and `DFinsupp.instCoalgebra`: on finitely supported functions $\iota \to_0 A$, each summand is a copy of $A$. The lemma `Finsupp.comul_single` gives $\Delta(\mathrm{single}\ i\ a) = (\mathrm{single}\ i \otimes \mathrm{single}\ i)(\Delta a)$, and `Finsupp.counit_single` gives $\varepsilon(\mathrm{single}\ i\ a) = \varepsilon(a)$.
3. `Pi.instCoalgebra`: the same for a product over a finite index type.
4. `LinearEquiv.coalgebra`: a linear equivalence $e : A \simeq B$ to a coalgebra $B$ transfers the structure to $A$.
5. `MulOpposite.instCoalgebra`: $A^{\mathrm{mop}}$ has the coalgebra structure of $A$, moved along the linear equivalence `MulOpposite.opLinearEquiv` (`MulOpposite.comul_def`, `MulOpposite.counit_def`). This instance matters when $A$ is also an algebra, because the antipode of a Hopf algebra is an algebra map to $A^{\mathrm{mop}}$.

The free module $R^{(\iota)}$, with $\Delta(e_i) = e_i \otimes e_i$ and $\varepsilon(e_i) = 1$, is the case $A = R$ of item 2. Each instance comes with a cocommutativity instance when the inputs are cocommutative.

#### Coalgebra maps

A coalgebra map $f : A \to B$ is a linear map with $\varepsilon_B \circ f = \varepsilon_A$ and $(f \otimes f) \circ \Delta_A = \Delta_B \circ f$. The structure is `CoalgHom` with the notation `A →ₗc[R] B`, and its axioms are `CoalgHom.counit_comp` and `CoalgHom.map_comp_comul`. The class `CoalgHomClass` covers all bundled maps that are coalgebra maps, such as the bialgebra maps of the next section. The API follows the pattern of `AlgHom`: `CoalgHom.id`, `CoalgHom.comp`, `CoalgHom.ext`, and the coercion `CoalgHom.toLinearMap` with the simp lemma `CoalgHom.coe_linearMapOfClass`. A map sends representations to representations: `Coalgebra.Repr.induced` turns a representation of $\Delta a$ into one of $\Delta (f a)$.

The counit is a coalgebra map `Coalgebra.counitCoalgHom R A : A →ₗc[R] R`, and it is the only one. This is `Coalgebra.ext_to_ring`, and `Coalgebra.subsingleton_to_ring` states it as an instance. Proof: let $f : A \to R$ be a coalgebra map. The counit of $R$ is the identity, so the axiom $\varepsilon_R \circ f = \varepsilon_A$ reads $f = \varepsilon_A$. So $R$ is a terminal object for coalgebras. In the other direction, `CoalgHom.ext_of_ring` says that a coalgebra map out of $R$ is fixed by its value at $1$.

#### Coalgebra equivalences

The structure `CoalgEquiv`, with the notation `A ≃ₗc[R] B`, is a linear equivalence that is a coalgebra map. The usual API is there: `CoalgEquiv.refl`, `CoalgEquiv.symm`, `CoalgEquiv.trans`, `CoalgEquiv.toLinearEquiv` and `CoalgEquiv.toCoalgHom`. The constructor `CoalgEquiv.ofCoalgHom` takes a map and a two-sided inverse. The constructor `CoalgEquiv.ofBijective` takes only a bijective coalgebra map. The inverse $g$ of a bijective coalgebra map $f$ is a coalgebra map, because $\varepsilon \circ g = \varepsilon \circ f \circ g = \varepsilon$ and
$$(g \otimes g) \circ \Delta = (g \otimes g) \circ \Delta \circ f \circ g = (g \otimes g) \circ (f \otimes f) \circ \Delta \circ g = \Delta \circ g.$$
The term `CoalgEquiv.toCoalgebra` goes the other way from `LinearEquiv.coalgebra`: it states that a coalgebra equivalence respects the structures that are already there.

#### Coideals and quotients

A submodule $I$ of a coalgebra $C$ over a commutative ring is a *coideal* if $\varepsilon$ vanishes on $I$ and $\Delta$ sends $I$ into the kernel of $C \otimes C \to (C/I) \otimes (C/I)$. This is the class `Submodule.IsCoideal`, with the fields `Submodule.IsCoideal.counit_eq_zero` and `Submodule.IsCoideal.map_mkQ_comul_eq_zero`. The ring must be a `CommRing` and the module an `AddCommGroup`, because the quotient module needs negation. The criterion `Submodule.isCoideal_iff_comul_mem` gives the textbook form: $I$ is a coideal if and only if $\varepsilon(I) = 0$ and
$$\Delta(I) \subseteq I \otimes C + C \otimes I,$$
where the two summands are the ranges of `LinearMap.rTensor C I.subtype` and `LinearMap.lTensor C I.subtype`. The proof uses the right exactness of the tensor product from Chapter 2: the kernel of $C \otimes C \to (C/I) \otimes (C/I)$ is exactly $I \otimes C + C \otimes I$.

The quotient $C / I$ is then a coalgebra, and `Coalgebra.Quotient.mkQCoalgHom I` is the projection as a coalgebra map. The simp lemmas `Coalgebra.Quotient.comul_mk` and `Coalgebra.Quotient.counit_mk` compute the structure on a class $[x]$.

#### Tensor products of coalgebras

If $A$ and $B$ are coalgebras, then $A \otimes B$ is a coalgebra by `TensorProduct.instCoalgebra`, with
$$\Delta(a \otimes b) = \sum (a_{(1)} \otimes b_{(1)}) \otimes (a_{(2)} \otimes b_{(2)}), \qquad \varepsilon(a \otimes b) = \varepsilon(a)\,\varepsilon(b).$$
These are `TensorProduct.comul_tmul` and `TensorProduct.counit_tmul`. In Lean the comultiplication is $(\Delta_A \otimes \Delta_B)$ followed by the middle swap `TensorProduct.tensorTensorTensorComm`. The instance is more general than the case of one ring. The factor $A$ may be a coalgebra over an $R$-algebra $S$ and $B$ a coalgebra over $R$, and then $A \otimes_R B$ is an $S$-coalgebra. With $A = S$ this is the base change of an $R$-coalgebra to $S$. The counit on a pure tensor is `ε y • ε x`, with the scalar of $R$ acting on the element of $S$.

The structure maps are coalgebra maps or equivalences:

| Lean name | Type |
| --- | --- |
| `Coalgebra.TensorProduct.map` | $(A \to_c B) \to (C \to_c D) \to (A \otimes C \to_c B \otimes D)$ |
| `Coalgebra.TensorProduct.assoc` | $(A \otimes B) \otimes C \simeq_c A \otimes (B \otimes C)$ |
| `Coalgebra.TensorProduct.lid` | $R \otimes A \simeq_c A$, $r \otimes a \mapsto r a$ |
| `Coalgebra.TensorProduct.rid` | $A \otimes_R R \simeq_c A$ |
| `CoalgHom.lTensor`, `CoalgHom.rTensor` | $\mathrm{id} \otimes f$ and $f \otimes \mathrm{id}$ |

For a cocommutative coalgebra $C$, the comultiplication itself is a coalgebra map `Coalgebra.comulCoalgHom R C : C →ₗc[R] C ⊗[R] C`. This map is the diagonal of the category of cocommutative coalgebras. Its bialgebra version `Bialgebra.comulBialgHom` appears in Section 2.

#### The simp set for coassociativity

Proofs about coalgebras often compare two long composites of maps of the form $f \otimes g$, associators, flips and comultiplications. The module CoassocSimps holds a simp set for these goals. It takes `TensorProduct.map`, `TensorProduct.assoc` and `TensorProduct.comm` as the basic maps. It writes composites with right association, merges $(f_2 \otimes g_2) \circ (f_1 \otimes g_1)$ into $(f_2 \circ f_1) \otimes (g_2 \circ g_1)$, and moves associators to the right until coassociativity cancels them against a $\Delta$. The lemmas `CoassocSimps.coassoc_left` and `CoassocSimps.coassoc_right` do the cancellation, and simprocs such as `CoassocSimps.lid_comp_map_simproc` remove the unit isomorphisms. The rewriting is not confluent with the counit axiom, so the module adds `CoassocSimps.map_counit_comp_comul_left` and `CoassocSimps.map_counit_comp_comul_right`, which state the counit axiom after a map $f$.

#### Common errors

1. A learner looks for the comultiplication in the namespace `Coalgebra` and does not find it. The fields belong to the structure class: the names are `CoalgebraStruct.comul` and `CoalgebraStruct.counit`, or the notations `δ` and `ε` after `open RingTheory.LinearMap`.
2. A learner applies `Submodule.isCoideal_iff_comul_mem` over a semiring such as $\mathbb{N}$. The quotient of a coalgebra needs a `CommRing` and an `AddCommGroup`, and the class `Submodule.IsCoideal` does not exist without them.
3. A learner expects `TensorProduct.counit_tmul` to give `ε x * ε y`. For the general instance over $S$ and $R$ the value is `ε y • ε x`. Over one ring, rewrite with `smul_eq_mul` and `mul_comm`.

### Exercises

1. (A) Show that the comultiplication $\Delta(e_i) = e_i \otimes e_i$ and the counit $\varepsilon(e_i) = 1$ on $R^{(\iota)}$ satisfy the three axioms, and identify this coalgebra with an instance of the library.
2. (A) Use `Coalgebra.ext_to_ring` to prove that for coalgebra maps $f : A \to B$ and $g : B \to R$, the composite $g \circ f$ equals the counit of $A$.
3. (B) Let $C$ have the basis $c_0, c_1, \dots$ with $\Delta(c_n) = \sum_{i + j = n} c_i \otimes c_j$ and $\varepsilon(c_n) = [n = 0]$. Prove that the span of $c_1, c_2, \dots$ is a coideal by `Submodule.isCoideal_iff_comul_mem`, and identify the quotient.
4. (B) Prove that the kernel of a coalgebra map $f : C \to D$ over a field is a coideal of $C$, and that $C / \ker f$ is isomorphic to the image of $f$ as a coalgebra.
5. (B) Prove that $\Delta(a \otimes b)$ in `TensorProduct.comul_tmul` is coassociative, using the coassociativity of $A$ and $B$ and the naturality of the middle swap.
6. (C) Prove that $\Delta : C \to C \otimes C$ is a coalgebra map for a cocommutative coalgebra $C$, as `Coalgebra.comulCoalgHom` states. Then prove the converse: if $\Delta$ is a coalgebra map, apply $\varepsilon \otimes \mathrm{id} \otimes \mathrm{id} \otimes \varepsilon$ to the axiom and deduce that $C$ is cocommutative.

### Reference

<?reference?>
