---
title: Star homomorphisms
kind: api
modules:
  - Mathlib.Algebra.Star.MonoidHom
  - Mathlib.Algebra.Star.StarRingHom
  - Mathlib.Algebra.Star.StarAlgHom
explains:
  E2: [StarMulEquiv.ofStarMonoidHom, StarRingEquiv.ofStarRingHom, StarAlgHom.ofId, StarAlgEquiv.ofAlgEquiv, StarAlgEquiv.ofBijective, StarAlgHom.prodEquiv, Pi.evalStarAlgHom]
  E1: auto
families: []
requires: [V06.C01, V06.C08]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Star homomorphisms

### Overview

A star ring has two kinds of structure: the ring operations and the involution $x \mapsto x^*$. A map between star rings is a *star homomorphism* when it respects both. Complex conjugation on $\mathbb{C}$, the conjugate transpose on matrices and the adjoint on bounded operators are star structures, and the maps between such objects that a mathematician uses respect the star. Examples are the evaluation of a continuous function at a point, the inclusion of a star subalgebra and conjugation by a unitary element.

The three modules of this section give a bundled structure for each level of structure: monoids, non-unital rings and algebras. Each structure extends the matching homomorphism of Chapter 1 or Chapter 8 with one field, which says $f(x^*) = f(x)^*$. Each structure has an equivalence form. The API is the same at each level, so this section first describes the shared pattern, and then the constructions that are special to star algebras.

### The library around it

#### The structures and their notation

The table gives the six structures and their notation. The notation follows the pattern of the plain homomorphisms, with a star after the arrow.

| Lean name | Notation | Extends |
|---|---|---|
| `StarMonoidHom` | `A →⋆* B` | the monoid homomorphism `A →* B` |
| `StarMulEquiv` | `A ≃⋆* B` | the multiplicative equivalence `A ≃* B` |
| `NonUnitalStarRingHom` | `A →⋆ₙ+* B` | the non-unital ring homomorphism `A →ₙ+* B` |
| `StarRingEquiv` | `A ≃⋆+* B` | the ring equivalence `A ≃+* B` |
| `NonUnitalStarAlgHom` | `A →⋆ₙₐ[R] B` | the non-unital algebra homomorphism `A →ₙₐ[R] B` |
| `StarAlgHom` | `A →⋆ₐ[R] B` | the algebra homomorphism `A →ₐ[R] B` |
| `StarAlgEquiv` | `A ≃⋆ₐ[R] B` | the ring equivalence with a star and with scalars |

There is no unital star ring homomorphism in this list. A unital star ring homomorphism is a star algebra homomorphism over $\mathbb{Z}$, so the library does not give it a separate structure. The source types need only the operations, not the axioms of a star ring: a `StarMonoidHom` needs a monoid and a star on each side, and a `StarAlgEquiv` needs only an addition, a multiplication, a scalar action and a star.

Each structure has a function coercion through `FunLike` or `EquivLike`. The statement that a map respects the star is the class `StarHomClass`, which lives with the star rings in `Mathlib.Algebra.Star.Basic`. Its one field is `StarHomClass.map_star`: $f(x^*) = f(x)^*$. The lemma is a simp lemma, and the root namespace exports it under the short name, so a proof can apply it to $f$ and $x$ without the prefix. The class `StarRingEquivClass` bundles the star condition with the conditions of a ring equivalence. For the other maps, the library uses `StarHomClass` together with a plain class: `NonUnitalRingHomClass` for ring maps, and `AlgHomClass` or `NonUnitalAlgHomClass` for algebra maps. So a lemma about all star algebra homomorphisms takes a type $F$ with `[FunLike F A B] [AlgHomClass F R A B] [StarHomClass F A B]`.

#### The shared API

Each structure has the same list of basic declarations. The table shows them for `StarAlgHom`. The names for the other structures replace the prefix.

| Lean name | Statement |
|---|---|
| `StarAlgHom.ext` | two maps that agree at each point are equal |
| `StarAlgHom.ext_iff` | $f = g \iff \forall x,\ f(x) = g(x)$ |
| `StarAlgHom.coe_mk` | the coercion of a map built with the anonymous constructor |
| `StarAlgHom.id` | the identity map |
| `StarAlgHom.comp` | the composite $g \circ f$ |
| `StarAlgHom.comp_apply` | $(g \circ f)(x) = g(f(x))$ |
| `StarAlgHom.comp_assoc` | composition is associative |
| `StarAlgHom.id_comp` | $\mathrm{id} \circ f = f$ |
| `StarAlgHom.copy` | replaces the function by an equal function, for good definitional equalities |
| `StarAlgHom.ofClass` | turns an element of a type with the classes into a `StarAlgHom` |

The forgetful maps have the names `StarAlgHom.toAlgHom`, `StarAlgHom.toNonUnitalStarAlgHom` and `StarMonoidHom.toMonoidHom`. Their coercion lemmas, such as `StarAlgHom.coe_toAlgHom` and `StarAlgHom.coe_toNonUnitalStarAlgHom`, are simp lemmas that remove the forgetful map. So the simp normal form of a star homomorphism applied to a point is the bare coercion `f x`.

The endomorphisms form a monoid under composition. The instances are `StarMonoidHom.instMonoid` and `StarAlgHom.instMonoid`, with multiplication the composition and unit the identity. The lemma `StarMonoidHom.coe_one` says that the unit is the identity function. For non-unital star algebra homomorphisms there is also a zero map, and `NonUnitalStarAlgHom.instMonoidWithZero` gives a monoid with zero. This instance needs `StarAddMonoid A`, because the zero map respects the star only when $0^* = 0$.

The equivalences add the inverse. Each has `refl`, `symm` and `trans`, with the simp lemmas `StarAlgEquiv.apply_symm_apply`, `StarAlgEquiv.symm_apply_apply`, `StarAlgEquiv.symm_symm` and `StarAlgEquiv.trans_apply`. The inverse of a star equivalence respects the star automatically: if $f(y^*) = f(y)^*$ for each $y$, then for $x = f(y)$, $f^{-1}(x^*) = f^{-1}(f(y)^*) = f^{-1}(f(y^*)) = y^* = f^{-1}(x)^*$. The automorphisms of a star algebra form a group, `StarAlgEquiv.aut`, with multiplication `StarAlgEquiv.aut_mul` given by composition. The forgetful maps `StarAlgEquiv.toStarRingEquiv`, `StarAlgEquiv.toAlgEquiv` and `StarAlgEquiv.toStarAlgHom` connect the equivalences to the other structures.

#### Equivalences from homomorphisms

There are three ways to make a star equivalence from data that is easier to get.

1. From two homomorphisms that are inverse to each other. `StarMulEquiv.ofStarMonoidHom f g` takes $f : A \to B$ and $g : B \to A$ with the hypotheses `g.comp f = StarMonoidHom.id A` and `f.comp g = StarMonoidHom.id B`. The hypotheses are equalities of bundled maps, so a proof gives them with the tactic *ext*. The same pattern gives `StarRingEquiv.ofStarRingHom` and `StarAlgEquiv.ofStarAlgHom`.
2. From an algebra equivalence and a proof for the star. `StarAlgEquiv.ofAlgEquiv f h` takes `f : A ≃ₐ[R] B` and `h : ∀ x, f (star x) = star (f x)`. This is the usual route, because the library has many algebra equivalences, and the star condition is often a short computation.
3. From a bijective homomorphism. `StarAlgEquiv.ofBijective f hf` takes a map $f$ in a type with `NonUnitalAlgHomClass` and `StarHomClass`, and a proof that $f$ is bijective. The inverse function comes from choice, so the definition is noncomputable. The lemma `StarAlgEquiv.coe_ofBijective` says that the forward map is $f$.

The functor `StarAlgEquiv.arrowCongr` takes two star algebra equivalences $e_1 : A_1 \simeq A_1'$ and $e_2 : A_2 \simeq A_2'$ and gives the bijection between the homomorphism types, $f \mapsto e_2 \circ f \circ e_1^{-1}$. The form `StarAlgEquiv.arrowCongr'` does the same for non-unital star algebra homomorphisms.

#### Special star algebra homomorphisms

The algebra map of a star algebra is a star homomorphism. `StarAlgHom.ofId R A : R →⋆ₐ[R] A` is the map $r \mapsto r \cdot 1$. It needs `StarModule R A`, which says $(r \cdot a)^* = r^* \cdot a^*$. The proof that it respects the star is one line: $(r \cdot 1)^* = r^* \cdot 1^* = r^* \cdot 1$, by `StarModule.star_smul` and `star_one`. The lemma `StarAlgHom.ofId_apply` says that the map sends $r$ to `algebraMap R A r`.

The product of star algebras has the componentwise star, and the universal property of the product holds in the star category.

| Lean name | Statement |
|---|---|
| `StarAlgHom.fst` | the projection $A \times B \to A$ |
| `StarAlgHom.snd` | the projection $A \times B \to B$ |
| `StarAlgHom.prod` | $f : A \to B$ and $g : A \to C$ give $x \mapsto (f(x), g(x))$ |
| `StarAlgHom.fst_prod` | $\mathrm{fst} \circ (f, g) = f$ |
| `StarAlgHom.prod_fst_snd` | $(\mathrm{fst}, \mathrm{snd}) = \mathrm{id}$ |
| `StarAlgHom.prodEquiv` | $(A \to B) \times (A \to C) \simeq (A \to B \times C)$ |
| `NonUnitalStarAlgHom.inl` | $a \mapsto (a, 0)$, a non-unital map |
| `NonUnitalStarAlgHom.inr` | $b \mapsto (0, b)$, a non-unital map |

The maps `NonUnitalStarAlgHom.inl` and `NonUnitalStarAlgHom.inr` exist only in the non-unital form, because $(1, 0)$ is not the unit of $A \times B$. For an indexed family of star algebras, `Pi.evalStarAlgHom R A j` is the evaluation $(\forall i, A_i) \to A_j$ at the index $j$.

A star algebra homomorphism over $S$ is also one over a smaller ring $R$ when $S$ is an $R$-algebra with a compatible scalar tower. `NonUnitalStarAlgHom.restrictScalars` gives this for non-unital maps. The unital form `StarAlgHom.restrictScalars` lives with the star subalgebras in `Mathlib.Algebra.Star.Subalgebra`.

#### Common errors

1. A search for a separate unital star ring homomorphism type finds nothing. Use `A →⋆ₐ[ℤ] B` or a `StarAlgHom` over the natural base ring, or state the lemma with the classes `RingHomClass` and `StarHomClass`.
2. The lemma `StarHomClass.map_star` applies to each map with `StarHomClass`, so the structures have no specialised form of it in their own namespaces. Apply the class lemma, and let instance search find the class.
3. `StarMulEquiv.ofStarMonoidHom` asks for equalities of bundled maps, not for the pointwise identities. Prove each hypothesis with the tactic *ext* followed by the pointwise identity.

### Exercises

1. (A) Show that the composite of two star monoid homomorphisms respects the star, and compare the proof with the definition of `StarMonoidHom.comp`.
2. (A) Use `StarAlgEquiv.ofAlgEquiv` to turn the identity algebra equivalence of a star algebra into `StarAlgEquiv.refl`, and prove that the two are equal with `StarAlgEquiv.ext`.
3. (B) Prove that the inverse function of a bijective star ring homomorphism respects the star, and explain why `StarAlgEquiv.ofBijective` needs no star hypothesis for the inverse.
4. (B) Show that complex conjugation is a star algebra equivalence of $\mathbb{C}$ over $\mathbb{R}$, but that it is not an algebra homomorphism over $\mathbb{C}$.
5. (B) Prove that `StarAlgHom.prodEquiv` is a bijection by the universal property of the product, with `StarAlgHom.fst_prod` and `StarAlgHom.prod_fst_snd`.
6. (C) Let $A$ be a star algebra over a commutative star ring $R$ with `StarModule R A`. Prove that `StarAlgHom.ofId R A` is the only star algebra homomorphism $R \to A$, and that it is the initial object of the category of star algebras over $R$.

### Reference

<?reference?>
