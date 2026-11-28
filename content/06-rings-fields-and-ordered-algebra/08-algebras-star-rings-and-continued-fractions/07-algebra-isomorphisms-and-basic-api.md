---
title: Algebra isomorphisms and the basic algebra API
kind: api
modules:
  - Mathlib.Algebra.Algebra.Basic
  - Mathlib.Algebra.Algebra.Equiv
  - Mathlib.Algebra.Algebra.Field
  - Mathlib.Algebra.Algebra.Rat
  - Mathlib.Algebra.Algebra.Hom.Rat
  - Mathlib.Algebra.Algebra.ZMod
  - Mathlib.Algebra.Algebra.Shrink
  - Mathlib.Algebra.Algebra.TransferInstance
explains:
  E2: [faithfulSMul_iff_algebraMap_injective, algebra_compatible_smul, Module.End.instAlgebra, AlgEquiv.ofBijective, MulSemiringAction.toAlgAut, AlgEquiv.autCongr, RingEquiv.toIntAlgEquiv, Rat.algebra_rat_subsingleton, RingHom.equivRatAlgHom, ZMod.algebra]
  E1: auto
families: []
requires: [V06.C01, V06.C03, V06.C04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Algebra isomorphisms and the basic algebra API

### Overview

Section 1 defines an algebra over a commutative ring, the algebra homomorphisms and the subalgebras. This section gives the everyday API around these definitions. It explains when the structure map $R \to A$ is injective, how the scalar actions of a tower agree, and why the endomorphisms of a module form an algebra. It then studies the algebra isomorphisms `A ≃ₐ[R] B`: how to build them, how they form a group, and how a group action gives automorphisms.

The last part treats algebra structures that are unique. Every ring has exactly one $\mathbb{Z}$-algebra structure, every ring has at most one $\mathbb{Q}$-algebra structure, and a ring of characteristic $p$ has exactly one $\mathbb{Z}/p$-algebra structure. So a ring homomorphism between two $\mathbb{Q}$-algebras is automatically a $\mathbb{Q}$-algebra homomorphism. The section needs the rings and fields of Chapters 1 and 3 and the characteristic of Chapter 4.

### The library around it

#### Injective structure maps

The structure map of an algebra need not be injective: the map $\mathbb{Z} \to \mathbb{Z}/n$ is not. Mathlib expresses injectivity with the class `FaithfulSMul R A`, which says that $r \cdot a = s \cdot a$ for all $a$ implies $r = s$. The theorem `faithfulSMul_iff_algebraMap_injective` says that this class holds exactly when `algebraMap R A` is injective. Proof: $r \cdot a = \operatorname{algebraMap}(r) \, a$ by `Algebra.smul_def`. If $r$ and $s$ act in the same way, then they act in the same way on $a = 1$, so $\operatorname{algebraMap}(r) = \operatorname{algebraMap}(s)$. The converse is clear. The theorem `FaithfulSMul.algebraMap_injective` is the direction that a proof uses most, and `algebraMap.coe_inj` is its simp form for the coercion.

A faithful algebra passes properties down to the base ring. The theorems `NoZeroDivisors.of_faithfulSMul`, `IsDomain.of_faithfulSMul` and `IsCancelMulZero.of_faithfulSMul` say that $R$ has no zero divisors, is a domain, or is cancellative when $A$ has the property. The theorem `Algebra.charZero_of_charZero` goes up: a faithful algebra over a ring of characteristic zero has characteristic zero. For domains, `Module.isTorsionFree_iff_faithfulSMul` says that faithfulness is the same as torsion freeness. Two theorems give bijectivity from linear data: `bijective_algebraMap_of_linearEquiv` and `surjective_algebraMap_of_linearMap` show that an algebra that is free of rank one over $F$ by a linear equivalence has a bijective structure map.

The coercion of `algebraMap` respects the operations. The lemmas `algebraMap.coe_sum` and `algebraMap.coe_prod` move a finite sum or product past the coercion. The module `Mathlib.Algebra.Algebra.Field` adds `algebraMap.coe_inv`, `algebraMap.coe_div`, `algebraMap.coe_zpow` and `algebraMap.coe_ratCast` for an algebra between division rings. For instance `algebraMap.coe_div` says $\uparrow(r/s) = \uparrow r / \uparrow s$ when $R$ is a semifield and $A$ is a division semiring.

#### Towers and endomorphisms

Let $M$ be an $A$-module that is also an $R$-module, with the tower condition `IsScalarTower R A M`. The theorem `algebra_compatible_smul` says $r \cdot m = \operatorname{algebraMap}(r) \cdot m$. Proof: $\operatorname{algebraMap}(r) \cdot m = (r \cdot 1) \cdot m = r \cdot (1 \cdot m) = r \cdot m$, by the tower condition. The lemma `smul_algebra_smul_comm` deduces that the two actions commute, $a \cdot (r \cdot m) = r \cdot (a \cdot m)$, and the instances `IsScalarTower.to_smulCommClass` and `Algebra.to_smulCommClass` register this fact.

The endomorphisms of a module form an algebra. The instance `Module.End.instAlgebra` makes `Module.End S M` an $R$-algebra when the actions of $R$ and $S$ on $M$ commute. The structure map sends $a$ to the scalar map $a \cdot \mathrm{id}$, by `Module.algebraMap_end_eq_smul_id`. Over a semifield, `Module.ker_algebraMap_end` says that this scalar map has kernel $0$ when $a \neq 0$. The lemmas `LinearMap.map_algebraMap_mul` and `LinearMap.map_mul_algebraMap` say that an $R$-linear map between algebras commutes with multiplication by scalars.

Some instances build algebras from smaller pieces. `Algebra.ofSubsemiring` makes $A$ an algebra over each subsemiring $S$ of $R$. `ULift.algebra` and `PUnit.algebra` cover the universe lift and the one-element ring. `Algebra.semiringToRing` and `RingHom.commSemiringToCommRing` give the negation on a semiring that is an algebra over a ring, which is useful when the instance of a ring is not found. The submonoid `Algebra.algebraMapSubmonoid S M` is the image of a submonoid $M$ of $R$ in $S$; localization uses it. The identity `Algebra.mul_sub_algebraMap_commutes` says that $x$ commutes with $x - r$, and `Algebra.mul_sub_algebraMap_pow_commutes` extends it to $(x - r)^n$.

#### Building algebra isomorphisms

An algebra isomorphism `A₁ ≃ₐ[R] A₂` is a ring isomorphism that commutes with the structure maps. The forgetful maps are `AlgEquiv.toRingEquiv`, `AlgEquiv.toLinearEquiv`, `AlgEquiv.toAlgHom` and `AlgEquiv.toEquiv`. The class `AlgEquivClass` lets a lemma about algebra isomorphisms apply to other types of bundled isomorphisms. The constructors are these.

| Lean name | Statement |
| --- | --- |
| `AlgEquiv.ofBijective` | a bijective algebra homomorphism is an isomorphism |
| `AlgEquiv.ofAlgHom` | two algebra homomorphisms that are inverse to each other |
| `AlgEquiv.ofLinearEquiv` | a linear isomorphism that respects multiplication |
| `AlgEquiv.ofCommutes` | a ring isomorphism that commutes with `algebraMap` |
| `AlgEquiv.refl`, `AlgEquiv.symm`, `AlgEquiv.trans` | identity, inverse and composition |

For `AlgEquiv.ofBijective` the proof is short: the inverse function $g$ of a bijective ring homomorphism $f$ is additive and multiplicative, because $f(g(x) g(y)) = xy = f(g(xy))$ and $f$ is injective. In the same way $g$ commutes with the structure maps. The lemma `AlgEquiv.coe_ofBijective` says that the function of the result is $f$. The usual simp lemmas `AlgEquiv.apply_symm_apply` and `AlgEquiv.symm_apply_apply` cancel an isomorphism against its inverse.

The automorphisms `A₁ ≃ₐ[R] A₁` form a group by the instance `AlgEquiv.aut`. The product is composition: `AlgEquiv.aut_mul` says $\phi \psi = \psi.\mathrm{trans}\ \phi$, so `AlgEquiv.mul_apply` gives $(\phi\psi)(x) = \phi(\psi(x))$. The lemma `AlgEquiv.coe_pow` says that $\phi^n$ is the $n$-th iterate. The map `AlgEquiv.algHomUnitsEquiv` identifies the automorphism group with the units of the monoid of algebra endomorphisms. The maps `AlgEquiv.toAlgHomHom` and `AlgEquiv.toLinearMapHom` are the monoid homomorphisms that forget the inverse.

An isomorphism $e : A_1 \cong A_2$ moves other objects. `AlgEquiv.autCongr e` is the group isomorphism $\operatorname{Aut}(A_1) \cong \operatorname{Aut}(A_2)$, $\phi \mapsto e \phi e^{-1}$. `AlgEquiv.arrowCongr` and `AlgEquiv.equivCongr` do the same for the homomorphisms and the isomorphisms between two pairs of algebras. `LinearEquiv.conjAlgEquiv` sends a linear isomorphism $M_1 \cong M_2$ to the algebra isomorphism $\operatorname{End}(M_1) \cong \operatorname{End}(M_2)$ by conjugation.

A group action by ring automorphisms gives algebra automorphisms. Let $G$ act on $A$ by `MulSemiringAction` and commute with the action of $R$. Then `MulSemiringAction.toAlgEquiv R A g` is the automorphism $a \mapsto g \cdot a$, and `MulSemiringAction.toAlgAut G R A` is the group homomorphism $G \to \operatorname{Aut}_R(A)$. Galois theory uses this map for the action of a Galois group on a field.

#### Unique algebra structures

The structure maps from $\mathbb{N}$, $\mathbb{Z}$ and $\mathbb{Q}$ are unique, because a ring homomorphism from these rings is determined by its value $1$ at $1$. The instances `nat_algebra_subsingleton`, `int_algebra_subsingleton` and `Rat.algebra_rat_subsingleton` say that each of these algebra structures is unique when it exists. For $\mathbb{Q}$ the proof uses that a ring homomorphism $f : \mathbb{Q} \to A$ satisfies $f(m/n) \cdot f(n) = f(m)$, so $f(m/n) = m \cdot n^{-1}$ is forced.

So a ring isomorphism respects these structures. `RingEquiv.toNatAlgEquiv` and `RingEquiv.toIntAlgEquiv` turn a ring isomorphism into an algebra isomorphism over $\mathbb{N}$ or $\mathbb{Z}$, and `RingEquiv.equivIntAlgEquiv` says that the two kinds of isomorphism are the same. The module `Mathlib.Algebra.Algebra.Hom.Rat` does this over $\mathbb{Q}$: `RingHom.toRatAlgHom` and `RingHom.equivRatAlgHom` identify the ring homomorphisms between two $\mathbb{Q}$-algebras with the $\mathbb{Q}$-algebra homomorphisms, and `RingEquiv.toRatAlgEquiv` is the version for isomorphisms. The lemma `RingHom.map_rat_algebraMap` is the key step: $f(\operatorname{algebraMap}(q)) = \operatorname{algebraMap}(q)$ for any ring homomorphism $f$.

The module `Mathlib.Algebra.Algebra.Rat` also gives `DivisionRing.toRatAlgebra` (see Section 1) and `DivisionSemiring.toNNRatAlgebra`, the $\mathbb{Q}_{\geq 0}$-algebra structure on a division semiring of characteristic zero. The classes `RingHomClass.toLinearMapClassRat` and `RingHomClass.toLinearMapClassNNRat` say that a ring homomorphism is $\mathbb{Q}$-linear.

The module `Mathlib.Algebra.Algebra.ZMod` treats $\mathbb{Z}/n$. If $R$ has characteristic $p$, then `ZMod.algebra R p` is the $\mathbb{Z}/p$-algebra structure, and `ZMod.instSubsingletonAlgebra` says that a ring has at most one $\mathbb{Z}/p$-algebra structure, for any $p$. The variant `ZMod.algebra'` gives a $\mathbb{Z}/n$-algebra structure when the characteristic $m$ divides $n$. Both are reducible definitions, not instances, so a proof must name them. They take the characteristic as an explicit argument, and the library treats them as local instances that a proof turns on when it needs them.

#### Transfer along equivalences

The module `Mathlib.Algebra.Algebra.TransferInstance` moves an algebra structure along a bijection of types. `Equiv.algebra R e` puts on $\alpha$ the $R$-algebra structure of $\beta$ through $e : \alpha \simeq \beta$, and `Equiv.algEquiv R e` is the resulting isomorphism. The module `Mathlib.Algebra.Algebra.Shrink` applies this to `Shrink α`, a copy of a small type in a lower universe: `Shrink.instAlgebra` is its algebra structure and `Shrink.algEquiv` is the isomorphism with $\alpha$.

#### Common errors

1. `FaithfulSMul R A` is the Mathlib form of "the structure map is injective". The class does not mention `algebraMap`, so a proof gets the injectivity with `FaithfulSMul.algebraMap_injective` and gets the class back with `faithfulSMul_iff_algebraMap_injective`.
2. The product in the group of automorphisms is $\phi\psi = \phi \circ \psi$, but `AlgEquiv.trans` composes in the other order: `ψ.trans φ` is $\phi \circ \psi$. A rewrite with `AlgEquiv.aut_mul` changes the order of the arguments.
3. `ZMod.algebra` is not an instance. A goal that needs a `ZMod p`-algebra structure on a ring of characteristic $p$ must use `letI := ZMod.algebra R p` or a similar local instance.

### Exercises

1. (A) Prove that the structure map of a nonzero algebra over a field is injective, with `faithfulSMul_iff_algebraMap_injective`.
2. (A) Show that the map $\phi \mapsto \phi^{-1}$ on `A ≃ₐ[R] A` agrees with `AlgEquiv.symm`.
3. (B) Prove that the inverse function of a bijective algebra homomorphism commutes with `algebraMap`.
4. (B) Show that a ring homomorphism $f : \mathbb{Q}[X] \to \mathbb{R}$ is determined by $f(X)$, with `RingHom.equivRatAlgHom` and the universal property of Section 1.
5. (B) Prove that $\mathbb{Z}/6$ has no $\mathbb{Z}/3$-algebra structure, by a characteristic argument.
6. (C) Prove `Rat.algebra_rat_subsingleton` on paper: two ring homomorphisms $\mathbb{Q} \to A$ are equal.

### Reference

<?reference?>
