---
title: Building and transferring ring structures
kind: api
modules:
  - Mathlib.Algebra.Ring.InjSurj
  - Mathlib.Algebra.Ring.Hom.InjSurj
  - Mathlib.Algebra.Ring.TransferInstance
  - Mathlib.Algebra.Ring.Shrink
  - Mathlib.Algebra.Ring.ULift
  - Mathlib.Algebra.Ring.PUnit
  - Mathlib.Algebra.Ring.Opposite
  - Mathlib.Algebra.Ring.Ext
  - Mathlib.Algebra.Ring.MinimalAxioms
  - Mathlib.Algebra.Ring.FunLike
  - Mathlib.Algebra.Ring.WithZero
  - Mathlib.Algebra.Ring.Fin
explains:
  E2: [Ring.ofMinimalAxioms, Function.Injective.ring, Function.Surjective.ring, Equiv.ring, Equiv.ringEquiv, Ring.ext, MulOpposite.instRing, RingHom.toOpposite]
  E1: auto
families: []
requires: [V05.C01, V05.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Building and transferring ring structures

### Overview

A ring structure on a type is data: the operations, and the proofs of the axioms. Section 1 states the axioms, and Section 3 shows that a subring is again a ring. This section treats the other ways in which the library produces ring structures. A structure can be built from a short list of axioms. It can be pulled back along an injective map, or pushed forward along a surjective map, when the map respects the operations. It can be carried across a bijection, or to a copy of the type in another universe. And each ring has an opposite ring, with the order of the products reversed.

These constructions are the tools behind many instances of later chapters. The quotient ring of Chapter 2 can get its axioms by a push forward along the quotient map, and the opposite ring turns a right module into a left module in Volume 7. The section also explains the extensionality lemmas, which say when two ring structures on the same type are equal.

### The library around it

#### A ring from few axioms

The class `Ring` has many fields, because it also holds the natural and integer powers and scalar multiples, the subtraction and the casts. The module `Mathlib.Algebra.Ring.MinimalAxioms` gives a constructor that needs only the operations $+$, $\times$, $-$, $0$, $1$ and eight laws. The constructor `Ring.ofMinimalAxioms` asks for the associativity of $+$, the laws $0 + a = a$ and $-a + a = 0$, the associativity of $\times$, the laws $1 a = a = a 1$, and the two distributive laws. It does not ask for the commutativity of addition, because the other laws prove it.

**Proposition.** In a structure with these eight laws, $a + b = b + a$.

*Proof.* The laws $0 + a = a$ and $-a + a = 0$ with associativity make the addition a group, so cancellation holds on both sides. Expand $(1 + 1)(a + b)$ in two ways. The left distributive law and $1 x = x$ give $(1 + 1) a + (1 + 1) b = a + a + b + b$. The right distributive law gives $1 (a + b) + 1 (a + b) = a + b + a + b$. Cancel $a$ on the left and $b$ on the right of $a + a + b + b = a + b + a + b$. This gives $a + b = b + a$. $\square$

The proofs of $0 a = 0$ and $a 0 = 0$ are the usual ones, and the constructor fills the other fields with their default values. The variant `CommRing.ofMinimalAxioms` asks for the commutativity of multiplication and drops the laws that follow from it. Both are definitions, not instances: a user writes `instance : Ring R := Ring.ofMinimalAxioms ...` for a new type.

#### Pulling back and pushing forward

Let $f : S \to R$ be an injective map between types with ring operations, and assume that $f$ respects each operation: $f(x + y) = f x + f y$, $f(x y) = f x \cdot f y$, $f 0 = 0$, $f 1 = 1$, and the same for negation, subtraction, powers, scalar multiples and casts. If $R$ is a ring, then $S$ is a ring. Each axiom for $S$ follows from the axiom for $R$ and injectivity: for example $f(x (y + z)) = f x (f y + f z) = f(x y + x z)$, so $x (y + z) = x y + x z$. The definition is `Function.Injective.ring`. In the other direction, if $f : R \to S$ is surjective and respects the operations, then `Function.Surjective.ring` makes $S$ a ring: two elements of $S$ have preimages, and each law in $S$ is the image of the law in $R$.

The module `Mathlib.Algebra.Ring.InjSurj` has one such definition for each class of the hierarchy: `Function.Injective.semiring`, `Function.Injective.commRing`, `Function.Injective.distrib`, `Function.Injective.addGroupWithOne`, `Function.Surjective.commSemiring`, and so on. They follow the pattern of `Function.Injective.group` from Volume 5. The hypotheses list the operations in a fixed order, and a caller passes one proof for each. For `nsmul` and `zsmul` the hypothesis has the form `∀ n x, f (n • x) = n • f x`. The module `Mathlib.Algebra.Ring.Hom.InjSurj` adds `Function.Injective.isDomain`: a ring with an injective homomorphism of monoids with zero into a domain is a domain.

The subrings of Section 3 get their ring structure by this pull back along the inclusion. The quotient rings of Chapter 2 can get theirs by the push forward along the quotient map.

#### Transfer along a bijection

A bijection $e : \alpha \simeq \beta$ carries each structure on $\beta$ to $\alpha$: define $x + y = e^{-1}(e x + e y)$ and $x y = e^{-1}(e x \cdot e y)$. The module `Mathlib.Algebra.Ring.TransferInstance` gives `Equiv.ring`, `Equiv.commRing`, `Equiv.semiring` and the other classes. With these structures the bijection is a ring isomorphism, `Equiv.ringEquiv e : α ≃+* β`, with `Equiv.ringEquiv_apply` and `Equiv.ringEquiv_symm_apply`. The lemma `Equiv.isDomain` transfers the property of being a domain. The construction is a special case of the pull back along an injective map, since $e$ is injective and respects the transferred operations by definition.

Two special cases have their own modules. The type `Shrink α` is a copy of a small type $\alpha$ in a lower universe. The module `Mathlib.Algebra.Ring.Shrink` gives it the ring instances, such as `Shrink.instRing`, `Shrink.instCommRing` and `Shrink.instIsDomain`, and the isomorphism `Shrink.ringEquiv`. The type `ULift R` is a copy of $R$ in a higher universe. The module `Mathlib.Algebra.Ring.ULift` gives the instances `ULift.ring`, `ULift.commRing` and the others, the isomorphism `ULift.ringEquiv : ULift R ≃+* R`, and the map `RingHom.ulift` of a ring homomorphism. The simp lemmas `ULift.up_natCast`, `ULift.down_natCast`, `ULift.up_intCast` and `ULift.up_ofNat` move casts across `ULift.up` and `ULift.down`.

#### Small examples

The one-point type is the zero ring: `PUnit.commRing` in `Mathlib.Algebra.Ring.PUnit`. It is the terminal object of the category of rings. The module `Mathlib.Algebra.Ring.WithZero` gives `WithZero α` a semiring structure when $\alpha$ has one, with `WithZero.instSemiring` and `WithZero.instDistrib`. The module `Mathlib.Algebra.Ring.Fin` holds `RingEquiv.piFinTwo`, the isomorphism between functions on `Fin 2` and pairs: $\prod_{i \in \{0, 1\}} R_i \cong R_0 \times R_1$.

The module `Mathlib.Algebra.Ring.FunLike` builds ring structures on a type of bundled maps from the pointwise operations. The definitions `FunLike.ring`, `FunLike.commRing` and `FunLike.semiring` take a type `F` with an injective coercion to functions that respects the operations. The variants `FunLike.compRing` and `FunLike.compSemiring` use composition as the multiplication, for maps from a type to itself. They are abbreviations, not instances, to keep the instance search short.

#### The opposite ring

The opposite ring $R^{\mathrm{op}}$ has the same elements and the same addition as $R$, and the product $x \cdot_{\mathrm{op}} y = y x$. The type is `Rᵐᵒᵖ`, with the maps `MulOpposite.op` and `MulOpposite.unop` from Volume 5, and `MulOpposite.op_mul` says $\mathrm{op}(x y) = \mathrm{op}(y)\,\mathrm{op}(x)$. The module `Mathlib.Algebra.Ring.Opposite` gives the instances `MulOpposite.instSemiring`, `MulOpposite.instRing`, `MulOpposite.instCommRing` and `MulOpposite.instIsDomain`. The axioms of $R^{\mathrm{op}}$ follow from those of $R$: the left distributive law of $R^{\mathrm{op}}$ is the right distributive law of $R$. For a commutative ring, $R \cong R^{\mathrm{op}}$ by `RingEquiv.toOpposite`. The additive opposite `Rᵃᵒᵖ` reverses the addition, and the module gives it the same instances, such as `AddOpposite.instRing`. The casts commute with `op`: `MulOpposite.op_natCast`, `MulOpposite.op_intCast` and `MulOpposite.op_ofNat`.

The module also handles homomorphisms. A homomorphism $f : R \to S$ gives $f^{\mathrm{op}} : R^{\mathrm{op}} \to S^{\mathrm{op}}$, and `RingHom.op` is this bijection, with inverse `RingHom.unop`. A map $f : R \to S$ that is additive and multiplicative is also a homomorphism $R \to S^{\mathrm{op}}$ when its values commute. *Proof.* In $S^{\mathrm{op}}$ the product of $f x$ and $f y$ is $f y \cdot f x$, and this equals $f x \cdot f y = f(x y)$ by the hypothesis. $\square$ The definition is `RingHom.toOpposite`, and `RingHom.fromOpposite` is the version with source $R^{\mathrm{op}}$. The non-unital forms are `NonUnitalRingHom.op`, `NonUnitalRingHom.toOpposite` and `NonUnitalRingHom.fromOpposite`.

#### Equality of ring structures

Two ring structures on the same type are equal when they have the same addition and the same multiplication. The rest of the data, such as the zero, the negation, the powers and the casts, is determined by these two operations. The module `Mathlib.Algebra.Ring.Ext` proves this for each class: `Ring.ext`, `CommRing.ext`, `Semiring.ext`, `NonAssocRing.ext`, `NonUnitalRing.ext`, with the forms `Semiring.ext_iff` and `CommSemiring.ext_iff`. For the additive classes with a one, such as `AddMonoidWithOne.ext`, the hypotheses are the addition and the one. The lemmas `Ring.toSemiring_injective` and `CommRing.toRing_injective` say that the forgetful maps between the classes are injective. The proof of `Ring.ext` reduces to the extensionality of each parent structure: the zero is determined by the addition as its neutral element, the one by the multiplication, and the negation as the inverse in the additive group.

These lemmas matter when two instances meet in one goal, for example when a type has a ring structure from a general construction and another from a special one. If the two operations agree, `Ring.ext` shows that the structures are equal, and the goal can be rewritten.

#### Common errors

1. The definitions `Function.Injective.ring` and `Equiv.ring` are not instances. A user must declare the instance with `instance : Ring S := ...`, and must give the operations on $S$ first, since the hypotheses speak about them.
2. In `Rᵐᵒᵖ` the product is reversed, so `MulOpposite.op (x * y)` is `op y * op x`. A rewrite with `MulOpposite.op_mul` swaps the factors, and forgetting this gives a goal that `simp` cannot close.
3. A homomorphism $R \to S^{\mathrm{op}}$ is an anti-homomorphism $R \to S$, not a homomorphism. The transpose of matrices over a commutative ring is an example: it is a ring homomorphism to the opposite ring.

### Exercises

1. (A) Use `Function.Injective.ring` to show that a subset of a ring that contains $0$ and $1$ and is closed under $+$, $-$ and $\times$ is a ring.
2. (A) Show that the map $x \mapsto x^{\mathrm{op}}$ is a ring isomorphism $R \to R^{\mathrm{op}}$ if and only if $R$ is commutative.
3. (B) Show that the transpose is a ring isomorphism $M_n(R) \to M_n(R)^{\mathrm{op}}$ for a commutative ring $R$.
4. (B) Let $e : \alpha \simeq \mathbb{Z}$ be a bijection. Describe the ring structure `Equiv.ring e` on $\alpha$, and prove that `Equiv.ringEquiv e` is a ring isomorphism.
5. (B) Prove that a structure with the eight laws of `Ring.ofMinimalAxioms` satisfies $0 a = 0$ and $(-a) b = -(a b)$.
6. (C) Show that the endomorphism ring of the additive group $\mathbb{Z}^2$, with composition, is isomorphic to its opposite ring.

### Reference

<?reference?>
