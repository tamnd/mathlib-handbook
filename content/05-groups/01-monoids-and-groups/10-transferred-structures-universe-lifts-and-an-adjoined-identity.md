---
title: Transferred structures, universe lifts and an adjoined identity
kind: api
modules:
  - Mathlib.Algebra.Group.InjSurj
  - Mathlib.Algebra.Group.TransferInstance
  - Mathlib.Algebra.Group.Shrink
  - Mathlib.Algebra.Group.ULift
  - Mathlib.Algebra.Group.PUnit
  - Mathlib.Algebra.Group.WithOne.Defs
  - Mathlib.Algebra.Group.WithOne.Basic
  - Mathlib.Algebra.Group.WithOne.Map
explains:
  E2: [Function.Injective.group, Function.Surjective.group, Equiv.group, Equiv.mulEquiv, Finite.exists_type_univ_nonempty_mulEquiv, MulEquiv.ulift, WithOne.lift, WithOne.coe_mul]
  E1: auto
families: []
requires: [V01.C03, V01.C04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Transferred structures, universe lifts and an adjoined identity

### Overview

A new type often gets its group structure from an old one. A subtype gets it by an injective map into a group. A quotient gets it by a surjective map out of a group. A type in bijection with a group gets it by the bijection. In each case the group axioms on the new type follow from the axioms on the old type, and the proof is the same each time. The module `Mathlib.Algebra.Group.InjSurj` writes this proof once for each class of the hierarchy, and `Mathlib.Algebra.Group.TransferInstance` does it for an equivalence.

The other modules of this section apply this idea to standard constructions of types. `ULift α` moves `α` to a higher universe, `Shrink α` moves a small type to a lower universe, and the type PUnit is the trivial group. The last construction is different: `WithOne α` adds a new identity element to a semigroup, and it makes a monoid. The section explains each construction, its simp lemmas and its universal property. It uses the classes of Chapter 1 and the homomorphisms of Chapter 2.

### The library around it

#### Structures along injective and surjective maps

**Theorem (Pullback of a group structure).** Let $M_1$ have a product, an identity, an inverse, a division and powers by $\mathbb{N}$ and $\mathbb{Z}$. Let $M_2$ be a group and let $f : M_1 \to M_2$ be injective. If $f$ preserves each of these operations, then $M_1$ is a group.

*Proof.* Each axiom is an equation between two terms. Apply $f$ to both sides and push $f$ inside with the hypotheses. The two images are equal by the axiom in $M_2$. Then $f$ is injective, so the two terms are equal in $M_1$. $\square$

The construction is `Function.Injective.group`. Its arguments are the map, the proof of injectivity and one equation for each operation: `f 1 = 1`, `f (x * y) = f x * f y`, `f x⁻¹ = (f x)⁻¹`, `f (x / y) = f x / f y`, and the two equations for the powers. The powers are part of the data of a group in Mathlib, so the caller gives them. The same pattern gives `Function.Injective.monoid`, `Function.Injective.commGroup`, `Function.Injective.cancelMonoid`, `Function.Injective.divisionMonoid` and one construction for each other class. The cancellation properties are propositions, and `Function.Injective.isCancelMul` is a theorem.

**Theorem (Pushforward of a group structure).** Let $M_1$ be a group and let $f : M_1 \to M_2$ be surjective. If $f$ preserves the operations, then $M_2$ is a group.

*Proof.* Each element of $M_2$ is $f(x)$ for some $x$. Write each side of an axiom with such elements, pull $f$ out with the hypotheses, and apply the axiom in $M_1$. $\square$

The construction is `Function.Surjective.group`, with the same list of hypotheses. The list of the surjective forms is shorter, because cancellation does not pass along a surjection: a quotient of a cancellative monoid need not cancel. These constructions are definitions with the keyword abbrev, and they are not instances. A typical use is the definition of an instance on a subtype, for example `Subtype.coe_injective.group _ rfl (fun _ _ => rfl) ...`, where each equation holds by definition.

#### Structures along an equivalence

The module `Mathlib.Algebra.Group.TransferInstance` transfers a structure along an equivalence `e : α ≃ β`. The operations on `α` are defined from those of `β` by conjugation with $e$.

| Lean name | Statement |
|---|---|
| `Equiv.mul_def` | $x y = e^{-1}(e(x) e(y))$ |
| `Equiv.one_def` | $1 = e^{-1}(1)$ |
| `Equiv.inv_def` | $x^{-1} = e^{-1}(e(x)^{-1})$ |
| `Equiv.pow_def` | $x^n = e^{-1}(e(x)^n)$ |
| `Equiv.smul_def` | $n \cdot x = e^{-1}(n \cdot e(x))$ |

With these operations, `Equiv.group e` makes `α` a group when `β` is one, and the same pattern gives `Equiv.monoid`, `Equiv.commGroup`, `Equiv.addCommGroup` and the others. The proof is `Function.Injective.group` for the injective map $e$. With the transferred product, $e$ becomes an isomorphism: `Equiv.mulEquiv e` is the form `α ≃* β` of $e$, and `Equiv.addEquiv e` is the additive form.

**Theorem (Finite groups in any universe).** A finite group in a universe $u$ is isomorphic to a finite group in each universe $v$.

*Proof.* A finite type with $n$ elements is in bijection with `Fin n`, and so with `ULift (Fin n)` in the universe $v$. Transfer the group structure along this bijection with `Equiv.group`. Then `Equiv.mulEquiv` gives the isomorphism. $\square$

The lemma is `Finite.exists_type_univ_nonempty_mulEquiv`. It lets a statement about all finite groups in one universe apply to finite groups in another universe.

#### Universe lifts and shrinking

The type `ULift α` is a copy of `α` in a higher universe, with the projection down. The module `Mathlib.Algebra.Group.ULift` gives the copy each structure of `α`, from `ULift.mul` and `ULift.one` to `ULift.group` and `ULift.commGroup`. The simp lemmas have the pattern `ULift.<op>_down`: for example `ULift.mul_down` states $(x y).\mathrm{down} = x.\mathrm{down} \cdot y.\mathrm{down}$, and `ULift.one_down` states $1.\mathrm{down} = 1$. The isomorphism `MulEquiv.ulift` is `ULift α ≃* α`, and `AddEquiv.ulift` is the additive form.

For a type `α` that is small in a lower universe, `Shrink α` is a copy of `α` in that universe, with the equivalence `equivShrink α : α ≃ Shrink α`. The module `Mathlib.Algebra.Group.Shrink` transfers the structures to it, by the method of the previous part: `Shrink.instGroup`, `Shrink.instCommGroup` and the others. The lemmas `equivShrink_mul` and `equivShrink_symm_mul` state that the equivalence respects the product, and `Shrink.mulEquiv` is the isomorphism `Shrink α ≃* α`. The actions pass too, by `Shrink.instMulAction`.

The type PUnit has one element. The module `Mathlib.Algebra.Group.PUnit` makes it a commutative group, by `PUnit.commGroup`, and an additive commutative group, by `PUnit.addCommGroup`. Each operation gives the unique element: `PUnit.mul_eq` states $x y = \mathrm{unit}$, and `PUnit.one_eq` and `PUnit.inv_eq` are the same for the identity and the inverse. This is the trivial group, the terminal object of the category of groups.

#### Adjoining an identity

**Definition (Adjoined identity).** Let $\alpha$ be a semigroup. The type `WithOne α` has the elements of $\alpha$ and one new element $1$. The product extends the product of $\alpha$, and $1$ is an identity.

The elements of $\alpha$ enter by the coercion `WithOne.coe`, and `WithOne.coe_inj` states that it is injective. The new element is not in the image, by `WithOne.coe_ne_one`. A proof about `WithOne α` usually splits into two cases, by `WithOne.cases_on`, or by `WithOne.forall` and `WithOne.exists`. The partial inverse `WithOne.unone` takes an element $x \neq 1$ back to $\alpha$, and `WithOne.unoneD d` sends $1$ to the default value $d$.

**Theorem (Adjoined identity makes a monoid).** If $\alpha$ is a semigroup, then `WithOne α` is a monoid. If $\alpha$ is commutative, then `WithOne α` is a commutative monoid.

*Proof.* Associativity has eight cases, by whether each of the three factors is $1$. In each case with a factor $1$, both sides reduce to the product of the other factors. The case with no factor $1$ is associativity in $\alpha$, by `WithOne.coe_mul`. Commutativity is the same with four cases. $\square$

The instances are `WithOne.instMonoid` and `WithOne.instCommMonoid`. An inverse on $\alpha$ extends with $1^{-1} = 1$, by `WithOne.instInv`, and `WithOne.coe_inv` states that the coercion respects it. The construction adds a new identity even when $\alpha$ is already a monoid, so `WithOne α` then has two idempotents.

**Theorem (Universal property).** Let $\alpha$ have a product and let $M$ be a monoid. Each multiplicative map $f : \alpha \to M$ extends in exactly one way to a monoid homomorphism `WithOne α →* M`.

*Proof.* The extension must send $1$ to $1$ and $a$ to $f(a)$. These values define a monoid homomorphism, by a case check for each product. $\square$

The equivalence is `WithOne.lift`, from `α →ₙ* M` to `WithOne α →* M`. The lemmas `WithOne.lift_coe` and `WithOne.lift_one` compute it, and `WithOne.lift_unique` is the uniqueness. The functor on maps is `WithOne.mapMulHom`, and on isomorphisms it is `MulEquiv.withOneCongr`. The module `Mathlib.Algebra.Group.WithOne.Map` has the maps of types `WithOne.map` and `WithOne.map₂`, with the lemmas `WithOne.map_coe` and `WithOne.map₂_coe_coe`. The additive form of the whole construction is `WithZero`, and Chapter 9 uses it to adjoin a zero to a group.

#### Common errors

1. A learner declares `Function.Injective.group` as an instance. It is a definition with explicit hypotheses, and it must be applied inside an instance declaration, with each equation proved.
2. A learner expects `Equiv.group e` to make $e$ an isomorphism of the original structures on `α` and `β`. It defines a new structure on `α`. If `α` already has a product, the two products can differ, and Lean sees two instances.
3. A learner uses `WithOne α` for a monoid `α` and expects the old identity to remain the identity. The coercion sends the old identity to an element different from the new $1$.

### Exercises

1. (A) Let $H$ be a subset of a group $G$ that contains $1$ and is closed under products and inverses. Write down the hypotheses of `Function.Injective.group` for the inclusion of $H$ into $G$, and say why each holds by definition.
2. (A) Prove `(x * y).down = x.down * y.down` for `x y : ULift G`, and state the isomorphism `MulEquiv.ulift`.
3. (B) Let $e : \alpha \simeq \mathbb{Z}$ be a bijection. Describe the identity of `α` under `Equiv.addGroup e`, and show that $e$ is an additive isomorphism for this structure.
4. (B) Show that the semigroup $(\mathbb{N}_{\geq 1}, +)$ with an adjoined identity is isomorphic to $(\mathbb{N}, +)$, with the additive form of `WithOne.lift`.
5. (B) Let $M$ be a monoid. Prove that the map `WithOne M →* M` that extends the identity map of $M$ is surjective but not injective.
6. (B) Prove that cancellation does not pass along a surjective homomorphism: give a cancellative commutative monoid with a quotient that does not cancel.

### Reference

<?reference?>
