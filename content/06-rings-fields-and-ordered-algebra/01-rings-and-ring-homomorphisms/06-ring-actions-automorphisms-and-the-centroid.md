---
title: Ring actions, automorphisms and the centroid
kind: api
modules:
  - Mathlib.Algebra.Ring.Action.Basic
  - Mathlib.Algebra.Ring.Action.Group
  - Mathlib.Algebra.Ring.Action.End
  - Mathlib.Algebra.Ring.Action.ConjAct
  - Mathlib.Algebra.Ring.Action.Field
  - Mathlib.Algebra.Ring.Action.Invariant
  - Mathlib.Algebra.Ring.Action.Rat
  - Mathlib.Algebra.Ring.Action.Submonoid
  - Mathlib.Algebra.Ring.Action.Subobjects
  - Mathlib.Algebra.Ring.Aut
  - Mathlib.Algebra.Ring.AddAut
  - Mathlib.Algebra.Ring.CentroidHom
explains:
  E2: [MulSemiringAction, MulSemiringAction.toRingHom, MulSemiringAction.toRingAut, RingAut, IsInvariantSubring, CentroidHom, CentroidHom.comp_mul_comm, CentroidHom.centerIsoCentroid]
  E1: auto
families: []
requires: [V05.C01, V05.C02, V05.C03]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Ring actions, automorphisms and the centroid

### Overview

A group acts on a ring when each group element moves the ring by a ring automorphism. The Galois group of a field extension acts on the large field in this way, and a group of symmetries of a space acts on the ring of functions on that space. Volume 5 defines group actions on sets and actions by additive automorphisms. This section treats the ring case: the class `MulSemiringAction`, the group `RingAut R` of ring automorphisms, the subrings that an action preserves, and the fixed points.

The second half of the section treats the centroid of a ring. A centroid homomorphism is an additive map $T : A \to A$ that commutes with left and right multiplication: $T(a b) = T(a) b = a T(b)$. The centroid is the natural ring of scalars of a nonassociative algebra, and for a ring with a unit it is the center. Both topics use the homomorphisms and the subrings of Sections 2 and 3.

### The library around it

#### Monoid actions on rings

Let $M$ be a monoid and $R$ a semiring. An action of $M$ on $R$ is a `MulSemiringAction M R` when each map $x \mapsto m \cdot x$ is a ring endomorphism:
$$m \cdot (x + y) = m \cdot x + m \cdot y, \quad m \cdot 0 = 0, \quad m \cdot (x y) = (m \cdot x)(m \cdot y), \quad m \cdot 1 = 1.$$
The class extends `DistribMulAction M R`, which holds the two additive laws, and adds the fields `MulSemiringAction.smul_mul` and `MulSemiringAction.smul_one`. Through `MulSemiringAction.toMulDistribMulAction` it is also an action on the multiplicative monoid of $R$. The module `Mathlib.Algebra.Ring.Action.Basic` gives the bundled form: `MulSemiringAction.toRingHom M R m` is the map $x \mapsto m \cdot x$ as a ring homomorphism `R →+* R`, and `toRingHom_injective` says that the map $m \mapsto (x \mapsto m \cdot x)$ is injective when the action is faithful.

The ring endomorphisms of $R$ act on $R$ by evaluation: `RingHom.applyMulSemiringAction` with `RingHom.smul_def`, which says $f \cdot a = f(a)$. This action is faithful by `RingHom.applyFaithfulSMul`. A homomorphism of monoids $N \to M$ turns an action of $M$ into an action of $N$, by `MulSemiringAction.compHom`. The module `Mathlib.Algebra.Ring.Action.Subobjects` restricts an action to a submonoid or a subgroup, with `Submonoid.mulSemiringAction` and `Subgroup.mulSemiringAction`.

An algebra is not a ring action in general. The scalar multiplication $r \cdot x$ of an $R$-algebra is additive in $x$, but $r \cdot (x y) = (r \cdot x) y \ne (r \cdot x)(r \cdot y)$. The two notions answer different questions: an algebra uses the ring $R$ as scalars, and a ring action uses a group as symmetries.

#### Group actions and ring automorphisms

The ring automorphisms of $R$ form a group `RingAut R` under composition. The module `Mathlib.Algebra.Ring.Aut` defines it as `R ≃+* R`, with `RingAut.mul_apply` for $(f g)(x) = f(g(x))$, `RingAut.one_apply`, `RingAut.inv_apply` and `RingAut.coe_pow`. Forgetful homomorphisms send it to the other automorphism groups: `RingAut.toAddAut`, `RingAut.toMulAut` and `RingAut.toPerm`.

For a group $G$, an action by ring endomorphisms is an action by ring automorphisms, since $g^{-1}$ gives the inverse map. The module `Mathlib.Algebra.Ring.Action.Group` defines `MulSemiringAction.toRingEquiv G R : G →* R ≃+* R`, and `Mathlib.Algebra.Ring.Action.End` gives the same homomorphism into the group, `MulSemiringAction.toRingAut G R : G →* RingAut R`. Conversely, `RingAut.applyMulSemiringAction` makes `RingAut R` act on $R$ by evaluation, and the action is faithful (`RingAut.apply_faithfulSMul`). So an action of $G$ on $R$ by ring automorphisms is the same as a group homomorphism $G \to \mathrm{Aut}(R)$, as for actions on sets in Volume 5.

Two actions come from the units of the ring. The units act on $R$ by conjugation, $u \cdot x = u x u^{-1}$, and this is an action by ring automorphisms: `ConjAct.unitsMulSemiringAction` in `Mathlib.Algebra.Ring.Action.ConjAct`. The units also act by left and right multiplication, but these maps are only additive: `AddAut.mulLeft` and `AddAut.mulRight` in `Mathlib.Algebra.Ring.AddAut` give homomorphisms from $R^\times$ to the additive automorphisms of $R$.

In a division ring, a ring action respects inverses: `smul_inv''` in `Mathlib.Algebra.Ring.Action.Field` states $m \cdot x^{-1} = (m \cdot x)^{-1}$. *Proof.* If $x = 0$ both sides are $0$. Otherwise $(m \cdot x)(m \cdot x^{-1}) = m \cdot (x x^{-1}) = m \cdot 1 = 1$, and in a division ring a right inverse is the inverse. $\square$ The module `Mathlib.Algebra.Ring.Action.Rat` holds the scalar actions of $\mathbb{Q}$ and $\mathbb{Q}_{\ge 0}$ on a division ring, such as `Rat.instDistribSMul`.

#### Invariant subrings and fixed points

A subring $S \subseteq R$ is invariant under an action of $M$ if $m \cdot x \in S$ for all $m \in M$ and $x \in S$. The class is `IsInvariantSubring M S`, with the field `IsInvariantSubring.smul_mem`. An invariant subring inherits the action, by `IsInvariantSubring.toMulSemiringAction`, and the inclusion `IsInvariantSubring.subtypeHom` is equivariant. The class asks for stability, not for each element to be fixed.

The fixed points $R^M = \{x \in R : m \cdot x = x \text{ for all } m\}$ form a subring, the ring of invariants. The module `Mathlib.Algebra.Ring.Action.Submonoid` records the additive part: `FixedPoints.addSubmonoid M α` and `FixedPoints.addSubgroup M α`, with membership lemmas `FixedPoints.mem_addSubmonoid` and `FixedPoints.mem_addSubgroup`. The subring of fixed points of a field is the fixed field of Galois theory, and Volume 11 develops it with `FixedPoints.subfield`.

#### Centroid homomorphisms

Let $A$ be a nonassociative, nonunital semiring. A centroid homomorphism is an additive map $T : A \to A$ with
$$T(a b) = T(a)\, b \quad \text{and} \quad T(a b) = a\, T(b)$$
for all $a, b \in A$. The type is `CentroidHom A`, defined in `Mathlib.Algebra.Ring.CentroidHom`, with the class `CentroidHomClass` and its fields `CentroidHomClass.map_mul_left` and `CentroidHomClass.map_mul_right`. The maps follow the bundled design of the other morphisms: a coercion to functions, `CentroidHom.ext` for extensionality, `CentroidHom.comp` and `CentroidHom.id` for composition and the identity, and `CentroidHom.copy`. For a module $A$ over a commutative ring $R$ whose scalars commute with the product, multiplication by a scalar is a centroid homomorphism, by `Module.toCentroidHom`.

The centroid homomorphisms form a semiring under pointwise addition and composition: `CentroidHom.instSemiring`, and `CentroidHom.instRing` when $A$ is a ring. The map `CentroidHom.toEnd` embeds it into the ring `AddMonoid.End A` of additive endomorphisms, and `CentroidHom.toEndRingHom` is the bundled ring homomorphism. The lemma `CentroidHom.centroid_eq_centralizer_mulLeftRight` describes the image: it is the centralizer of the left and right multiplications. The simp lemmas `CentroidHom.toEnd_add`, `CentroidHom.toEnd_mul` and `CentroidHom.toEnd_pow` say that `CentroidHom.toEnd` respects the operations.

Two centroid homomorphisms commute on products.

**Proposition.** For $S, T$ in the centroid and $a, b \in A$, $T(S(a b)) = S(T(a b))$.

*Proof.* Use the two laws in turn: $T(S(a b)) = T(S(a)\, b) = S(a)\, T(b) = S(a\, T(b)) = S(T(a b))$. $\square$

The lemma is `CentroidHom.comp_mul_comm`. If each element of $A$ is a sum of products, the centroid is commutative. The library proves a variant: `CentroidHom.commRing` makes the centroid a commutative ring when $A$ has the property that $a r b = 0$ for all $r$ implies $a = 0$ or $b = 0$.

#### The centroid and the center

For a semiring $A$ with a unit, the centroid is the center. A central element $z$ gives the centroid homomorphism $x \mapsto z x$. In the other direction, a centroid homomorphism $T$ satisfies $T(x) = T(1 \cdot x) = T(1)\, x$ and $T(x) = T(x \cdot 1) = x\, T(1)$, so $T$ is multiplication by $T(1)$, and $T(1)$ commutes with each $x$. The isomorphism is `CentroidHom.centerIsoCentroid`, from the center `Subsemiring.center A` to `CentroidHom A`. Without a unit there is only a homomorphism `CentroidHom.centerToCentroid` from the nonunital center, and the centroid can be larger.

The center of a nonassociative semiring has a stronger definition than for a ring: an element $z$ is central if it commutes with each element and associates with each pair. The lemma `NonUnitalNonAssocSemiring.mem_center_iff` states this condition in terms of left and right multiplication, and `NonUnitalNonAssocCommSemiring.mem_center_iff` simplifies it for a commutative multiplication.

#### Common errors

1. An algebra structure `Algebra R A` is not a `MulSemiringAction R A`. The scalar multiplication of an algebra does not respect products in the way that an action does, so the lemmas of this section do not apply to it.
2. `IsInvariantSubring M S` says that $S$ is stable under the action, not that the action fixes each element of $S$. The elements fixed by the action form `FixedPoints.addSubgroup`, or the subfield of fixed points in a field.
3. For a ring without a unit, `CentroidHom.centerIsoCentroid` does not apply. The centroid of $2\mathbb{Z}$ with the usual product, for example, contains the identity map, which is not multiplication by an element of $2\mathbb{Z}$.

### Exercises

1. (A) Show that complex conjugation gives an action of the group $\mathbb{Z}/2$ on $\mathbb{C}$ by ring automorphisms, and compute its ring of invariants.
2. (A) Prove that the only ring automorphism of $\mathbb{Q}$ is the identity, so `RingAut ℚ` is trivial.
3. (B) Let $G$ act on $R$ by ring automorphisms. Show that the fixed points form a subring, and that it is a subfield when $R$ is a field.
4. (B) Show that the conjugation action of $R^\times$ on $R$ is trivial if and only if each unit of $R$ is central.
5. (B) Compute the centroid of the ring $M_n(K)$ of matrices over a field $K$, and check that it agrees with the center.
6. (C) Let $A$ be a nonunital ring with $A^2 = A$, that is, each element is a sum of products. Prove that the centroid of $A$ is commutative.

### Reference

<?reference?>
