---
title: Transport of shifts and shift sequences
kind: api
modules:
  - Mathlib.CategoryTheory.Shift.Adjunction
  - Mathlib.CategoryTheory.Shift.Pullback
  - Mathlib.CategoryTheory.Shift.Opposite
  - Mathlib.CategoryTheory.Shift.Induced
  - Mathlib.CategoryTheory.Shift.Localization
  - Mathlib.CategoryTheory.Shift.Linear
  - Mathlib.CategoryTheory.Shift.Quotient
  - Mathlib.CategoryTheory.Shift.Twist
  - Mathlib.CategoryTheory.Shift.CommShiftTwo
  - Mathlib.CategoryTheory.Shift.ShiftSequence
  - Mathlib.CategoryTheory.Shift.InducedShiftSequence
  - Mathlib.CategoryTheory.Shift.SingleFunctors
  - Mathlib.CategoryTheory.Shift.SingleFunctorsLift
explains:
  E2: [CategoryTheory.Adjunction.rightAdjointCommShift, CategoryTheory.Equivalence.commShiftInverse, CategoryTheory.PullbackShift, CategoryTheory.HasShift.localized, CategoryTheory.HasShift.quotient, CategoryTheory.TwistShiftData, CategoryTheory.Functor.ShiftSequence, CategoryTheory.Functor.shiftMap, CategoryTheory.SingleFunctors]
  E1: auto
families: []
requires: [V24.C05, V24.C07, V24.C08, V25.C04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Transport of shifts and shift sequences

### Overview

Section 1 defined a shift on a category, a functor that commutes with shifts, and shifted morphisms. In practice a shift is rarely built from nothing. It comes from another category by a construction: an adjunction, an equivalence, a change of the index monoid, the opposite category, a fully faithful functor, a localization or a quotient. The homotopy category of complexes is a quotient, and the derived category is a localization. The modules of this section make each construction carry the shift and the commutation isomorphisms.

The section has three parts. The first part transports shifts and `CommShift` structures along the constructions above. The second part changes the coherence isomorphisms of a shift by units of the center of the category, and uses this to define bifunctors that commute with shifts in two variables, with the sign $(-1)^{pq}$ of the tensor product of complexes. The third part treats families of functors indexed by the shift monoid. A shift sequence for a homological functor $H$ is a family $H^n$ with $H^n(X) \cong H(X[n])$, and the single functors of complexes form a family $C \to D$ that is compatible with the shift of $D$.

In the text $g \circ f$ is the textbook composite, and Mathlib writes `f ≫ g`. The shift of $X$ by $a$ is $X[a]$, written `X⟦a⟧`, and the shift of a morphism $f$ is written `f⟦a⟧'`.

### The library around it

#### Adjunctions and equivalences

The module `Mathlib.CategoryTheory.Shift.Adjunction` works with an adjunction $F \dashv G$ between categories $C$ and $D$ that have shifts by $A$. The class `Adjunction.CommShift adj A` assumes `F.CommShift A` and `G.CommShift A`, and it says that the unit and the counit commute with the shifts, in the sense of `NatTrans.CommShift` from Section 1. It is a property, not data.

**Proposition.** Let $A$ be an additive group and let $F \dashv G$. A `CommShift` structure on $F$ gives a unique `CommShift` structure on $G$ that makes the adjunction compatible with the shifts. This is `Adjunction.rightAdjointCommShift`, and the reverse direction is `Adjunction.leftAdjointCommShift`.

*Proof sketch.* Fix $a$ with inverse $-a$. The isomorphism $\varphi_a : F(X[a]) \cong F(X)[a]$ gives, by the theory of mates of Volume 24, Chapter 5, an isomorphism $G(Y[a]) \cong G(Y)[a]$, because $T_a$ is an equivalence with inverse $T_{-a}$ and so has $T_{-a}$ as a right adjoint. The condition `Adjunction.CommShift.CompatibilityUnit` says that $\eta_X[a] = \psi_a(FX) \circ G(\varphi_a(X)) \circ \eta_{X[a]}$, and the lemma `Adjunction.CommShift.compatibilityUnit_unique_right` says that $\varphi_a$ fixes $\psi_a$ through this equation. The condition holds for $a = 0$ and is stable under the addition of indices, so the family $\psi_a$ satisfies the coherence of a `CommShift` structure. The condition on the counit, `Adjunction.CommShift.CompatibilityCounit`, follows from the one on the unit by the triangle identities. $\square$

The instances `Adjunction.commShift_of_leftAdjoint` and `Adjunction.commShift_of_rightAdjoint` record that the adjunction is compatible with the shifts for the structures so built. For an equivalence $E : C \simeq D$ the class `Equivalence.CommShift E A` packages the same condition for the unit and counit isomorphisms. The definition `Equivalence.commShiftInverse` gives a `CommShift` structure on `E.inverse` from one on `E.functor`, and `Equivalence.commShiftFunctor` goes the other way. The constructor `Equivalence.CommShift.mk'` checks the condition on the adjunction of $E$.

#### Change of index, opposites and induced shifts

The module `Mathlib.CategoryTheory.Shift.Pullback` changes the index monoid. Let $\varphi : A \to B$ be a morphism of additive monoids and let $C$ have a shift by $B$. The type synonym `PullbackShift C φ` is $C$ with the shift by $A$ given by $X \mapsto X[\varphi(a)]$. The isomorphism `pullbackShiftIso C φ a b h` identifies the shift by $a$ with the shift by $b$ when $b = \varphi(a)$. The definition `PullbackShift.functor` sees a functor $F : C \to D$ as a functor between the pullback shifts, and the instance `Functor.commShiftPullback` gives its `CommShift` structure. The definitions `PullbackShift.natTrans` and `PullbackShift.adjunction`, with the instance `Adjunction.commShiftPullback`, do the same for natural transformations and adjunctions. The sum map $M \times M \to M$ is used below.

The module `Mathlib.CategoryTheory.Shift.Opposite` gives the naive shift on the opposite category. The type synonym `OppositeShift C A` is $C^{\mathrm{op}}$ with the shift by $a$ equal to the opposite of the shift by $a$ on $C$. For a functor $F$ that commutes with shifts, `OppositeShift.functor A F` is $F^{\mathrm{op}}$ between these categories, and `Functor.commShiftOp` gives its `CommShift` structure. The definition `Functor.commShiftUnop` goes back. The definitions `OppositeShift.natTrans` and `OppositeShift.adjunction` treat natural transformations and adjunctions, and the instance `Adjunction.commShift_op` says that the opposite adjunction is compatible with the shifts. This naive shift is not the shift that makes $C^{\mathrm{op}}$ pretriangulated: Section 5 uses the shift by $-n$ instead.

The module `Mathlib.CategoryTheory.Shift.Induced` puts a shift on the target of a functor. Let $F : C \to D$ be a functor such that precomposition with $F$ is full and faithful on functor categories, for example a localization functor or a quotient functor. Let $s_a : D \to D$ be functors with isomorphisms $s_a \circ F \cong F \circ T_a$. Then `HasShift.induced F A s i` is a shift on $D$ whose shift functors are the $s_a$, as the lemma `shiftFunctor_of_induced` states. The definition `Functor.CommShift.ofInduced` makes $F$ commute with the shifts.

#### Localization and quotients

The module `Mathlib.CategoryTheory.Shift.Localization` applies the induced shift to a localization. A morphism property $W$ on $C$ is compatible with the shift when $f \in W$ if and only if $f[a] \in W$, for all $a$. This is the class `MorphismProperty.IsCompatibleWithShift W A`, and `MorphismProperty.IsCompatibleWithShift.iff` is the equivalence for one morphism.

**Proposition.** Let $L : C \to D$ be a localization functor for $W$, and let $W$ be compatible with the shift by $A$. Then $D$ has a shift by $A$, and $L$ commutes with the shifts. These are `HasShift.localized L W A` and `Functor.CommShift.localized L W A`.

*Proof sketch.* The composite $L \circ T_a$ inverts $W$, because $T_a$ sends $W$ into $W$ and $L$ inverts $W$. By the universal property of the localization from Chapter 4, there is a functor $s_a : D \to D$ with $s_a \circ L \cong L \circ T_a$. Precomposition with $L$ is full and faithful on functor categories, by the same universal property. So the construction `HasShift.induced` of the previous module applies. $\square$

The instances `HasShift.localization` and `MorphismProperty.commShift_Q` apply this to the constructed localization `W.Localization` and its functor `W.Q`. If a functor that commutes with the shifts induces a functor on the localized category, then `Functor.commShiftOfLocalization` makes the induced functor commute with the shifts, and `NatTrans.commShift_iso_hom_of_localization` makes the relating isomorphism compatible. The definition `LocalizerMorphism.commShift` does the same for a localizer morphism of Chapter 4. The module `Mathlib.CategoryTheory.Shift.Linear` has one result, `Shift.linear_of_localization`: when $C$ and $D$ are $R$-linear and the shift functors of $C$ are $R$-linear, the induced shift functors of the localized category are $R$-linear too.

The module `Mathlib.CategoryTheory.Shift.Quotient` treats the quotient of $C$ by a relation `r : HomRel C` on morphisms. The class `HomRel.IsCompatibleWithShift r A` says that $f \sim g$ implies $f[a] \sim g[a]$. Under this class `HasShift.quotient r A` is a shift on `Quotient r`, and the instance `Quotient.functor_commShift` makes the quotient functor commute with the shifts. A functor $F$ that commutes with the shifts and sends related morphisms to equal morphisms factors through the quotient, and `Quotient.liftCommShift` gives the induced functor its `CommShift` structure.

#### Twisted shifts and bifunctors

The module `Mathlib.CategoryTheory.Shift.Twist` changes the coherence isomorphisms of a shift. A structure `TwistShiftData C A` holds units $z(a, b)$ of the center `CatCenter C`, which is the ring of endomorphisms of the identity functor. The fields say that $z(0, 0) = 1$, that $z(a + b, c)\, z(a, b) = z(a, b + c)\, z(b, c)$, and that each $z(a, b)$ commutes with the shifts. The type synonym `TwistShiftData.Category t` has the same shift functors as $C$, but its isomorphism $T_{a+b} \cong T_b \circ T_a$ is the old one multiplied by $z(a, b)$. The construction is `TwistShiftData.shiftMkCore`, the instance is `TwistShiftData.hasShift`, and `TwistShiftData.shiftIso` identifies the new shift functors with the old ones.

The module `Mathlib.CategoryTheory.Shift.CommShiftTwo` uses a twist to define bifunctors that commute with shifts. A `CommShift₂Setup D M` is a twist of the pullback of the shift of $D$ along the sum map $M \times M \to M$, with units $\varepsilon(m, n)$. The class `Functor.CommShift₂ G h` says that each $G(X_1, -)$ and each $G(-, X_2)$ commutes with the shifts, naturally in the other variable. It also says that the two isomorphisms $G(X_1[m], X_2[n]) \cong G(X_1, X_2)[m][n]$, one through the first variable first and one through the second variable first, differ by $\varepsilon(m, n)$ and the commutation of the shifts. This is the equation `Functor.commShift₂_comm`. For $M = \mathbb{Z}$ and a preadditive $D$, the setup `CommShift₂Setup.int` has $z((m_1, m_2), (n_1, n_2)) = (-1)^{m_1 n_2}$ and $\varepsilon(p, q) = (-1)^{pq}$. The abbreviation `Functor.CommShift₂Int G` is the class for this setup. The class `NatTrans.CommShift₂` is the condition on a natural transformation between such bifunctors.

**Example.** The total tensor product of two complexes has $(K[p] \otimes L[q])^n = \bigoplus_{i+j=n} K^{i+p} \otimes L^{j+q}$, and this is the term of degree $n + p + q$ of $K \otimes L$. Moving $K[p]$ out first and $L[q]$ out second, or the other way, differs by the Koszul sign $(-1)^{pq}$. This sign is the reason for `Functor.CommShift₂Int`.

#### Shift sequences

The module `Mathlib.CategoryTheory.Shift.ShiftSequence` defines the class `Functor.ShiftSequence F M` for a functor $F : C \to A$ out of a category with a shift by $M$. It holds functors `F.shift n` for $n \in M$, an isomorphism `F.isoShiftZero M : F.shift 0 ≅ F`, and isomorphisms `F.shiftIso n a a' h : shiftFunctor C n ⋙ F.shift a ≅ F.shift a'` for $n + a = a'$, with conditions for $n = 0$ and for sums. The derived isomorphism `F.isoShift n` identifies $F \circ T_n$ with $F^n$. The point is that $F^n$ can have its own definition: for the homology functor $H$ of a derived category, $H^n$ is the $n$th cohomology functor and not $H \circ T_n$. The instance `Functor.ShiftSequence.tautological` takes $F^n = F \circ T_n$, and `Functor.ShiftSequence.leftComp` transports a shift sequence along a functor that commutes with the shifts.

**Definition.** For $f : X \to Y[n]$ and $n + a = a'$, the morphism `F.shiftMap f a a' h` from $F^a(X)$ to $F^{a'}(Y)$ is the composite $F^a(X) \to F^a(Y[n]) \cong F^{a'}(Y)$ of $F^a(f)$ and the component of `F.shiftIso n a a' h` at $Y$.

For a homological functor this is the map that a morphism of degree $n$ induces on cohomology, for example a connecting map. The lemmas `Functor.shiftMap_comp` and `Functor.shiftMap_comp'` compute it on a composite: for $f : X \to Y[n]$ and $g : Y \to Z$, the map of $g[n] \circ f$ is $F^{a'}(g) \circ$ the map of $f$, and for $f : X \to Y$ and $g : Y \to Z[n]$, the map of $g \circ f$ is the map of $g$ composed with $F^a(f)$. The lemma `Functor.shiftIso_add` gives the coherence of `shiftIso` for a sum of indices.

The module `Mathlib.CategoryTheory.Shift.InducedShiftSequence` transports a shift sequence to a localized category. If $L : C \to D$ commutes with the shifts, precomposition with $L$ is full and faithful, $L \circ F \cong G$, and $G$ has a shift sequence, then `Functor.ShiftSequence.induced` gives a shift sequence on $F$ with chosen functors $F'_m$ such that $L \circ F'_m \cong G^m$.

#### Single functors

The module `Mathlib.CategoryTheory.Shift.SingleFunctors` defines `SingleFunctors C D A` for a category $D$ with a shift by $A$. A term holds functors `F.functor a : C ⥤ D` for $a \in A$ and isomorphisms `F.shiftIso n a a' h : F.functor a' ⋙ shiftFunctor D n ≅ F.functor a` for $n + a = a'$, with conditions for $n = 0$ and for sums, stated by `SingleFunctors.shiftIso_add`. The model is the family that sends $X$ to the complex with $X$ in degree $a$ and zero elsewhere.

These families form a category. The morphisms are `SingleFunctors.Hom`, the families of natural transformations that commute with the isomorphisms, and `SingleFunctors.isoMk` builds an isomorphism from isomorphisms in each degree. The functor `SingleFunctors.evaluation C D a` takes the functor of degree $a$. For a functor $G : D \to E$ that commutes with the shifts, `F.postcomp G` is the family $G \circ F_a$, and `SingleFunctors.postcompFunctor` is the corresponding functor. The isomorphism `SingleFunctors.postcompPostcompIso` compares postcomposition with $G$ and then $G'$ with postcomposition with $G' \circ G$.

The module `Mathlib.CategoryTheory.Shift.SingleFunctorsLift` goes the other way. Let $G : D \to E$ be full and faithful and commute with the shifts. Let $F$ be a family of single functors to $E$, and let $\Phi_a : C \to D$ be functors with $G \circ \Phi_a \cong F_a$. Then `SingleFunctors.lift F G Φ hΦ` is a family of single functors to $D$ with functors $\Phi_a$, and `SingleFunctors.liftPostcompIso` identifies its postcomposition with $G$ with $F$.

#### Common errors

1. `OppositeShift C A` carries the naive shift, with the shift by $a$ equal to the opposite of the shift by $a$. The pretriangulated structure on $C^{\mathrm{op}}$ of Section 5 uses another shift, by $-a$, on `Cᵒᵖ` itself. The two must not be confused, and a `CommShift` instance for one does not apply to the other.
2. In `Functor.ShiftSequence` the functor `F.shift n` is data and is not defined as `shiftFunctor C n ⋙ F`. Only the isomorphism `F.isoShift n` relates the two, so a rewrite of one into the other fails, and the lemmas about `shiftMap` must be used.
3. `Functor.CommShift₂Int` does not say that the two ways to move the shifts out of $G(X_1[p], X_2[q])$ agree. They differ by $(-1)^{pq}$, and a proof that omits the sign fails for odd $p$ and $q$.

### Exercises

1. (A) Let $\varphi : \mathbb{Z} \to \mathbb{Z}$ be $n \mapsto 2n$. Describe the shift of `PullbackShift C φ` by $1$ and by $-3$, and compute `pullbackShiftIso` for $a = 1$, $b = 2$.
2. (A) Let $W$ be the quasi-isomorphisms of cochain complexes. Prove that $W$ is compatible with the shift by $\mathbb{Z}$, using that the cohomology of $K[1]$ in degree $n$ is the cohomology of $K$ in degree $n + 1$.
3. (B) Let $E : C \simeq D$ be an equivalence and let $E$ commute with the shifts by an additive group. Show that the inverse of $E$ commutes with the shifts, and write the isomorphism $E^{-1}(Y[a]) \cong E^{-1}(Y)[a]$ with the unit and counit of $E$.
4. (B) Check that $z((m_1, m_2), (n_1, n_2)) = (-1)^{m_1 n_2}$ satisfies the cocycle condition of `TwistShiftData`, and compute $\varepsilon(p, q) = z((0, q), (p, 0))^{-1} z((p, 0), (0, q))$.
5. (B) Let $F$ have a shift sequence, $f : X \to Y[m]$ and $g : Y \to Z[n]$. Express the map of the shifted composite of $g$ and $f$ of degree $n + m$ in terms of `F.shiftMap f` and `F.shiftMap g`.
6. (C) Let $D$ be the category of $\mathbb{Z}$-graded abelian groups. Build a term of `SingleFunctors Ab D ℤ` whose functor of degree $a$ puts a group in degree $a$, and check the condition for a sum of indices.

### Reference

<?reference?>
