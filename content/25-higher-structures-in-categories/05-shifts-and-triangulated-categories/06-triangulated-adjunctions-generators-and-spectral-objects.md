---
title: Triangulated adjunctions, generators and spectral objects
kind: api
modules:
  - Mathlib.CategoryTheory.Triangulated.Adjunction
  - Mathlib.CategoryTheory.Triangulated.Yoneda
  - Mathlib.CategoryTheory.Triangulated.WeakKernels
  - Mathlib.CategoryTheory.Triangulated.Orthogonal
  - Mathlib.CategoryTheory.Triangulated.LocalizingSubcategory
  - Mathlib.CategoryTheory.Triangulated.Generators
  - Mathlib.CategoryTheory.Triangulated.SpectralObject
explains:
  E2: [CategoryTheory.Adjunction.isTriangulated_rightAdjoint, CategoryTheory.Adjunction.isTriangulated_leftAdjoint, CategoryTheory.Adjunction.IsTriangulated, CategoryTheory.Pretriangulated.isWeakLimitKernelForkOfDistTriangle, CategoryTheory.ObjectProperty.isLocal_trW, CategoryTheory.ObjectProperty.IsVerdierRightLocalizing.fullyFaithful, CategoryTheory.ObjectProperty.triangEnvelope_le_iff, CategoryTheory.ObjectProperty.IsStrongTriangulatedGenerator, CategoryTheory.Triangulated.SpectralObject]
  E1: auto
families: []
requires: [V24.C05, V24.C08, V25.C02, V25.C03, V25.C04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Triangulated adjunctions, generators and spectral objects

### Overview

Sections 2 and 3 set up pretriangulated and triangulated categories, triangulated functors and triangulated subcategories with their Verdier quotients. This section collects the results that a user of these notions meets next. An adjoint of a triangulated functor is triangulated. The functors $\mathrm{Hom}(A, -)$ and $\mathrm{Hom}(-, B)$ are homological. A distinguished triangle gives a weak kernel. The orthogonal of a triangulated subcategory is triangulated, and it describes the local objects for the Verdier localization. A subcategory that satisfies a factorization condition has a fully faithful Verdier quotient. A set of objects generates a triangulated envelope, and this gives the notions of classical and strong generators. Finally, a spectral object is a family of distinguished triangles indexed by pairs of composable arrows, which is the input of a spectral sequence.

The proofs of the results on left adjoints use the opposite category of Section 5, so that section is a prerequisite in spirit, even where the statements do not mention $C^{\mathrm{op}}$.

In the text $g \circ f$ is the textbook composite, and Mathlib writes `f ≫ g`. The shift of $X$ by $n$ is $X[n]$, written `X⟦n⟧`.

### The library around it

#### Adjoints of triangulated functors

The module `Mathlib.CategoryTheory.Triangulated.Adjunction` works with an adjunction $F \dashv G$ between pretriangulated categories, where $F$ and $G$ commute with the shifts and the adjunction is compatible with the shifts, in the sense of `Adjunction.CommShift` of Section 4. By `Adjunction.rightAdjointCommShift` of that section, a `CommShift` structure on $F$ always gives such a structure on $G$.

**Theorem.** If $F$ is triangulated, then $G$ is triangulated. This is `Adjunction.isTriangulated_rightAdjoint`.

*Proof sketch.* Let $X \xrightarrow{u} Y \xrightarrow{v} Z \xrightarrow{w} X[1]$ be distinguished in $D$. The functor $G$ is additive, because it is a right adjoint. Complete $G(u)$ to a distinguished triangle $GX \to GY \to Z' \to GX[1]$ of $C$. Apply $F$: the image is distinguished, and the counit gives a commutative square from $FGX \to FGY$ to $X \to Y$. By the completion axiom there is $h : FZ' \to Z$ that extends it to a morphism of triangles. Let $h^\flat : Z' \to GZ$ be its adjoint. Then $(1, 1, h^\flat)$ is a morphism of triangles from the completed triangle to the image of the given triangle under $G$. For each object $T$ of $C$, the functor $\mathrm{Hom}(T, -)$ sends the first triangle to a long exact sequence, and by adjunction it sends the second one to the long exact sequence of $\mathrm{Hom}(FT, -)$ on the triangle of $D$. The five lemma shows that $h^\flat$ induces bijections on $\mathrm{Hom}(T, -)$ for all $T$, so $h^\flat$ is an isomorphism by the Yoneda lemma. Hence the image triangle is isomorphic to a distinguished triangle. $\square$

**Corollary.** If $G$ is triangulated, then $F$ is triangulated. This is `Adjunction.isTriangulated_leftAdjoint`.

*Proof.* The opposite adjunction $G^{\mathrm{op}} \dashv F^{\mathrm{op}}$ is compatible with the shifts of Section 5. By `Functor.op_isTriangulated_iff`, the functor $G^{\mathrm{op}}$ is triangulated. The theorem gives that $F^{\mathrm{op}}$ is triangulated, and `Functor.isTriangulated_of_op` gives that $F$ is triangulated. $\square$

The class `Adjunction.IsTriangulated adj` says that $F$ and $G$ are triangulated and that the adjunction commutes with the shifts. The constructors `Adjunction.IsTriangulated.mk'` and `Adjunction.IsTriangulated.mk''` need only one of the two functors to be triangulated, by the two results above. The instances `Adjunction.IsTriangulated.id` and `Adjunction.IsTriangulated.comp` treat the identity and composites. For an equivalence $E$ the abbreviation `Equivalence.IsTriangulated E` asks that the functor and the inverse of $E$ are triangulated, and the instances `Equivalence.IsTriangulated.refl`, `Equivalence.IsTriangulated.symm` and `Equivalence.IsTriangulated.trans` make it stable under the operations on equivalences.

#### Representable functors and weak kernels

The module `Mathlib.CategoryTheory.Triangulated.Yoneda` proves that `preadditiveCoyoneda.obj A`, the functor $\mathrm{Hom}(A, -)$ to abelian groups, is homological on $C$, and that `preadditiveYoneda.obj B`, the functor $\mathrm{Hom}(-, B)$, is homological on $C^{\mathrm{op}}$. These are the instances `Pretriangulated.instIsHomologicalAddCommGrpCatObjOppositeFunctorPreadditiveCoyoneda` and `Pretriangulated.instIsHomologicalOppositeAddCommGrpCatObjFunctorPreadditiveYoneda`. Each functor also gets a shift sequence in the sense of Section 4, whose functor of degree $n$ is $\mathrm{Hom}(A, -[n])$ or $\mathrm{Hom}(-, B[n])$. These are the instances `Pretriangulated.instShiftSequenceAddCommGrpCatObjOppositeFunctorPreadditiveCoyonedaInt` and `Pretriangulated.instShiftSequenceOppositeAddCommGrpCatObjFunctorPreadditiveYonedaInt`. The shift sequence for $\mathrm{Hom}(-, B)$ uses the bijection `ShiftedHom.opEquiv'` of Section 5.

The module `Mathlib.CategoryTheory.Triangulated.WeakKernels` reads the exactness of $\mathrm{Hom}(T, -)$ as a universal property. For a distinguished triangle $X \xrightarrow{u} Y \xrightarrow{v} Z \to X[1]$, the fork `Pretriangulated.kernelForkOfDistTriangle T hT` is $u$ as a kernel fork of $v$, since $v \circ u = 0$.

**Proposition.** This fork is a weak kernel: each $t : T \to Y$ with $v \circ t = 0$ factors as $t = u \circ s$, but $s$ need not be unique. This is `Pretriangulated.isWeakLimitKernelForkOfDistTriangle`.

*Proof.* The sequence $\mathrm{Hom}(T, X) \to \mathrm{Hom}(T, Y) \to \mathrm{Hom}(T, Z)$ is exact, because $\mathrm{Hom}(T, -)$ is homological. So $t$, which goes to zero, comes from some $s$. $\square$

Every morphism lies in a distinguished triangle, after a rotation. So a pretriangulated category has weak kernels, and this is the instance `Pretriangulated.instHasWeakKernels` of the class `Limits.HasWeakKernels`.

#### Orthogonals and localizing subcategories

The module `Mathlib.CategoryTheory.Triangulated.Orthogonal` treats a triangulated subcategory $P$ of $C$. Its right orthogonal `P.rightOrthogonal` holds the objects $Y$ with $\mathrm{Hom}(X, Y) = 0$ for all $X$ in $P$, and its left orthogonal `P.leftOrthogonal` is dual. Instances show that both are stable under the shifts, closed under extensions and triangulated. The proof is the long exact sequence of $\mathrm{Hom}(X, -)$ and the five lemma, again.

**Theorem.** The objects that are local for the class `P.trW` of Section 3 are the objects of the right orthogonal of $P$. This is `ObjectProperty.isLocal_trW`, and `ObjectProperty.isColocal_trW` is the dual for the left orthogonal.

*Proof sketch.* Let $s : X \to X'$ be in `P.trW`, with a distinguished triangle $X \to X' \to W \to X[1]$ and $W$ in $P$. For $Y$ in the right orthogonal, $\mathrm{Hom}(W, Y) = 0$ and $\mathrm{Hom}(W[-1], Y) = 0$, because $P$ is stable under the shifts. The long exact sequence of $\mathrm{Hom}(-, Y)$ shows that $\mathrm{Hom}(X', Y) \to \mathrm{Hom}(X, Y)$ is bijective, so $Y$ is local. Conversely, for $W$ in $P$ the morphism $W \to 0$ is in `P.trW`, so a local object $Y$ has $\mathrm{Hom}(W, Y) = \mathrm{Hom}(0, Y) = 0$. $\square$

As a consequence, `ObjectProperty.rightOrthogonal.map_bijective_of_isTriangulated` says that for $Y$ in the right orthogonal and a localization $L$ for `P.trW`, the map $\mathrm{Hom}(X, Y) \to \mathrm{Hom}(LX, LY)$ is bijective for every $X$. The lemma `ObjectProperty.leftOrthogonal.map_bijective_of_isTriangulated` is the dual. These need the octahedral axiom on $C$.

The module `Mathlib.CategoryTheory.Triangulated.LocalizingSubcategory` compares two Verdier quotients. Let $A$ and $B$ be triangulated subcategories of $C$, with $B$ closed under isomorphisms. The class `ObjectProperty.IsVerdierRightLocalizing A B` asks that each morphism $X \to Y$ with $X$ in $B$ and $Y$ in $A$ factors through an object of $A \cap B$, by `ObjectProperty.IsVerdierRightLocalizing.fac`. The class `ObjectProperty.IsVerdierLeftLocalizing A B` asks the same for $X$ in $A$ and $Y$ in $B$. The localizer morphism `ObjectProperty.triangulatedLocalizerMorphism A B` is the inclusion of $A$ in $C$, from the class `(B.inverseImage A.ι).trW` to `B.trW`.

**Theorem.** If $A$ is right or left $B$-localizing, then the induced functor from $A / (A \cap B)$ to $C / B$ is fully faithful. These are `ObjectProperty.IsVerdierRightLocalizing.fullyFaithful` and `ObjectProperty.IsVerdierLeftLocalizing.fullyFaithful`.

The left case follows from the right case through the opposite category: the instances of the module show that $A$ is left $B$-localizing if and only if `A.op` is right `B.op`-localizing, which is `ObjectProperty.isVerdierRightLocalizing_op_iff`.

#### Generators

The module `Mathlib.CategoryTheory.Triangulated.Generators` defines the objects generated by a property $P$. The property `P.triangEnvelopeIter n` holds the objects that can be reached from $P$ by shifts, finite products, retracts and at most $n$ extensions. In symbols, let $P_0$ be the closure of $P$ under shifts, binary products and retracts. Then `ObjectProperty.triangEnvelopeIter_zero` says that the property for $n = 0$ is $P_0$, and `ObjectProperty.triangEnvelopeIter_succ` says that the property for $n + 1$ is the closure under retracts of the extensions of objects of $P_0$ by objects of the property for $n$. The union over $n$ is `P.triangEnvelope`.

**Proposition.** For a triangulated $C$, `P.triangEnvelope` is the smallest triangulated property that contains $P$ and is closed under retracts. In Mathlib, for $Q$ triangulated and closed under retracts, `P.triangEnvelope ≤ Q` holds if and only if `P ≤ Q`. This is `ObjectProperty.triangEnvelope_le_iff`.

*Proof sketch.* The envelope contains $P$ by `ObjectProperty.le_triangEnvelope`. It is stable under shifts and retracts, and it is closed under extensions because the extension of an object of level $n$ by an object of level $m$ has level $n + m + 1$, by `ObjectProperty.triangEnvelopeIter_add`, which needs the octahedral axiom. So it is triangulated when $C$ is triangulated. Each step of the construction stays inside a $Q$ that contains $P$, so it is the smallest one. $\square$

The property $P$ is a classical generator, `ObjectProperty.IsClassicalTriangulatedGenerator P`, if every object lies in `P.triangEnvelope`. It is a strong generator, `ObjectProperty.IsStrongTriangulatedGenerator P`, if there is one $n$ with `P.triangEnvelopeIter n = ⊤`, which is `ObjectProperty.isStrongTriangulatedGenerator_iff`. A strong generator is classical, by `ObjectProperty.IsStrongTriangulatedGenerator.isClassicalTriangulatedGenerator`. These notions differ from the generators of Chapter 3, such as `ObjectProperty.IsStrongGenerator`, which are defined by detection of morphisms.

#### Spectral objects

The module `Mathlib.CategoryTheory.Triangulated.SpectralObject` defines `Triangulated.SpectralObject C ι` for a category $\iota$, often a poset such as the extended integers. A spectral object holds a functor `ω₁` from the arrows of $\iota$ to $C$, written $f \mapsto X(f)$, and a natural connecting morphism. For composable arrows $f : i \to j$ and $g : j \to k$, the connecting morphism `X.δ f g` goes from $X(g)$ to $X(f)[1]$, and the triangle

$$X(f) \to X(g \circ f) \to X(g) \xrightarrow{\delta} X(f)[1]$$

is distinguished. The triangle is `X.triangle f g`, and `X.triangle_distinguished` states that it is distinguished. The lemma `SpectralObject.δ_naturality` is the naturality of $\delta$ in the pair $(f, g)$, and `X.mapTriangle` is the morphism of triangles that a morphism of pairs induces.

**Example.** Section 7 builds the main example from a t-structure. There $\iota$ is the extended integers, and $X(a \to b)$ is the truncation $\tau_{\ge a} \tau_{< b} A$ of a fixed object $A$.

Morphisms of spectral objects are `SpectralObject.Hom`, natural transformations of the functors `ω₁` that commute with $\delta$. A triangulated functor $F$ sends a spectral object to `X.mapTriangulatedFunctor F`, and `Functor.mapTriangulatedSpectralObject` is the induced functor on the categories of spectral objects. The definition `X.precomp` changes the index category along a functor. A homological functor $H$ with a shift sequence sends a spectral object to the spectral object `X.mapHomologicalFunctor H` of `Abelian.SpectralObject`, in an abelian category, whose value in degree $n$ at $f$ is $H^n(X(f))$. Its connecting maps are the connecting maps of the long exact sequences of $H$ on the triangles of $X$. The spectral sequence of such an abelian spectral object belongs to homological algebra.

#### Common errors

1. `Adjunction.isTriangulated_rightAdjoint` needs the instance `adj.CommShift ℤ`, and not only `CommShift` structures on $F$ and $G$. If $G$ has a `CommShift` structure that is unrelated to the one of $F$, the result does not apply. Use `Adjunction.rightAdjointCommShift` to get a compatible structure.
2. `ObjectProperty.IsStrongTriangulatedGenerator` and `ObjectProperty.IsStrongGenerator` of Chapter 3 are different notions. The first is about the number of extensions needed to reach every object, and the second is about the detection of isomorphisms.
3. The weak kernel of `Pretriangulated.isWeakLimitKernelForkOfDistTriangle` has no uniqueness. Two lifts of $t$ differ by a morphism that factors through $Z[-1] \to X$, so a proof by `ext` on the lift fails.

### Exercises

1. (A) Let $X \to Y \to Z \to X[1]$ be distinguished and let $A$ be an object. Write the long exact sequence of `preadditiveCoyoneda.obj (op A)` for this triangle, with four terms on each side of $\mathrm{Hom}(A, Y)$.
2. (A) Show that the zero property and the property of all objects are triangulated, and compute their right orthogonals.
3. (B) Let $P$ be triangulated. Prove that the right orthogonal of $P$ is closed under extensions, from the long exact sequence of $\mathrm{Hom}(X, -)$ for $X$ in $P$.
4. (B) Show that if $P \le Q$, then `P.triangEnvelopeIter n ≤ Q.triangEnvelopeIter n` for all $n$, and deduce that a property that contains a strong generator is a strong generator.
5. (B) Let $F \dashv G$ be an adjoint equivalence of pretriangulated categories and let $F$ be triangulated. Use the results of the section to show that `Equivalence.IsTriangulated` holds for the corresponding equivalence.
6. (C) Let $X$ be a spectral object indexed by $\iota$ and let $i$ be an object of $\iota$. Use the triangle of the pair $(1_i, f)$ for an arrow $f : i \to j$ to show that $X(1_i)$ is a zero object.

### Reference

<?reference?>
