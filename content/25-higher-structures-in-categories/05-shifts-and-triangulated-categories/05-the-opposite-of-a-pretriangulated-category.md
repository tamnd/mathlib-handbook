---
title: The opposite of a pretriangulated category
kind: api
modules:
  - Mathlib.CategoryTheory.Triangulated.Opposite.Basic
  - Mathlib.CategoryTheory.Triangulated.Opposite.Triangle
  - Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
  - Mathlib.CategoryTheory.Triangulated.Opposite.Triangulated
  - Mathlib.CategoryTheory.Triangulated.Opposite.Functor
  - Mathlib.CategoryTheory.Triangulated.Opposite.OpOp
  - Mathlib.CategoryTheory.Triangulated.Opposite.Subcategory
  - Mathlib.CategoryTheory.Shift.ShiftedHomOpposite
explains:
  E2: [CategoryTheory.Pretriangulated.shiftFunctorOpIso, CategoryTheory.Pretriangulated.triangleOpEquivalence, CategoryTheory.Pretriangulated.mem_distTriang_op_iff, CategoryTheory.Pretriangulated.Opposite.instIsTriangulatedOpposite, CategoryTheory.Functor.op_isTriangulated_iff, CategoryTheory.Functor.map_distinguished_op_exact, CategoryTheory.ObjectProperty.trW_op_iff, CategoryTheory.ShiftedHom.opEquiv]
  E1: auto
families: []
requires: [V24.C08, V25.C02, V25.C04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The opposite of a pretriangulated category

### Overview

The axioms of a pretriangulated category are self dual. If $C$ is pretriangulated, then $C^{\mathrm{op}}$ is pretriangulated, and if $C$ satisfies the octahedral axiom, then $C^{\mathrm{op}}$ satisfies it too. This duality halves many proofs. A statement about cohomological functors $C^{\mathrm{op}} \to \mathsf{Ab}$, such as the exactness of $\mathrm{Hom}(-, B)$ on a distinguished triangle, follows from the statement about homological functors on $C^{\mathrm{op}}$. A statement about left adjoints follows from the statement about right adjoints. Section 6 uses both of these.

The difficulty is in the details. The shift on $C^{\mathrm{op}}$ must be chosen, and a triangle of $C^{\mathrm{op}}$ must be matched with a triangle of $C$. Mathlib makes the choices that need no signs. The modules of this section build the shift, the equivalence of triangles, the class of distinguished triangles and the octahedral axiom on $C^{\mathrm{op}}$. They then show that a functor is triangulated if and only if its opposite is, that the opposite of a triangulated subcategory is triangulated, and that shifted morphisms of $C$ and of $C^{\mathrm{op}}$ correspond.

In the text $g \circ f$ is the textbook composite, and Mathlib writes `f ≫ g`. The shift of $X$ by $n$ is $X[n]$, written `X⟦n⟧`. For an object $X$ of $C$ the object `Opposite.op X` of $C^{\mathrm{op}}$ is written $X^{\circ}$.

### The library around it

#### The shift on the opposite category

Section 4 gave the naive shift on `OppositeShift C A`, with the shift by $n$ equal to the opposite of the shift by $n$. This is the wrong shift for triangles. A distinguished triangle $X \to Y \to Z \to X[1]$ of $C$ should give a triangle $Z^{\circ} \to Y^{\circ} \to X^{\circ} \to Z^{\circ}[1]$ of $C^{\mathrm{op}}$. The last morphism must come from $h : Z \to X[1]$, and a morphism $X^{\circ} \to Z^{\circ}[1]$ in $C^{\mathrm{op}}$ is a morphism from the shift of $Z$ to $X$ in $C$. The shift of $Z$ must be $Z[-1]$, so that $h$ gives $Z[-1] \to X$ by the shift equivalence.

The module `Mathlib.CategoryTheory.Triangulated.Opposite.Basic` builds this shift. It pulls back the naive shift along the negation $\mathbb{Z} \to \mathbb{Z}$, with the construction `PullbackShift` of Section 4. The result is a scoped instance on `Cᵒᵖ`. It is active only after `open CategoryTheory.Pretriangulated.Opposite`, because the opposite category has other natural shifts. With this instance the shift by $n$ on $C^{\mathrm{op}}$ is the opposite of the shift by $-n$ on $C$, and `shiftFunctorOpIso C n m h` is the isomorphism of the shift by $n$ on $C^{\mathrm{op}}$ with the opposite of the shift by $m$ on $C$, for $n + m = 0$. The equality is definitional, but `rw` and `simp` do not see through the instance. Use the isomorphism instead.

The equivalence `opShiftFunctorEquivalence C n` is the autoequivalence of $C^{\mathrm{op}}$ with functor the shift by $n$ of $C^{\mathrm{op}}$ and inverse the opposite of the shift by $n$ of $C$. It gives the bijection `opShiftFunctorEquivalenceSymmHomEquiv` between morphisms from the opposite of $X^{\circ}$ shifted in $C$ to $Y$ and morphisms $X \to Y[n]$ in $C^{\mathrm{op}}$. This bijection is the translation tool of the whole section.

#### Triangles and distinguished triangles

The module `Mathlib.CategoryTheory.Triangulated.Opposite.Triangle` gives the equivalence `triangleOpEquivalence C` from the opposite of the category of triangles of $C$ to the category of triangles of $C^{\mathrm{op}}$. Its functor `TriangleOpEquivalence.functor` sends $X \xrightarrow{f} Y \xrightarrow{g} Z \xrightarrow{h} X[1]$ to $Z^{\circ} \xrightarrow{g^{\circ}} Y^{\circ} \xrightarrow{f^{\circ}} X^{\circ} \to Z^{\circ}[1]$, where the last morphism comes from $h$ through the bijection above. No sign is added. The inverse is `TriangleOpEquivalence.inverse`, and the unit and counit are `TriangleOpEquivalence.unitIso` and `TriangleOpEquivalence.counitIso`.

The module `Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated` defines the distinguished triangles of $C^{\mathrm{op}}$. The set `Pretriangulated.Opposite.distinguishedTriangles C` holds the triangles of $C^{\mathrm{op}}$ that correspond to a distinguished triangle of $C$ under the equivalence. The lemma `mem_distTriang_op_iff` states this for the scoped pretriangulated instance, and the lemmas `op_distinguished` and `unop_distinguished` go in both directions on a given triangle.

**Theorem.** With this shift and these triangles, $C^{\mathrm{op}}$ is pretriangulated.

*Proof sketch.* Each axiom of $C^{\mathrm{op}}$ is an axiom of $C$ after the translation, up to a rotation. Closure under isomorphisms is `Pretriangulated.Opposite.isomorphic_distinguished`: an isomorphism of triangles of $C^{\mathrm{op}}$ gives an isomorphism of the corresponding triangles of $C$. The contractible triangle $X \to X \to 0 \to X[1]$ of $C^{\mathrm{op}}$ corresponds, by `Pretriangulated.Opposite.contractibleTriangleIso`, to a rotation of the contractible triangle of the unopposite of $X$ in $C$, so it is distinguished by `Pretriangulated.Opposite.contractible_distinguished`. A morphism $f : X \to Y$ of $C^{\mathrm{op}}$ is the opposite of a morphism of $C$ in the other direction. Complete that morphism to a distinguished triangle of $C$ and rotate it once: the result corresponds to a triangle of $C^{\mathrm{op}}$ that starts with $f$. This is `Pretriangulated.Opposite.distinguished_cocone_triangle`. The rotation of $C^{\mathrm{op}}$ corresponds to the inverse rotation of $C$, by the isomorphism `Pretriangulated.Opposite.rotateTriangleOpEquivalenceInverseObjRotateUnopIso`. So `Pretriangulated.Opposite.rotate_distinguished_triangle` follows from the rotation axiom of $C$ and its converse. The completion of morphisms of triangles, `Pretriangulated.Opposite.complete_distinguished_triangle_morphism`, follows from the same axiom of $C$ for the opposite square. $\square$

The module `Mathlib.CategoryTheory.Triangulated.Opposite.Triangulated` has one instance, `Pretriangulated.Opposite.instIsTriangulatedOpposite`: if $C$ satisfies the octahedral axiom, then so does $C^{\mathrm{op}}$. The octahedron of $C^{\mathrm{op}}$ for $u_{12}$ and $u_{23}$ is an octahedron of $C$ for the opposite morphisms in the reverse order, read backwards.

The lemma `Functor.map_distinguished_op_exact` is the first use. Let $F : C^{\mathrm{op}} \to A$ be a homological functor to an abelian category. For a distinguished triangle $T$ of $C$, the image under $F$ of the opposite of the short complex $X \to Y \to Z$ of $T$ is exact. A cohomological functor on $C$ is a homological functor on $C^{\mathrm{op}}$, so this gives the exactness of $\mathrm{Hom}(-, B)$ from that of $\mathrm{Hom}(A, -)$.

#### Functors and the double opposite

The module `Mathlib.CategoryTheory.Triangulated.Opposite.Functor` treats a functor $F : C \to D$ that commutes with the shifts. The scoped instance `Pretriangulated.Opposite.commShiftFunctorOpInt` gives $F^{\mathrm{op}}$ a `CommShift` structure for the shifts by $-n$. The isomorphism `Functor.mapTriangleOpCompTriangleOpEquivalenceFunctor` says that the triangle functors of $F$ and $F^{\mathrm{op}}$ commute with the equivalences of triangles, and `Functor.opMapTriangleCompTriangleOpEquivalenceInverse` is the same statement for the inverse. The scoped instances `Pretriangulated.Opposite.commShift_natTrans_op_int` and `Pretriangulated.Opposite.commShift_adjunction_op_int` do the same for natural transformations and adjunctions.

**Theorem.** Let $C$ and $D$ be pretriangulated and $F : C \to D$ commute with the shifts. Then $F$ is triangulated if and only if $F^{\mathrm{op}}$ is triangulated. This is `Functor.op_isTriangulated_iff`.

*Proof.* The image of a distinguished triangle of $C^{\mathrm{op}}$ under $F^{\mathrm{op}}$ corresponds, by `Functor.mapTriangleOpCompTriangleOpEquivalenceFunctor`, to the image under $F$ of the corresponding triangle of $C$. A triangle of $D^{\mathrm{op}}$ is distinguished if and only if the corresponding triangle of $D$ is distinguished. So $F^{\mathrm{op}}$ preserves distinguished triangles if and only if $F$ does. The two directions are `Pretriangulated.Opposite.functor_isTriangulated_op` and `Functor.isTriangulated_of_op`. $\square$

The module `Mathlib.CategoryTheory.Triangulated.Opposite.OpOp` checks the double opposite. The functors `opOp C` and `unopUnop C` commute with the shifts, through `Pretriangulated.Opposite.OpOpCommShift.iso` and `Pretriangulated.Opposite.UnopUnopCommShift.iso`, and they are triangulated by `Pretriangulated.instIsTriangulatedOppositeOpOp` and `Pretriangulated.instIsTriangulatedOppositeUnopUnop`. The instance `Pretriangulated.instIsTriangulatedOppositeOpOpEquivalence` says that the equivalence `opOpEquivalence C` is a triangulated equivalence. So the duality is an involution up to a triangulated equivalence.

#### Subcategories and shifted morphisms

The module `Mathlib.CategoryTheory.Triangulated.Opposite.Subcategory` shows that the opposite `P.op` of a triangulated subcategory `P` of $C$ is a triangulated subcategory of $C^{\mathrm{op}}$. The instances are `ObjectProperty.instIsStableUnderShiftOppositeOpInt` and `ObjectProperty.instIsTriangulatedOppositeOp`, with `ObjectProperty.instIsTriangulatedUnopOfOpposite` in the other direction. The class `trW` of Section 3 is self dual too: `ObjectProperty.trW_op_iff` says that a morphism $f$ of $C^{\mathrm{op}}$ is in `P.op.trW` if and only if its unopposite is in `P.trW`. The reason is that $f$ and its unopposite have the same cone up to a shift and a rotation.

The module `Mathlib.CategoryTheory.Shift.ShiftedHomOpposite` compares shifted morphisms. For a category with a shift by $\mathbb{Z}$, the bijection `ShiftedHom.opEquiv n` goes from `ShiftedHom X Y n`, the morphisms $X \to Y[n]$, to `ShiftedHom (op Y) (op X) n`. It sends $f$ to the morphism that corresponds to $f[-n] : X[-n] \to Y$, after the identification of $Y[n][-n]$ with $Y$. The variant `ShiftedHom.opEquiv'` allows a shift on the target, for $n + a = a'$. The lemma `ShiftedHom.opEquiv_symm_comp` says that the bijection reverses the composition of shifted morphisms, and `ShiftedHom.opEquiv_symm_add` says that it is additive. These lemmas serve the study of the functor $\mathrm{Hom}(-, B)$ on $C^{\mathrm{op}}$ and its shift sequence.

#### Common errors

1. The pretriangulated instance on `Cᵒᵖ` is scoped. Without `open CategoryTheory.Pretriangulated.Opposite` the class `Pretriangulated Cᵒᵖ` is not found, and the shift on `Cᵒᵖ` may be another one. The naive shift of `OppositeShift C ℤ` is not this shift.
2. The shift by $n$ on `Cᵒᵖ` is defined as the opposite of the shift by $-n$ on `C`, but `simp` and `rw` do not unfold the instance. Rewrite with the isomorphism `shiftFunctorOpIso` instead.
3. The equivalence of triangles reverses the order of the objects. The first object of the triangle of $C^{\mathrm{op}}$ is the third object $Z$ of the triangle of $C$, not $X$.

### Exercises

1. (A) Let $X \xrightarrow{f} Y \xrightarrow{g} Z \xrightarrow{h} X[1]$ be distinguished in $C$. Write the triangle of $C^{\mathrm{op}}$ given by `TriangleOpEquivalence.functor` and describe its third morphism as a morphism of $C$.
2. (A) Use `Functor.map_distinguished_op_exact` to show that for a distinguished triangle $X \to Y \to Z \to X[1]$ and an object $B$, the sequence $\mathrm{Hom}(Z, B) \to \mathrm{Hom}(Y, B) \to \mathrm{Hom}(X, B)$ is exact.
3. (B) Show that the contractible triangle $X^{\circ} \to X^{\circ} \to 0 \to X^{\circ}[1]$ of $C^{\mathrm{op}}$ corresponds to a rotation of the contractible triangle of $X$ in $C$, and say which rotation.
4. (B) Let $F \dashv G$ be an adjunction of pretriangulated categories with $G$ triangulated. Use `Functor.op_isTriangulated_iff` to reduce the statement that $F$ is triangulated to a statement about right adjoints.
5. (B) For $f : X \to Y[a]$ and $g : Y \to Z[b]$, state the formula of `ShiftedHom.opEquiv_symm_comp` in words, and check it for $a = b = 0$.
6. (C) Let $P$ be a triangulated subcategory of $C$. Prove that a morphism $f$ of $C$ has its cone in $P$ if and only if the opposite morphism has its cone in `P.op`, with a rotation of triangles.

### Reference

<?reference?>
