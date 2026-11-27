---
title: Triangulated categories and functors
kind: theory
modules:
  - Mathlib.CategoryTheory.Triangulated.Triangulated
  - Mathlib.CategoryTheory.Triangulated.Functor
  - Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
  - Mathlib.CategoryTheory.Triangulated.Subcategory
  - Mathlib.CategoryTheory.Localization.Triangulated
explains:
  E3: [CategoryTheory.Triangulated.Octahedron, CategoryTheory.IsTriangulated, CategoryTheory.Functor.IsTriangulated, CategoryTheory.Functor.IsHomological, CategoryTheory.Functor.homologicalKernel, CategoryTheory.ObjectProperty.IsTriangulated, CategoryTheory.ObjectProperty.trW, CategoryTheory.MorphismProperty.IsCompatibleWithTriangulation, CategoryTheory.Triangulated.Localization.pretriangulated, CategoryTheory.Triangulated.Localization.isTriangulated]
  E2: [CategoryTheory.IsTriangulated.octahedron_axiom, CategoryTheory.Triangulated.someOctahedron, CategoryTheory.Triangulated.Octahedron.mem, CategoryTheory.Triangulated.Octahedron.ofIso, CategoryTheory.IsTriangulated.mk', CategoryTheory.Functor.mapTriangle, CategoryTheory.Functor.map_distinguished, CategoryTheory.Functor.map_distinguished_iff, CategoryTheory.Functor.mapTriangleRotateIso, CategoryTheory.Functor.map_distinguished_exact, CategoryTheory.Functor.IsHomological.mk', CategoryTheory.Functor.homologySequenceδ, CategoryTheory.Functor.homologySequence_exact₂, CategoryTheory.Functor.isHomological_of_localization, CategoryTheory.ObjectProperty.IsTriangulatedClosed₂, CategoryTheory.ObjectProperty.trW_iff, CategoryTheory.ObjectProperty.extensionProduct, CategoryTheory.Functor.essImageDistTriang, CategoryTheory.Functor.distTriang_iff, CategoryTheory.Triangulated.Localization.isTriangulated_functor]
  E1: auto
families: []
requires: [V24.C08, V25.C02, V25.C03, V25.C04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Triangulated categories and functors

### Overview

The axioms of Section 2 do not control the cone of a composite. If $X_1 \to X_2 \to X_3$ are two maps, the cones of the two maps and of the composite should be related, as the quotients $X_3/X_1$, $X_3/X_2$ and $X_2/X_1$ are related by the third isomorphism theorem. The octahedral axiom gives this relation, and a pretriangulated category with this axiom is *triangulated*. This section states the axiom and uses it to prove the main construction of the theory: the Verdier quotient of a triangulated category by a triangulated subcategory. The quotient is a localization in the sense of Chapter 4. The class of morphisms with a cone in the subcategory has a calculus of fractions, and the localized category is again triangulated. The section also treats triangulated functors and homological functors, which are the source of long exact sequences.

In the text $g \circ f$ is the textbook composite, and Mathlib writes `f ≫ g`.

### Definitions

**Definition (Octahedral axiom).** A pretriangulated category $C$ is *triangulated* if it satisfies the following condition. Let $u_{12} : X_1 \to X_2$, $u_{23} : X_2 \to X_3$ and $u_{13} = u_{23} \circ u_{12}$, and let
$$X_1 \xrightarrow{u_{12}} X_2 \xrightarrow{v_{12}} Z_{12} \xrightarrow{w_{12}} X_1[1], \quad X_2 \xrightarrow{u_{23}} X_3 \xrightarrow{v_{23}} Z_{23} \xrightarrow{w_{23}} X_2[1], \quad X_1 \xrightarrow{u_{13}} X_3 \xrightarrow{v_{13}} Z_{13} \xrightarrow{w_{13}} X_1[1]$$
be distinguished. Then there are $m_1 : Z_{12} \to Z_{13}$ and $m_3 : Z_{13} \to Z_{23}$ with
$$m_1 \circ v_{12} = v_{13} \circ u_{23}, \quad w_{13} \circ m_1 = w_{12}, \quad m_3 \circ v_{13} = v_{23}, \quad u_{12}[1] \circ w_{13} = w_{23} \circ m_3,$$
such that $Z_{12} \xrightarrow{m_1} Z_{13} \xrightarrow{m_3} Z_{23} \xrightarrow{v_{12}[1] \circ w_{23}} Z_{12}[1]$ is distinguished.

**Definition (Triangulated functor).** Let $C$ and $D$ be pretriangulated and let $F : C \to D$ commute with the shifts by $\mathbb{Z}$, with isomorphisms $\varphi_n$. The image of a triangle $(f, g, h)$ is the triangle $(Ff, Fg, \varphi_1 \circ Fh)$. The functor $F$ is *triangulated* if it sends distinguished triangles to distinguished triangles.

**Definition (Homological functor).** Let $C$ be pretriangulated and $\mathcal{A}$ abelian. A functor $H : C \to \mathcal{A}$ is *homological* if it preserves zero morphisms and $H(X) \to H(Y) \to H(Z)$ is exact for each distinguished triangle $X \to Y \to Z \to X[1]$. Write $H^n = H \circ T_n$. The *homological kernel* of $H$ is the class of objects $X$ with $H^n(X) = 0$ for all $n$.

**Definition (Triangulated subcategory).** A property $P$ of objects of $C$ is a *triangulated subcategory* if it contains a zero object, it is stable under the shifts, and for each distinguished triangle $X_1 \to X_2 \to X_3 \to X_1[1]$ with $X_1, X_3 \in P$, the object $X_2$ is isomorphic to an object of $P$. The class $W_P$ consists of the morphisms $f$ that have a distinguished triangle $X \xrightarrow{f} Y \to Z \to X[1]$ with $Z \in P$.

::: mathlib
`CategoryTheory.Triangulated.Octahedron` · `Mathlib.CategoryTheory.Triangulated.Triangulated`

The structure has the fields `m₁`, `m₃`, `comm₁` to `comm₄` and `mem`, in the order of the definition above. The class `IsTriangulated C` has the single field `octahedron_axiom`, which gives `Nonempty (Octahedron comm h₁₂ h₂₃ h₁₃)`. In a proof, `someOctahedron` chooses one.

<?decl CategoryTheory.Triangulated.Octahedron?>
:::

### Theorems and proofs

**Theorem (Triangulated functors are additive).** A triangulated functor $F : C \to D$ preserves zero objects and binary biproducts, and it is additive.

*Proof.* The contractible triangle $0 \to 0 \to 0 \to 0[1]$ of the zero object is distinguished. Its image is distinguished, and its first map is the identity of $F(0)$, which is an isomorphism. By Section 2, the third object $F(0)$ is zero. Each zero morphism $X \to Y$ factors through $0$, so $F$ sends it to a morphism that factors through $F(0)$, which is zero.

For $X_1$ and $X_3$, the triangle $X_1 \to X_1 \times X_3 \to X_3 \xrightarrow{0} X_1[1]$ is distinguished by Section 2. Its image and the triangle $FX_1 \to FX_1 \times FX_3 \to FX_3 \xrightarrow{0} FX_1[1]$ are distinguished, and the comparison map $F(X_1 \times X_3) \to FX_1 \times FX_3$, with the identities of $FX_1$ and $FX_3$, is a morphism of triangles. By the five lemma of Section 2, the comparison map is an isomorphism. A functor between preadditive categories that preserves binary products is additive, by Volume 24, Chapter 8. ∎

**Theorem (Long exact sequence).** Let $H$ be homological and $X \xrightarrow{f} Y \xrightarrow{g} Z \xrightarrow{h} X[1]$ distinguished. The sequence
$$\cdots \to H^n(X) \xrightarrow{H^n f} H^n(Y) \xrightarrow{H^n g} H^n(Z) \xrightarrow{\delta} H^{n+1}(X) \xrightarrow{H^{n+1} f} H^{n+1}(Y) \to \cdots$$
is exact, where $\delta = H(\varphi) \circ H^n(h)$ for the isomorphism $\varphi : X[1][n] \cong X[n+1]$. For example, $\mathrm{Hom}(W, -)$ is homological for each $W$.

*Proof.* By Section 2, the shift of a distinguished triangle by $n$, with its maps multiplied by $(-1)^n$, is distinguished. A sign does not change the kernel or the image of a map, so $H$ applied to the shifted triangle gives exactness at $H^n(Y)$. The rotations of $T$ are distinguished, and applying the same argument to them gives exactness at $H^n(Z)$ and at $H^{n+1}(X)$. The sign of $-f[1]$ in the rotation again does not change exactness. The example is the exactness theorem of Section 2. ∎

**Theorem (Homological kernels).** The homological kernel of a homological functor $H$ is a triangulated subcategory. A morphism $f$ is in $W_P$ for this kernel $P$ if and only if $H^n(f)$ is an isomorphism for all $n$.

*Proof.* A zero object $0$ has $H^n(0) = 0$, because $H$ is additive. If $X$ is in the kernel, then $H^n(X[a]) \cong H^{a+n}(X) = 0$, through $\mu_{a,n}$, so $X[a]$ is in the kernel. Let $X_1 \to X_2 \to X_3 \to X_1[1]$ be distinguished with $X_1, X_3$ in the kernel. The exact sequence $H^n(X_1) \to H^n(X_2) \to H^n(X_3)$ has zero outer terms, so $H^n(X_2) = 0$.

For the second claim, let $X \xrightarrow{f} Y \to Z \to X[1]$ be distinguished. Since cones are unique up to isomorphism, $f \in W_P$ if and only if $H^n(Z) = 0$ for all $n$. Consider the exact sequence
$$H^{n-1}(Z) \to H^n(X) \xrightarrow{H^n f} H^n(Y) \to H^n(Z) \to H^{n+1}(X) \xrightarrow{H^{n+1} f} H^{n+1}(Y).$$
If all $H^k(Z)$ are zero, $H^n f$ is injective and surjective. Conversely, if all $H^k f$ are isomorphisms, the map $H^n(Y) \to H^n(Z)$ is zero, because its kernel is the image of the surjective map $H^n f$. The map $H^n(Z) \to H^{n+1}(X)$ is zero, because its image is the kernel of the injective map $H^{n+1} f$. Exactness at $H^n(Z)$ then gives $H^n(Z) = 0$. ∎

**Theorem (Calculus of fractions for $W_P$).** Let $C$ be triangulated and $P$ a triangulated subcategory. Then $W_P$ is multiplicative, and it has a left and a right calculus of fractions.

*Proof.* An isomorphism has a cone that is a zero object, and $P$ contains a zero object up to isomorphism, so identities are in $W_P$. Let $u_{12}, u_{23} \in W_P$ with cones $Z_{12}, Z_{23}$ in $P$, and take any distinguished triangle on $u_{13} = u_{23} \circ u_{12}$ with cone $Z_{13}$. The octahedral axiom gives a distinguished triangle $Z_{12} \to Z_{13} \to Z_{23} \to Z_{12}[1]$. Since $P$ is closed under extensions, $Z_{13}$ is isomorphic to an object of $P$, so $u_{13} \in W_P$.

For the Ore condition, let $s : X' \to X$ be in $W_P$, with a distinguished triangle $X' \xrightarrow{s} X \xrightarrow{g} Z \xrightarrow{h} X'[1]$ and $Z \in P$, and let $f : X' \to Y$. Take a distinguished triangle $Y \xrightarrow{s'} Y' \to Z \xrightarrow{f[1] \circ h} Y[1]$, by axiom 3 applied to $f[1] \circ h$ and rotation. Then $s' \in W_P$. The pair $(f, 1_Z)$ on the first and third objects satisfies the third square, and the rotated form of axiom 5 gives $b : X \to Y'$ with $b \circ s = s' \circ f$.

For the cancellation, let $f_1 \circ s = f_2 \circ s$ with $s$ as above and $f_i : X \to Y$. Then $(f_1 - f_2) \circ s = 0$. By the exact sequence of $\mathrm{Hom}(-, Y)$, $f_1 - f_2 = q \circ g$ for some $q : Z \to Y$. Take a distinguished triangle $Z \xrightarrow{q} Y \xrightarrow{r} Y' \to Z[1]$. Its rotation shows that $r$ has the cone $Z[1] \in P$, so $r \in W_P$. Since $r \circ q = 0$, $r \circ (f_1 - f_2) = 0$, that is, $r \circ f_1 = r \circ f_2$. The right calculus is the dual argument in $C^{\mathrm{op}}$. ∎

**Theorem (The Verdier quotient).** Let $C$ be triangulated, $P$ a triangulated subcategory and $L : C \to D$ a localization functor for $W_P$, where $D$ has the shift induced by $L$. Then $D$ is pretriangulated, with the distinguished triangles the triangles isomorphic to images of distinguished triangles of $C$. With this structure, $D$ is triangulated, $L$ is a triangulated functor, and $L$ sends each object of $P$ to a zero object.

*Outline of proof.* By the theorem above and Chapter 4, $D$ is preadditive and $L$ is additive. The class $W_P$ is stable under the shifts, so the shifts of $C$ descend to $D$, and $L$ commutes with the shifts. The class $W_P$ is also compatible with the triangulation: a morphism of distinguished triangles with two components in $W_P$ can be completed by a third in $W_P$, by the octahedral axiom.

Axioms 1, 2 and 4 hold for the images of distinguished triangles because $L$ commutes with rotation. For axiom 3, a morphism of $D$ is $L(s)^{-1} \circ L(f)$, and the image of a triangle on $f$ in $C$, composed with the isomorphism $L(s)$, gives a triangle on it. For axiom 5, write the given square in $D$ as fractions with a common denominator, lift it to $C$ by the calculus of fractions, and complete it there. The octahedral axiom in $D$ follows in the same way from the one in $C$. Finally, for $X \in P$, the map $X \to 0$ has the cone $X[1] \in P$, so $L(X) \to L(0)$ is an isomorphism and $L(X)$ is zero. ∎

### Examples

**Example (Octahedron for an identity).** Let $u_{12} = 1_{X_1}$, so that $X_2 = X_1$ and $u_{13} = u_{23}$. The contractible triangle gives $Z_{12} = 0$. The same distinguished triangle serves on $u_{23}$ and on $u_{13}$, so $Z_{13} = Z_{23}$. Then $m_1 = 0$ and $m_3 = 1$ satisfy the four equations, and $0 \to Z_{23} \xrightarrow{1} Z_{23} \to 0$ is distinguished by Exercise 1 of Section 2.

**Example (Quasi-isomorphisms).** Let $\mathcal{A}$ be abelian and $K(\mathcal{A})$ the homotopy category of cochain complexes, with the cone triangles of Section 2. The functor $H^0$ to $\mathcal{A}$ is homological, and $H^n$ is the $n$-th cohomology. Its homological kernel is the class of acyclic complexes. By the theorem on homological kernels, $W_P$ is the class of quasi-isomorphisms. The Verdier quotient is the derived category $D(\mathcal{A})$ of Volume 26, and the theorems of this section make it triangulated, with $\mathrm{Hom}_{D(\mathcal{A})}(X, Y[n])$ as the groups of Section 1.

**Example (Additivity in the homotopy category).** The theorem on triangulated functors gives additivity for free. For example, a triangulated functor between homotopy categories sends a biproduct of complexes to a biproduct, without a separate argument.

### The library around it

::: mathlib
`CategoryTheory.ObjectProperty.trW` · `Mathlib.CategoryTheory.Triangulated.Subcategory`

For `P : ObjectProperty C`, `P.trW f` holds when there is a distinguished triangle `Triangle.mk f g h` whose third object satisfies `P`. Instances give `P.trW.IsMultiplicative`, `P.trW.HasLeftCalculusOfFractions` and `P.trW.HasRightCalculusOfFractions` for `[IsTriangulated C] [P.IsTriangulated]`. The source notes that `P.IsTriangulated` does not assume closure under isomorphisms, because the bounded below complexes in the homotopy category are not closed under isomorphisms.

<?decl CategoryTheory.ObjectProperty.trW?>
:::

::: mathlib
`CategoryTheory.Triangulated.Localization.pretriangulated` · `Mathlib.CategoryTheory.Localization.Triangulated`

For a localization `L : C ⥤ D` at `W` with `[W.HasLeftCalculusOfFractions]` and `[W.IsCompatibleWithTriangulation]`, this definition is the pretriangulated structure on `D` whose distinguished triangles are `L.essImageDistTriang`. Then `isTriangulated_functor` makes `L` triangulated, and `isTriangulated` gives the octahedral axiom when `C` is triangulated. `Functor.distTriang_iff` describes the distinguished triangles of any compatible structure.

<?decl CategoryTheory.Triangulated.Localization.pretriangulated?>
:::

`Functor.homologySequenceδ` is the connecting map, and `homologySequence_exact₁` to `homologySequence_exact₃` give the long exact sequence for a functor with a chosen shift sequence. `ObjectProperty.extensionProduct P Q` is the class of objects that are extensions of an object of $Q$ by an object of $P$. A fully faithful triangulated functor to a triangulated category makes its source triangulated, by `IsTriangulated.of_fully_faithful_triangulated_functor`.

Common errors of a learner:

- The octahedral axiom gives existence of $m_1$ and $m_3$. They are not unique, and they are not the maps that axiom 5 gives for the two obvious squares in general.
- `Functor.IsTriangulated` needs a `CommShift ℤ` instance. The image triangle uses `F.commShiftIso 1`, and two choices of this instance give two notions of triangulated functor.
- `IsHomological` asks for exactness at the middle object only. The long exact sequence is a theorem.

### Exercises

1. (A) Show that the identity functor is triangulated and that a composite of triangulated functors is triangulated.
2. (A) Show that $\mathrm{Hom}(-, W) : C^{\mathrm{op}} \to \mathrm{Ab}$ sends distinguished triangles to exact sequences.
3. (B) Let $P$ be the class of zero objects. Show that $P$ is a triangulated subcategory, that $W_P$ is the class of isomorphisms, and that the Verdier quotient is equivalent to $C$.
4. (B) Let $H$ be homological. Show that if $H^n(f)$ is an isomorphism for all $n$, then $H^n(g \circ f)$ is an isomorphism for all $n$ if and only if $H^n(g)$ is one for all $n$.
5. (B) In the octahedral axiom, show that $w_{23} \circ m_3 \circ v_{13} = 0$ from the four equations and the results of Section 2.
6. (C) Let $P$ be a triangulated subcategory and $X \in P$. Show that $L(X)$ is zero in the Verdier quotient, and give an example in $K(\mathcal{A})$ of an object $Y \notin P$ with $L(Y) = 0$ when $P$ is not closed under isomorphisms.

### Notes and history

Verdier introduced triangulated categories, the octahedral axiom and the quotient by a triangulated subcategory in his thesis, published in 1996 as *Des catégories dérivées des catégories abéliennes*. The source of `Triangulated.Octahedron` cites the Stacks Project, tag 05QK, for the form of the axiom. The derived category of an abelian category is the main example, and Volume 26 constructs it in Mathlib with the results of this section.

All the Mathlib files of this section are by Joël Riou.

### Reference

<?reference?>
