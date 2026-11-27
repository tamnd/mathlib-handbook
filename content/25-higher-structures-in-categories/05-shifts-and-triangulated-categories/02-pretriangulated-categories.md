---
title: Pretriangulated categories
kind: theory
modules:
  - Mathlib.CategoryTheory.Triangulated.Basic
  - Mathlib.CategoryTheory.Triangulated.Rotate
  - Mathlib.CategoryTheory.Triangulated.Pretriangulated
  - Mathlib.CategoryTheory.Triangulated.TriangleShift
explains:
  E3: [CategoryTheory.Pretriangulated.Triangle, CategoryTheory.Pretriangulated.TriangleMorphism, CategoryTheory.Pretriangulated.Triangle.rotate, CategoryTheory.Pretriangulated, CategoryTheory.Pretriangulated.comp_distTriang_mor_zero₁₂, CategoryTheory.Pretriangulated.Triangle.coyoneda_exact₂, CategoryTheory.Pretriangulated.Triangle.yoneda_exact₂, CategoryTheory.Pretriangulated.isIso₂_of_isIso₁₃, CategoryTheory.Pretriangulated.Triangle.isZero₃_iff_isIso₁, CategoryTheory.Pretriangulated.exists_iso_of_arrow_iso]
  E2: [CategoryTheory.Pretriangulated.Triangle.mk, CategoryTheory.Pretriangulated.contractibleTriangle, CategoryTheory.Pretriangulated.Triangle.isoMk, CategoryTheory.Pretriangulated.Triangle.invRotate, CategoryTheory.Pretriangulated.triangleRotation, CategoryTheory.Pretriangulated.Triangle.shiftFunctor, CategoryTheory.Pretriangulated.distinguished_iff_of_iso, CategoryTheory.Pretriangulated.rot_of_distTriang, CategoryTheory.Pretriangulated.inv_rot_of_distTriang, CategoryTheory.Pretriangulated.complete_distinguished_triangle_morphism₁, CategoryTheory.Pretriangulated.distinguished_cocone_triangle₁, CategoryTheory.Pretriangulated.Triangle.mor₃_eq_zero_iff_epi₂, CategoryTheory.Pretriangulated.Triangle.isZero₂_iff, CategoryTheory.Pretriangulated.Triangle.shift_distinguished, CategoryTheory.Pretriangulated.binaryBiproductTriangle, CategoryTheory.Pretriangulated.binaryBiproductTriangle_distinguished, CategoryTheory.Pretriangulated.exists_iso_binaryBiproduct_of_distTriang, CategoryTheory.Pretriangulated.productTriangle_distinguished, CategoryTheory.Pretriangulated.shortComplexOfDistTriangle]
  E1: auto
families: []
requires: [V24.C03, V24.C08, V25.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Pretriangulated categories

### Overview

In an abelian category, the short exact sequences control homology. The derived category and the homotopy category of complexes are additive, but they are not abelian, and a morphism in them does not have a kernel or a cokernel in a useful sense. Their replacement for the short exact sequence is the distinguished triangle $X \to Y \to Z \to X[1]$. The third object is a cone of the first map. It is unique only up to an isomorphism that is not unique. This section gives the axioms of a pretriangulated category, which are the axioms of Verdier without the octahedral axiom. From these axioms it proves that each representable functor turns distinguished triangles into long exact sequences, a five lemma for triangles, and the fact that each monomorphism splits.

In the text $g \circ f$ is the textbook composite, and Mathlib writes `f ≫ g`. The category $C$ is preadditive, it has a zero object and a shift by $\mathbb{Z}$, and each shift functor is additive. The shift is from Section 1.

### Definitions

**Definition (Triangle).** A *triangle* in $C$ is a diagram $X \xrightarrow{f} Y \xrightarrow{g} Z \xrightarrow{h} X[1]$. A *morphism* from this triangle to $X' \to Y' \to Z' \to X'[1]$ is a triple $(a, b, c)$ of morphisms $a : X \to X'$, $b : Y \to Y'$ and $c : Z \to Z'$ with $b \circ f = f' \circ a$, $c \circ g = g' \circ b$ and $a[1] \circ h = h' \circ c$. Triangles and their morphisms form a preadditive category. A morphism of triangles is an isomorphism if and only if its three components are isomorphisms.

**Definition (Rotation).** The *rotation* of the triangle $(f, g, h)$ is the triangle $Y \xrightarrow{g} Z \xrightarrow{h} X[1] \xrightarrow{-f[1]} Y[1]$. The *inverse rotation* is $Z[-1] \xrightarrow{-h[-1]} X \xrightarrow{f} Y \xrightarrow{g} Z$, after the identifications $X[1][-1] \cong X$ and $Z[-1][1] \cong Z$. The two functors are inverse equivalences of the category of triangles.

**Definition (Pretriangulated category).** A *pretriangulated category* is a category $C$ as above with a class of triangles, the *distinguished triangles*, such that:

1. a triangle isomorphic to a distinguished triangle is distinguished;
2. for each $X$, the triangle $X \xrightarrow{1} X \to 0 \to X[1]$ is distinguished;
3. each $f : X \to Y$ is the first morphism of a distinguished triangle $X \xrightarrow{f} Y \to Z \to X[1]$;
4. a triangle is distinguished if and only if its rotation is distinguished;
5. for distinguished triangles $T$ and $T'$, and $a : X \to X'$, $b : Y \to Y'$ with $b \circ f = f' \circ a$, there is $c : Z \to Z'$ such that $(a, b, c)$ is a morphism of triangles.

The object $Z$ of axiom 3 is a *cone* of $f$. The triangle of axiom 2 is the *contractible triangle* of $X$. The morphism $c$ of axiom 5 is not unique, and this is the main defect of the theory.

::: mathlib
`CategoryTheory.Pretriangulated` · `Mathlib.CategoryTheory.Triangulated.Pretriangulated`

The class has the fields `distinguishedTriangles`, `isomorphic_distinguished`, `contractible_distinguished`, `distinguished_cocone_triangle`, `rotate_distinguished_triangle` and `complete_distinguished_triangle_morphism`, in the order of the definition above. The notation `distTriang C` is the set of distinguished triangles. The source notes that the category is assumed preadditive and not additive. Binary biproducts are then a theorem.

<?decl CategoryTheory.Pretriangulated?>
:::

### Theorems and proofs

Fix a pretriangulated category $C$ and a distinguished triangle $T = (X \xrightarrow{f} Y \xrightarrow{g} Z \xrightarrow{h} X[1])$. By axiom 4, the rotations and the inverse rotations of $T$ are distinguished, so each statement about the first two maps of $T$ gives a statement about any two consecutive maps.

**Theorem (Consecutive maps compose to zero).** $g \circ f = 0$, $h \circ g = 0$ and $f[1] \circ h = 0$.

*Proof.* The pair $(1_X, f)$ goes from the contractible triangle $X \xrightarrow{1} X \to 0 \to X[1]$ to $T$, and it satisfies $f \circ 1_X = f \circ 1_X$. By axiom 5 there is $c : 0 \to Z$ that completes it to a morphism of triangles. The second square says $c \circ 0 = g \circ f$, so $g \circ f = 0$. The rotation $(g, h, -f[1])$ is distinguished, and the same argument gives $h \circ g = 0$ and $-f[1] \circ h = 0$. ∎

**Theorem (The long exact sequence of a representable functor).** For each object $W$, the sequence of abelian groups
$$\cdots \to \mathrm{Hom}(W, X) \xrightarrow{f_*} \mathrm{Hom}(W, Y) \xrightarrow{g_*} \mathrm{Hom}(W, Z) \xrightarrow{h_*} \mathrm{Hom}(W, X[1]) \xrightarrow{-f[1]_*} \mathrm{Hom}(W, Y[1]) \to \cdots$$
is exact. Dually, the sequence of the functors $\mathrm{Hom}(-, W)$ is exact.

*Proof.* By rotation, it is sufficient to prove exactness at $\mathrm{Hom}(W, Y)$. The previous theorem gives $g_* \circ f_* = 0$. Let $u : W \to Y$ with $g \circ u = 0$. Rotate the contractible triangle of $W$ to get the distinguished triangle $W \to 0 \to W[1] \xrightarrow{-1} W[1]$, and rotate $T$ to get $Y \xrightarrow{g} Z \xrightarrow{h} X[1] \xrightarrow{-f[1]} Y[1]$. The pair $(u, 0)$ satisfies the first square, because $g \circ u = 0 = 0 \circ 0$. Axiom 5 gives $c : W[1] \to X[1]$ with $-f[1] \circ c = u[1] \circ (-1)$, that is, $f[1] \circ c = u[1]$. The shift functor $T_1$ is an equivalence by Section 1, so it is full and faithful. Thus $c = v[1]$ for some $v : W \to X$, and $(f \circ v)[1] = u[1]$ gives $f \circ v = u$. For the dual statement, let $u : Y \to W$ with $u \circ f = 0$. The triangle $0 \to W \xrightarrow{1} W \to 0$ is distinguished, because it is a rotation of the contractible triangle of $W$. The pair $(0, u)$ from $T$ to this triangle satisfies the first square, and axiom 5 gives $c : Z \to W$ with $c \circ g = u$. ∎

**Corollary (Monomorphisms split).** If $f$ is a monomorphism, then $h = 0$ and $f$ is a split monomorphism. Dually, each epimorphism in $C$ is split.

*Proof.* The inverse rotation $Z[-1] \xrightarrow{-h[-1]} X \xrightarrow{f} Y \xrightarrow{g} Z$ is distinguished, so $f \circ h[-1] = 0$ by the first theorem. Since $f$ is a monomorphism, $h[-1] = 0$, and $h = 0$ because $T_{-1}$ is faithful. Apply the exact sequence of $\mathrm{Hom}(-, X)$ to the inverse rotation: the identity $1_X$ satisfies $1_X \circ (-h[-1]) = 0$, so $1_X = r \circ f$ for some $r : Y \to X$. ∎

**Corollary (Isomorphisms and zero cones).** The map $f$ is an isomorphism if and only if $Z$ is a zero object.

*Proof.* Suppose that $Z$ is zero. Then $Z[-1]$ is zero, because $T_{-1}$ is an additive equivalence. In the exact sequence $\mathrm{Hom}(W, Z[-1]) \to \mathrm{Hom}(W, X) \to \mathrm{Hom}(W, Y) \to \mathrm{Hom}(W, Z)$ of the inverse rotation, the outer groups are zero, so $f_*$ is bijective for each $W$. By the Yoneda lemma, $f$ is an isomorphism.

Suppose that $f$ is an isomorphism. Then $g \circ f = 0$ gives $g = 0$, and $f[1] \circ h = 0$ gives $h = 0$, because $f[1]$ is an isomorphism. Apply exactness at $\mathrm{Hom}(Z, Z)$: the identity satisfies $h \circ 1_Z = 0$, so $1_Z = g \circ v = 0$ for some $v$. Thus $Z$ is zero. ∎

**Theorem (Five lemma for triangles).** Let $(a, b, c) : T \to T'$ be a morphism of distinguished triangles. If two of $a, b, c$ are isomorphisms, the third is an isomorphism.

*Proof.* Suppose that $a$ and $c$ are isomorphisms. Fix $W$ and apply $\mathrm{Hom}(W, -)$ to the inverse rotations of $T$ and $T'$, which continue with the next term $\mathrm{Hom}(W, X[1])$. The result is a commutative diagram of exact sequences
$$\mathrm{Hom}(W, Z[-1]) \to \mathrm{Hom}(W, X) \to \mathrm{Hom}(W, Y) \to \mathrm{Hom}(W, Z) \to \mathrm{Hom}(W, X[1])$$
over the same sequence for $T'$, with vertical maps given by $c[-1]$, $a$, $b$, $c$ and $a[1]$. The squares commute because $(a, b, c)$ is a morphism of triangles. The four outer vertical maps are bijective. By the five lemma for abelian groups, $b_*$ is bijective for each $W$, and $b$ is an isomorphism by the Yoneda lemma. The other two cases follow by rotation, because the rotation of $(a, b, c)$ is $(b, c, a[1])$ and $a[1]$ is an isomorphism if and only if $a$ is one. ∎

**Corollary (Uniqueness of cones).** Two distinguished triangles on the same morphism $f$ are isomorphic.

*Proof.* Let $T$ and $T'$ have the same $f$. Apply axiom 5 to $(1_X, 1_Y)$. The resulting morphism $(1_X, 1_Y, c)$ has two isomorphisms among its components, so $c$ is an isomorphism by the five lemma. ∎

The isomorphism $c$ is not unique in general, and Exercise 5 gives an example.

### Examples

**Example (The homotopy category).** Let $\mathcal{A}$ be an additive category and $f : X \to Y$ a morphism of cochain complexes. The *mapping cone* has $\mathrm{Cone}(f)^n = X^{n+1} \oplus Y^n$ and the differential $(x, y) \mapsto (-d x, f x + d y)$. The square of this differential is $(d^2 x, -f d x + d f x + d^2 y) = 0$, because $f$ commutes with $d$. The maps $Y \to \mathrm{Cone}(f)$, $y \mapsto (0, y)$, and $\mathrm{Cone}(f) \to X[1]$, $(x, y) \mapsto x$, are morphisms of complexes. In the homotopy category $K(\mathcal{A})$, the triangles isomorphic to $X \to Y \to \mathrm{Cone}(f) \to X[1]$ form a pretriangulated structure. Volume 26 proves this. The minus sign in the rotation corresponds to the sign of the differential of $X[1]$ in Section 1.

**Example (Abelian groups are not pretriangulated).** Multiplication by $2$ on $\mathbb{Z}$ is a monomorphism of abelian groups that does not split, because $\mathbb{Z}$ is not a direct summand of itself with quotient $\mathbb{Z}/2$. By the corollary on monomorphisms, the category of abelian groups has no pretriangulated structure for any shift. The same argument applies to each abelian category that has a monomorphism that does not split.

**Example (Graded vector spaces).** Let $k$ be a field and let $C$ be the category of $\mathbb{Z}$-graded $k$-vector spaces with the shift $(V[1])_n = V_{n+1}$. Every complex of $k$-vector spaces is homotopy equivalent to its cohomology with zero differential, so $C$ is equivalent to the homotopy category of complexes of $k$-vector spaces, and the cone triangles make it pretriangulated. Here each monomorphism splits, as the corollary requires.

### The library around it

::: mathlib
`CategoryTheory.Pretriangulated.isIso₂_of_isIso₁₃` · `Mathlib.CategoryTheory.Triangulated.Pretriangulated`

For a morphism `φ : T ⟶ T'` of distinguished triangles, `IsIso φ.hom₁` and `IsIso φ.hom₃` give `IsIso φ.hom₂`. The variants `isIso₃_of_isIso₁₂` and `isIso₁_of_isIso₂₃` cover the other two cases, and `exists_iso_of_arrow_iso` is the uniqueness of cones.

<?decl CategoryTheory.Pretriangulated.isIso₂_of_isIso₁₃?>
:::

A triangle in Mathlib has the fields `obj₁`, `obj₂`, `obj₃`, `mor₁`, `mor₂` and `mor₃`, and `Triangle.mk f g h` builds one. The exact sequences are given one place at a time: `Triangle.coyoneda_exact₂` is exactness at $\mathrm{Hom}(W, Y)$ for $\mathrm{Hom}(W, -)$, and `Triangle.yoneda_exact₂` is the dual statement. The file also gives instances `SplitMonoCategory C` and `SplitEpiCategory C`, and it constructs binary biproducts from the triangles with a zero third map. `binaryBiproductTriangle_distinguished` says that $X_1 \to X_1 \oplus X_2 \to X_2 \xrightarrow{0} X_1[1]$ is distinguished. `Triangle.shiftFunctor C n` shifts a triangle by $n$ and multiplies its maps by $(-1)^n$, and `Triangle.shift_distinguished` keeps it distinguished.

Common errors of a learner:

- The rotation has the sign $-f[1]$. A triangle with $+f[1]$ in the third place is in general not distinguished.
- `Triangle.invRotate` contains the isomorphisms of `shiftEquiv C 1`, because $Z[-1][1]$ is not equal to $Z$ as an object.
- Axiom 5 gives existence and not uniqueness. A construction that picks $c$ by `choose` does not give a functor from arrows to triangles.

### Exercises

1. (A) Show that $X \xrightarrow{0} 0 \to X[1] \xrightarrow{-1} X[1]$ and $0 \to X \xrightarrow{1} X \to 0$ are distinguished.
2. (A) Show that a morphism $f$ in a pretriangulated category is a monomorphism if and only if $h = 0$ in a distinguished triangle on $f$.
3. (B) Prove the exactness of the sequence of the functors $\mathrm{Hom}(-, W)$ in detail.
4. (B) Show that a direct sum of two distinguished triangles is distinguished. *Hint:* take a distinguished triangle on $f_1 \oplus f_2$, map the sum into it with axiom 5 twice, and apply the five lemma.
5. (B) Let $T$ be the direct sum of the distinguished triangles $X \to 0 \to X[1] \xrightarrow{-1} X[1]$ and $0 \to Y \xrightarrow{1} Y \to 0$ of Exercise 1. Show that the morphisms $c$ that complete $(0, 0)$ to an endomorphism of $T$ are the maps $X[1] \oplus Y \to X[1] \oplus Y$ that factor as the projection to $X[1]$, a map $u : X[1] \to Y$ and the inclusion of $Y$. Give graded vector spaces $X$ and $Y$ for which $u$ can be nonzero.
6. (C) Let $X \xrightarrow{f} Y \xrightarrow{g} Z \xrightarrow{h} X[1]$ be distinguished with $h = 0$. Show that $Y$ is a biproduct of $X$ and $Z$ with inclusions $f$ and a section of $g$. *Hint:* use the corollary on monomorphisms for $f$ and its dual for $g$.

### Notes and history

Verdier introduced triangulated categories in his thesis, published in 1996 as *Des catégories dérivées des catégories abéliennes*, and Puppe gave a similar notion for stable homotopy. The five lemma for triangles and the split monomorphisms are standard consequences of the axioms. The source cites the Stacks Project, tag 014A, for the five lemma.

The Mathlib Authors of `Triangulated.Basic` and `Triangulated.Rotate` are Luke Kershaw. The file `Triangulated.Pretriangulated` is by Luke Kershaw and Joël Riou, and `Triangulated.TriangleShift` is by Joël Riou.

### Reference

<?reference?>
