---
title: The mapping cone and the triangulated structure
kind: theory
modules:
  - Mathlib.Algebra.Homology.HomotopyCategory.Shift
  - Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
  - Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
  - Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
  - Mathlib.Algebra.Homology.HomotopyCategory.HomologicalFunctor
explains:
  E3: [CochainComplex.shiftFunctor, CochainComplex.mappingCone, CochainComplex.mappingCone.triangle, HomotopyCategory.Pretriangulated.distinguishedTriangles, HomotopyCategory.instPretriangulatedIntUp, HomotopyCategory.instIsTriangulatedIntUp, HomotopyCategory.instIsHomologicalIntUpHomologyFunctor]
  E2: [CochainComplex.shiftFunctorObjXIso, CochainComplex.shiftFunctorZero', CochainComplex.shiftFunctorAdd', CochainComplex.instHasShiftInt, CochainComplex.shiftEval, Homotopy.shift, HomotopyCategory.hasShift, HomotopyCategory.commShiftQuotient, CategoryTheory.Functor.mapCochainComplexShiftIso, CochainComplex.mappingCone.inl, CochainComplex.mappingCone.inr, CochainComplex.mappingCone.fst, CochainComplex.mappingCone.snd, CochainComplex.mappingCone.δ_inl, CochainComplex.mappingCone.ext_from, CochainComplex.mappingCone.ext_to, CochainComplex.mappingCone.desc, CochainComplex.mappingCone.descHomotopy, CochainComplex.mappingCone.lift, CochainComplex.mappingCone.liftHomotopy, CochainComplex.mappingCone.isZero_X_iff, CochainComplex.mappingCone.homotopyToZeroOfId, CochainComplex.mappingCone.triangleh, CochainComplex.mappingCone.map, CochainComplex.mappingCone.mapOfHomotopy, CochainComplex.mappingCone.triangleMap, CochainComplex.mappingCone.rotateHomotopyEquiv, CochainComplex.mappingCone.rotateTrianglehIso, CochainComplex.mappingCone.shiftIso, CochainComplex.mappingCone.shiftTrianglehIso, CochainComplex.mappingCone.mapTrianglehIso, HomotopyCategory.Pretriangulated.isomorphic_distinguished, HomotopyCategory.Pretriangulated.contractible_distinguished, HomotopyCategory.Pretriangulated.distinguished_cocone_triangle, HomotopyCategory.Pretriangulated.rotate_distinguished_triangle, HomotopyCategory.Pretriangulated.invRotate_distinguished_triangle', HomotopyCategory.Pretriangulated.shift_distinguished_triangle, HomotopyCategory.Pretriangulated.complete_distinguished_triangle_morphism, HomotopyCategory.mappingCone_triangleh_distinguished, HomotopyCategory.instIsTriangulatedIntUpMapHomotopyCategory, CochainComplex.mappingConeCompTriangle, CochainComplex.mappingConeCompTriangleh, CochainComplex.mappingConeCompHomotopyEquiv, HomotopyCategory.mappingConeCompTriangleh_distinguished]
  E1: auto
families: []
requires: [V24.C08, V25.C01, V25.C02, V25.C05, V26.C01, V26.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The mapping cone and the triangulated structure

### Overview

The category of complexes is abelian when $C$ is, but the homotopy category $K(C)$ of Section 1 is not abelian in general. Its replacement for a short exact sequence is a distinguished triangle $X \to Y \to Z \to X[1]$, in the sense of Volume 25, Chapter 5. In $K(C)$ the third object of the triangle on a map $\varphi$ is the mapping cone of $\varphi$, the homotopy cofiber of Section 1 for cochain complexes indexed by $\mathbb{Z}$.

This section defines the shift $K[n]$ of a cochain complex and the mapping cone, and it proves that the triangles $F \to G \to \mathrm{Cone}(\varphi) \to F[1]$ and the triangles isomorphic to them make $K(C)$ a triangulated category. It proves the rotation axiom and the completion of morphisms with explicit formulas and signs. At the end it proves that each cohomology functor $H^n : K(C) \to C$ is homological: it turns distinguished triangles into long exact sequences.

Throughout, $C$ is preadditive with binary biproducts, and abelian for cohomology. All complexes are cochain complexes indexed by $\mathbb{Z}$, so $d^n : K^n \to K^{n+1}$. Mathlib writes `f ≫ g` for $g \circ f$. Formulas on elements stand for matrices of maps.

### Definitions

**Definition (Shift of a cochain complex).** Let $n \in \mathbb{Z}$ and let $K$ be a cochain complex. The *shift* $K[n]$ is the complex with
$$K[n]^i = K^{i+n}, \qquad d_{K[n]}^i = (-1)^n d_K^{i+n}.$$
A map $f : K \to L$ gives $f[n] : K[n] \to L[n]$ with $f[n]^i = f^{i+n}$, without a sign. A homotopy $h$ from $f$ to $g$ gives the homotopy $(-1)^n h$ from $f[n]$ to $g[n]$.

The complexes $K[m][n]$ and $K[m+n]$ have the same terms and the same differential $(-1)^{m+n} d$. Mathlib records this by isomorphisms that are the identity in each degree, and they satisfy the coherence conditions of a shift by $\mathbb{Z}$ (Volume 25, Chapter 5). Since the shift preserves homotopies, it passes to $K(C)$.

**Definition (Mapping cone).** Let $\varphi : F \to G$ be a map of cochain complexes. The *mapping cone* of $\varphi$ is the complex
$$\mathrm{Cone}(\varphi)^n = F^{n+1} \oplus G^n, \qquad d(x, y) = (-d x, \ \varphi x + d y).$$
It is the homotopy cofiber of $\varphi$ from Section 1, so $d \circ d = 0$ by the computation there. It comes with the maps of complexes
$$\mathrm{inr} : G \to \mathrm{Cone}(\varphi), \ y \mapsto (0, y), \qquad p : \mathrm{Cone}(\varphi) \to F[1], \ (x, y) \mapsto -x.$$
Check that $p$ commutes with the differentials: $p(d(x, y)) = p(-dx, \varphi x + dy) = dx$, and $d_{F[1]}(p(x, y)) = -d(-x) = dx$.

**Definition (Standard triangle).** The *standard triangle* of $\varphi$ is the triangle
$$F \xrightarrow{\ \varphi\ } G \xrightarrow{\ \mathrm{inr}\ } \mathrm{Cone}(\varphi) \xrightarrow{\ p\ } F[1]$$
of cochain complexes. Its image in $K(C)$ is the standard triangle in $K(C)$. A triangle in $K(C)$ is *distinguished* if it is isomorphic, as a triangle in $K(C)$, to the standard triangle of some map of complexes $\varphi$.

The composite of two consecutive maps of a standard triangle is null homotopic, but not zero: $\mathrm{inr} \circ \varphi$ is $x \mapsto (0, \varphi x)$, and the family $s(x) = (x, 0)$ is a homotopy from it to $0$ (Section 1). The composite $p \circ \mathrm{inr}$ is zero.

::: mathlib
`CochainComplex.mappingCone` · `Mathlib.Algebra.Homology.HomotopyCategory.MappingCone`

`mappingCone φ` is defined as `homotopyCofiber φ`. The structure maps are given as cochains of the complex of morphisms `HomComplex`: `inl φ : Cochain F (mappingCone φ) (-1)` is $x \mapsto (x, 0)$ of degree $-1$, `inr φ : G ⟶ mappingCone φ` is a map of complexes, `fst φ : Cocycle (mappingCone φ) F 1` is $(x, y) \mapsto x$ of degree $1$, and `snd φ : Cochain (mappingCone φ) G 0` is $(x, y) \mapsto y$. The lemma `δ_inl` says that the differential of `inl φ` is `Cochain.ofHom (φ ≫ inr φ)`, which is the null homotopy of $\mathrm{inr} \circ \varphi$. Maps out of the cone are built with `desc φ α β eq` from `α : Cochain F K (-1)` and `β : G ⟶ K` with `δ (-1) 0 α = Cochain.ofHom (φ ≫ β)`, and maps into the cone with `lift`. `ext_from` and `ext_to` reduce equalities of maps to the components.

<?decl CochainComplex.mappingCone?>
:::

### Theorems and proofs

**Theorem (The homotopy category is pretriangulated).** Let $C$ be additive. The distinguished triangles make $K(C)$ a pretriangulated category: they satisfy the axioms of Volume 25, Chapter 5. The distinguished triangles are closed under isomorphism, the triangle $X \xrightarrow{1} X \to 0 \to X[1]$ is distinguished, each morphism is the first map of a distinguished triangle, the rotation and the inverse rotation of a distinguished triangle are distinguished, and each commutative square between the first maps of two distinguished triangles extends to a morphism of triangles.

*Proof of closure under isomorphism and of existence.* The class is closed under isomorphism by its definition. A morphism of $K(C)$ from $F$ to $G$ is the class $[\varphi]$ of a map of complexes, because the quotient functor is full. The standard triangle of $\varphi$ is a distinguished triangle on $[\varphi]$. $\square$

*Proof for the contractible triangle.* Take $\varphi = 1_X$. Section 1 showed that $\mathrm{Cone}(1_X)$ is contractible, so it is a zero object of $K(C)$. The triangle $X \xrightarrow{1} X \to \mathrm{Cone}(1_X) \to X[1]$ is then isomorphic to $X \xrightarrow{1} X \to 0 \to X[1]$ by the identity maps on $X$ and the unique isomorphism $\mathrm{Cone}(1_X) \cong 0$. $\square$

*Proof of the completion of morphisms.* Let $\varphi_1 : F_1 \to G_1$ and $\varphi_2 : F_2 \to G_2$ be maps of complexes, and let $a : F_1 \to F_2$ and $b : G_1 \to G_2$ be maps with $[b \varphi_1] = [\varphi_2 a]$ in $K(C)$. It suffices to treat standard triangles. Choose a homotopy $s$ from $b \varphi_1$ to $\varphi_2 a$, so $s^{n+1} : F_1^{n+1} \to G_2^{n}$ and
$$b \varphi_1 - \varphi_2 a = d s + s d.$$
Define $c : \mathrm{Cone}(\varphi_1) \to \mathrm{Cone}(\varphi_2)$ by $c(x, y) = (a x, \ b y + s x)$. It commutes with the differentials. On one side,
$$c(d(x, y)) = c(-dx, \ \varphi_1 x + dy) = (-a\, dx, \ b \varphi_1 x + b\, dy - s\, dx).$$
On the other side,
$$d(c(x, y)) = (-d a x, \ \varphi_2 a x + d b y + d s x).$$
The first components agree because $a$ is a map of complexes, and the second components agree because $b\, dy = d b y$ and $b \varphi_1 x - s\, dx = \varphi_2 a x + d s x$, which is the homotopy relation applied to $x$. The square with $\mathrm{inr}$ commutes on the nose: $c(0, y) = (0, b y)$. The square with $p$ commutes on the nose: $p_2(c(x, y)) = -a x = a[1](p_1(x, y))$. So $(a, b, c)$ is a morphism of triangles in $K(C)$. $\square$

*Proof of the rotation axiom.* Let $\varphi : F \to G$ and write $M = \mathrm{Cone}(\varphi)$. The rotation of the standard triangle of $\varphi$ is
$$G \xrightarrow{\ \mathrm{inr}\ } M \xrightarrow{\ p\ } F[1] \xrightarrow{\ -\varphi[1]\ } G[1].$$
The claim is that it is isomorphic in $K(C)$ to the standard triangle of $\psi = \mathrm{inr} : G \to M$,
$$G \xrightarrow{\ \psi\ } M \xrightarrow{\ \mathrm{inr}_\psi\ } \mathrm{Cone}(\psi) \xrightarrow{\ p_\psi\ } G[1].$$
The terms of the cone are $\mathrm{Cone}(\psi)^n = G^{n+1} \oplus F^{n+1} \oplus G^n$. Write an element as $(u, x, y)$. The differential is
$$d(u, x, y) = (-du, \ -dx, \ u + \varphi x + dy).$$
Define $\beta : \mathrm{Cone}(\psi) \to F[1]$ by $\beta(u, x, y) = -x$ and $\alpha : F[1] \to \mathrm{Cone}(\psi)$ by $\alpha(x) = (\varphi x, -x, 0)$.

Step 1: both are maps of complexes. For $\beta$: $\beta(d(u, x, y)) = dx$ and $d_{F[1]}(-x) = dx$. For $\alpha$: $d(\alpha(x)) = (-d \varphi x, dx, \varphi x - \varphi x) = (-\varphi dx, dx, 0)$, and $\alpha(d_{F[1]} x) = \alpha(-dx) = (-\varphi dx, dx, 0)$.

Step 2: they are inverse homotopy equivalences. First, $\beta \alpha = 1$. Next, $1 - \alpha \beta$ sends $(u, x, y)$ to $(u + \varphi x, 0, y)$. Let $t(u, x, y) = (y, 0, 0)$, from degree $n$ to degree $n - 1$. Then
$$(t d + d t)(u, x, y) = (u + \varphi x + dy, 0, 0) + (-dy, 0, y) = (u + \varphi x, 0, y).$$
So $t$ is a homotopy from $1$ to $\alpha \beta$.

Step 3: the maps $(1_G, 1_M, \beta)$ form a morphism of triangles in $K(C)$ from the standard triangle of $\psi$ to the rotated triangle. The first square is trivial. The second square commutes on the nose: $\beta(\mathrm{inr}_\psi(x, y)) = \beta(0, x, y) = -x = p(x, y)$. For the third square compare $-\varphi[1] \circ \beta$, which sends $(u, x, y)$ to $\varphi x$, with $p_\psi$, which sends it to $-u$. The difference $p_\psi - (-\varphi[1] \beta)$ is $(u, x, y) \mapsto -(u + \varphi x)$. The family $t'(u, x, y) = -y$, from $\mathrm{Cone}(\psi)^n$ to $G[1]^{n-1} = G^n$, is a homotopy from this difference to $0$:
$$d_{G[1]} t' + t' d = d y - (u + \varphi x + dy) = -(u + \varphi x).$$
So the third square commutes in $K(C)$. The three components are isomorphisms in $K(C)$, so the rotated triangle is distinguished. $\square$

The inverse rotation needs a similar computation with the isomorphism $\mathrm{Cone}(\varphi)[n] \cong \mathrm{Cone}(\varphi[n])$ that changes the sign of the first component by $(-1)^n$. Mathlib proves it as `invRotate_distinguished_triangle'`. This finishes the proof of the theorem.

**Theorem (The homotopy category is triangulated).** $K(C)$ satisfies the octahedral axiom. For maps $f : X_1 \to X_2$ and $g : X_2 \to X_3$, the triangle
$$\mathrm{Cone}(f) \xrightarrow{\ u\ } \mathrm{Cone}(g f) \xrightarrow{\ v\ } \mathrm{Cone}(g) \xrightarrow{\ w\ } \mathrm{Cone}(f)[1]$$
with $u(x, y) = (x, g y)$, $v(x, z) = (f x, z)$ and $w = \mathrm{inr}_f[1] \circ p_g$ is distinguished.

*Proof.* The maps $u$ and $v$ are the maps `mappingCone.map` of the squares $(1, g)$ and $(f, 1)$, so they are maps of complexes. The composite $v u$ sends $(x, y)$ to $(f x, g y)$. Mathlib constructs a homotopy equivalence between $\mathrm{Cone}(g)$ and $\mathrm{Cone}(u)$ that makes the triangle above isomorphic in $K(C)$ to the standard triangle of $u$, by a computation of the same kind as the rotation axiom. So the triangle is distinguished. The octahedral axiom asks for such a triangle whose maps are compatible with the three triangles on $f$, $g$ and $g f$. For standard triangles the compatibilities hold by the formulas for $u$, $v$ and $w$, and Volume 25, Chapter 5 reduces the general case to standard triangles, because every distinguished triangle is isomorphic to a standard one. $\square$

**Theorem (Cohomology is homological).** Let $C$ be abelian. For each $n \in \mathbb{Z}$ the functor $H^n : K(C) \to C$ is homological: for each distinguished triangle $X \to Y \to Z \to X[1]$ the sequence $H^n(X) \to H^n(Y) \to H^n(Z)$ is exact. Consequently each distinguished triangle gives a long exact sequence
$$\cdots \to H^n(X) \to H^n(Y) \to H^n(Z) \to H^{n+1}(X) \to H^{n+1}(Y) \to \cdots.$$

*Proof.* Exactness is invariant under isomorphism of triangles. Let $T$ be distinguished. By the inverse rotation axiom, $T' = T$ rotated backwards is distinguished, so $T'$ is isomorphic to a standard triangle on some $\varphi : F \to G$. The rotation is a functor, and the rotation of $T'$ is isomorphic to $T$. So $T$ is isomorphic to the rotated standard triangle
$$G \xrightarrow{\ \mathrm{inr}\ } \mathrm{Cone}(\varphi) \xrightarrow{\ p\ } F[1] \xrightarrow{\ -\varphi[1]\ } G[1].$$
In each degree, $0 \to G^n \to F^{n+1} \oplus G^n \to F^{n+1} \to 0$ with the maps $y \mapsto (0, y)$ and $(x, y) \mapsto -x$ is split short exact. So $0 \to G \to \mathrm{Cone}(\varphi) \to F[1] \to 0$ is a short exact sequence of complexes, and the long exact cohomology sequence of Chapter 2 gives exactness at $H^n(\mathrm{Cone}(\varphi))$. The long exact sequence of the triangle follows by rotation, with $H^n(X[1]) = H^{n+1}(X)$. $\square$

**Corollary (Cones detect quasi-isomorphisms).** A map of complexes $\varphi$ is a quasi-isomorphism if and only if $\mathrm{Cone}(\varphi)$ is acyclic. It is a homotopy equivalence if and only if $\mathrm{Cone}(\varphi)$ is contractible.

*Proof.* In the long exact sequence $H^{n}(\mathrm{Cone}\, \varphi) \to H^{n+1}(F) \to H^{n+1}(G) \to H^{n+1}(\mathrm{Cone}\, \varphi)$ the map in the middle is $H^{n+1}(\varphi)$, up to sign. All maps $H(\varphi)$ are isomorphisms if and only if all groups $H(\mathrm{Cone}\, \varphi)$ vanish. For the second claim, in a pretriangulated category a morphism is an isomorphism if and only if its third object is zero (Volume 25, Chapter 5), and a complex is zero in $K(C)$ if and only if it is contractible (Section 1). $\square$

### Examples

**Example (The cone of multiplication by $n$).** Let $F = G = \mathbb{Z}$ in degree $0$ and $\varphi = n$, with $n \ne 0$. Then $\mathrm{Cone}(\varphi)$ has $F^0 = \mathbb{Z}$ in degree $-1$ and $G^0 = \mathbb{Z}$ in degree $0$, with $d(x, 0) = (0, n x)$. So $\mathrm{Cone}(\varphi)$ is the complex $\mathbb{Z} \xrightarrow{n} \mathbb{Z}$ in degrees $-1$ and $0$, with $H^{-1} = 0$ and $H^0 = \mathbb{Z}/n$. The long exact sequence of the triangle reads
$$0 \to H^{-1}(\mathrm{Cone}) \to \mathbb{Z} \xrightarrow{n} \mathbb{Z} \to \mathbb{Z}/n \to 0,$$
and the cone is a free resolution of $\mathbb{Z}/n$. The cone replaces the cokernel up to quasi-isomorphism.

**Example (The cone of a quasi-isomorphism).** Let $F$ be $\mathbb{Z} \xrightarrow{2} \mathbb{Z}$ in degrees $-1$ and $0$, let $G = \mathbb{Z}/2$ in degree $0$, and let $\varphi$ be the reduction mod $2$ in degree $0$. It is a map of complexes because the composite $\mathbb{Z} \xrightarrow{2} \mathbb{Z} \to \mathbb{Z}/2$ is zero, and it is a quasi-isomorphism. The cone has $F^{0} = \mathbb{Z}$ in degree $-1$, $F^{1} \oplus G^0 = \mathbb{Z}/2$ in degree $0$, and $F^{-1} \oplus G^{-2} = \mathbb{Z}$ in degree $-2$. It is the complex $\mathbb{Z} \xrightarrow{-2} \mathbb{Z} \to \mathbb{Z}/2$ in degrees $-2$, $-1$, $0$, which is exact, as the corollary says. It is not contractible, because the surjection $\mathbb{Z} \to \mathbb{Z}/2$ does not split. So $\varphi$ is a quasi-isomorphism and not a homotopy equivalence.

**Example (The octahedral triangle for $2$ and $3$).** Let $X_1 = X_2 = X_3 = \mathbb{Z}$ in degree $0$, with $f = 2$ and $g = 3$, so $g f = 6$. By the first example, $\mathrm{Cone}(f)$, $\mathrm{Cone}(g f)$ and $\mathrm{Cone}(g)$ are $\mathbb{Z} \xrightarrow{2} \mathbb{Z}$, $\mathbb{Z} \xrightarrow{6} \mathbb{Z}$ and $\mathbb{Z} \xrightarrow{3} \mathbb{Z}$ in degrees $-1$ and $0$, with $H^0$ equal to $\mathbb{Z}/2$, $\mathbb{Z}/6$ and $\mathbb{Z}/3$. The map $u(x, y) = (x, 3 y)$ induces $y \mapsto 3 y$ from $\mathbb{Z}/2$ to $\mathbb{Z}/6$, and $v(x, z) = (2 x, z)$ induces the reduction $\mathbb{Z}/6 \to \mathbb{Z}/3$. All other cohomology groups vanish, so the long exact sequence of the octahedral triangle is the short exact sequence $0 \to \mathbb{Z}/2 \xrightarrow{3} \mathbb{Z}/6 \to \mathbb{Z}/3 \to 0$.

### The library around it

::: mathlib
`HomotopyCategory.instPretriangulatedIntUp` · `Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated`

The instance gives `Pretriangulated (HomotopyCategory C (ComplexShape.up ℤ))` when `C` is preadditive with binary biproducts and a zero object. Its distinguished triangles are `HomotopyCategory.Pretriangulated.distinguishedTriangles C`, the triangles isomorphic to some `mappingCone.triangleh φ`, the image of `mappingCone.triangle φ`. The axioms are the lemmas `isomorphic_distinguished`, `contractible_distinguished`, `distinguished_cocone_triangle`, `rotate_distinguished_triangle`, `invRotate_distinguished_triangle'` and `complete_distinguished_triangle_morphism`. The third map of `mappingCone.triangle φ` is `Cocycle.homOf ((-fst φ).rightShift 1 0 _)`, the map $(x, y) \mapsto -x$ of the text.

<?decl HomotopyCategory.instPretriangulatedIntUp?>
:::

The constructions in the proofs have names. `mappingCone.homotopyToZeroOfId` is the contraction of the cone of an identity, `mapOfHomotopy` and `map` are the maps $c$ of the completion axiom, and `triangleMap` is the morphism of triangles. `rotateHomotopyEquiv` is the homotopy equivalence of $F[1]$ with $\mathrm{Cone}(\mathrm{inr})$, and `rotateTrianglehIso` is the isomorphism of triangles. `shiftIso` is $\mathrm{Cone}(\varphi)[n] \cong \mathrm{Cone}(\varphi[n])$, with `shiftTrianglehIso` and the lemma `shift_distinguished_triangle`. An additive functor $G : C \to D$ commutes with cones by `mapTrianglehIso`, and the instance `instIsTriangulatedIntUpMapHomotopyCategory` says that the induced functor $K(C) \to K(D)$ is triangulated.

::: mathlib
`HomotopyCategory.instIsTriangulatedIntUp` · `Mathlib.Algebra.Homology.HomotopyCategory.Triangulated`

The instance gives `IsTriangulated (HomotopyCategory C (ComplexShape.up ℤ))`. The triangle of the octahedral axiom is `CochainComplex.mappingConeCompTriangle f g`, whose third map is `(triangle g).mor₃ ≫ (inr f)⟦1⟧'`. `mappingConeCompHomotopyEquiv` compares it with a standard triangle, and `mappingConeCompTriangleh_distinguished` is the conclusion. The proof applies `IsTriangulated.mk'`, which needs an octahedron only for a diagram isomorphic to the given one.

<?decl HomotopyCategory.instIsTriangulatedIntUp?>
:::

The shift is `CochainComplex.shiftFunctor C n`, with the identification `shiftFunctorObjXIso : (K⟦n⟧).X i ≅ K.X m` for `m = i + n`, the isomorphisms `shiftFunctorZero'` and `shiftFunctorAdd'`, and the instance `CochainComplex.instHasShiftInt`. `Homotopy.shift` shifts a homotopy with the sign `n.negOnePow`, the instance `HomotopyCategory.hasShift` passes the shift to $K(C)$, and `commShiftQuotient` says that the quotient functor commutes with the shifts. The instance `HomotopyCategory.instIsHomologicalIntUpHomologyFunctor` is the theorem on cohomology. Its proof uses `HomotopyCategory.distinguished_iff_iso_trianglehOfDegreewiseSplit`, which characterizes the distinguished triangles by degreewise split short exact sequences, as in the proof above.

Common errors of a learner:

- The terms of the cone are $F^{n+1} \oplus G^n$. Writing $F^n \oplus G^{n-1}$ is the convention of chain complexes and gives wrong degrees for `CochainComplex`.
- The third map of the standard triangle is $(x, y) \mapsto -x$ in Mathlib. Some textbooks use $+x$ with another sign in the differential. Results that depend on signs must be read with the convention of the source.
- The composite $\mathrm{inr} \circ \varphi$ is not zero in the category of complexes. It is zero only in $K(C)$.
- `K⟦n⟧` has the terms of $K$ moved by $n$ and the differential multiplied by $(-1)^n$, but a map `f⟦n⟧'` has no sign.

### Exercises

1. (A) Compute the mapping cone of the zero map $F \to G$ and show that it is $F[1] \oplus G$ as a complex.
2. (A) Let $\varphi : \mathbb{Z} \to \mathbb{Z}/n$ be the quotient map, both complexes in degree $0$. Write $\mathrm{Cone}(\varphi)$ and compute its cohomology.
3. (B) Show that $K[n]$ with the sign $(-1)^n$ is a complex, and that the complex with the same terms and the differential $d$ without the sign is isomorphic to $K[n]$. *Hint:* multiply degree $i$ by a suitable sign $\epsilon_i$.
4. (B) Show that $\varphi[1] \circ p : \mathrm{Cone}(\varphi) \to G[1]$ is null homotopic, and give the homotopy. *Hint:* try $t(x, y) = \pm y$ from degree $n$ to degree $n - 1$.
5. (B) Let $0 \to A \xrightarrow{f} B \xrightarrow{g} Q \to 0$ be a short exact sequence of complexes that splits in each degree. Show that the map $\mathrm{Cone}(f) \to Q$, $(x, y) \mapsto g y$, is a homotopy equivalence. *Hint:* use the splittings to write $B^n = A^n \oplus Q^n$ and build the inverse.
6. (C) Prove the inverse rotation axiom directly: show that $\mathrm{Cone}(\varphi)[-1] \xrightarrow{-p[-1]} F \xrightarrow{\varphi} G \xrightarrow{\mathrm{inr}} \mathrm{Cone}(\varphi)$ is isomorphic in $K(C)$ to a standard triangle.
7. (C) Let $C$ be abelian. Use the triangulated structure to show that the quasi-isomorphisms of $K(C)$ satisfy two out of three: if two of $\varphi$, $\psi$ and $\psi \varphi$ are quasi-isomorphisms, so is the third. *Hint:* use the octahedral triangle and the long exact sequence.

### Notes and history

Verdier introduced triangulated categories in his thesis, and the homotopy category of complexes with the mapping cone triangles was his first example. The signs of the cone and of the shift vary between sources. The source file states that it follows the convention of Verdier with the signs of Conrad's book on Grothendieck duality and of the Stacks Project, tag 014P, and that this formalization first appeared in the Liquid Tensor Experiment.

The Mathlib Authors of the files `HomotopyCategory.Shift`, `HomotopyCategory.MappingCone`, `HomotopyCategory.Pretriangulated`, `HomotopyCategory.Triangulated` and `HomotopyCategory.HomologicalFunctor` are Joël Riou.

### Reference

<?reference?>
