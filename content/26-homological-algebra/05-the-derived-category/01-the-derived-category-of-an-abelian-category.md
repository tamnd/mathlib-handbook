---
title: The derived category of an abelian category
kind: theory
modules:
  - Mathlib.Algebra.Homology.Localization
  - Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
  - Mathlib.Algebra.Homology.DerivedCategory.Basic
  - Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
  - Mathlib.Algebra.Homology.DerivedCategory.ShortExact
  - Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
  - Mathlib.Algebra.Homology.DerivedCategory.Plus
explains:
  E3: [HomologicalComplexUpToQuasiIso, HomologicalComplexUpToQuasiIso.Q_map_eq_of_homotopy, HomotopyCategory.quasiIso, HomotopyCategory.subcategoryAcyclic, HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic, HasDerivedCategory, DerivedCategory, DerivedCategory.Q, DerivedCategory.Qh, DerivedCategory.triangleOfSES_distinguished, DerivedCategory.homologyFunctor, DerivedCategory.isIso_iff, DerivedCategory.Plus.Qh_map_bijective_of_isKInjective]
  E2: [HomologicalComplexUpToQuasiIso.Q, HomologicalComplexUpToQuasiIso.Qh, ComplexShape.QFactorsThroughHomotopy, HomotopyCategory.mem_subcategoryAcyclic_iff, HasDerivedCategory.standard, DerivedCategory.mem_distTriang_iff, DerivedCategory.mappingCone_triangle_distinguished, DerivedCategory.singleFunctor, DerivedCategory.isIso_Q_map_iff_quasiIso, DerivedCategory.Q_map_eq_of_homotopy, DerivedCategory.triangleOfSES, DerivedCategory.triangleOfSESδ, CategoryTheory.ShortComplex.ShortExact.singleTriangle, CategoryTheory.ShortComplex.ShortExact.singleTriangle_distinguished, DerivedCategory.homologyFunctorFactors, DerivedCategory.HomologySequence.δ, DerivedCategory.HomologySequence.exact₂, DerivedCategory.HomologySequence.exact₃, DerivedCategory.Plus.Q, DerivedCategory.Plus.Qh, HomotopyCategory.Plus.subcategoryAcyclic, HomotopyCategory.Plus.quasiIso_eq_subcategoryAcyclic_trW]
  E1: auto
families: []
requires: [V24.C08, V25.C02, V25.C04, V25.C05, V26.C02, V26.C03]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The derived category of an abelian category

### Overview

Homology forgets much of a complex, but it does not forget enough. The complex $\mathbb{Z} \xrightarrow{2} \mathbb{Z}$ and the module $\mathbb{Z}/2$ in degree $0$ have the same cohomology, and the map from the first to the second is a quasi-isomorphism. There is no map of complexes in the other direction that induces an isomorphism. A projective resolution $P \to M$ is a quasi-isomorphism of the same kind.

The derived category $D(A)$ of an abelian category $A$ repairs this. It is the category of cochain complexes in which each quasi-isomorphism becomes an isomorphism. The construction is a localization in the sense of Volume 25, Chapter 4. This section shows that $D(A)$ is a Verdier quotient of the homotopy category $K(A)$ of Chapter 3, so it is triangulated. Short exact sequences give distinguished triangles, cohomology detects isomorphisms, and K-injective complexes compute morphisms.

In this section all complexes are cochain complexes indexed by $\mathbb{Z}$, with $d : K^n \to K^{n+1}$. The cone of $f : K \to L$ is $\operatorname{Cone}(f)^n = K^{n+1} \oplus L^n$ with $d(a, b) = (-da, f(a) + db)$, as in Chapter 3. In the text $g \circ f$ is the composite, and Mathlib writes `f ≫ g`.

### Definitions

Let $A$ be an abelian category. Write $C(A)$ for the category of cochain complexes in $A$ indexed by $\mathbb{Z}$, and $K(A)$ for its homotopy category. The objects of $K(A)$ are the complexes, and its morphisms are the homotopy classes of maps of complexes. Chapter 3 proves that $K(A)$ is triangulated, with the triangles $K \to L \to \operatorname{Cone}(f) \to K[1]$ as distinguished triangles, and that each cohomology functor $H^n : K(A) \to A$ is homological.

**Definition (Quasi-isomorphism in the homotopy category).** A morphism $f : K \to L$ of $K(A)$ is a *quasi-isomorphism* if $H^n(f)$ is an isomorphism for each $n \in \mathbb{Z}$. This does not depend on the representative of the homotopy class, because homotopic maps induce the same map on cohomology (Chapter 3).

**Definition (Acyclic complexes).** A complex $K$ is *acyclic* if $H^n(K) = 0$ for all $n$. The acyclic complexes form a full subcategory of $K(A)$. It is the kernel of the homological functor $H^0$ in the sense of Volume 25, Chapter 5: an object $K$ is in it when $H^0(K[n]) = H^n(K)$ is zero for all $n$.

**Definition (Derived category).** The *derived category* of $A$ is a category $D(A)$ with a functor $Q : C(A) \to D(A)$ that is a localization of $C(A)$ at the class of quasi-isomorphisms. So $Q$ sends each quasi-isomorphism to an isomorphism, and each functor $F : C(A) \to E$ with this property factors as $F \cong G \circ Q$ for a functor $G$ that is unique up to a unique isomorphism.

**Definition (Single complex).** For $X \in A$ and $n \in \mathbb{Z}$, the complex $X[-n]$ has $X$ in degree $n$ and $0$ in the other degrees. The composite of $X \mapsto X[-n]$ with $Q$ is the functor $\iota_n : A \to D(A)$. In particular $\iota_0(X)$ is $X$ placed in degree $0$.

**Definition (K-injective complex).** A complex $I$ is *K-injective* if each map of complexes $Z \to I$ from an acyclic complex $Z$ is homotopic to zero. Equivalently, $\operatorname{Hom}_{K(A)}(Z, I) = 0$ for each acyclic $Z$.

A bounded below complex of injective objects is K-injective. Chapter 4 builds such complexes as injective resolutions.

::: mathlib
`DerivedCategory` · `Mathlib.Algebra.Homology.DerivedCategory.Basic`

`DerivedCategory C` is defined as `HomologicalComplexUpToQuasiIso C (ComplexShape.up ℤ)`, a localization of `CochainComplex C ℤ` at `HomologicalComplex.quasiIso C (ComplexShape.up ℤ)`. The definition needs the instance `[HasDerivedCategory.{w} C]`, which asserts that this localization exists with morphisms in `Type w`. The functor is `DerivedCategory.Q : CochainComplex C ℤ ⥤ DerivedCategory C`. The single functors are `DerivedCategory.singleFunctor C n : C ⥤ DerivedCategory C`.

<?decl DerivedCategory?>
:::

::: mathlib
`HasDerivedCategory` · `Mathlib.Algebra.Homology.DerivedCategory.Basic`

`HasDerivedCategory.{w} C` is an abbreviation for `MorphismProperty.HasLocalization.{w}` of the quasi-isomorphisms. It is a class, and a theorem must not depend on which instance holds. Use `HasDerivedCategory.standard C` with `letI` only to obtain a derived category when none is available. The morphisms of a localization are classes of zigzags, so the universe is a real choice.

<?decl HasDerivedCategory?>
:::

### Theorems and proofs

The first theorem shows that homotopic maps become equal in $D(A)$. The proof uses a cylinder. For a complex $K$, let $\operatorname{Cyl}(K)^n = K^n \oplus K^{n+1} \oplus K^n$ with
$$d(a, b, c) = (da + b,\; -db,\; dc - b).$$
Then $d(d(a,b,c)) = (d(da + b) - db,\; d d b,\; d(dc - b) + db) = 0$, so $\operatorname{Cyl}(K)$ is a complex. Let $i_0(a) = (a, 0, 0)$, $i_1(c) = (0, 0, c)$ and $p(a, b, c) = a + c$. These are maps of complexes, and $p \circ i_0 = p \circ i_1 = 1_K$.

**Lemma (The cylinder).** The map $p : \operatorname{Cyl}(K) \to K$ is a homotopy equivalence. A homotopy $h$ from $f : K \to L$ to $g : K \to L$, that is a family $h^n : K^n \to L^{n-1}$ with $f - g = dh + hd$, gives a map of complexes $\varphi : \operatorname{Cyl}(K) \to L$ with $\varphi \circ i_0 = f$ and $\varphi \circ i_1 = g$.

*Proof.* Let $s : \operatorname{Cyl}(K)^n \to \operatorname{Cyl}(K)^{n-1}$ be $s(a, b, c) = (0, -c, 0)$, where $c \in K^n$ goes to the middle summand $K^{(n-1)+1} = K^n$. Then
$$ds(a,b,c) = d(0, -c, 0) = (-c,\; dc,\; c), \qquad sd(a,b,c) = s(da + b, -db, dc - b) = (0,\; b - dc,\; 0).$$
The sum is $(-c, b, c) = (a, b, c) - (a + c, 0, 0) = (1 - i_0 \circ p)(a, b, c)$. So $i_0 \circ p$ is homotopic to the identity, and with $p \circ i_0 = 1$ this makes $p$ a homotopy equivalence. For the second claim, put $\varphi(a, b, c) = f(a) + h(b) + g(c)$, with $h = h^{n+1} : K^{n+1} \to L^n$. Then
$$\varphi(d(a,b,c)) = f(da) + f(b) - h(db) + g(dc) - g(b),$$
and $d\varphi(a,b,c) = d f(a) + d h(b) + d g(c)$. Since $f$ and $g$ commute with $d$, the two agree exactly when $f(b) - g(b) = dh(b) + hd(b)$, and this is the homotopy relation. By the definitions, $\varphi i_0 = f$ and $\varphi i_1 = g$. $\square$

**Theorem (Homotopic maps are equal in the derived category).** If $f, g : K \to L$ are homotopic, then $Q(f) = Q(g)$.

*Proof.* Take $\varphi$ as in the lemma. The map $p$ is a homotopy equivalence, so $H^n(p)$ is an isomorphism for each $n$, and $p$ is a quasi-isomorphism. Thus $Q(p)$ is an isomorphism. From $Q(p) \circ Q(i_0) = 1 = Q(p) \circ Q(i_1)$ it follows that $Q(i_0) = Q(p)^{-1} = Q(i_1)$. Then $Q(f) = Q(\varphi) \circ Q(i_0) = Q(\varphi) \circ Q(i_1) = Q(g)$. $\square$

**Corollary (The derived category is a localization of the homotopy category).** The functor $Q$ factors as $Q \cong Q_h \circ \pi$, where $\pi : C(A) \to K(A)$ is the quotient functor. The functor $Q_h : K(A) \to D(A)$ is a localization of $K(A)$ at the quasi-isomorphisms.

*Proof.* By the theorem, $Q$ is constant on homotopy classes, so it factors through $\pi$. Let $F : K(A) \to E$ invert the quasi-isomorphisms. Then $F \circ \pi$ inverts the quasi-isomorphisms of $C(A)$, so $F \circ \pi \cong G \circ Q_h \circ \pi$ for some $G$, unique up to unique isomorphism. The functor $\pi$ is the identity on objects and full, so this isomorphism is an isomorphism $F \cong G \circ Q_h$. $\square$

**Theorem (Quasi-isomorphisms and acyclic cones).** A morphism $f : K \to L$ of $K(A)$ is a quasi-isomorphism if and only if $\operatorname{Cone}(f)$ is acyclic.

*Proof.* Write $M = \operatorname{Cone}(f)$. The triangle $K \to L \to M \to K[1]$ is distinguished in $K(A)$ and $H^0$ is homological, so it gives the long exact sequence
$$\cdots \to H^{n-1}(M) \to H^n(K) \xrightarrow{H^n(f)} H^n(L) \to H^n(M) \to H^{n+1}(K) \xrightarrow{H^{n+1}(f)} H^{n+1}(L) \to \cdots.$$
Suppose that each $H^n(f)$ is an isomorphism. Exactness at $H^n(L)$ says that the kernel of $H^n(L) \to H^n(M)$ is the image of $H^n(f)$, which is all of $H^n(L)$, so this map is zero. Exactness at $H^n(M)$ says that the kernel of $H^n(M) \to H^{n+1}(K)$ is the image of the zero map, so $H^n(M) \to H^{n+1}(K)$ is a monomorphism. Its image is the kernel of $H^{n+1}(f)$, which is zero. A monomorphism with zero image has a zero source, so $H^n(M) = 0$. Conversely, suppose that $H^n(M) = 0$ for all $n$. The sequence $0 = H^{n-1}(M) \to H^n(K) \to H^n(L) \to H^n(M) = 0$ is exact, so $H^n(f)$ is an isomorphism. $\square$

**Corollary (The derived category is a Verdier quotient).** The quasi-isomorphisms of $K(A)$ are the morphisms $W$ of Volume 25, Chapter 5, attached to the triangulated subcategory of acyclic complexes. So $D(A)$ is the Verdier quotient of $K(A)$ by the acyclic complexes. It carries a pretriangulated structure whose distinguished triangles are the triangles isomorphic to the images under $Q_h$ of distinguished triangles of $K(A)$. With it, $Q_h$ is a triangulated functor, and $D(A)$ is triangulated.

*Proof.* The acyclic complexes are closed under shifts, since $H^n(K[1]) = H^{n+1}(K)$. They satisfy the two out of three property for distinguished triangles by the long exact sequence, so they form a triangulated subcategory. By the theorem, its class $W$ is the class of quasi-isomorphisms. The remaining claims are the theorem of Volume 25, Chapter 5, on the localization of a triangulated category at the class $W$ of a triangulated subcategory. $\square$

By this corollary the distinguished triangles of $D(A)$ are the triangles isomorphic to the image $Q(K) \to Q(L) \to Q(\operatorname{Cone}(f)) \to Q(K)[1]$ of a cone triangle.

**Theorem (Short exact sequences give triangles).** Let $0 \to X_1 \xrightarrow{f} X_2 \xrightarrow{g} X_3 \to 0$ be a short exact sequence in $C(A)$. The map $\sigma : \operatorname{Cone}(f) \to X_3$, $\sigma(a, b) = g(b)$, is a quasi-isomorphism. With $\delta = Q(\operatorname{pr}) \circ Q(\sigma)^{-1}$, where $\operatorname{pr} : \operatorname{Cone}(f) \to X_1[1]$ is the projection, the triangle
$$Q(X_1) \xrightarrow{Q(f)} Q(X_2) \xrightarrow{Q(g)} Q(X_3) \xrightarrow{\delta} Q(X_1)[1]$$
is distinguished in $D(A)$.

*Proof.* First, $\sigma$ is a map of complexes: $\sigma(d(a, b)) = g(f(a) + db) = g(db) = d g(b)$, since $g \circ f = 0$. It is surjective in each degree, since $g$ is. Its kernel $N$ is the subcomplex of pairs $(a, f(c))$ with $a \in X_1^{n+1}$ and $c \in X_1^n$, since $\ker g = \operatorname{im} f$. As $f$ is a monomorphism, $(a, c) \mapsto (a, f(c))$ is an isomorphism from $\operatorname{Cone}(1_{X_1})$ to $N$: indeed $d(a, f(c)) = (-da, f(a + dc))$, which is the image of $d(a, c) = (-da, a + dc)$.

The cone of the identity is acyclic. Let $(a, c)$ be a cycle of $\operatorname{Cone}(1_{X_1})$ in degree $n$. Then $-da = 0$ and $a + dc = 0$, so $a = -dc$, and $d(c, 0) = (-dc, c) = (a, c)$. So each cycle is a boundary. The same computation runs with the generalized elements of Volume 25, Chapter 2, in any abelian category.

The long exact cohomology sequence of $0 \to N \to \operatorname{Cone}(f) \to X_3 \to 0$ from Chapter 2 now gives $0 = H^n(N) \to H^n(\operatorname{Cone}(f)) \to H^n(X_3) \to H^{n+1}(N) = 0$. So $\sigma$ is a quasi-isomorphism and $Q(\sigma)$ is an isomorphism. The map $\sigma$ is compatible with the cone triangle: $\sigma$ composed with the inclusion $X_2 \to \operatorname{Cone}(f)$, $b \mapsto (0, b)$, is $g$. So the triangle of the theorem is isomorphic, by $(1, 1, Q(\sigma))$, to the image of the cone triangle of $f$, which is distinguished. $\square$

**Theorem (Cohomology detects isomorphisms).** Let $H^n : D(A) \to A$ be the functor with $H^n \circ Q \cong H^n$. A morphism $u : X \to Y$ of $D(A)$ is an isomorphism if and only if $H^n(u)$ is an isomorphism for each $n$.

*Proof.* The functor $H^n$ exists by the universal property, since cohomology inverts quasi-isomorphisms. It is homological: a distinguished triangle of $D(A)$ is isomorphic to the image of a cone triangle, and $H^n$ of a cone triangle is exact by Chapter 3. A functor maps isomorphisms to isomorphisms, so the condition is necessary. For the converse, complete $u$ to a distinguished triangle $X \to Y \to Z \to X[1]$. The long exact sequence $H^n(X) \to H^n(Y) \to H^n(Z) \to H^{n+1}(X) \to H^{n+1}(Y)$, with the outer maps isomorphisms, gives $H^n(Z) = 0$ by the argument in the proof of the theorem on acyclic cones. Each object of $D(A)$ is isomorphic to $Q(M)$ for a complex $M$, so $H^n(M) = 0$ for all $n$. Then the map $0 \to M$ is a quasi-isomorphism, and $Z \cong Q(M) \cong Q(0) = 0$. A distinguished triangle $X \to Y \to 0 \to X[1]$ has its first map an isomorphism (Volume 25, Chapter 5). $\square$

**Theorem (K-injective targets).** Let $K$ be any complex and $I$ a K-injective complex. The map $\operatorname{Hom}_{K(A)}(K, I) \to \operatorname{Hom}_{D(A)}(Q(K), Q(I))$ is bijective.

*Proof.* The class $W$ of a triangulated subcategory has a calculus of left and right fractions (Volume 25, Chapters 4 and 5). So each morphism $Q(K) \to Q(I)$ is $Q(t) \circ Q(s)^{-1}$ for a quasi-isomorphism $s : K' \to K$ and a morphism $t : K' \to I$ in $K(A)$. Complete $s$ to a distinguished triangle $K' \xrightarrow{s} K \to M \to K'[1]$. Then $M$ is acyclic, and so is $M[-1]$. The functor $\operatorname{Hom}_{K(A)}(-, I)$ turns the triangle into the exact sequence
$$\operatorname{Hom}(M, I) \to \operatorname{Hom}(K, I) \xrightarrow{s^*} \operatorname{Hom}(K', I) \to \operatorname{Hom}(M[-1], I).$$
The outer groups are zero because $I$ is K-injective. So $s^*$ is bijective. Surjectivity: take $v$ with $v \circ s = t$. Then $Q(v) = Q(t) \circ Q(s)^{-1}$. Injectivity: if $Q(v) = 0$, the calculus of fractions gives a quasi-isomorphism $s : K' \to K$ with $v \circ s = 0$ in $K(A)$. Then $s^*(v) = 0$, and $v = 0$. $\square$

This is the reason why injective resolutions compute morphisms in the derived category. The next section uses it for Ext groups.

### Examples

**Example (A quasi-isomorphism without inverse).** Let $K$ be the complex $\mathbb{Z} \xrightarrow{2} \mathbb{Z}$ in degrees $-1$ and $0$. The map $q : K \to \mathbb{Z}/2[0]$, which is the projection in degree $0$, is a map of complexes, because the composite $\mathbb{Z} \xrightarrow{2} \mathbb{Z} \to \mathbb{Z}/2$ is zero. In cohomology, $H^{-1}(K) = \ker 2 = 0$ and $H^0(K) = \mathbb{Z}/2\mathbb{Z}$, so $q$ is a quasi-isomorphism. So $Q(K) \cong \iota_0(\mathbb{Z}/2)$ in $D(\mathbf{Ab})$. A map of complexes $\mathbb{Z}/2[0] \to K$ is a homomorphism $\mathbb{Z}/2 \to \mathbb{Z}$, so it is zero. Hence $Q(q)^{-1}$ is not of the form $Q(u)$ for a map $u$ of complexes.

**Example (An acyclic complex that is not contractible).** Let $E$ be the complex $\mathbb{Z} \xrightarrow{2} \mathbb{Z} \to \mathbb{Z}/2$ in degrees $0, 1, 2$. It is exact, so $E$ is acyclic and $Q(E) \cong 0$. In $K(\mathbf{Ab})$ the object $E$ is not zero. Suppose $1_E = dh + hd$. In degree $2$ the term $hd$ vanishes, because $E^3 = 0$. So $1_{\mathbb{Z}/2} = d^1 \circ h^2$ with $h^2 : \mathbb{Z}/2 \to \mathbb{Z}$. This $h^2$ is zero, so $1 = 0$ on $\mathbb{Z}/2$, a contradiction. So $D(A)$ has fewer objects up to isomorphism than $K(A)$.

**Example (The triangle of $\mathbb{Z} \xrightarrow{2} \mathbb{Z}$).** The short exact sequence $0 \to \mathbb{Z} \xrightarrow{2} \mathbb{Z} \to \mathbb{Z}/2 \to 0$, placed in degree $0$, gives a distinguished triangle
$$\iota_0(\mathbb{Z}) \xrightarrow{2} \iota_0(\mathbb{Z}) \to \iota_0(\mathbb{Z}/2) \xrightarrow{\delta} \iota_0(\mathbb{Z})[1].$$
The morphism $\delta$ is not zero. If it were, the triangle would split (Volume 25, Chapter 5), and $\iota_0(\mathbb{Z}) \cong \iota_0(\mathbb{Z}) \oplus \iota_0(\mathbb{Z}/2)$. Apply $H^0$: then $\mathbb{Z} \cong \mathbb{Z} \oplus \mathbb{Z}/2$, but $\mathbb{Z}$ has no element of order $2$. In the next section $\delta$ becomes the generator of $\operatorname{Ext}^1(\mathbb{Z}/2, \mathbb{Z}) \cong \mathbb{Z}/2$.

### The library around it

The localization `HomologicalComplexUpToQuasiIso C c` works for any complex shape `c`. The cylinder argument needs the class `ComplexShape.QFactorsThroughHomotopy c`, which holds when each index `j` has an `i` with `c.Rel i j`.

::: mathlib
`HomologicalComplexUpToQuasiIso.Q_map_eq_of_homotopy` · `Mathlib.Algebra.Homology.Localization`

For a homotopy `h : Homotopy f g`, the lemma gives `Q.map f = Q.map g`. The functor `HomologicalComplexUpToQuasiIso.Qh` goes from `HomotopyCategory C c`, and `quotientCompQhIso` is the isomorphism `quotient ⋙ Qh ≅ Q`.

<?decl HomologicalComplexUpToQuasiIso.Q_map_eq_of_homotopy?>
:::

::: mathlib
`HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic` · `Mathlib.Algebra.Homology.HomotopyCategory.Acyclic`

The subcategory `HomotopyCategory.subcategoryAcyclic C` is defined as the homological kernel of `HomotopyCategory.homologyFunctor C (up ℤ) 0`, and `mem_subcategoryAcyclic_iff` unfolds it to the vanishing of all cohomology. The lemma states `HomotopyCategory.quasiIso C (up ℤ) = (subcategoryAcyclic C).trW`.

<?decl HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic?>
:::

The triangulated structure on `DerivedCategory C` is the one of `Triangulated.Localization.pretriangulated` applied to `Qh`, and the lemma `DerivedCategory.mem_distTriang_iff` characterizes the distinguished triangles as the triangles isomorphic to `Q.mapTriangle.obj (mappingCone.triangle f)`.

::: mathlib
`DerivedCategory.triangleOfSES_distinguished` · `Mathlib.Algebra.Homology.DerivedCategory.ShortExact`

For `hS : S.ShortExact` with `S : ShortComplex (CochainComplex C ℤ)`, the triangle `triangleOfSES hS` has third morphism `triangleOfSESδ hS : Q.obj S.X₃ ⟶ (Q.obj S.X₁)⟦1⟧`. It is built from the quasi-isomorphism `mappingCone.descShortComplex S` of `Mathlib.Algebra.Homology.HomotopyCategory.ShortExact`, which is the map $\sigma$ of the theorem. For a short exact sequence of objects of `C`, `ShortComplex.ShortExact.singleTriangle_distinguished` gives the same triangle for the single complexes in degree `0`.

<?decl DerivedCategory.triangleOfSES_distinguished?>
:::

::: mathlib
`DerivedCategory.isIso_iff` · `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`

`DerivedCategory.homologyFunctor C n : DerivedCategory C ⥤ C` comes with `homologyFunctorFactors : Q ⋙ homologyFunctor C n ≅ HomologicalComplex.homologyFunctor C _ n`. It is homological, and `DerivedCategory.HomologySequence.δ T n₀ n₁ h` is the connecting map of a distinguished triangle `T`, with exactness lemmas `exact₁`, `exact₂` and `exact₃`. The lemma `isIso_iff` states `IsIso f ↔ ∀ n, IsIso ((homologyFunctor C n).map f)`.

<?decl DerivedCategory.isIso_iff?>
:::

::: mathlib
`DerivedCategory.Plus.Qh_map_bijective_of_isKInjective` · `Mathlib.Algebra.Homology.DerivedCategory.Plus`

The bounded below derived category `DerivedCategory.Plus C` is the full subcategory of `DerivedCategory C` of the objects with cohomology bounded below; its definition is in `Mathlib.Algebra.Homology.DerivedCategory.TStructure`. The file `Plus` gives `DerivedCategory.Plus.Qh` from `HomotopyCategory.Plus C`, proves `HomotopyCategory.Plus.quasiIso_eq_subcategoryAcyclic_trW`, and proves that `Qh.map` is bijective on morphisms to a complex with `CochainComplex.IsKInjective`.

<?decl DerivedCategory.Plus.Qh_map_bijective_of_isKInjective?>
:::

Common errors of a learner:

- A morphism of `DerivedCategory C` is not a map of complexes. Only morphisms of the form `Q.map f` come from maps of complexes. To show that two morphisms of `DerivedCategory C` are equal, a proof often uses `Localization` lemmas or the calculus of fractions, not an extensionality lemma in each degree.
- `HomologicalComplex.quasiIso` is a class of maps of complexes, and `HomotopyCategory.quasiIso` is a class of morphisms of the homotopy category. The lemma `HomotopyCategory.quotient_map_mem_quasiIso_iff` translates between them.

### Exercises

1. (A) Let $X \in A$ and $n \in \mathbb{Z}$. Compute $H^m(\iota_0(X)[n])$ for all $m$. *Hint:* the shift moves the nonzero term to degree $-n$.
2. (B) Let $f : \mathbb{Z} \to \mathbb{Z}$ be multiplication by $n \neq 0$. Show that $\operatorname{Cone}(\iota_0(f))$ is isomorphic in $D(\mathbf{Ab})$ to $\iota_0(\mathbb{Z}/n)$, and give the quasi-isomorphism. *Hint:* follow the first example.
3. (B) Show that a map of complexes $f$ is a homotopy equivalence when $\operatorname{Cone}(f)$ is contractible. Then use the second example to show that the converse of "homotopy equivalences are quasi-isomorphisms" fails. *Hint:* use the triangle of $f$ in $K(A)$, and the fact that a morphism whose cone is zero is an isomorphism.
4. (B) Let $u : X \to Y$ be a morphism of $D(A)$ with $H^n(u) = 0$ for all $n$. Show by an example in $D(\mathbf{Ab})$ that $u$ can be nonzero. *Hint:* the morphism $\delta$ of the third example.
5. (C) Let $A$ be semisimple, for example $\mathbf{Vect}_k$. Show that each complex $K$ is isomorphic in $D(A)$ to the complex $\bigoplus_n H^n(K)[-n]$ with zero differential. *Hint:* write $K^n = B^n \oplus H^n \oplus C^n$ with $d$ an isomorphism $C^n \to B^{n+1}$, and show that the inclusion of the complex $H$ is a quasi-isomorphism.
6. (C) Prove that the functor $\iota_0 : A \to D(A)$ is faithful. *Hint:* compose with $H^0$.

### Notes and history

The derived category is due to Grothendieck, who needed it for duality in algebraic geometry, and to his student Verdier, who wrote its foundations in his thesis, published in 1996 as *Des catégories dérivées des catégories abéliennes*. The construction of $D(A)$ as a Verdier quotient of $K(A)$ is the one of that thesis.

The Mathlib Authors of all seven modules of this section are listed as Joël Riou.

### Reference

<?reference?>
