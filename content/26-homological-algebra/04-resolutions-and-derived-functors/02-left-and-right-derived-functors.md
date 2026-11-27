---
title: Left and right derived functors
kind: theory
modules:
  - Mathlib.CategoryTheory.Abelian.LeftDerived
  - Mathlib.CategoryTheory.Abelian.RightDerived
explains:
  E3: [CategoryTheory.Functor.leftDerived, CategoryTheory.Functor.rightDerived, CategoryTheory.ProjectiveResolution.isoLeftDerivedObj, CategoryTheory.InjectiveResolution.isoRightDerivedObj, CategoryTheory.Functor.leftDerivedZeroIsoSelf, CategoryTheory.Functor.rightDerivedZeroIsoSelf, CategoryTheory.Functor.isZero_leftDerived_obj_projective_succ, CategoryTheory.Functor.isZero_rightDerived_obj_injective_succ]
  E2: [CategoryTheory.Functor.leftDerivedToHomotopyCategory, CategoryTheory.ProjectiveResolution.isoLeftDerivedToHomotopyCategoryObj, CategoryTheory.Functor.leftDerived_map_eq, CategoryTheory.NatTrans.leftDerivedToHomotopyCategory, CategoryTheory.NatTrans.leftDerived, CategoryTheory.NatTrans.leftDerived_id, CategoryTheory.NatTrans.leftDerived_comp, CategoryTheory.ProjectiveResolution.leftDerived_app_eq, CategoryTheory.ProjectiveResolution.fromLeftDerivedZero', CategoryTheory.Functor.fromLeftDerivedZero, CategoryTheory.ProjectiveResolution.fromLeftDerivedZero_eq, CategoryTheory.Functor.rightDerivedToHomotopyCategory, CategoryTheory.InjectiveResolution.isoRightDerivedToHomotopyCategoryObj, CategoryTheory.Functor.rightDerived_map_eq, CategoryTheory.NatTrans.rightDerivedToHomotopyCategory, CategoryTheory.NatTrans.rightDerived, CategoryTheory.NatTrans.rightDerived_id, CategoryTheory.NatTrans.rightDerived_comp, CategoryTheory.InjectiveResolution.rightDerived_app_eq, CategoryTheory.InjectiveResolution.toRightDerivedZero', CategoryTheory.Functor.toRightDerivedZero, CategoryTheory.InjectiveResolution.toRightDerivedZero_eq]
  E1: auto
families: []
requires: [V24.C08, V25.C02, V26.C01, V26.C02, V26.C03]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Left and right derived functors

### Overview

An additive functor $F$ between abelian categories need not preserve exactness. The tensor product $- \otimes \mathbb{Z}/2$ turns the injection $\mathbb{Z} \xrightarrow{2} \mathbb{Z}$ into the zero map $\mathbb{Z}/2 \to \mathbb{Z}/2$. The left derived functors $L_n F$ measure this failure. They are defined by applying $F$ to a projective resolution and taking homology. When $F$ is right exact, $L_0 F$ is $F$ itself, and a short exact sequence gives a long exact sequence that continues the right exact sequence of $F$ to the left.

This section defines $L_n F$ and $R^n F$, proves that they do not depend on the choice of the resolutions, that they vanish on projective or injective objects in positive degrees, and that $L_0 F \cong F$ for right exact $F$ and $R^0 F \cong F$ for left exact $F$. It proves the long exact sequence on paper, with the horseshoe lemma. Mathlib has no long exact sequence for these functors in this edition, and the section says what it has instead.

The categories $C$ and $D$ are abelian, and $F : C \to D$ is additive. Projective and injective resolutions, their lifts and the homotopies between lifts are from Section 1. Homotopies and the homotopy category are from Chapter 3, and the homology of complexes and the long exact homology sequence are from Chapter 2. Right exact means that $F$ preserves finite colimits, and left exact that it preserves finite limits, as in Volume 25, Chapter 2.

### Definitions

**Definition (Left derived functors).** Assume that $C$ has enough projectives, and choose a projective resolution $P(X) \to X$ for each object $X$. For $n \geq 0$, the *$n$-th left derived functor* of $F$ is
$$L_n F(X) = H_n\big(F(P(X))\big),$$
the $n$-th homology of the chain complex $\cdots \to F(P_1) \to F(P_0) \to 0$. The augmentation $Z$ is not part of the complex. For $f : X \to Y$, let $f_\bullet : P(X) \to P(Y)$ be a lift, and set $L_n F(f) = H_n(F(f_\bullet))$.

**Definition (Right derived functors).** Assume that $C$ has enough injectives, and choose an injective resolution $X \to I(X)$ for each object. The *$n$-th right derived functor* of $F$ is
$$R^n F(X) = H^n\big(F(I(X))\big),$$
the $n$-th cohomology of $0 \to F(I^0) \to F(I^1) \to \cdots$, with $R^n F(f) = H^n(F(f^\bullet))$ for an extension $f^\bullet$ of $f$.

In the form of the homotopy category, $L_n F$ is the composite
$$C \xrightarrow{\ P\ } K(C) \xrightarrow{\ K(F)\ } K(D) \xrightarrow{\ H_n\ } D$$
of the resolution functor of Section 1, the functor that $F$ induces on homotopy categories, and homology. This is how Mathlib defines it.

::: mathlib
`CategoryTheory.Functor.leftDerived` · `Mathlib.CategoryTheory.Abelian.LeftDerived`

For `F : C ⥤ D` with `[F.Additive]`, in abelian categories with `[HasProjectiveResolutions C]`, `F.leftDerived n : C ⥤ D` is `F.leftDerivedToHomotopyCategory ⋙ HomotopyCategory.homologyFunctor D _ n`. The first factor is `projectiveResolutions C ⋙ F.mapHomotopyCategory _`. Because the resolution functor lands in the homotopy category, functoriality needs no separate proof: it is functoriality of a composite. The docstring of the file says that the definition will change when derived functors on the derived category enter Mathlib.

<?decl CategoryTheory.Functor.leftDerived?>
:::

### Theorems and proofs

**Theorem (Independence of the resolution).** Let $P$ and $P'$ be projective resolutions of $X$. Then $H_n(F(P)) \cong H_n(F(P'))$, by an isomorphism that is natural in the following sense: for $f : X \to Y$, resolutions $P$ of $X$ and $Q$ of $Y$, and any lift $g : P \to Q$ of $f$, the map $H_n(F(g))$ corresponds to $L_n F(f)$ under these isomorphisms. In particular $L_n F(f)$ does not depend on the lift.

*Proof.* By Section 1 the lifts $\alpha : P \to P'$ and $\beta : P' \to P$ of $1_X$ satisfy $\beta \alpha \simeq 1$ and $\alpha \beta \simeq 1$. An additive functor sends a homotopy $h$ to a homotopy $F(h)$: apply $F$ to $f - g = dh + hd$ and use $F(a + b) = F(a) + F(b)$ and $F(ab) = F(a) F(b)$. So $F(\beta) F(\alpha) \simeq 1$ and $F(\alpha) F(\beta) \simeq 1$. Homotopic maps induce the same map on homology (Chapter 3, Section 1), so $H_n(F(\alpha))$ and $H_n(F(\beta))$ are inverse isomorphisms. For the naturality, two lifts $g, g'$ of $f$ are homotopic by Section 1, so $F(g) \simeq F(g')$ and $H_n(F(g)) = H_n(F(g'))$. If $g$ lifts $f$ from $P$ to $Q$, $\alpha$ lifts $1_X$ from $P(X)$ to $P$ and $\gamma$ lifts $1_Y$ from $Q$ to $P(Y)$, then $\gamma g \alpha$ lifts $f$ from $P(X)$ to $P(Y)$. So $H_n(F(\gamma)) H_n(F(g)) H_n(F(\alpha)) = L_n F(f)$. $\square$

**Proposition (Derived functors vanish on projectives).** If $X$ is projective, then $L_n F(X) = 0$ for $n \geq 1$. Dually, if $X$ is injective, then $R^n F(X) = 0$ for $n \geq 1$.

*Proof.* The complex with $X$ in degree $0$ and $\pi = 1_X$ is a projective resolution of $X$. By the theorem, $L_n F(X)$ is the $n$-th homology of the complex $F(X)$ in degree $0$, which is zero for $n \geq 1$. The injective case is dual. $\square$

**Theorem ($L_0$ of a right exact functor).** There is a natural transformation $L_0 F \to F$. It is an isomorphism if $F$ is right exact. Dually, there is a natural transformation $F \to R^0 F$, an isomorphism if $F$ is left exact.

*Proof.* Let $P \to X$ be a projective resolution. By definition, $L_0 F(X) = H_0(F(P)) = \operatorname{coker}\big(F(d_1) : F(P_1) \to F(P_0)\big)$, since $F(P)$ has nothing in degree $-1$. The composite $F(\pi) F(d_1) = F(\pi d_1) = 0$, so $F(\pi)$ factors through the cokernel. This gives $L_0 F(X) \to F(X)$. It is natural because a lift $f_\bullet$ satisfies $\pi f_0 = f \pi$, so $F(\pi) F(f_0) = F(f) F(\pi)$.

Now let $F$ be right exact. The sequence $P_1 \xrightarrow{d_1} P_0 \xrightarrow{\pi} X \to 0$ is exact, so $\pi$ is a cokernel of $d_1$. A right exact functor preserves cokernels, so $F(\pi)$ is a cokernel of $F(d_1)$. Hence the map $\operatorname{coker} F(d_1) \to F(X)$ is an isomorphism. The dual argument uses $0 \to X \to I^0 \to I^1$, which is a kernel sequence, and the fact that a left exact functor preserves kernels. $\square$

Without right exactness the map $L_0 F \to F$ need not be an isomorphism. The examples give a case where $L_0 F = 0$ and $F \ne 0$.

**Proposition (Naturality in the functor).** A natural transformation $\alpha : F \to G$ of additive functors gives natural transformations $L_n \alpha : L_n F \to L_n G$, with $L_n(1_F) = 1$ and $L_n(\beta \alpha) = L_n(\beta) L_n(\alpha)$.

*Proof.* For each $X$ the maps $\alpha_{P_k} : F(P_k) \to G(P_k)$ form a map of complexes $F(P) \to G(P)$, because $\alpha$ is natural with respect to the differentials. Apply $H_n$. The naturality in $X$ follows from the naturality of $\alpha$ with respect to the lifts $f_k$. The identities hold degreewise. $\square$

**Lemma (Horseshoe lemma).** Let $0 \to A \xrightarrow{i} B \xrightarrow{p} Q \to 0$ be a short exact sequence in $C$, and let $P^A \to A$ and $P^Q \to Q$ be projective resolutions. Then $B$ has a projective resolution $P^B$ with $P^B_n = P^A_n \oplus P^Q_n$, such that the inclusions and projections of the sums form a short exact sequence of complexes $0 \to P^A \to P^B \to P^Q \to 0$ over $0 \to A \to B \to Q \to 0$.

*Proof.* In degree $0$, the map $\pi^Q : P^Q_0 \to Q$ lifts through the epimorphism $p$ to a map $\lambda : P^Q_0 \to B$, because $P^Q_0$ is projective. Define $\pi^B : P^A_0 \oplus P^Q_0 \to B$ by $\pi^B(a, q) = i \pi^A(a) + \lambda(q)$. The diagram with rows $0 \to P^A_0 \to P^B_0 \to P^Q_0 \to 0$ and $0 \to A \to B \to Q \to 0$ commutes. The outer vertical maps are epimorphisms, so by the snake lemma (Chapter 1) $\pi^B$ is an epimorphism, and the kernels form a short exact sequence $0 \to K^A \to K^B \to K^Q \to 0$. The resolutions $P^A$ and $P^Q$ continue as resolutions of $K^A$ and $K^Q$, shifted by one degree. Repeat the construction with this new short exact sequence. In each degree the differential of $P^B$ has the matrix $\begin{pmatrix} d^A & \ast \\ 0 & d^Q \end{pmatrix}$, so the sums form a complex and the inclusion and projection are maps of complexes. $\square$

**Theorem (The long exact sequence of derived functors).** Let $0 \to A \to B \to Q \to 0$ be a short exact sequence in $C$. There are connecting maps $\delta_n : L_n F(Q) \to L_{n-1} F(A)$ and a long exact sequence
$$\cdots \to L_n F(A) \to L_n F(B) \to L_n F(Q) \xrightarrow{\delta_n} L_{n-1} F(A) \to \cdots \to L_0 F(B) \to L_0 F(Q) \to 0.$$
Dually, for right derived functors there is a long exact sequence $0 \to R^0 F(A) \to R^0 F(B) \to R^0 F(Q) \to R^1 F(A) \to \cdots$.

*Proof.* Take resolutions $P^A$ and $P^Q$ and the horseshoe resolution $P^B$. In each degree the sequence $0 \to P^A_n \to P^A_n \oplus P^Q_n \to P^Q_n \to 0$ is split exact. An additive functor preserves biproducts, so $0 \to F(P^A_n) \to F(P^B_n) \to F(P^Q_n) \to 0$ is split exact for each $n$. So $0 \to F(P^A) \to F(P^B) \to F(P^Q) \to 0$ is a short exact sequence of complexes in $D$. The long exact homology sequence of Chapter 2 gives the sequence of the theorem, after the identification of $H_n(F(P^B))$ with $L_n F(B)$ by the independence theorem. It ends with $L_0 F(Q) \to 0$ because $F(P^Q)$ has nothing in degree $-1$. $\square$

For a right exact $F$ the end of the sequence is $L_1 F(Q) \to F(A) \to F(B) \to F(Q) \to 0$, the right exact sequence of $F$. So $L_1 F(Q)$ measures the failure of $F(A) \to F(B)$ to be injective.

### Examples

**Example (Reduction mod $2$).** Let $F(A) = A / 2A = A \otimes \mathbb{Z}/2$ on abelian groups. It is right exact. Resolve $\mathbb{Z}/n$ by $\mathbb{Z} \xrightarrow{n} \mathbb{Z}$. Applying $F$ gives $\mathbb{Z}/2 \xrightarrow{n} \mathbb{Z}/2$. If $n$ is even, the map is zero, so $L_1 F(\mathbb{Z}/n) = \mathbb{Z}/2$ and $L_0 F(\mathbb{Z}/n) = \mathbb{Z}/2$. If $n$ is odd, the map is an isomorphism, so $L_1 F(\mathbb{Z}/n) = 0$ and $L_0 F(\mathbb{Z}/n) = 0$. In both cases $L_0 F(\mathbb{Z}/n) = (\mathbb{Z}/n)/2(\mathbb{Z}/n)$, as the theorem says. The groups $L_k F$ vanish for $k \geq 2$, because the resolution has length $1$.

**Example (The long exact sequence for $0 \to \mathbb{Z} \to \mathbb{Z} \to \mathbb{Z}/2 \to 0$).** Keep $F = - \otimes \mathbb{Z}/2$. Here $\mathbb{Z}$ is projective, so $L_1 F(\mathbb{Z}) = 0$, and $L_1 F(\mathbb{Z}/2) = \mathbb{Z}/2$ by the first example. The long exact sequence reads
$$0 \to L_1 F(\mathbb{Z}/2) \xrightarrow{\delta} F(\mathbb{Z}) \xrightarrow{2} F(\mathbb{Z}) \to F(\mathbb{Z}/2) \to 0,$$
that is, $0 \to \mathbb{Z}/2 \to \mathbb{Z}/2 \xrightarrow{0} \mathbb{Z}/2 \to \mathbb{Z}/2 \to 0$. It is exact: $\delta$ is an isomorphism onto the kernel of the zero map, and the last map is an isomorphism onto its target. The group $L_1 F(\mathbb{Z}/2)$ is exactly the kernel that $F$ creates.

**Example (A right derived functor).** Let $F(A) = A[2] = \{a \in A : 2 a = 0\}$, which is $\operatorname{Hom}(\mathbb{Z}/2, A)$. It is left exact. Resolve $\mathbb{Z}$ by the injective resolution $\mathbb{Q} \to \mathbb{Q}/\mathbb{Z}$ of Section 1. Then $F(\mathbb{Q}) = 0$ and $F(\mathbb{Q}/\mathbb{Z}) = \{0, \tfrac12\} \cong \mathbb{Z}/2$. The complex $F(I)$ is $0 \to \mathbb{Z}/2$ in degrees $0$ and $1$. So $R^0 F(\mathbb{Z}) = 0 = \mathbb{Z}[2]$, and $R^1 F(\mathbb{Z}) = \mathbb{Z}/2$. Section 3 identifies $R^1 F(\mathbb{Z})$ with $\operatorname{Ext}^1(\mathbb{Z}/2, \mathbb{Z})$ and computes it a second way.

**Counterexample (Without right exactness).** Let $F = \operatorname{Hom}(\mathbb{Z}/2, -)$ again, but take its left derived functors. A free abelian group has no element of order $2$, so $F(P) = 0$ for each free $P$. Hence $L_n F = 0$ for every $n$, while $F(\mathbb{Z}/2) = \mathbb{Z}/2$. The map $L_0 F \to F$ is not an isomorphism. Left derived functors of a functor that is not right exact lose information.

### The library around it

::: mathlib
`CategoryTheory.ProjectiveResolution.isoLeftDerivedObj` · `Mathlib.CategoryTheory.Abelian.LeftDerived`

For `P : ProjectiveResolution X`, the isomorphism `P.isoLeftDerivedObj F n` identifies `(F.leftDerived n).obj X` with the homology in degree `n` of `(F.mapHomologicalComplex _).obj P.complex`. This is the independence theorem. `Functor.leftDerived_map_eq` computes `(F.leftDerived n).map f` from any lift `g` with `g ≫ Q.π = P.π ≫ (single₀ C).map f`. `Functor.isZero_leftDerived_obj_projective_succ` is the vanishing on projectives, proved with `ProjectiveResolution.self`.

<?decl CategoryTheory.ProjectiveResolution.isoLeftDerivedObj?>
:::

`Functor.fromLeftDerivedZero F : F.leftDerived 0 ⟶ F` is the natural transformation of the theorem on $L_0$, computed on a resolution by `ProjectiveResolution.fromLeftDerivedZero'` and `fromLeftDerivedZero_eq`. Under `[PreservesFiniteColimits F]` it is an isomorphism, packaged as `Functor.leftDerivedZeroIsoSelf F : F.leftDerived 0 ≅ F`. `NatTrans.leftDerived α n` is the transformation $L_n \alpha$, with `leftDerived_id`, `leftDerived_comp` and `ProjectiveResolution.leftDerived_app_eq`.

::: mathlib
`CategoryTheory.Functor.rightDerived` · `Mathlib.CategoryTheory.Abelian.RightDerived`

Under `[HasInjectiveResolutions C]`, `F.rightDerived n` is `F.rightDerivedToHomotopyCategory ⋙ HomotopyCategory.homologyFunctor D _ n`, built from `injectiveResolutions C`. The dual names are `InjectiveResolution.isoRightDerivedObj`, `Functor.rightDerived_map_eq`, `Functor.isZero_rightDerived_obj_injective_succ`, `NatTrans.rightDerived`, `Functor.toRightDerivedZero : F ⟶ F.rightDerived 0` and, under `[PreservesFiniteLimits F]`, `Functor.rightDerivedZeroIsoSelf F : F.rightDerived 0 ≅ F`.

<?decl CategoryTheory.Functor.rightDerived?>
:::

The index of this edition has no declaration for the long exact sequence of `Functor.leftDerived` or `Functor.rightDerived` attached to a short exact sequence, and no declaration for the horseshoe lemma. The long exact sequences that Mathlib has are those of homology for a short exact sequence of complexes (Chapter 2) and those of the Ext groups in the derived category (Chapter 5), for example `CategoryTheory.Abelian.Ext.covariant_sequence_exact₂`.

::: mathlib
`CategoryTheory.Abelian.Ext.covariant_sequence_exact₂` · `Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences`

The exactness of $\operatorname{Ext}^n(X, A) \to \operatorname{Ext}^n(X, B) \to \operatorname{Ext}^n(X, Q)$ for a short exact sequence $0 \to A \to B \to Q \to 0$. Chapter 5 treats it.

<?decl CategoryTheory.Abelian.Ext.covariant_sequence_exact₂?>
:::

Common errors of a learner:

- The complex $F(P)$ does not contain $F(X)$. Including the augmentation gives the wrong $H_0$.
- Left derived functors are useful for right exact functors and right derived functors for left exact ones. The other combination, as the counterexample shows, gives little.
- `F.leftDerived n` needs `[F.Additive]` and `[HasProjectiveResolutions C]`. Without the instance for resolutions the term does not elaborate. With enough projectives the instance is found automatically.
- The value of `F.leftDerived n` on an object is defined by a chosen resolution. To compute with another resolution, use `isoLeftDerivedObj`; do not unfold the definition.

### Exercises

1. (A) Compute $L_n F(\mathbb{Z}/n)$ for $F = - \otimes \mathbb{Z}/3$ and $n = 6$.
2. (A) Show that an exact additive functor has $L_n F = 0$ for all $n \geq 1$.
3. (B) Let $R = \mathbb{Z}/4$ and $F = - \otimes_R \mathbb{Z}/2$ on $R$-modules. Use the periodic resolution of Section 1 to show that $L_n F(\mathbb{Z}/2) = \mathbb{Z}/2$ for every $n \geq 0$.
4. (B) Prove dimension shifting: if $0 \to K \to P \to X \to 0$ is exact with $P$ projective, then $L_{n+1} F(X) \cong L_n F(K)$ for $n \geq 1$, and $L_1 F(X) = \ker(F(K) \to F(P))$ when $F$ is right exact.
5. (B) Let $F(A) = A[n]$ on abelian groups. Compute $R^1 F(\mathbb{Z})$ and $R^1 F(\mathbb{Z}/m)$ with the injective resolutions of Section 1. *Hint:* the answer for $\mathbb{Z}/m$ involves $\gcd(m, n)$.
6. (C) Show that an additive functor $F$ is right exact if and only if $L_0 F \to F$ is an isomorphism, when $C$ has enough projectives. *Hint:* for the converse, use the long exact sequence and the fact that $L_0 F$ is right exact.
7. (C) Prove the universal property of $(L_n F)_n$: for right exact $F$, the family $L_n F$ with its connecting maps is a universal $\delta$-functor. *Hint:* use dimension shifting and the vanishing of $L_n F$ on projectives.

### Notes and history

Cartan and Eilenberg, *Homological Algebra* (1956), defined the derived functors of an additive functor between module categories by projective and injective resolutions, with the long exact sequences and the horseshoe lemma. Grothendieck, in the Tohoku paper of 1957, placed them in abelian categories and characterized them as universal $\delta$-functors. The later definition by derived categories, due to Verdier and Grothendieck, gives the same groups and is the subject of Chapter 5.

The Mathlib Authors of `Abelian.LeftDerived` are Kim Morrison, Riccardo Brasca, Adam Topaz, Jujian Zhang and Joël Riou. The file `Abelian.RightDerived` is by Jujian Zhang, Kim Morrison and Joël Riou.

### Reference

<?reference?>
