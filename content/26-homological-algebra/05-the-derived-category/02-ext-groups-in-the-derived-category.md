---
title: Ext groups in the derived category
kind: theory
modules:
  - Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
  - Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
  - Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
  - Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
  - Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
  - Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
  - Mathlib.Algebra.Category.ModuleCat.Ext.Baer
  - Mathlib.Algebra.Category.ModuleCat.Ext.DimensionShifting
  - Mathlib.Algebra.Homology.DerivedCategory.SmallShiftedHom
  - Mathlib.Algebra.Homology.LocalCohomology
  - Mathlib.Algebra.Homology.LinearYonedaObj
explains:
  E3: [CategoryTheory.HasExt, CategoryTheory.Abelian.Ext, CategoryTheory.Abelian.Ext.comp, CategoryTheory.Abelian.Ext.mk₀, CategoryTheory.Abelian.Ext.mk₀_bijective, CategoryTheory.ShortComplex.ShortExact.extClass, CategoryTheory.ShortComplex.ShortExact.extClass_naturality, CategoryTheory.Abelian.Ext.covariantSequence_exact, CategoryTheory.Abelian.Ext.contravariantSequence_exact, CategoryTheory.Abelian.Ext.δ, CategoryTheory.Abelian.Ext.subsingleton_of_projective, CategoryTheory.Abelian.Ext.subsingleton_of_injective, ModuleCat.ext_quotient_one_subsingleton_iff, ModuleCat.hasInjectiveDimensionLT_of_quotients]
  E2: [CategoryTheory.hasExt_of_hasDerivedCategory, CategoryTheory.HasExt.standard, CategoryTheory.hasExt_of_enoughProjectives, CategoryTheory.hasExt_of_enoughInjectives, CategoryTheory.Abelian.Ext.hom, CategoryTheory.Abelian.Ext.homEquiv, CategoryTheory.Abelian.Ext.comp_assoc, CategoryTheory.Abelian.Ext.comp_hom, CategoryTheory.Abelian.Ext.mk₀_comp_mk₀, CategoryTheory.Abelian.Ext.addEquiv₀, CategoryTheory.Abelian.Ext.bilinearComp, CategoryTheory.Abelian.Ext.postcomp, CategoryTheory.Abelian.Ext.precomp, CategoryTheory.Abelian.Ext.chgUniv, CategoryTheory.Abelian.extFunctor, CategoryTheory.ShortComplex.ShortExact.extClass_hom, CategoryTheory.ShortComplex.ShortExact.comp_extClass, CategoryTheory.ShortComplex.ShortExact.extClass_comp, CategoryTheory.Abelian.Ext.covariantSequence, CategoryTheory.Abelian.Ext.contravariantSequence, CategoryTheory.Abelian.Ext.covariant_sequence_exact₃, CategoryTheory.Abelian.Ext.contravariant_sequence_exact₃, CategoryTheory.Abelian.Ext.δ_exact₃, CategoryTheory.Abelian.Ext.one_subsingleton_iff_of_projective, CategoryTheory.Abelian.Ext.instModule, CategoryTheory.Abelian.Ext.smul_eq_comp_mk₀, CategoryTheory.Abelian.Ext.linearEquiv₀, CategoryTheory.Abelian.linearExtFunctor, ModuleCat.injective_iff_subsingleton_ext_quotient_one, ModuleCat.hasInjectiveDimensionLT_iff_quotients, ModuleCat.projectiveShortComplex, ModuleCat.shortExact_projectiveShortComplex, precomp_extClass_surjective_of_projective_X₂, postcomp_extClass_surjective_of_projective_X₂]
  E1: auto
families: []
requires: [V07, V25.C02, V25.C05, V26.C02, V26.C04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Ext groups in the derived category

### Overview

Chapter 4 defines $\operatorname{Ext}^n(X, Y)$ as the cohomology of $\operatorname{Hom}(P, Y)$ for a projective resolution $P$ of $X$. That definition needs enough projectives, and the Yoneda product and the long exact sequences need separate constructions. In the derived category all of this is one idea: $\operatorname{Ext}^n(X, Y)$ is the group of morphisms $X \to Y[n]$ in $D(A)$. Composition of morphisms gives the product. A short exact sequence gives a class in $\operatorname{Ext}^1$, and the long exact sequences come from the triangulated structure.

This section defines the Ext groups in this way and proves their main properties: $\operatorname{Ext}^0 = \operatorname{Hom}$, the long exact sequences, the computation by projective resolutions, and the vanishing for projective and injective objects. For modules over a ring it proves Baer's criterion in the form $\operatorname{Ext}^1(R/I, M) = 0$, and a bound on the injective dimension by dimension shifting.

The notation of the previous section stays in force. For $X \in A$, write $X$ also for the object $\iota_0(X)$ of $D(A)$. Mathlib writes `α.comp β h` for the composite "first $\alpha$, then $\beta$", which the text writes $\beta \cdot \alpha$.

### Definitions

**Definition (Ext groups).** Let $A$ be an abelian category with a derived category. For $X, Y \in A$ and $n \in \mathbb{N}$,
$$\operatorname{Ext}^n(X, Y) = \operatorname{Hom}_{D(A)}(X, Y[n]).$$
It is an abelian group, because $D(A)$ is additive.

**Definition (Yoneda product).** For $\alpha \in \operatorname{Ext}^a(X, Y)$ and $\beta \in \operatorname{Ext}^b(Y, Z)$, the product $\beta \cdot \alpha \in \operatorname{Ext}^{a+b}(X, Z)$ is the composite
$$X \xrightarrow{\alpha} Y[a] \xrightarrow{\beta[a]} Z[b][a] \cong Z[a+b].$$

The product is associative, because composition is associative and the isomorphisms $Z[b][a] \cong Z[a+b]$ are coherent (Volume 25, Chapter 5). It is bilinear, because $D(A)$ is additive and the shift is additive.

**Definition (Class of a short exact sequence).** Let $S : 0 \to X_1 \xrightarrow{f} X_2 \xrightarrow{g} X_3 \to 0$ be short exact in $A$. Its class $e_S \in \operatorname{Ext}^1(X_3, X_1)$ is the third morphism $\delta : X_3 \to X_1[1]$ of the distinguished triangle $X_1 \to X_2 \to X_3 \xrightarrow{\delta} X_1[1]$ of the previous section.

**Definition (Injective dimension).** An object $M$ has *injective dimension* $< n$ if $\operatorname{Ext}^i(Y, M) = 0$ for all $Y$ and all $i \geq n$.

So $M$ has injective dimension $< 1$ exactly when $\operatorname{Ext}^i(-, M)$ vanishes for $i \geq 1$, and the theorem on injectives below shows that this holds for injective $M$.

::: mathlib
`CategoryTheory.Abelian.Ext` · `Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic`

`Ext X Y n : Type w` for `n : ℕ` is defined as a `SmallShiftedHom` of the localization at the quasi-isomorphisms, between the single complexes in degree `0`, shifted by `(n : ℤ)`. It needs `[HasExt.{w} C]`, a smallness condition, not a full derived category. When a derived category exists, `Ext.homEquiv` identifies `Ext X Y n` with `ShiftedHom ((singleFunctor C 0).obj X) ((singleFunctor C 0).obj Y) (n : ℤ)`, and `α.hom` is the image of `α`. The group structure is transported from the standard derived category. The source names étale sheaves as a case where the derived category lives in a larger universe than the Ext groups.

<?decl CategoryTheory.Abelian.Ext?>
:::

::: mathlib
`CategoryTheory.HasExt` · `Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic`

`HasExt.{w} C` asserts that the morphisms between single complexes and their shifts in the localization are `w`-small. The instance `hasExt_of_hasDerivedCategory` derives it from `HasDerivedCategory.{w} C`. The theorems `hasExt_of_enoughProjectives` and `hasExt_of_enoughInjectives` derive it, with `LocallySmall.{w} C`, from enough projectives or injectives; they are not instances. For modules, `ModuleCat.{v} R` has `HasExt.{v}` when `R` is `v`-small.

<?decl CategoryTheory.HasExt?>
:::

### Theorems and proofs

**Theorem (Degree zero).** The map $\operatorname{Hom}_A(X, Y) \to \operatorname{Ext}^0(X, Y)$, $u \mapsto \iota_0(u)$, is bijective, and it sends composition to the Yoneda product.

*Proof.* Compatibility with composition holds because $\iota_0$ is a functor. Injectivity: if $\iota_0(u) = 0$, then $u = H^0(\iota_0(u)) = 0$. Surjectivity: by the calculus of fractions of the previous section, a morphism $\varphi : X \to Y$ in $D(A)$ is $Q(t) \circ Q(s)^{-1}$ for a complex $K$, a quasi-isomorphism $s : K \to X[0]$ and a map $t : K \to Y[0]$. Let $K'$ be the truncation with $K'^n = K^n$ for $n < 0$, $K'^0 = \ker(d^0)$ and $K'^n = 0$ for $n > 0$. The inclusion $j : K' \to K$ is a quasi-isomorphism, because $H^n(K) \cong H^n(X[0]) = 0$ for $n > 0$. A map of complexes from $K'$ to a complex concentrated in degree $0$ is a map $K'^0 \to X$ that vanishes on the image of $d^{-1}$, so $s \circ j$ and $t \circ j$ both factor through the projection $\pi : K' \to H^0(K')[0]$:
$$s \circ j = \bar s[0] \circ \pi, \qquad t \circ j = \bar t[0] \circ \pi.$$
The map $\pi$ is a quasi-isomorphism, because $H^n(K') = H^n(K) = 0$ for $n \neq 0$. Then $\bar s[0]$ is a quasi-isomorphism between single complexes, so $\bar s$ is an isomorphism in $A$. Hence
$$\varphi = Q(t j) \circ Q(s j)^{-1} = Q(\bar t[0]) \circ Q(\pi) \circ Q(\pi)^{-1} \circ Q(\bar s[0])^{-1} = \iota_0(\bar t \circ \bar s^{-1}). \;\square$$

**Lemma (Bounded above complexes of projectives).** Let $P$ be a complex of projective objects with $P^n = 0$ for $n > 0$, and let $Z$ be acyclic. Each map of complexes $f : P \to Z$ is homotopic to zero.

*Proof.* Construct $h^n : P^n \to Z^{n-1}$ with $f^n = d h^n + h^{n+1} d$, by descending induction on $n$. For $n > 0$ put $h^n = 0$; the relation holds since $P^n = 0$. Suppose $h^m$ is built for $m > n$. Let $g = f^n - h^{n+1} d : P^n \to Z^n$. Then
$$d g = d f^n - d h^{n+1} d = f^{n+1} d - (f^{n+1} - h^{n+2} d) d = 0,$$
since $d d = 0$. So $g$ maps into the cycles of $Z^n$, which equal the boundaries because $Z$ is acyclic. The map $d : Z^{n-1} \to \operatorname{im} d$ is an epimorphism and $P^n$ is projective, so $g = d h^n$ for some $h^n$. This is the relation in degree $n$. $\square$

**Theorem (Computation by a projective resolution).** Let $P \to X$ be a projective resolution, written as a cochain complex with $P^{-k} = P_k$. Then $\operatorname{Ext}^n(X, Y) \cong H^n(\operatorname{Hom}(P_\bullet, Y))$, the cohomology of $\operatorname{Hom}(P_0, Y) \to \operatorname{Hom}(P_1, Y) \to \cdots$.

*Proof.* The augmentation $P \to X[0]$ is a quasi-isomorphism, so $\operatorname{Ext}^n(X, Y) \cong \operatorname{Hom}_{D(A)}(P, Y[n])$. By the lemma, $\operatorname{Hom}_{K(A)}(-, Z) = 0$ for acyclic $Z$ and maps out of $P$. The proof of the theorem on K-injective targets of the previous section, with arrows reversed, shows that $\operatorname{Hom}_{K(A)}(P, Y[n]) \to \operatorname{Hom}_{D(A)}(P, Y[n])$ is bijective. The complex $Y[n]$ has $Y$ in degree $-n$ and zero elsewhere. A map of complexes $P \to Y[n]$ is a morphism $u : P_n \to Y$ with $u \circ d = 0$ on $P_{n+1}$. A homotopy to zero is a morphism $h : P_{n-1} \to Y$ with $u = h \circ d$. So $\operatorname{Hom}_{K(A)}(P, Y[n])$ is the kernel of $\operatorname{Hom}(P_n, Y) \to \operatorname{Hom}(P_{n+1}, Y)$ modulo the image of $\operatorname{Hom}(P_{n-1}, Y)$. $\square$

So the Ext groups of this section agree with the Ext groups of Chapter 4.

**Theorem (Vanishing).** If $P$ is projective, then $\operatorname{Ext}^{n+1}(P, Y) = 0$ for all $Y$ and $n \geq 0$. If $I$ is injective, then $\operatorname{Ext}^{n+1}(X, I) = 0$ for all $X$ and $n \geq 0$.

*Proof.* The complex $P[0]$ is a projective resolution of $P$. Its Hom complex is $\operatorname{Hom}(P, Y)$ in degree $0$, so its cohomology in degree $n + 1$ is zero. The second claim is dual: $I[0]$ is a K-injective complex, so $\operatorname{Hom}_{D(A)}(X, I[n+1]) = \operatorname{Hom}_{K(A)}(X[0], I[n+1])$, and a map of complexes from a complex in degree $0$ to a complex in degree $-n-1$ is zero. $\square$

**Theorem (Long exact sequences).** Let $S : 0 \to X_1 \xrightarrow{f} X_2 \xrightarrow{g} X_3 \to 0$ be short exact and let $X, Y \in A$. For each $n$ the sequences
$$\operatorname{Ext}^n(X, X_1) \to \operatorname{Ext}^n(X, X_2) \to \operatorname{Ext}^n(X, X_3) \xrightarrow{e_S \cdot -} \operatorname{Ext}^{n+1}(X, X_1) \to \operatorname{Ext}^{n+1}(X, X_2) \to \operatorname{Ext}^{n+1}(X, X_3),$$
$$\operatorname{Ext}^n(X_3, Y) \to \operatorname{Ext}^n(X_2, Y) \to \operatorname{Ext}^n(X_1, Y) \xrightarrow{- \cdot e_S} \operatorname{Ext}^{n+1}(X_3, Y) \to \operatorname{Ext}^{n+1}(X_2, Y) \to \operatorname{Ext}^{n+1}(X_1, Y)$$
are exact. The unlabeled maps are the products with $\iota_0(f)$ and $\iota_0(g)$.

*Proof.* The triangle $T : X_1 \to X_2 \to X_3 \xrightarrow{e_S} X_1[1]$ is distinguished. Its rotations and its shifts are distinguished. A shift changes the signs of some morphisms, and a sign does not change the kernel or the image of a map. The functor $\operatorname{Hom}_{D(A)}(X, -)$ is homological (Volume 25, Chapter 5), so it gives an exact sequence from each distinguished triangle. Apply it to $T[n]$ and its rotation: the result is the first sequence, since $e_S[n] \circ \alpha = e_S \cdot \alpha$ for $\alpha : X \to X_3[n]$, up to a sign. The second sequence comes in the same way from the cohomological functor $\operatorname{Hom}_{D(A)}(-, Y[n])$. $\square$

The signs need care. Mathlib uses the product with $e_S$ as the connecting map of the first sequence, and the source states that it agrees with the connecting map in the book of Conrad on Grothendieck duality. For the contravariant sequence the product with $e_S$ is the standard connecting map only up to the sign $(-1)^{n+1}$. Mathlib defines the connecting map $\delta$ of the contravariant sequence as $(-1)^{n+1} (- \cdot e_S)$ for this reason, and states its exactness with $\delta$.

**Theorem (Naturality of the class).** Let $(u_1, u_2, u_3) : S \to T$ be a morphism of short exact sequences. Then $u_1 \cdot e_S = e_T \cdot u_3$ in $\operatorname{Ext}^1(S_3, T_1)$. Also $e_S \cdot g = 0$ and $f \cdot e_S = 0$.

*Proof.* The morphism of short exact sequences gives a morphism of the distinguished triangles of the previous section, since the map $\sigma$ of that section is natural. The square at the third morphism commutes; it is the first identity. The other two are the vanishing of two consecutive morphisms of a distinguished triangle. $\square$

**Theorem (Baer's criterion in Ext form).** Let $R$ be a ring, $I$ a left ideal and $M$ a left $R$-module. Then $\operatorname{Ext}^1(R/I, M) = 0$ if and only if each $R$-linear map $I \to M$ extends to $R$. So $M$ is injective if and only if $\operatorname{Ext}^1(R/I, M) = 0$ for all left ideals $I$.

*Proof.* Apply the contravariant sequence to $0 \to I \to R \to R/I \to 0$:
$$\operatorname{Hom}(R, M) \to \operatorname{Hom}(I, M) \to \operatorname{Ext}^1(R/I, M) \to \operatorname{Ext}^1(R, M).$$
The last group is zero by the vanishing theorem, since $R$ is projective. So $\operatorname{Ext}^1(R/I, M)$ is the cokernel of the restriction $\operatorname{Hom}(R, M) \to \operatorname{Hom}(I, M)$. It is zero exactly when each map $I \to M$ is a restriction. The second claim is Baer's criterion (Volume 7). $\square$

**Theorem (Injective dimension by ideals).** Let $n \geq 1$. If $\operatorname{Ext}^n(R/I, M) = 0$ for all left ideals $I$, then $M$ has injective dimension $< n$.

*Proof.* Induction on $n$. For $n = 1$ Baer's criterion makes $M$ injective, and the vanishing theorem gives $\operatorname{Ext}^i(Y, M) = 0$ for $i \geq 1$. Let $n \geq 1$ and suppose the claim for $n$. Suppose $\operatorname{Ext}^{n+1}(R/I, M) = 0$ for all $I$. Embed $M$ in an injective module $E$ (Volume 7) and let $M' = E/M$. The covariant sequence of $0 \to M \to E \to M' \to 0$ contains
$$\operatorname{Ext}^k(Y, E) \to \operatorname{Ext}^k(Y, M') \to \operatorname{Ext}^{k+1}(Y, M) \to \operatorname{Ext}^{k+1}(Y, E).$$
For $k \geq 1$ the outer groups vanish, so $\operatorname{Ext}^k(Y, M') \cong \operatorname{Ext}^{k+1}(Y, M)$. This is dimension shifting. With $k = n$ and $Y = R/I$, the hypothesis gives $\operatorname{Ext}^n(R/I, M') = 0$ for all $I$. By induction $M'$ has injective dimension $< n$, so $\operatorname{Ext}^{k+1}(Y, M) \cong \operatorname{Ext}^k(Y, M') = 0$ for all $k \geq n$. So $M$ has injective dimension $< n + 1$. $\square$

### Examples

**Example (Cyclic groups).** Over $\mathbb{Z}$, the module $\mathbb{Z}/m$ with $m \geq 1$ has the projective resolution $0 \to \mathbb{Z} \xrightarrow{m} \mathbb{Z} \to \mathbb{Z}/m \to 0$. For an abelian group $Y$, the Hom complex is $Y \xrightarrow{m} Y$ in degrees $0$ and $1$. So
$$\operatorname{Ext}^0(\mathbb{Z}/m, Y) = \{y \in Y : my = 0\}, \qquad \operatorname{Ext}^1(\mathbb{Z}/m, Y) = Y/mY,$$
and $\operatorname{Ext}^n(\mathbb{Z}/m, Y) = 0$ for $n \geq 2$. For $Y = \mathbb{Z}$: $\operatorname{Ext}^1(\mathbb{Z}/m, \mathbb{Z}) = \mathbb{Z}/m$. For $Y = \mathbb{Z}/k$: both groups are $\mathbb{Z}/\gcd(m, k)$. For $Y = \mathbb{Q}$: $\mathbb{Q}/m\mathbb{Q} = 0$, as the vanishing theorem predicts for the injective group $\mathbb{Q}$.

**Example (A generator of $\operatorname{Ext}^1(\mathbb{Z}/2, \mathbb{Z}/2)$).** Let $S$ be $0 \to \mathbb{Z} \xrightarrow{2} \mathbb{Z} \to \mathbb{Z}/2 \to 0$ and $T$ be $0 \to \mathbb{Z}/2 \xrightarrow{2} \mathbb{Z}/4 \to \mathbb{Z}/2 \to 0$, where the first map of $T$ sends $1$ to $2$. Let $\pi : \mathbb{Z} \to \mathbb{Z}/2$ and $\rho : \mathbb{Z} \to \mathbb{Z}/4$ be the reductions. Then $(\pi, \rho, 1) : S \to T$ is a morphism of short exact sequences: $\rho(2a) = 2a \bmod 4 = 2 \pi(a)$, and $\rho$ followed by reduction mod $2$ is $\pi$. By naturality, $\pi \cdot e_S = e_T$. The class $e_T$ is not zero: otherwise the triangle of $T$ splits and $H^0$ gives $\mathbb{Z}/4 \cong \mathbb{Z}/2 \oplus \mathbb{Z}/2$, which is false since $\mathbb{Z}/4$ has an element of order $4$. As $\operatorname{Ext}^1(\mathbb{Z}/2, \mathbb{Z}/2) \cong \mathbb{Z}/2$, the class $e_T$ generates it.

**Example (A polynomial ring).** Let $R = k[x]$ with $k$ a field, and let $k = R/(x)$. The resolution $0 \to R \xrightarrow{x} R \to k \to 0$ gives the complex $R \xrightarrow{x} R$ for $\operatorname{Hom}(-, R)$. So $\operatorname{Ext}^0(k, R) = 0$, because $x$ is injective on $R$, and $\operatorname{Ext}^1(k, R) = R/xR = k$. Since $R$ is a principal ideal domain, $\operatorname{Ext}^2(R/I, M) = 0$ for each ideal $I = (p)$, as the resolution $0 \to R \xrightarrow{p} R \to R/I \to 0$ has length one (for $I = 0$ the module $R$ is projective). By the last theorem, each $R$-module has injective dimension $< 2$.

**Example (An injective coresolution of $\mathbb{Z}$).** Let $0 \to \mathbb{Z} \to \mathbb{Q} \to \mathbb{Q}/\mathbb{Z} \to 0$. The group $\mathbb{Q}$ is divisible, hence injective. The covariant sequence and $\operatorname{Ext}^1(Y, \mathbb{Q}) = 0$ make $\operatorname{Ext}^1(Y, \mathbb{Z})$ the cokernel of $\operatorname{Hom}(Y, \mathbb{Q}) \to \operatorname{Hom}(Y, \mathbb{Q}/\mathbb{Z})$. For $Y = \mathbb{Z}/m$ the source is zero and the target is the $m$-torsion of $\mathbb{Q}/\mathbb{Z}$, which is cyclic of order $m$. This is the first example again.

### The library around it

::: mathlib
`CategoryTheory.Abelian.Ext.comp` · `Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic`

For `α : Ext X Y a`, `β : Ext Y Z b` and `h : a + b = c`, `α.comp β h : Ext X Z c`. The order is diagrammatic: `α` comes first. `Ext.mk₀ f : Ext X Y 0` is the class of `f : X ⟶ Y`, `mk₀_comp_mk₀` says `(mk₀ f).comp (mk₀ g) _ = mk₀ (f ≫ g)`, and `mk₀_bijective` and `addEquiv₀` identify degree `0` with `X ⟶ Y`. `Ext.postcomp β X h` and `Ext.precomp α Z h` are the additive maps of composition, and `extFunctor n : Cᵒᵖ ⥤ C ⥤ AddCommGrpCat` packs the functoriality.

<?decl CategoryTheory.Abelian.Ext.comp?>
:::

::: mathlib
`CategoryTheory.ShortComplex.ShortExact.extClass` · `Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass`

For `hS : S.ShortExact`, `hS.extClass : Ext S.X₃ S.X₁ 1`. The lemma `extClass_hom` identifies its image in the derived category with `hS.singleδ`. The lemmas `comp_extClass` and `extClass_comp` are the two vanishing statements, and `extClass_naturality` states `h₁.extClass.comp (mk₀ f.τ₁) _ = (mk₀ f.τ₃).comp h₂.extClass _`.

<?decl CategoryTheory.ShortComplex.ShortExact.extClass?>
:::

::: mathlib
`CategoryTheory.Abelian.Ext.covariantSequence_exact` · `Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences`

`Ext.covariantSequence X hS n₀ n₁ h` is a `ComposableArrows AddCommGrpCat 5` with the six groups of the first sequence, for `h : n₀ + 1 = n₁`, and `covariantSequence_exact` states its exactness. The pointwise forms are `covariant_sequence_exact₁`, `₂` and `₃`. `contravariantSequence` is the other sequence, with `1 + n₀ = n₁`. The definition `Ext.δ hS n₀ n₁ h` is `(-1) ^ n₁ • hS.extClass.comp e _`; the source states that this sign makes it consistent with the book of Conrad on Grothendieck duality. Use `δ_exact₁` and `δ_exact₃` with `Ext.δ`.

<?decl CategoryTheory.Abelian.Ext.covariantSequence_exact?>
:::

::: mathlib
`ModuleCat.hasInjectiveDimensionLT_of_quotients` · `Mathlib.Algebra.Category.ModuleCat.Ext.Baer`

The statements use `Ext ↧(Shrink.{v} (R ⧸ I)) M n`, because `R` and its quotients may live in a larger universe than `ModuleCat.{v} R`, and they assume `[Small.{v} R]`. `ext_quotient_one_subsingleton_iff` is the first part of Baer's theorem above, with `Subsingleton` for the vanishing of a group. `HasInjectiveDimensionLT M n` is defined in `Mathlib.CategoryTheory.Abelian.Injective.Dimension` by the vanishing of `Ext Y M i` for `n ≤ i`.

<?decl ModuleCat.hasInjectiveDimensionLT_of_quotients?>
:::

The file `Mathlib.Algebra.Category.ModuleCat.Ext.DimensionShifting` gives `ModuleCat.projectiveShortComplex M`, the sequence $0 \to N \to R^{(M)} \to M \to 0$ with a free middle term, and two surjectivity results for the connecting maps. Note that `postcomp_extClass_surjective_of_projective_X₂` assumes that the middle term is injective, despite its name. If $A$ is $R$-linear, `Ext X Y n` is an $R$-module (`Ext.instModule`), `smul_eq_comp_mk₀` writes $r \cdot \alpha$ as the product with $r \cdot 1_Y$, and `linearExtFunctor` takes values in `ModuleCat R`. The comparison with resolutions is `ProjectiveResolution.extEquivCohomologyClass` in `Mathlib.CategoryTheory.Abelian.Projective.Ext`.

The module `Mathlib.Algebra.Homology.DerivedCategory.SmallShiftedHom` sends cohomology classes of the Hom complex of Chapter 3, Section 3 to morphisms. The map `CochainComplex.HomComplex.CohomologyClass.toSmallShiftedHom` takes a class of degree $n$ from $K$ to $L$ to a shifted morphism of `CategoryTheory.Localization.SmallShiftedHom` for the quasi-isomorphisms. The map `CochainComplex.HomComplex.CohomologyClass.toShiftedHom` takes it to a morphism $Q(K) \to Q(L)[n]$ in the derived category. The lemmas `CochainComplex.HomComplex.CohomologyClass.toSmallShiftedHom_mk` and `CochainComplex.HomComplex.CohomologyClass.toShiftedHom_mk` compute them on the class of a cocycle, through the morphism of complexes $K \to L[n]$ that the cocycle gives. Section 4 shows that these maps are bijective when $L$ is K-injective.

The module `Mathlib.Algebra.Homology.LinearYonedaObj` computes these Ext groups with a projective resolution. For a chain complex $K$ indexed by $\mathbb{N}$ in an $R$-linear category and an object $Y$, the cochain complex `ChainComplex.linearYonedaObj` has the $R$-module of morphisms $K_n \to Y$ in degree $n$, with the differentials of $K$ and no signs. The isomorphism `ChainComplex.extendLinearYonedaObjIso` identifies its extension to $\mathbb{Z}$ with the complex `CochainComplex.linearHomComplex` of morphisms from $K$ to $Y$ in degree $0$; in each degree the identification has the sign $(-1)^{n(n+1)/2}$. For a projective resolution $P$ of $X$, the isomorphism `CategoryTheory.ProjectiveResolution.extIsoHomologyLinearYonedaObj` then identifies $\operatorname{Ext}^n(X, Y)$ with the cohomology in degree $n$ of the complex of morphisms from $P$ to $Y$, which is the classical definition of Chapter 4.

The module `Mathlib.Algebra.Homology.LocalCohomology` uses these Ext groups for modules. For a commutative ring $R$ and an ideal $J$, the functor `localCohomology` $J$ $i$ on $R$-modules sends $M$ to the colimit of the modules $\operatorname{Ext}^i(R/J^t, M)$ over $t$. The general form `localCohomology.ofDiagram` takes a colimit over any diagram of ideals, through `localCohomology.ringModIdeals`. The variant `localCohomology.ofSelfLERadical` takes the colimit over all ideals whose radical contains $J$. For a Noetherian ring, `localCohomology.isoSelfLERadical` identifies the two forms, and `localCohomology.isoOfSameRadical` shows that two ideals with the same radical give isomorphic local cohomology.

Common errors of a learner:

- `α.comp β h` means "$\alpha$ then $\beta$". The degree equation `h` has the degree of `α` first.
- The degree of `CategoryTheory.Abelian.Ext` is a natural number. The shift in the derived category is by the integer `(n : ℤ)`, and a cast appears in `Ext.homEquiv`.
- The vanishing results are stated with `Subsingleton (Ext P Y (n + 1))`, not with an equality to `0`.
- The precomposition with `extClass` is not the connecting map of the contravariant sequence. Use `Ext.δ`.

### Exercises

1. (A) Compute $\operatorname{Ext}^n_{\mathbb{Z}}(\mathbb{Z}/6, \mathbb{Z}/4)$ for all $n$. *Hint:* use the first example with $m = 6$, $k = 4$.
2. (A) Let $S$ be short exact and suppose that $g$ has a section $\sigma$, with $g \circ \sigma = 1$. Show that $e_S = 0$. *Hint:* $e_S = e_S \circ g \circ \sigma$, and $e_S \cdot g = 0$.
3. (B) Let $R = \mathbb{Z}/4$ and $k = \mathbb{Z}/2$. Using the periodic resolution $\cdots \xrightarrow{2} R \xrightarrow{2} R \to k \to 0$, show that $\operatorname{Ext}^n_R(k, k) \cong \mathbb{Z}/2$ for all $n \geq 0$. *Hint:* all maps of the Hom complex are zero.
4. (B) Prove that $\operatorname{Ext}^n_{\mathbb{Z}}(X, Y) = 0$ for $n \geq 2$ and all abelian groups. *Hint:* a subgroup of a free abelian group is free, so each $X$ has a resolution of length one.
5. (B) Show that an abelian group $M$ is injective if and only if $M/mM = 0$ for all $m \geq 1$. *Hint:* Baer's criterion in Ext form with the first example.
6. (C) Let $R = k[x, y]$ and $k = R/(x, y)$. Use the resolution $0 \to R \to R^2 \to R \to k \to 0$ with maps $r \mapsto (-yr, xr)$ and $(a, b) \mapsto xa + yb$ to compute $\operatorname{Ext}^n(k, R)$. *Hint:* the answer is $k$ for $n = 2$ and $0$ otherwise.
7. (C) Prove the second sequence of the long exact sequence theorem from the first one in the opposite category, and explain where the sign $(-1)^{n+1}$ can appear. *Hint:* the opposite of a triangulated category is triangulated with a shift that changes signs.

### Notes and history

The groups $\operatorname{Ext}$ go back to the work of Eilenberg and Mac Lane on group extensions, and the derived functor form is in Cartan and Eilenberg, *Homological Algebra* (1956). The product of extensions is due to Yoneda. The definition as morphisms in the derived category is in the thesis of Verdier, published in 1996. The criterion for injective modules is due to Baer.

The Mathlib Authors of the six `DerivedCategory.Ext` modules of this section are listed as Joël Riou, and the authors of `ModuleCat.Ext.Baer` and `ModuleCat.Ext.DimensionShifting` are listed as Nailin Guan.

### Reference

<?reference?>
