---
title: Properties of morphisms and immersions
kind: theory
modules:
  - Mathlib.AlgebraicGeometry.Morphisms.Affine
  - Mathlib.AlgebraicGeometry.Morphisms.AffineAnd
  - Mathlib.AlgebraicGeometry.Morphisms.Basic
  - Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
  - Mathlib.AlgebraicGeometry.Morphisms.Constructors
  - Mathlib.AlgebraicGeometry.Morphisms.Immersion
  - Mathlib.AlgebraicGeometry.Morphisms.IsIso
  - Mathlib.AlgebraicGeometry.Morphisms.LocalClosure
  - Mathlib.AlgebraicGeometry.Morphisms.LocalIso
  - Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
  - Mathlib.AlgebraicGeometry.Morphisms.Preimmersion
  - Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
  - Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
  - Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
  - Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
  - Mathlib.AlgebraicGeometry.Morphisms.SurjectiveOnStalks
  - Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
explains:
  E3: [AlgebraicGeometry.IsZariskiLocalAtTarget, AlgebraicGeometry.IsZariskiLocalAtSource, AlgebraicGeometry.AffineTargetMorphismProperty.IsLocal, AlgebraicGeometry.HasAffineProperty, AlgebraicGeometry.HasRingHomProperty, AlgebraicGeometry.affineLocally, AlgebraicGeometry.isIso_iff_isOpenImmersion_and_surjective, AlgebraicGeometry.IsAffineHom, AlgebraicGeometry.QuasiCompact, AlgebraicGeometry.QuasiSeparated, AlgebraicGeometry.SurjectiveOnStalks, AlgebraicGeometry.IsPreimmersion, AlgebraicGeometry.IsClosedImmersion, AlgebraicGeometry.IsImmersion, AlgebraicGeometry.IsSchemeTheoreticallyDominant]
  E2: [AlgebraicGeometry.AffineTargetMorphismProperty, AlgebraicGeometry.targetAffineLocally, AlgebraicGeometry.HasAffineProperty.iff_of_isAffine, AlgebraicGeometry.HasRingHomProperty.Spec_iff, AlgebraicGeometry.HasRingHomProperty.iff_of_isAffine, AlgebraicGeometry.affineAnd, AlgebraicGeometry.targetAffineLocally_affineAnd_iff, AlgebraicGeometry.topologically, AlgebraicGeometry.stalkwise, AlgebraicGeometry.sourceLocalClosure, AlgebraicGeometry.Surjective, AlgebraicGeometry.IsDominant, AlgebraicGeometry.IsLocalIso, AlgebraicGeometry.isomorphisms_eq_stalkwise, AlgebraicGeometry.isIso_SpecMap_iff, AlgebraicGeometry.isOpenImmersion_eq_inf, AlgebraicGeometry.isOpenImmersion_SpecMap_iff_of_surjective, AlgebraicGeometry.quasiCompact_iff_forall_isAffineOpen, AlgebraicGeometry.quasiSeparated_eq_diagonal_is_quasiCompact, AlgebraicGeometry.quasiSeparatedSpace_iff_forall_affineOpens, AlgebraicGeometry.isLocalization_basicOpen_of_qcqs, AlgebraicGeometry.IsClosedImmersion.spec_of_surjective, AlgebraicGeometry.IsClosedImmersion.Spec_iff, AlgebraicGeometry.isClosedImmersion_iff_isAffineHom, AlgebraicGeometry.isClosed_singleton_iff_isClosedImmersion, AlgebraicGeometry.IsPreimmersion.SpecMap_iff, AlgebraicGeometry.IsImmersion.isImmersion_iff_exists, AlgebraicGeometry.Scheme.Hom.liftCoborder, AlgebraicGeometry.Scheme.Hom.coborderRange, AlgebraicGeometry.SurjectiveOnStalks.Spec_iff, AlgebraicGeometry.SurjectiveOnStalks.isEmbedding_pullback, AlgebraicGeometry.IsSchemeTheoreticallyDominant.of_isDominant, AlgebraicGeometry.isSchemeTheoreticallyDominant_iff_isDominant]
  E1: auto
families: []
requires: [V09.C02, V10.C02, V13.C05, V24.C04, V28.C03, V28.C04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Properties of morphisms and immersions

### Overview

Grothendieck's view of algebraic geometry is relative: the important objects are morphisms $f : X \to Y$. A good property of morphisms is checked on small pieces. Usually it is local on the target, often also local on the source, and over affine opens it is a property of ring homomorphisms. Mathlib makes these three patterns into type classes on `MorphismProperty Scheme`, and each concrete property gets its general theory from them.

This section sets up the frame and then treats the first properties: isomorphisms and open immersions, affine, quasi-compact and quasi-separated morphisms, morphisms surjective on stalks, preimmersions, immersions and closed immersions, and scheme-theoretically dominant morphisms.

### Definitions

For a morphism $f : X \to Y$ and an open $U \subseteq Y$, write $f|_U : f^{-1}(U) \to U$ for the restriction. For affine opens $U \subseteq Y$ and $V \subseteq f^{-1}(U)$, write $f^\sharp_{U,V} : \mathcal{O}_Y(U) \to \mathcal{O}_X(V)$ for the map on sections followed by restriction.

**Definition (Property of morphisms).** A *property of morphisms* $P$ assigns to each morphism of schemes a proposition. It *respects isomorphisms* when $P(f)$ implies $P(e \circ f)$ and $P(f \circ e)$ for isomorphisms $e$. It is *stable under base change* when $P(f)$ implies $P(f')$ for each pullback $f'$ of $f$.

**Definition (Local on the target).** A property $P$ that respects isomorphisms is *local on the target* when, for each $f : X \to Y$ and each family of opens $(U_i)$ with $\bigcup_i U_i = Y$, the property $P(f)$ holds if and only if $P(f|_{U_i})$ holds for all $i$.

**Definition (Local on the source).** A property $P$ that respects isomorphisms is *local on the source* when, for each $f : X \to Y$ and each family of opens $(V_i)$ with $\bigcup_i V_i = X$, the property $P(f)$ holds if and only if $P(f \circ \iota_{V_i})$ holds for all $i$, with $\iota_{V_i} : V_i \to X$ the inclusion.

**Definition (Affine target property).** An *affine target property* $Q$ is a property of morphisms $f : X \to Y$ with $Y$ affine. It is *local* when it respects isomorphisms, when $Q(f)$ implies $Q(f|_{D(r)})$ for each $r \in \mathcal{O}_Y(Y)$, and when $Q(f|_{D(r_j)})$ for finitely many $r_1, \dots, r_n$ that generate the unit ideal implies $Q(f)$. The property $\operatorname{targetAffineLocally}(Q)$ holds for $f$ when $Q(f|_U)$ holds for every affine open $U \subseteq Y$. A property $P$ *has the affine property* $Q$ when $Q$ is local and $P = \operatorname{targetAffineLocally}(Q)$.

**Definition (Property from ring homomorphisms).** Let $Q$ be a property of ring homomorphisms. Then $\operatorname{affineLocally}(Q)$ holds for $f$ when $Q(f^\sharp_{U,V})$ holds for all affine opens $U \subseteq Y$ and $V \subseteq f^{-1}(U)$. A property $P$ *has the ring homomorphism property* $Q$ when $Q$ is local in the sense of commutative algebra (it respects isomorphisms, is preserved by localization and holds when it holds on a finite cover by localizations, on the source and on the target) and $P = \operatorname{affineLocally}(Q)$.

**Definition (Topological and stalkwise properties).** For a property $T$ of continuous maps, $f$ is *topologically* $T$ when its underlying map has $T$. The morphism $f$ is *surjective* when the underlying map is surjective, and *dominant* when the image is dense. For a property $Q$ of ring homomorphisms, $f$ is *stalkwise* $Q$ when every stalk map $f^\sharp_x : \mathcal{O}_{Y, f(x)} \to \mathcal{O}_{X, x}$ has $Q$.

**Definition (Affine, quasi-compact and quasi-separated morphisms).** The morphism $f$ is *affine* when $f^{-1}(U)$ is affine for every affine open $U \subseteq Y$. It is *quasi-compact* when $f^{-1}(U)$ is quasi-compact for every quasi-compact open $U \subseteq Y$. It is *quasi-separated* when the diagonal $\Delta_f : X \to X \times_Y X$ is quasi-compact.

**Definition (Immersions).** The morphism $f$ is *surjective on stalks* when every stalk map $f^\sharp_x$ is surjective. It is a *preimmersion* when it is surjective on stalks and its underlying map is a topological embedding. It is a *closed immersion* when it is surjective on stalks and its underlying map is a closed embedding. It is an *immersion* when it is a preimmersion and $f(X)$ is locally closed in $Y$.

The usual definition of a closed immersion asks that $\mathcal{O}_Y \to f_* \mathcal{O}_X$ be surjective. For a closed embedding, the stalk of $f_*\mathcal{O}_X$ is $\mathcal{O}_{X,x}$ at $f(x)$ and $0$ off $f(X)$, so the two definitions agree.

**Definition (Scheme-theoretically dominant).** The *kernel* of $f$ is the ideal sheaf $\ker f \subseteq \mathcal{O}_Y$ of sections whose image in $f_* \mathcal{O}_X$ is zero. The morphism $f$ is *scheme-theoretically dominant* when $\ker f = 0$.

### Theorems and proofs

**Lemma (Common basic opens).** Let $U = \operatorname{Spec} A$ and $W = \operatorname{Spec} B$ be affine opens of a scheme $Y$ and $x \in U \cap W$. An open $D \ni x$ exists that is a basic open of $U$ and a basic open of $W$.

*Proof.* The basic opens of $U$ form a basis, so $D_U(a) \subseteq U \cap W$ with $x \in D_U(a)$ exists. In the same way $D_W(b) \subseteq D_U(a)$ with $x \in D_W(b)$ exists. Let $\bar b$ be the restriction of $b$ to $D_U(a) = \operatorname{Spec} A_a$. Since $D_U(a) \subseteq W$, the points of $D_U(a)$ where $\bar b$ does not vanish are the points of $D_U(a)$ where $b$ does not vanish, so $D_{A_a}(\bar b) = D_W(b) \cap D_U(a) = D_W(b)$. Write $\bar b = c / a^n$ with $c \in A$. As $a$ is a unit on $D_U(a)$, $D_{A_a}(\bar b) = D_{A_a}(c) = D_U(ac)$. So $D = D_W(b) = D_U(ac)$ works. $\square$

**Theorem (Affine communication).** Let $Q$ be a local affine target property, and let $f : X \to Y$ have $Q(f|_{U_i})$ for an affine open cover $(U_i)$ of $Y$. Then $Q(f|_U)$ holds for every affine open $U \subseteq Y$. So $\operatorname{targetAffineLocally}(Q)$ is local on the target, and for affine $Y$ it holds for $f$ exactly when $Q(f)$ holds.

*Proof.* Let $U$ be affine and $x \in U$. Choose $i$ with $x \in U_i$, and by the lemma an open $D_x \ni x$ that is basic in $U$ and in $U_i$. The restriction $f|_{D_x}$ is the restriction of $f|_{U_i}$ to the basic open $D_x$ of $U_i$, so $Q(f|_{D_x})$ holds by the second axiom. The sets $D_x = D_U(r_x)$ cover $U$, and $U$ is quasi-compact, so finitely many $D_U(r_1), \dots, D_U(r_n)$ cover $U$. A prime of $\mathcal{O}_Y(U)$ that contains all $r_j$ would be a point of $U$ outside every $D_U(r_j)$, so the $r_j$ generate the unit ideal. The third axiom gives $Q(f|_U)$. For the locality on the target, take a cover $(W_k)$ of $Y$ with $\operatorname{targetAffineLocally}(Q)(f|_{W_k})$ for all $k$. The affine opens contained in some $W_k$ cover $Y$ and satisfy $Q$, so the first part gives $Q(f|_U)$ for every affine $U$. The rest follows from the first part. $\square$

**Theorem (Isomorphisms).** A morphism $f$ is an isomorphism if and only if it is an open immersion and surjective. The morphism $\operatorname{Spec} \varphi$ is an isomorphism if and only if the ring map $\varphi$ is bijective.

*Proof.* An isomorphism is an open immersion and surjective. Conversely, an open immersion is a homeomorphism onto the open set $f(X)$, which is $Y$ by surjectivity, so the underlying map is a homeomorphism. The stalk maps of an open immersion are isomorphisms. A morphism of sheaves that is an isomorphism on all stalks is an isomorphism, so $f$ is an isomorphism. For the second claim, $\operatorname{Spec}$ is fully faithful (Chapter 3), and a fully faithful functor reflects isomorphisms. $\square$

**Proposition (Quasi-compactness on affines).** A morphism $f$ is quasi-compact if and only if $f^{-1}(U)$ is quasi-compact for every affine open $U$. In particular an affine morphism is quasi-compact.

*Proof.* Affine opens are quasi-compact, so one direction is clear. Conversely, let $W$ be a quasi-compact open. The affine opens form a basis, so $W$ is a union of affine opens, and finitely many $U_1, \dots, U_n$ suffice. Then $f^{-1}(W) = \bigcup_j f^{-1}(U_j)$ is a finite union of quasi-compact sets, hence quasi-compact. For an affine morphism, each $f^{-1}(U)$ with $U$ affine is affine, hence quasi-compact. $\square$

In $\operatorname{Spec} A$ a quasi-compact open is a finite union of basic opens, and $D(a) \cap D(b) = D(ab)$, so the intersection of two quasi-compact opens is quasi-compact. Over an affine base, the index proves that a quasi-separated morphism is the same as a scheme in which two affine opens meet in a quasi-compact set.

**Proposition (Closed immersions from ideals).** Let $\varphi : R \to S$ be a surjective ring homomorphism with kernel $I$. Then $\operatorname{Spec} \varphi : \operatorname{Spec} S \to \operatorname{Spec} R$ is a closed immersion with image $V(I)$.

*Proof.* The map $\mathfrak{q} \mapsto \varphi^{-1}(\mathfrak{q})$ is a bijection from the primes of $S \cong R/I$ to the primes of $R$ that contain $I$, so the image is $V(I)$. It is a closed embedding: for $s = \varphi(r)$, the basic closed set $V(s)$ of $\operatorname{Spec} S$ maps onto $V(I) \cap V(r)$, so closed sets map to closed sets and the map is a homeomorphism onto the closed set $V(I)$. For the stalks, let $\mathfrak{q} \subseteq S$ and $\mathfrak{p} = \varphi^{-1}(\mathfrak{q})$. The stalk map is $R_{\mathfrak{p}} \to S_{\mathfrak{q}}$, $r/t \mapsto \varphi(r)/\varphi(t)$. Each element of $S_{\mathfrak{q}}$ has the form $\varphi(r)/\varphi(t)$ with $\varphi(t) \notin \mathfrak{q}$, that is $t \notin \mathfrak{p}$, so it is in the image. $\square$

The index proves the converse: a closed immersion $X \to \operatorname{Spec} R$ is isomorphic over $\operatorname{Spec} R$ to $\operatorname{Spec} R/I \to \operatorname{Spec} R$ for an ideal $I$. In general a closed immersion is affine, and surjective on sections over every affine open.

**Theorem (Immersions factor).** A morphism $f$ is an immersion if and only if $f = j \circ i$ with $i$ a closed immersion and $j$ an open immersion.

*Proof.* Let $f$ be an immersion and $Z = f(X)$. A locally closed set is open in its closure, so $W = Y \setminus (\overline{Z} \setminus Z)$ is open, and $Z = \overline{Z} \cap W$ is closed in $W$. The morphism $f$ factors through the open subscheme $W$ as $f = \iota_W \circ i$ (Chapter 3). The stalk maps of $i$ are those of $f$, since $\iota_W$ is an isomorphism on stalks, so they are surjective. The map $i$ is an embedding, as $f$ is, with closed image $Z$ in $W$, so $i$ is a closed immersion. Conversely, let $f = j \circ i$. A composite of embeddings is an embedding. The stalk map of $f$ at $x$ is the stalk map of $i$ composed with the stalk map of $j$, an isomorphism, so it is surjective. The image $j(i(X))$ is closed in the open set $j(Z)$, hence locally closed. $\square$

**Proposition (Dominant into reduced).** Let $f : X \to Y$ be dominant and $Y$ reduced. Then $f$ is scheme-theoretically dominant. If $f$ is quasi-compact, a scheme-theoretically dominant $f$ is dominant.

*Proof.* Let $U \subseteq Y$ be open and $s \in (\ker f)(U)$. For $x \in f^{-1}(U)$ the germ of $f^\sharp(s)$ at $x$ is zero, and the stalk map $\mathcal{O}_{Y,f(x)} \to \mathcal{O}_{X,x}$ is a local homomorphism, so $s(f(x)) = 0$ in the residue field $\kappa(f(x))$. So the closed set $\{y \in U : s(y) = 0\}$ contains $f(X) \cap U$, which is dense in $U$; hence it is $U$. On an affine open $\operatorname{Spec} A \subseteq U$, the restriction of $s$ lies in every prime of $A$, so it is nilpotent, and it is zero since $Y$ is reduced. The sheaf condition gives $s = 0$. The second claim is in the index; for quasi-compact $f$, the closed set cut out by $\ker f$ is the closure of $f(X)$. $\square$

### Examples

**Example (The origin of the affine line).** The surjection $k[x] \to k$, $x \mapsto 0$, gives a closed immersion $\operatorname{Spec} k \to \mathbb{A}^1_k$ onto the closed point $(x)$. The surjection $k[x] \to k[x]/(x^2)$ gives a second closed immersion with the same image. Its source is not isomorphic to $\operatorname{Spec} k$: the global sections $k[x]/(x^2)$ have the nonzero nilpotent $x$. So a closed immersion carries more than its closed image.

**Counterexample (A preimmersion that is not an immersion).** Let $f : \operatorname{Spec} \mathbb{Q} \to \operatorname{Spec} \mathbb{Z}$ come from $\mathbb{Z} \subseteq \mathbb{Q}$. The source is one point, so the map is an embedding onto the generic point $\{(0)\}$. The only stalk map is $\mathbb{Z}_{(0)} = \mathbb{Q} \to \mathbb{Q}$, the identity. So $f$ is a preimmersion. The closure of $\{(0)\}$ is $\operatorname{Spec} \mathbb{Z}$. If $\{(0)\}$ were locally closed, it would be open in its closure, so its complement, the set of all primes $(p)$, would be closed, that is $V(n)$ for some $n \neq 0$. But $V(n)$ is finite. So $f$ is not an immersion.

**Counterexample (Dominant but not scheme-theoretically dominant).** Let $f : \operatorname{Spec} k \to \operatorname{Spec} k[\varepsilon]/(\varepsilon^2)$ come from $\varepsilon \mapsto 0$. Both spaces are one point, so $f$ is a homeomorphism and dominant. The kernel of $k[\varepsilon]/(\varepsilon^2) \to k$ is $(\varepsilon) \neq 0$, and $f$ is affine, so $\ker f$ is the ideal sheaf of $(\varepsilon)$ and $f$ is not scheme-theoretically dominant.

### The library around it

::: mathlib
`AlgebraicGeometry.IsZariskiLocalAtTarget` · `Mathlib.AlgebraicGeometry.Morphisms.Basic`

`IsZariskiLocalAtTarget P` is `P.IsLocalAtTarget Scheme.zariskiPrecoverage`. `IsZariskiLocalAtTarget.restrict` gives `P (f ∣_ U)`, and `IsZariskiLocalAtTarget.iff_of_openCover` tests on a cover. The source version `IsZariskiLocalAtSource` has `IsZariskiLocalAtSource.iff_of_openCover`.

<?decl AlgebraicGeometry.IsZariskiLocalAtTarget?>
:::

::: mathlib
`AlgebraicGeometry.HasAffineProperty` · `Mathlib.AlgebraicGeometry.Morphisms.Basic`

`HasAffineProperty P Q` holds when `Q : AffineTargetMorphismProperty` satisfies `Q.IsLocal` and `P = targetAffineLocally Q`. The fields of `AffineTargetMorphismProperty.IsLocal` are `respectsIso`, `to_basicOpen` and `of_basicOpenCover`, as in the definition. `HasAffineProperty.iff_of_isAffine` gives `P f ↔ Q f` for affine `Y`. The helper `affineAnd Q` asks that the source is affine and that `Q` holds on global sections; `targetAffineLocally_affineAnd_iff` unfolds it.

<?decl AlgebraicGeometry.HasAffineProperty?>
:::

::: mathlib
`AlgebraicGeometry.HasRingHomProperty` · `Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties`

`HasRingHomProperty P Q` holds when `RingHom.PropertyIsLocal Q` and `P = affineLocally Q`, where `affineLocally Q f` asks `Q (f.appLE U V e).hom` for affine `U` and `V ≤ f ⁻¹ᵁ U`. `HasRingHomProperty.Spec_iff` is `P (Spec.map φ) ↔ Q φ.hom`, and `HasRingHomProperty.iff_of_isAffine` is `P f ↔ Q f.appTop.hom` for affine source and target.

<?decl AlgebraicGeometry.HasRingHomProperty?>
:::

::: mathlib
`AlgebraicGeometry.isIso_iff_isOpenImmersion_and_surjective` · `Mathlib.AlgebraicGeometry.Morphisms.IsIso`

The statement is `IsIso f ↔ IsOpenImmersion f ∧ Surjective f`. The stalkwise form is `isomorphisms_eq_stalkwise`, and `isIso_SpecMap_iff` is `IsIso (Spec.map f) ↔ Function.Bijective f.hom`. In `Morphisms.OpenImmersion`, `isOpenImmersion_eq_inf` writes `IsOpenImmersion` as `topologically IsOpenEmbedding ⊓ stalkwise (Function.Bijective ·)`, and `isOpenImmersion_SpecMap_iff_of_surjective` says that `Spec R/I → Spec R` is an open immersion exactly when `I` is generated by an idempotent.

<?decl AlgebraicGeometry.isIso_iff_isOpenImmersion_and_surjective?>
:::

::: mathlib
`AlgebraicGeometry.IsAffineHom` · `Mathlib.AlgebraicGeometry.Morphisms.Affine`

The field is `isAffine_preimage`. An instance gives `QuasiCompact f`.

<?decl AlgebraicGeometry.IsAffineHom?>
:::

::: mathlib
`AlgebraicGeometry.QuasiCompact` · `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`

The field `isCompact_preimage` asks compact preimages of compact opens. `quasiCompact_iff_forall_isAffineOpen` is the proposition above.

<?decl AlgebraicGeometry.QuasiCompact?>
:::

::: mathlib
`AlgebraicGeometry.QuasiSeparated` · `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`

The field is `QuasiCompact (pullback.diagonal f)`, and `quasiSeparated_eq_diagonal_is_quasiCompact` restates it with `MorphismProperty.diagonal`. `quasiSeparatedSpace_iff_forall_affineOpens` tests a scheme on pairs of affine opens. The qcqs lemma `isLocalization_basicOpen_of_qcqs` says that sections over a basic open of a quasi-compact quasi-separated `U` are a localization.

<?decl AlgebraicGeometry.QuasiSeparated?>
:::

::: mathlib
`AlgebraicGeometry.SurjectiveOnStalks` · `Mathlib.AlgebraicGeometry.Morphisms.SurjectiveOnStalks`

The field is `stalkMap_surjective : ∀ x, Function.Surjective (f.stalkMap x)`. `SurjectiveOnStalks.Spec_iff` reduces it to `RingHom.SurjectiveOnStalks`. `SurjectiveOnStalks.isEmbedding_pullback` says that a fiber product along such a morphism embeds in the product of the spaces.

<?decl AlgebraicGeometry.SurjectiveOnStalks?>
:::

::: mathlib
`AlgebraicGeometry.IsClosedImmersion` · `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`

The class extends `SurjectiveOnStalks f` with `isClosedEmbedding`. `IsClosedImmersion.spec_of_surjective` is the proposition on ideals and `IsClosedImmersion.Spec_iff` its converse. `isClosedImmersion_iff_isAffineHom` adds surjectivity on affine sections to `IsAffineHom`, and `isClosed_singleton_iff_isClosedImmersion` treats `Spec κ(x) → X`.

<?decl AlgebraicGeometry.IsClosedImmersion?>
:::

::: mathlib
`AlgebraicGeometry.IsPreimmersion` · `Mathlib.AlgebraicGeometry.Morphisms.Preimmersion`

The class extends `SurjectiveOnStalks f` with `isEmbedding`. `IsPreimmersion.SpecMap_iff` asks that `PrimeSpectrum.comap` is an embedding and that the ring map is surjective on stalks.

<?decl AlgebraicGeometry.IsPreimmersion?>
:::

::: mathlib
`AlgebraicGeometry.IsImmersion` · `Mathlib.AlgebraicGeometry.Morphisms.Immersion`

The class extends `IsPreimmersion f` with `isLocallyClosed_range`. `IsImmersion.isImmersion_iff_exists` is the factorization theorem; its two factors are `Scheme.Hom.liftCoborder` and the inclusion of `Scheme.Hom.coborderRange`, the open set $W$ of the proof.

<?decl AlgebraicGeometry.IsImmersion?>
:::

::: mathlib
`AlgebraicGeometry.IsSchemeTheoreticallyDominant` · `Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant`

The field is `ker_eq_bot : f.ker = ⊥`. `IsSchemeTheoreticallyDominant.of_isDominant` needs `IsReduced Y`, and `isSchemeTheoreticallyDominant_iff_isDominant` needs `QuasiCompact f` and `IsReduced Y`.

<?decl AlgebraicGeometry.IsSchemeTheoreticallyDominant?>
:::

`Morphisms.UnderlyingMap` defines the classes `Surjective` and `IsDominant`. `Morphisms.Constructors` defines `topologically` and `stalkwise`. `Morphisms.LocalIso` defines `IsLocalIso`: each point has an open neighbourhood on which `f` is an open immersion. `Morphisms.LocalClosure` defines `sourceLocalClosure P`, the morphisms that satisfy `P` on some cover of the source.

Common errors of a learner: `QuasiSeparated f` is a property of the diagonal, not of intersections in `X`, and the two agree only over a quasi-separated base. `IsClosedImmersion` in Mathlib asks surjectivity on stalks, not on sections; the two agree by the remark in the definitions. A preimmersion with closed image is a closed immersion, but a preimmersion need not be an immersion.

### Exercises

1. (A) Show that the composite of two affine morphisms is affine, and that a closed immersion $\operatorname{Spec} R/I \to \operatorname{Spec} R$ is affine. *Hint:* Use the definition; for the second, $V(I) \cap D(r)$ is the spectrum of $(R/I)_{\bar r}$.
2. (A) Let $D(x) = \operatorname{Spec} k[x, x^{-1}] \to \mathbb{A}^1_k$ be the open immersion. Show that it is dominant and scheme-theoretically dominant. *Hint:* $k[x] \to k[x, x^{-1}]$ is injective.
3. (B) Show that $\operatorname{Spec} k \times \operatorname{Spec} k \to \operatorname{Spec}(k \times k)$, the coproduct of the two closed immersions, is an isomorphism. *Hint:* The idempotents $(1, 0)$ and $(0, 1)$ split $\operatorname{Spec}(k \times k)$ into two open and closed points.
4. (B) Show that the property "the underlying map is injective" is local on the target and respects isomorphisms. *Hint:* Two points with the same image lie over one open $U_i$.
5. (B) Let $X \to \operatorname{Spec} \mathbb{Z}$ be a closed immersion with image $\{(p)\}$. Show that $X \cong \operatorname{Spec} \mathbb{Z}/p^n$ for some $n \geq 1$. *Hint:* Use the converse of the proposition on ideals; an ideal $(m)$ with $V(m) = \{(p)\}$ has $m = \pm p^n$.
6. (C) Show that a scheme $X$ is quasi-separated if and only if the intersection of any two affine opens is quasi-compact. *Hint:* For affine opens $U, V$, the set $\Delta^{-1}(U \times V)$ is $U \cap V$, and $U \times V$ is affine.

### Notes and history

The relative point of view and the study of properties local on the target and on the source are due to Grothendieck in EGA, 1960 to 1967. The affine communication lemma is the name in Vakil's notes; the Stacks project proves the same result for its properties of morphisms.

The Mathlib Author of `Morphisms.Basic`, `Morphisms.Affine`, `Morphisms.Constructors`, `Morphisms.Immersion`, `Morphisms.IsIso`, `Morphisms.OpenImmersion`, `Morphisms.Preimmersion`, `Morphisms.QuasiCompact`, `Morphisms.QuasiSeparated`, `Morphisms.RingHomProperties`, `Morphisms.SchemeTheoreticallyDominant`, `Morphisms.SurjectiveOnStalks` and `Morphisms.UnderlyingMap` is Andrew Yang. The Mathlib Author of `Morphisms.AffineAnd`, `Morphisms.LocalClosure` and `Morphisms.LocalIso` is Christian Merten. The Mathlib Authors of `Morphisms.ClosedImmersion` are Amelia Livingston, Christian Merten and Jonas van der Schaaf.

### Reference

<?reference?>
