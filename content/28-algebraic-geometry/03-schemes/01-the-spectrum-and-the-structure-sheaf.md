---
title: The spectrum and the structure sheaf
kind: theory
modules:
  - Mathlib.AlgebraicGeometry.AffineScheme
  - Mathlib.AlgebraicGeometry.GammaSpecAdjunction
  - Mathlib.AlgebraicGeometry.Spec
  - Mathlib.AlgebraicGeometry.StructureSheaf
explains:
  E3: [AlgebraicGeometry.Spec.structureSheaf, AlgebraicGeometry.StructureSheaf.isLocallyFraction, AlgebraicGeometry.StructureSheaf.stalkIso, AlgebraicGeometry.StructureSheaf.globalSectionsIso, AlgebraicGeometry.ΓSpec.adjunction, AlgebraicGeometry.IsAffine, AlgebraicGeometry.AffineScheme, AlgebraicGeometry.IsAffineOpen]
  E2: [AlgebraicGeometry.StructureSheaf.IsFraction, AlgebraicGeometry.StructureSheaf.const, AlgebraicGeometry.StructureSheaf.toStalk, AlgebraicGeometry.StructureSheaf.IsLocalization.to_basicOpen, AlgebraicGeometry.Spec.locallyRingedSpaceObj, AlgebraicGeometry.Spec.locallyRingedSpaceMap, AlgebraicGeometry.Scheme.toSpecΓ, AlgebraicGeometry.Spec.fullyFaithful, AlgebraicGeometry.Spec.homEquiv, AlgebraicGeometry.ΓSpec.isIso_adjunction_counit, AlgebraicGeometry.essImage_Spec, AlgebraicGeometry.AffineScheme.equivCommRingCat, AlgebraicGeometry.Scheme.isoSpec, AlgebraicGeometry.IsAffineOpen.isLocalization_basicOpen, AlgebraicGeometry.IsAffineOpen.fromSpec, AlgebraicGeometry.isBasis_basicOpen, AlgebraicGeometry.Spec.stalkIso]
  E1: auto
families: []
requires: [V06.C01, V06.C02, V09.C02, V10.C02, V13.C01, V24.C04, V24.C05, V28.C01, V28.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The spectrum and the structure sheaf

### Overview

A commutative ring $R$ gives a geometric object $\operatorname{Spec} R$. Its points are the prime ideals of $R$. Its open sets come from the Zariski topology. Its functions are the elements of $R$ and their local fractions. An element $r$ vanishes at $\mathfrak{p}$ when $r \in \mathfrak{p}$. The ring $R$ is not lost in this construction: the global functions on $\operatorname{Spec} R$ are again $R$.

This section builds the structure sheaf, computes its stalks and its sections on basic open sets, and proves the adjunction between global sections and $\operatorname{Spec}$. From the adjunction, affine schemes are the same as commutative rings with the arrows reversed.

### Definitions

Volume 9 treats the topology in full; this section recalls what it needs.

**Definition (Zariski topology).** For a subset $S \subseteq R$ let $V(S)$ be the set of primes $\mathfrak{p}$ with $S \subseteq \mathfrak{p}$. The sets $V(S)$ are the closed sets of a topology on $\operatorname{Spec} R$. For $f \in R$ the *basic open set* is $D(f) = \operatorname{Spec} R \setminus V(\{f\})$, the set of primes that do not contain $f$.

The rules $\bigcap_i V(S_i) = V(\bigcup_i S_i)$ and $V(I) \cup V(J) = V(IJ)$ give the axioms of closed sets; a prime that contains $IJ$ contains $I$ or $J$. The equality $D(f) \cap D(g) = D(fg)$ holds because a prime contains $fg$ exactly when it contains $f$ or $g$. Each open set is $\operatorname{Spec} R \setminus V(S) = \bigcup_{f \in S} D(f)$, so the sets $D(f)$ are a basis. The inclusion $D(f) \subseteq D(g)$ holds if and only if $f \in \sqrt{(g)}$, that is, $f^n = ag$ for some $n \geq 1$ and $a \in R$.

A function on $\operatorname{Spec} R$ takes a value in $R_{\mathfrak{p}}$ at $\mathfrak{p}$, not only in $\kappa(\mathfrak{p})$, because a nonzero nilpotent has value $0$ in each residue field.

**Definition (Locally fraction).** Let $U \subseteq \operatorname{Spec} R$ be open. A function $s : U \to \coprod_{\mathfrak{p} \in U} R_{\mathfrak{p}}$ with $s(\mathfrak{p}) \in R_{\mathfrak{p}}$ is a *locally fraction* when each $\mathfrak{p} \in U$ has an open neighbourhood $V \subseteq U$ and elements $a, g \in R$ such that for all $\mathfrak{q} \in V$, $g \notin \mathfrak{q}$ and $s(\mathfrak{q}) = a/g$ in $R_{\mathfrak{q}}$.

**Definition (Structure sheaf).** The *structure sheaf* $\mathcal{O}$ of $\operatorname{Spec} R$ assigns to an open $U$ the set $\mathcal{O}(U)$ of locally fractions on $U$. Addition and multiplication are pointwise, and the restriction maps restrict the functions.

Sums and products of locally fractions are locally fractions, since $a/g + b/h = (ah + bg)/(gh)$ and $gh \notin \mathfrak{q}$. So $\mathcal{O}(U)$ is a subring of $\prod_{\mathfrak{p} \in U} R_{\mathfrak{p}}$. The condition is local on $U$, so compatible sections glue, and $\mathcal{O}$ is a sheaf. For $a \in R$ and $g \in R$, the *constant section* $a/g$ on $D(g)$ is the function $\mathfrak{q} \mapsto a/g$. For $a \in R$ the section $a/1$ on $\operatorname{Spec} R$ gives a ring map $R \to \mathcal{O}(\operatorname{Spec} R)$, and it gives a ring map $R \to \mathcal{O}_{\mathfrak{p}}$ to each stalk.

### Theorems and proofs

**Theorem (Stalks).** For each prime $\mathfrak{p}$ of $R$, the map $\mathcal{O}_{\mathfrak{p}} \to R_{\mathfrak{p}}$, $[s] \mapsto s(\mathfrak{p})$, is an isomorphism of rings. Its inverse sends $a/g$ to the germ of the constant section $a/g$ on $D(g)$.

*Proof.* The map is a well defined ring map, because restriction does not change the value at $\mathfrak{p}$. It is surjective: for $a/g \in R_{\mathfrak{p}}$ with $g \notin \mathfrak{p}$, the constant section $a/g$ on $D(g)$ is a section on a neighbourhood of $\mathfrak{p}$, and its value at $\mathfrak{p}$ is $a/g$. For injectivity, let $s$ and $t$ be sections near $\mathfrak{p}$ with $s(\mathfrak{p}) = t(\mathfrak{p})$. Shrink the domain to an open $V \ni \mathfrak{p}$ on which $s = a/g$ and $t = b/h$, with $g, h \notin \mathfrak{q}$ for all $\mathfrak{q} \in V$. The equality $a/g = b/h$ in $R_{\mathfrak{p}}$ gives $c \notin \mathfrak{p}$ with $c(ah - bg) = 0$. For $\mathfrak{q} \in V \cap D(c)$ the same $c$ shows $a/g = b/h$ in $R_{\mathfrak{q}}$. So $s$ and $t$ agree on the open neighbourhood $V \cap D(c)$ of $\mathfrak{p}$, and their germs are equal. $\square$

**Theorem (Sections on a basic open set).** For $f \in R$ the map $\psi : R_f \to \mathcal{O}(D(f))$, $a/f^n \mapsto (\mathfrak{q} \mapsto a/f^n)$, is an isomorphism of rings. For $f = 1$ it gives $R \cong \mathcal{O}(\operatorname{Spec} R)$.

*Proof.* The map is well defined, because $f \notin \mathfrak{q}$ for $\mathfrak{q} \in D(f)$, and it is a ring map.

Injectivity. Let $\psi(a/f^n) = \psi(b/f^m)$. Put $d = f^m a - f^n b$ and $I = \operatorname{Ann}(d)$. For each $\mathfrak{p} \in D(f)$ the equality $a/f^n = b/f^m$ in $R_{\mathfrak{p}}$ gives $c \notin \mathfrak{p}$ with $cd = 0$, so $I \not\subseteq \mathfrak{p}$. Thus $V(I) \cap D(f) = \emptyset$, so $V(I) \subseteq V(f)$ and $f \in \sqrt{I}$. Then $f^l d = 0$ for some $l$, and this says $a/f^n = b/f^m$ in $R_f$.

Surjectivity. Let $s \in \mathcal{O}(D(f))$. Each point of $D(f)$ has a neighbourhood $V$ on which $s = a/h$ with $h$ outside each prime of $V$. Shrink $V$ to a basic open set $D(k) \subseteq V$; then $D(k) \subseteq D(h)$, so $k^n = ch$ and $a/h = ca/k^n$ on $D(k)$. Since $D(k^n) = D(k)$, the result is a cover of $D(f)$ by sets $D(h_i)$ with $s = a_i/h_i$ on $D(h_i)$. The inclusion $D(f) \subseteq \bigcup_i D(h_i)$ says $V(\{h_i\}) \subseteq V(f)$, so $f \in \sqrt{(h_i)_i}$ and $f^m = \sum_{i=1}^r b_i h_i$ for finitely many indices. Keep only these $r$ indices; the sets $D(h_1), \dots, D(h_r)$ still cover $D(f)$. On $D(h_i h_j) = D(h_i) \cap D(h_j)$ the two fractions $a_i/h_i$ and $a_j/h_j$ give the same section. By injectivity for the ring $R_{h_i h_j}$, there is $n$ with $(h_i h_j)^n (h_j a_i - h_i a_j) = 0$, and one $n$ serves for all pairs. Replace $a_i$ by $a_i h_i^n$ and $h_i$ by $h_i^{n+1}$. This does not change $a_i/h_i$ or $D(h_i)$, and now $h_j a_i = h_i a_j$ for all $i, j$. Write again $f^m = \sum_i b_i h_i$ for the new $h_i$ and put $a = \sum_i b_i a_i$. Then $h_j a = \sum_i b_i h_i a_j = f^m a_j$, so $a/f^m = a_j/h_j$ on $D(h_j)$. Thus $s = \psi(a/f^m)$. $\square$

**Proposition (Spec is a locally ringed space).** The pair $(\operatorname{Spec} R, \mathcal{O})$ is a locally ringed space. A ring map $\varphi : R \to S$ gives a morphism of locally ringed spaces $\operatorname{Spec} S \to \operatorname{Spec} R$, and this is a contravariant functor.

*Proof.* The stalk $R_{\mathfrak{p}}$ is a local ring. The map on points is $\mathfrak{q} \mapsto \varphi^{-1}(\mathfrak{q})$, and it is continuous because the preimage of $D(f)$ is $D(\varphi(f))$. On sections it sends a locally fraction $s$ on $U$ to $\mathfrak{q} \mapsto \varphi_{\mathfrak{q}}(s(\varphi^{-1}\mathfrak{q}))$, where $\varphi_{\mathfrak{q}} : R_{\varphi^{-1}\mathfrak{q}} \to S_{\mathfrak{q}}$ is the induced map. The stalk map is $\varphi_{\mathfrak{q}}$, and the preimage of $\mathfrak{q}S_{\mathfrak{q}}$ under it is $\varphi^{-1}(\mathfrak{q})R_{\varphi^{-1}\mathfrak{q}}$, so it is local. $\square$

**Theorem (Global sections and Spec).** Let $X$ be a locally ringed space and $R$ a commutative ring. The map that sends a morphism $f : X \to \operatorname{Spec} R$ to $f^\# : R = \mathcal{O}(\operatorname{Spec} R) \to \mathcal{O}_X(X)$ is a bijection between morphisms of locally ringed spaces $X \to \operatorname{Spec} R$ and ring maps $R \to \mathcal{O}_X(X)$. It is natural in $X$ and $R$. Thus $\Gamma$ is left adjoint to $\operatorname{Spec}$ as functors between locally ringed spaces and the opposite of commutative rings.

*Proof.* Fix $\varphi : R \to \mathcal{O}_X(X)$. For $x \in X$ let $\varphi_x : R \to \mathcal{O}_{X,x}$ be $\varphi$ followed by the germ map, and put $\mathfrak{p}_x = \varphi_x^{-1}(\mathfrak{m}_x)$. It is a prime ideal, because it is the preimage of a prime. For $r \in R$ the preimage of $D(r)$ is $X_r = \{x : \varphi(r)_x \text{ is a unit}\}$. This set is open, because an inverse of the germ $\varphi(r)_x$ is the germ of a section $t$ with $\varphi(r)t = 1$ near $x$. So $x \mapsto \mathfrak{p}_x$ is continuous. The local inverses agree on overlaps and glue, so $\varphi(r)$ is invertible on $X_r$. Define $\mathcal{O}(D(r)) = R_r \to \mathcal{O}_X(X_r)$ by $a/r^n \mapsto \varphi(a)\varphi(r)^{-n}$. These maps commute with restriction, and the sets $D(r)$ form a basis closed under intersection, so they define a morphism of sheaves. The stalk map at $x$ is $R_{\mathfrak{p}_x} \to \mathcal{O}_{X,x}$, $a/g \mapsto \varphi_x(a)\varphi_x(g)^{-1}$. The preimage of $\mathfrak{m}_x$ is $\mathfrak{p}_x R_{\mathfrak{p}_x}$, so the stalk map is local. On global sections the construction gives back $\varphi$, by the case $r = 1$.

Now let $f : X \to \operatorname{Spec} R$ be a morphism with $f^\# = \varphi$ on global sections. The stalk map $f^\#_x : R_{f(x)} \to \mathcal{O}_{X,x}$ is local and is compatible with $\varphi_x$. So for $r \in R$: $r \in f(x)$ if and only if $r/1 \in \mathfrak{m}_{f(x)}$, if and only if $\varphi_x(r) \in \mathfrak{m}_x$. Thus $f(x) = \mathfrak{p}_x$. On $D(r)$ the ring map $f^\# : R_r \to \mathcal{O}_X(X_r)$ extends $R \to \mathcal{O}_X(X_r)$, and by the universal property of $R_r$ it is the map built above. So $f$ is the morphism built from $\varphi$, and the two constructions are inverse. $\square$

**Corollary (Spec is fully faithful).** The functor $\operatorname{Spec}$ from the opposite of commutative rings to locally ringed spaces is fully faithful. Ring maps $R \to S$ correspond to morphisms $\operatorname{Spec} S \to \operatorname{Spec} R$.

*Proof.* Take $X = \operatorname{Spec} S$ in the theorem. Morphisms $\operatorname{Spec} S \to \operatorname{Spec} R$ correspond to ring maps $R \to \mathcal{O}(\operatorname{Spec} S) \cong S$, and the construction sends $\varphi$ to the morphism of the proposition. So the bijection is the map on arrows of $\operatorname{Spec}$. $\square$

**Definition (Affine scheme).** An *affine scheme* is a locally ringed space isomorphic to $\operatorname{Spec} R$ for some ring $R$.

**Corollary (Affine schemes and rings).** A locally ringed space $X$ is an affine scheme if and only if the unit $X \to \operatorname{Spec} \mathcal{O}_X(X)$ of the adjunction is an isomorphism. The functors $\Gamma$ and $\operatorname{Spec}$ give an equivalence between affine schemes and the opposite of the category of commutative rings.

*Proof.* If the unit is an isomorphism, $X$ is affine. Conversely, the unit is natural, so it suffices to treat $X = \operatorname{Spec} R$. By the triangle identities its unit is the image under $\operatorname{Spec}$ of the isomorphism $R \to \mathcal{O}(\operatorname{Spec} R)$. An adjunction restricts to an equivalence between the objects where the unit is an isomorphism and the objects where the counit is an isomorphism. Here the counit is an isomorphism on each ring. $\square$

**Definition (Affine open set).** An open set $U$ of a scheme $X$ is *affine* when the open subscheme $(U, \mathcal{O}_X|_U)$ is an affine scheme. For $f \in \mathcal{O}_X(U)$ the *basic open set* $X_f$ is the set of $x \in U$ at which the germ $f_x$ is a unit.

**Proposition (Basic open sets of an affine open set).** Let $U \subseteq X$ be an affine open set with $A = \mathcal{O}_X(U)$. For $f \in A$ the set $X_f$ is the image of $D(f)$ under $U \cong \operatorname{Spec} A$, and $\mathcal{O}_X(X_f) \cong A_f$. The sets $X_f$ for $f \in A$ are a basis of the topology of $U$.

*Proof.* Under the isomorphism $U \cong \operatorname{Spec} A$ the germ $f_{\mathfrak{p}}$ is $f/1 \in A_{\mathfrak{p}}$. It is a unit exactly when $f \notin \mathfrak{p}$, so $X_f$ corresponds to $D(f)$. The theorem on sections gives $\mathcal{O}(D(f)) \cong A_f$. The sets $D(f)$ are a basis of $\operatorname{Spec} A$. $\square$

### Examples

**Example (The points of Spec ℤ).** The primes of $\mathbb{Z}$ are $(0)$ and $(p)$ for the prime numbers $p$. The closure of $\{(p)\}$ is $V(p) = \{(p)\}$, so $(p)$ is a closed point. The closure of $\{(0)\}$ is $V(0)$, the whole space, so $(0)$ is the *generic point*. A proper closed set is $V(n)$ for some $n \neq 0$, the finite set of primes that divide $n$. The stalk at $(p)$ is $\mathbb{Z}_{(p)}$, the fractions with denominator prime to $p$, and its residue field is $\mathbb{F}_p$. The stalk at $(0)$ is $\mathbb{Q}$. The open set $D(6)$ omits $(2)$ and $(3)$, and $\mathcal{O}(D(6)) = \mathbb{Z}[1/6]$.

**Example (The affine line and its generic point).** Let $k$ be an algebraically closed field and $R = k[x]$. The primes are $(x - a)$ for $a \in k$ and $(0)$, because $k[x]$ is a principal ideal domain and the irreducible polynomials are linear. The closed points form the classical line $k$. The point $(0)$ is not closed: each nonempty open set contains it, and its closure is the whole line. Its stalk is the field $k(x)$ of rational functions.

**Example (A point with a nilpotent function).** Let $R = k[\varepsilon]/(\varepsilon^2)$. The only prime is $(\varepsilon)$, so $\operatorname{Spec} R$ is one point and $\mathcal{O}(\operatorname{Spec} R) = R$. The function $\varepsilon$ has the value $0$ in the residue field $k$, and it is not $0$. So a section of $\mathcal{O}$ is not determined by its values in the residue fields. This is the reason for the values in $R_{\mathfrak{p}}$ in the definition.

**Counterexample (A morphism of ringed spaces that is not local).** Let $R$ be a discrete valuation ring with uniformizer $\pi$ and fraction field $K$. Then $\operatorname{Spec} R$ has two points, the closed point $s$ and the generic point $\eta$, and $\{\eta\}$ is open. Map the one point of $\operatorname{Spec} K$ to $s$. The only open set that contains $s$ is the whole space, so the inclusion $R \to K$ gives a morphism of ringed spaces. Its stalk map at the point is $R \to K$, and it sends $\pi \in \mathfrak{m}_s$ to a unit, so it is not local. The ring map $R \to K$ sends its point to $\eta$, not to $s$. So the adjunction fails without the condition on stalk maps.

### The library around it

::: mathlib
`PrimeSpectrum` · `Mathlib.RingTheory.Spectrum.Prime.Defs`

`PrimeSpectrum R` is the type of prime ideals; a point `x` has the field `x.asIdeal`. The closed sets are `PrimeSpectrum.zeroLocus`, and `PrimeSpectrum.basicOpen r` is $D(r)$.

<?decl PrimeSpectrum?>
:::

::: mathlib
`AlgebraicGeometry.Spec.structureSheaf` · `Mathlib.AlgebraicGeometry.StructureSheaf`

`Spec.structureSheaf R : TopCat.Sheaf CommRingCat (PrimeSpectrum.Top R)` for `R : Type u` with `[CommRing R]`. The file works with an `R`-module `M`, and the ring case is `M = R`. The values lie in `StructureSheaf.Localizations M`, and `StructureSheaf.const` is the constant section $a/g$ on an open `U ≤ basicOpen g`.

<?decl AlgebraicGeometry.Spec.structureSheaf?>
:::

::: mathlib
`AlgebraicGeometry.StructureSheaf.isLocallyFraction` · `Mathlib.AlgebraicGeometry.StructureSheaf`

`StructureSheaf.IsFraction` says that a dependent function on `U` is $a/g$ at each point of `U`. The local predicate `isLocallyFraction R M` is its sheafification, as in the definition, and it is a `TopCat.LocalPredicate`.

<?decl AlgebraicGeometry.StructureSheaf.isLocallyFraction?>
:::

::: mathlib
`AlgebraicGeometry.StructureSheaf.stalkIso` · `Mathlib.AlgebraicGeometry.StructureSheaf`

An `R`-algebra isomorphism `Localization.AtPrime x.asIdeal ≃ₐ[R]` the stalk at `x`. The map from `R` is `StructureSheaf.toStalk`, and the instance `IsLocalization.to_stalk` states the universal property. For a scheme, `AlgebraicGeometry.Spec.stalkIso` is the same fact for the stalks of `Spec R`.

<?decl AlgebraicGeometry.StructureSheaf.stalkIso?>
:::

::: mathlib
`AlgebraicGeometry.StructureSheaf.globalSectionsIso` · `Mathlib.AlgebraicGeometry.StructureSheaf`

The isomorphism from `R` to the sections on `⊤`. The instance `StructureSheaf.IsLocalization.to_basicOpen` says that the sections on `PrimeSpectrum.basicOpen r` are `IsLocalization.Away r`, which is the theorem on basic open sets.

<?decl AlgebraicGeometry.StructureSheaf.globalSectionsIso?>
:::

::: mathlib
`AlgebraicGeometry.ΓSpec.adjunction` · `Mathlib.AlgebraicGeometry.GammaSpecAdjunction`

`ΓSpec.adjunction : Scheme.Γ.rightOp ⊣ Scheme.Spec` on schemes; `ΓSpec.locallyRingedSpaceAdjunction` is the version for locally ringed spaces. The unit at `X` is `Scheme.toSpecΓ X : X ⟶ Spec Γ(X, ⊤)`, built from the primes $\mathfrak{p}_x$ of the proof. The instance `ΓSpec.isIso_adjunction_counit` gives `Spec.fullyFaithful`, and `Spec.homEquiv` is the bijection `(Spec S ⟶ Spec R) ≃ (R ⟶ S)`. `Spec.locallyRingedSpaceObj` and `Spec.locallyRingedSpaceMap` give the proposition.

<?decl AlgebraicGeometry.ΓSpec.adjunction?>
:::

::: mathlib
`AlgebraicGeometry.IsAffine` · `Mathlib.AlgebraicGeometry.AffineScheme`

`IsAffine X` is a class with one field: `X.toSpecΓ` is an isomorphism. This is the criterion of the corollary, not the existence of some ring. The isomorphism itself is `X.isoSpec`. The lemma `essImage_Spec` says that `X` is in the essential image of `Scheme.Spec` if and only if `IsAffine X`.

<?decl AlgebraicGeometry.IsAffine?>
:::

::: mathlib
`AlgebraicGeometry.AffineScheme` · `Mathlib.AlgebraicGeometry.AffineScheme`

The full subcategory `Scheme.Spec.EssImageSubcategory`. The equivalence with rings is `AffineScheme.equivCommRingCat : AffineScheme ≌ CommRingCatᵒᵖ`.

<?decl AlgebraicGeometry.AffineScheme?>
:::

::: mathlib
`AlgebraicGeometry.IsAffineOpen` · `Mathlib.AlgebraicGeometry.AffineScheme`

`IsAffineOpen U` is `IsAffine U` for the open subscheme. The open immersion `IsAffineOpen.fromSpec` goes from `Spec Γ(X, U)` onto `U`. The proposition is `IsAffineOpen.isLocalization_basicOpen`: the sections on `X.basicOpen f` are `IsLocalization.Away f`. The lemma `isBasis_basicOpen` gives the basis for an affine scheme.

<?decl AlgebraicGeometry.IsAffineOpen?>
:::

Common errors of a learner: `Spec.map` is contravariant, so a ring map `R ⟶ S` gives `Spec S ⟶ Spec R`. `Spec` takes a `CommRingCat`, so a ring `R : Type u` enters as `Spec (CommRingCat.of R)`. `Γ(X, U)` is notation for `X.presheaf.obj (op U)`, with `op`. A point of `PrimeSpectrum R` is a structure, not an ideal, so the ideal is `x.asIdeal`. `IsAffine X` is about the map `X.toSpecΓ`, so from an isomorphism `f : X ⟶ Spec R` it follows by `IsAffine.of_isIso f` and the instance `isAffine_Spec`.

### Exercises

1. (A) Describe the points of $\operatorname{Spec} \mathbb{Z}/12$ and the stalk at each point. *Hint:* The primes of $\mathbb{Z}/12$ come from the primes of $\mathbb{Z}$ that contain $12$.
2. (A) Show that $\operatorname{Spec}(R \times S)$ is the disjoint union of two open sets homeomorphic to $\operatorname{Spec} R$ and $\operatorname{Spec} S$. *Hint:* Use the idempotents $(1, 0)$ and $(0, 1)$ and the sets $D(1, 0)$ and $D(0, 1)$.
3. (B) Show that $\operatorname{Spec} R$ is quasi-compact. *Hint:* Reduce to a cover by basic open sets and use $1 \in (f_i)_i$.
4. (B) Show that the closure of $\{\mathfrak{p}\}$ in $\operatorname{Spec} R$ is $V(\mathfrak{p})$, and that $\mathfrak{p}$ is a closed point if and only if it is maximal. *Hint:* A closed set $V(S)$ contains $\mathfrak{p}$ exactly when $S \subseteq \mathfrak{p}$.
5. (C) Let $K$ be a field. Show that morphisms $\operatorname{Spec} K \to \operatorname{Spec} R$ correspond to pairs of a prime $\mathfrak{p}$ and a field map $\kappa(\mathfrak{p}) \to K$. *Hint:* Use the adjunction and note that the kernel of $R \to K$ is prime.
6. (C) Let $U = \mathbb{A}^2_k \setminus \{(0,0)\}$, the open subset $D(x) \cup D(y)$ of $\operatorname{Spec} k[x, y]$. Show that $\mathcal{O}(U) = k[x, y]$, and deduce that $U$ is not affine. *Hint:* Compare $k[x, y]_x$ and $k[x, y]_y$ inside $k(x, y)$; if $U$ were affine, the inclusion $U \to \mathbb{A}^2_k$ would be an isomorphism.

### Notes and history

The spectrum with the Zariski topology and the structure sheaf is the work of Grothendieck in EGA, from 1960 to 1967; the topology carries the name of Zariski. The proof of the theorem on basic open sets follows Hartshorne, *Algebraic Geometry*, 1977, Proposition II.2.2. Buzzard, Commelin and Massot defined schemes in Lean in 2020 with the same sheaf of locally fractions.

The Mathlib Authors of `AlgebraicGeometry.StructureSheaf` are Johan Commelin, Kim Morrison and Andrew Yang. The Mathlib Authors of `AlgebraicGeometry.Spec` are Kim Morrison and Justus Springer. The Mathlib Author of `AlgebraicGeometry.GammaSpecAdjunction` is Junyan Xu. The Mathlib Author of `AlgebraicGeometry.AffineScheme` is Andrew Yang.

### Reference

<?reference?>
