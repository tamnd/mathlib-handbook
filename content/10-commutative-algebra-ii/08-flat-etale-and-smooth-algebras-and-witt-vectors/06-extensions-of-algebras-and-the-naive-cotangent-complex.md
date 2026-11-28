---
title: Extensions of algebras and the naive cotangent complex
kind: api
modules:
  - Mathlib.RingTheory.Extension.Basic
  - Mathlib.RingTheory.Extension.Cotangent.Basic
  - Mathlib.RingTheory.Extension.Cotangent.BaseChange
  - Mathlib.RingTheory.Extension.Cotangent.Basis
  - Mathlib.RingTheory.Extension.Cotangent.Free
  - Mathlib.RingTheory.Extension.Cotangent.LocalizationAway
  - Mathlib.RingTheory.Extension.ExtendScalars
explains:
  E2: [Algebra.Extension, Algebra.Extension.Cotangent, Algebra.Extension.cotangentComplex, Algebra.Extension.H1Cotangent, Algebra.Extension.exact_cotangentComplex_toKaehler, Algebra.Extension.H1Cotangent.map_eq, Algebra.Extension.tensorCotangentSpace, Algebra.Generators.cotangentCompLocalizationAwayEquiv, Algebra.Extension.h1CotangentEquivCotangent]
  E1: auto
families: []
requires: [V08, V09, V10.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Extensions of algebras and the naive cotangent complex

### Overview

Let $S$ be an $R$-algebra. An extension of $S$ is a surjection $P \to S$ of $R$-algebras, with kernel $I$. The typical case is a polynomial ring $P = R[X_i]$ that maps onto $S$. From an extension the library builds a short complex of $S$-modules, the naive cotangent complex
$$I/I^2 \xrightarrow{\ d\ } S \otimes_P \Omega_{P/R} \longrightarrow \Omega_{S/R} \longrightarrow 0.$$
The sequence is exact at the two right terms. The kernel of $d$ is the first homology $H_1$. Section 2 of this chapter uses $H_1$ to define smooth and étale algebras: $S$ is formally smooth when $\Omega_{S/R}$ is projective and $H_1 = 0$.

The modules in `Mathlib/RingTheory/Extension/` give the type of extensions, the maps between them, the complex above with its functoriality, and its behaviour under base change and localization. The next section uses these results for the special extensions that come from generators and presentations. A reader needs this API to prove that a given algebra is smooth or étale, or to compute $H_1$ in an example.

### The library around it

#### Extensions and their maps

The structure `Algebra.Extension R S` has a field `Ring`, the ring $P$, with instances `Algebra.Extension.commRing`, `Algebra.Extension.algebra₁` for the $R$-algebra structure and `Algebra.Extension.algebra₂` for the $P$-algebra structure of $S$, and the scalar tower $R \to P \to S$. The surjectivity is not a field. Instead the structure has a set map `Algebra.Extension.σ : S → P.Ring` with `Algebra.Extension.algebraMap_σ`, so $\sigma$ is a section of $P \to S$. The lemma `Algebra.Extension.algebraMap_surjective` then gives the surjectivity. The section is a choice of data, which makes some later constructions computable on the nose.

There are several ways to build an extension.

| Lean name | Extension |
|---|---|
| `Algebra.Extension.ofSurjective` | a surjective $R$-algebra map $f : P \to S$ |
| `Algebra.Extension.self` | the identity $S \to S$, with $I = 0$ |
| `Algebra.Extension.infinitesimal` | $P/I^2 \to S$, with kernel $I/I^2$ |
| `Algebra.Extension.baseChange` | $T \otimes_R P \to T \otimes_R S$ for an $R$-algebra $T$ |
| `Algebra.Extension.localization` | the localization of $P$ at the preimage of a submonoid of $S$ |
| `Algebra.Extension.extendScalars` | $P \to S$ seen as an extension over $P$ itself |

The kernel is `Algebra.Extension.ker`, an ideal of $P$. The lemmas `Algebra.Extension.ker_infinitesimal` and `Algebra.Extension.ker_baseChange` compute it for two of the constructions. For an extension $P \to S$ over $R$ and an extension $P' \to S'$ over $R'$, a map `Algebra.Extension.Hom P P'` is a ring map $P \to P'$ that makes both squares commute, over given maps $R \to R'$ and $S \to S'$. The library has `Algebra.Extension.Hom.id`, `Algebra.Extension.Hom.comp`, `Algebra.Extension.Hom.toAlgHom` and the constructor `Algebra.Extension.Hom.ofAlgHom`. The maps `Algebra.Extension.toInfinitesimal` and `Algebra.Extension.toBaseChange` are the canonical maps to the infinitesimal and base change extensions.

#### The cotangent module and the cotangent space

The cotangent module of $P$ is `Algebra.Extension.Cotangent P`, the module $I/I^2$. It is a copy of the module `Ideal.Cotangent` of the kernel, with the equivalence `Algebra.Extension.cotangentEquivCotangentKer`. The copy carries an $S$-module structure, `Algebra.Extension.Cotangent.module`; the module $I/I^2$ is killed by $I$, so the $P$-action descends to $S = P/I$. The class of $x \in I$ is `Algebra.Extension.Cotangent.mk x`, and the value in `Ideal.Cotangent` is `Algebra.Extension.Cotangent.val`. Two lemmas are used often:

1. `Algebra.Extension.Cotangent.mk_eq_zero_iff`: the class of $x$ is $0$ if and only if $x \in I^2$.
2. `Algebra.Extension.Cotangent.span_eq_top_of_span_eq_ker`: generators of $I$ give generators of $I/I^2$ as an $S$-module. So `Algebra.Extension.Cotangent.finite` says that $I/I^2$ is finite when $I$ is finitely generated.

The cotangent space is `Algebra.Extension.CotangentSpace P`, the module $S \otimes_P \Omega_{P/R}$. For a polynomial ring $P = R[X_i]$ it is free with basis $1 \otimes dX_i$, given by `Algebra.Generators.cotangentSpaceBasis`. The two maps of the complex are `Algebra.Extension.cotangentComplex`, which sends the class of $x$ to $1 \otimes dx$, and `Algebra.Extension.toKaehler`, the map $S \otimes_P \Omega_{P/R} \to \Omega_{S/R}$ induced by $P \to S$.

**Proposition.** The sequence $I/I^2 \to S \otimes_P \Omega_{P/R} \to \Omega_{S/R} \to 0$ is exact.

*Proof.* The map $\Omega_{P/R} \to \Omega_{S/R}$ is surjective, since $S$ is generated by the image of $P$. So `Algebra.Extension.toKaehler` is surjective. For exactness in the middle, $\Omega_{S/R}$ is the quotient of $\Omega_{P/R}$ by the relations $d(x)$ with $x \in I$ and $x \cdot \omega$ with $x \in I$. After the tensor product with $S$ the second kind of relation vanishes. So the kernel of the map to $\Omega_{S/R}$ is the image of the elements $1 \otimes dx$, $x \in I$, which is the image of $d$. $\square$

The two statements are `Algebra.Extension.toKaehler_surjective` and `Algebra.Extension.exact_cotangentComplex_toKaehler`. The first homology `Algebra.Extension.H1Cotangent P` is the kernel of `Algebra.Extension.cotangentComplex`, with the inclusion `Algebra.Extension.h1Cotangentι`. The lemma `Algebra.Extension.exact_hCotangentι_cotangentComplex` records the exactness, and `Algebra.Extension.subsingleton_h1Cotangent` says that $H_1 = 0$ if and only if $d$ is injective.

#### Functoriality and independence of the choice

A map of extensions $f : P \to P'$ induces maps on the three terms: `Algebra.Extension.Cotangent.map`, `Algebra.Extension.CotangentSpace.map` and `Algebra.Extension.H1Cotangent.map`. They commute with the maps of the complex, for example `Algebra.Extension.CotangentSpace.map_cotangentComplex`.

**Proposition.** Let $f, g : P \to P'$ be two maps of extensions over the same maps $R \to R'$ and $S \to S'$. Then $f$ and $g$ induce the same map $H_1(P) \to H_1(P')$.

*Proof.* For $x \in P$, the element $f(x) - g(x)$ lies in $I'$, because $f$ and $g$ agree after the map to $S'$. The map $x \mapsto f(x) - g(x) \bmod I'^2$ is a derivation $P \to I'/I'^2$ over $R$. So it induces an $S$-linear map $h : S \otimes_P \Omega_{P/R} \to I'/I'^2$. On $I/I^2$, the maps satisfy $\mathrm{Cot}(f) - \mathrm{Cot}(g) = h \circ d$. On the kernel of $d$ the right side is $0$. $\square$

The homotopy $h$ is `Algebra.Extension.Hom.sub`, and the identity is `Algebra.Extension.Cotangent.map_sub_map`. The proposition is `Algebra.Extension.H1Cotangent.map_eq`. As a consequence, two extensions with maps in both directions have isomorphic $H_1$, by `Algebra.Extension.H1Cotangent.equiv`. A polynomial extension has a map to every other extension, so $H_1$ does not depend on the choice of a polynomial ring. The library takes the extension $R[S] \to S$ with one variable for each element of $S$, and defines `Algebra.H1Cotangent R S` as its $H_1$. For any extension $P$, the map `Algebra.Extension.defaultHom R S P` from $R[S]$ to $P$ gives the comparison. The maps between algebras are `Algebra.H1Cotangent.map` and `Algebra.H1Cotangent.mapEquiv`. For generators $P$, the comparison is an isomorphism, `Algebra.Generators.equivH1Cotangent`.

#### Base change

Let $T$ be an $R$-algebra. The base change $T \otimes_R P \to T \otimes_R S$ is again an extension. The module `Mathlib.RingTheory.Extension.Cotangent.BaseChange` compares the terms of the complex.

| Lean name | Statement |
|---|---|
| `Algebra.Extension.tensorCotangentSpace` | $T \otimes_R (S \otimes_P \Omega_{P/R}) \cong$ the cotangent space of the base change |
| `Algebra.Extension.tensorCotangentOfFlat` | $T \otimes_R I/I^2 \cong$ the cotangent module of the base change, for $T$ flat |
| `Algebra.Extension.tensorH1CotangentOfFlat` | $T \otimes_R H_1(P) \cong H_1$ of the base change, for $T$ flat |
| `Algebra.tensorH1CotangentOfFlat` | $T \otimes_R H_1(S/R) \cong H_1(T \otimes_R S / T)$, for $T$ flat |
| `Algebra.Extension.tensorToH1Cotangent_bijective_of_flat` | the comparison map is bijective, for $T$ flat |

The cotangent space commutes with every base change, because $\Omega$ does. For $I/I^2$ and $H_1$ the proofs need flatness: $T \otimes_R -$ must keep the kernel of $P \to S$ and the kernel of $d$.

#### Localization away from an element

Let $S$ be generated over $R$ by a polynomial ring $P = R[X]$ with kernel $I$, and let $T = S_g$. Then $T = S[Y]/(gY - 1)$, and the composite presentation $R[X, Y] \to T$ has kernel $J$. The module `Mathlib.RingTheory.Extension.Cotangent.LocalizationAway` proves
$$J/J^2 \cong (T \otimes_S I/I^2) \times K/K^2,$$
where $K = (gY - 1)$ is the kernel of $S[Y] \to T$. This is `Algebra.Generators.cotangentCompLocalizationAwayEquiv`. The proof shows that $0 \to T \otimes_S I/I^2 \to J/J^2 \to K/K^2 \to 0$ is exact, and $K/K^2$ is free of rank one on the class of $gY - 1$, so the sequence splits. The kernel $J$ is described by `Algebra.Generators.comp_localizationAway_ker`: it is generated by $I$ and $gY - 1$. The injectivity on the left is `Algebra.Generators.liftBaseChange_injective_of_isLocalizationAway`.

#### Extension of scalars and bases

The module `Mathlib.RingTheory.Extension.ExtendScalars` regards $P \to S$ as an extension of $S$ over $P$, `Algebra.Extension.extendScalars`. Over $P$ the cotangent space is $0$, since $\Omega_{P/P} = 0$. So all of $I/I^2$ is $H_1$: `Algebra.Extension.h1CotangentEquivOfSurjective` gives $H_1 \cong I/I^2$ for an extension with surjective structure map $R \to P$. The isomorphism `Algebra.Extension.h1CotangentEquivCotangent` identifies `Algebra.H1Cotangent P.Ring S` with $I/I^2$. The lemma `Algebra.Extension.cotangentComplex_comp_h1CotangentEquivCotangent` says that, under this identification, the map $d$ of $P$ is the boundary map of the Jacobi-Zariski sequence of $R \to P \to S$. The equivalences `Algebra.Extension.cotangentExtendScalarsEquiv` and `Algebra.Extension.h1CotangentExtendScalarsEquiv` compare the terms for $P$ and for the extension over $P$.

The modules `Mathlib.RingTheory.Extension.Cotangent.Basis` and `Mathlib.RingTheory.Extension.Cotangent.Free` work with bases. Let $S$ be finitely presented, with finite generators $P$. If $I/I^2$ is free, then `Algebra.Generators.exists_presentation_of_free_cotangent` gives a presentation with the same generators and one more, such that the images of the relations form a basis of the new $I'/I'^2$. The general form is `Algebra.Generators.exists_presentation_of_basis_cotangent`. The restricted map `Algebra.Generators.cotangentRestrict` composes $d$ with the projection to the coordinates $dX_{u(j)}$ of a subset of the variables. The lemma `Algebra.Generators.cotangentRestrict_bijective_of_basis_kaehlerDifferential` says that it is bijective when the other variables give a basis of $\Omega_{S/R}$ and $H_1(S/R) = 0$. Then `Algebra.PreSubmersivePresentation.isUnit_jacobian_of_cotangentRestrict_bijective` concludes that the presentation is submersive, in the sense of the next section.

#### Common errors

1. `Algebra.Extension.Cotangent P` is a copy of the `Ideal.Cotangent` of the kernel, not the same type. The $S$-module structure is on the copy. Use `Algebra.Extension.Cotangent.mk` and `Algebra.Extension.Cotangent.val` to move between them.
2. `Algebra.H1Cotangent R S` is defined with one fixed extension. For another extension $P$, the module $H_1(P)$ is only isomorphic to it, through `Algebra.Extension.H1Cotangent.equiv` or `Algebra.Generators.equivH1Cotangent`.
3. The base change results for $I/I^2$ and $H_1$ need `Module.Flat R T`. Only the cotangent space commutes with an arbitrary base change.

### Exercises

1. (A) For $S = R[X]/(f)$ and $P = R[X]$, show that $I/I^2$ is generated by the class of $f$, and that $d$ sends it to $f' \, dX$.
2. (A) Show that the extension `Algebra.Extension.self R S` has $I = 0$, and deduce that its cotangent module is $0$.
3. (B) For $S = k[X]/(X^2)$ over a field $k$ of characteristic not $2$, compute $I/I^2$ and the map $d$, and show that $H_1 \cong k$.
4. (B) For $S = k[X]/(X^2)$ over a field of characteristic $2$, show that $d = 0$ and $H_1 \cong S$.
5. (B) Prove that $H_1(S_g/S) = 0$ for a localization away from $g$, using $S_g = S[Y]/(gY - 1)$.
6. (B) Let $S = R[X]/(f)$, where $f$ is a nonzerodivisor of $R[X]$. Show that $I/I^2$ is free of rank one, and that $H_1$ is the annihilator of $f'(x)$ in $S$, where $x$ is the class of $X$.

### Reference

<?reference?>
