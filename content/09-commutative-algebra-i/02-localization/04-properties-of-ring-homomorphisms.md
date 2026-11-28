---
title: Properties of ring homomorphisms
kind: api
modules:
  - Mathlib.RingTheory.RingHom.Bijective
  - Mathlib.RingTheory.RingHom.Injective
  - Mathlib.RingTheory.RingHom.Surjective
  - Mathlib.RingTheory.RingHom.Finite
  - Mathlib.RingTheory.RingHom.FiniteType
  - Mathlib.RingTheory.RingHom.FinitePresentation
  - Mathlib.RingTheory.RingHom.EssFiniteType
  - Mathlib.RingTheory.RingHom.Integral
  - Mathlib.RingTheory.RingHom.QuasiFinite
  - Mathlib.RingTheory.RingHom.PurelyInseparable
  - Mathlib.RingTheory.RingHom.Locally
  - Mathlib.RingTheory.RingHom.Flat
  - Mathlib.RingTheory.RingHom.FaithfullyFlat
  - Mathlib.RingTheory.RingHom.Unramified
  - Mathlib.RingTheory.RingHom.Smooth
  - Mathlib.RingTheory.RingHom.StandardSmooth
  - Mathlib.RingTheory.RingHom.LocallyStandardSmooth
  - Mathlib.RingTheory.RingHom.Etale
  - Mathlib.RingTheory.RingHom.OpenImmersion
explains:
  E2: [RingHom.locally_iff_of_localizationSpanTarget, RingHom.FaithfullyFlat.iff_flat_and_comap_surjective, RingHom.Etale.iff_flat_and_formallyUnramified, RingHom.FormallyUnramified.of_surjective, RingHom.QuasiFinite.of_finite, RingHom.Flat.of_isField]
  E1: auto
families: []
requires: [V06.C02, V09.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Properties of ring homomorphisms

### Overview

An algebra $S$ over a commutative ring $R$ is the same thing as a ring homomorphism $f : R \to S$. Mathlib states most finiteness and flatness conditions for algebras, as classes such as `Algebra.FiniteType` or `Module.Flat`. Algebraic geometry needs the same conditions for homomorphisms, because a morphism of affine schemes is a homomorphism of rings in the other direction. The modules `Mathlib.RingTheory.RingHom.*` translate each condition into a predicate on `R →+* S`, and they prove the formal properties that the theory of schemes uses: stability under composition, under base change and under localization.

The section uses the localizations of Sections 1 to 3. The definitions of flat, smooth and étale algebras belong to Volume 10. Here they appear only through their translations to ring homomorphisms, and the text states what the library proves about these translations.

### The library around it

**The translation.** For each property of algebras there is a predicate on ring homomorphisms. The predicate holds for $f$ when the property holds for the algebra structure on $S$ that $f$ defines, that is `RingHom.toAlgebra f`. The predicates are `RingHom.Finite`, `RingHom.FiniteType`, `RingHom.FinitePresentation`, `RingHom.EssFiniteType`, `RingHom.IsIntegral`, `RingHom.QuasiFinite`, `RingHom.IsPurelyInseparable`, `RingHom.Flat`, `RingHom.FaithfullyFlat`, `RingHom.FormallyUnramified`, `RingHom.FormallySmooth`, `RingHom.Smooth`, `RingHom.IsStandardSmooth`, `RingHom.Etale` and `RingHom.IsStandardOpenImmersion`. A lemma on the structure map goes back: it says that the predicate holds for the structure map $R \to S$ of an algebra exactly when the algebra class holds. Examples are `RingHom.flat_algebraMap_iff`, `RingHom.faithfullyFlat_algebraMap_iff`, `RingHom.smooth_algebraMap`, `RingHom.etale_algebraMap`, `RingHom.formallySmooth_algebraMap`, `RingHom.formallyUnramified_algebraMap`, `RingHom.quasiFinite_algebraMap` and `RingHom.isPurelyInseparable_algebraMap_iff`. In the other direction, lemmas such as `RingHom.Smooth.toAlgebra`, `RingHom.Etale.toAlgebra` and `RingHom.QuasiFinite.toAlgebra` give the algebra class from the predicate. Many of the predicates carry the attribute algebraize, so the tactic algebraize makes the passage automatically inside a proof.

**The meta-properties.** A property $P$ of ring homomorphisms is itself a variable of type `∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop`. The files `Mathlib.RingTheory.RingHomProperties` and `Mathlib.RingTheory.LocalProperties.Basic` define the conditions on such a $P$ that the theory of schemes needs.

| Lean name | Condition on $P$ |
|---|---|
| `RingHom.RespectsIso` | $P(f)$ implies $P(e \circ f)$ and $P(f \circ e)$ for every ring isomorphism $e$ |
| `RingHom.StableUnderComposition` | $P(f)$ and $P(g)$ imply $P(g \circ f)$ |
| `RingHom.ContainsIdentities` | $P(\mathrm{id}_R)$ holds for every ring $R$ |
| `RingHom.IsStableUnderBaseChange` | $P(R \to S)$ implies $P(T \to T \otimes_R S)$ |
| `RingHom.LocalizationPreserves` | $P(R \to S)$ implies $P(M^{-1} R \to M^{-1} S)$ |
| `RingHom.HoldsForLocalizationAway` | $P(R \to R_r)$ holds for every $r$ |
| `RingHom.OfLocalizationSpan` | if $(r_i)$ generates $R$ and every $R_{r_i} \to S_{r_i}$ has $P$, then $f$ has $P$ |
| `RingHom.OfLocalizationSpanTarget` | if $(s_i)$ generates $S$ and every $R \to S_{s_i}$ has $P$, then $f$ has $P$ |
| `RingHom.PropertyIsLocal` | a structure that collects the localization conditions |

Each file of the family then proves these conditions for its own predicate. The names follow one pattern, with the property in front: `RingHom.finite_stableUnderComposition`, `RingHom.finite_isStableUnderBaseChange`, `RingHom.finite_localizationPreserves`, `RingHom.finite_ofLocalizationSpan`, `RingHom.finiteType_isLocal`, `RingHom.finitePresentation_isLocal`, `RingHom.isIntegral_stableUnderComposition`. The newer files put the property in a namespace instead: `RingHom.Flat.stableUnderComposition`, `RingHom.Flat.propertyIsLocal`, `RingHom.Etale.propertyIsLocal`, `RingHom.Smooth.propertyIsLocal`, `RingHom.FormallyUnramified.propertyIsLocal`, `RingHom.QuasiFinite.propertyIsLocal`. A reader who needs a meta-property of a predicate can guess the name in one of the two forms and look it up.

**Bijective, injective and surjective maps.** There is no special predicate for these maps: $P$ is `fun f ↦ Function.Bijective f`, and so on. The files `Mathlib.RingTheory.RingHom.Bijective`, `Mathlib.RingTheory.RingHom.Injective` and `Mathlib.RingTheory.RingHom.Surjective` prove the meta-properties for these $P$, for example `RingHom.Bijective.ofLocalizationSpan`, `RingHom.Bijective.isStableUnderBaseChange`, `RingHom.injective_stableUnderComposition`, `RingHom.surjective_ofLocalizationSpan` and `RingHom.surjective_isStableUnderBaseChange`. The lemma `RingHom.surjective_localRingHom_of_surjective` says that a surjection $f : R \to S$ induces a surjection $R_{f^{-1}(\mathfrak{P})} \to S_{\mathfrak{P}}$ for each prime $\mathfrak{P}$ of $S$.

**Finiteness.** The files on `RingHom.Finite`, `RingHom.FiniteType`, `RingHom.FinitePresentation` and `RingHom.EssFiniteType` follow the same plan. The lemmas `RingHom.localization_away_map_finite` and `RingHom.localization_away_map_finiteType` state that finiteness passes to the map $R_r \to S_{f(r)}$. For essentially finite type maps there are also `RingHom.EssFiniteType.comp`, `RingHom.EssFiniteType.of_comp`, `RingHom.EssFiniteType.comp_iff` and `RingHom.EssFiniteType.residueFieldMap`. The integral maps of `Mathlib.RingTheory.RingHom.Integral` satisfy `RingHom.isIntegral_ofLocalizationSpan`. A quasi-finite map has finite fibres in the sense of Volume 10, and `RingHom.QuasiFinite.of_finite` proves that a finite map is quasi-finite. The lemma `RingHom.QuasiFinite.of_isIntegral_of_finiteType` handles a composition $g \circ f$ where $f$ is integral, $g$ is a standard open immersion and $g \circ f$ is of finite type. The predicate `RingHom.IsPurelyInseparable` of `Mathlib.RingTheory.RingHom.PurelyInseparable` translates the purely inseparable extensions of Volume 11, with the lemmas `RingHom.IsPurelyInseparable.id` and `RingHom.IsPurelyInseparable.comp`.

**Properties that hold locally.** The file `Mathlib.RingTheory.RingHom.Locally` defines `RingHom.Locally P f`. It holds when there is a set $\{t_i\}$ that generates the unit ideal of $S$ such that $P$ holds for each composition $R \to S \to S_{t_i}$. The lemma `RingHom.locally_iff_finite` says that a finite set is enough. The lemma `RingHom.locally_of` says that $P(f)$ implies `RingHom.Locally P f` when $P$ respects isomorphisms. The proof takes the set $\{1\}$: the map $S \to S_1$ is an isomorphism. The lemma `RingHom.locally_iff_of_localizationSpanTarget` says that the two conditions are equivalent when $P$ also satisfies `RingHom.OfLocalizationSpanTarget`, because that condition is exactly the converse. The file then proves that `RingHom.Locally P` keeps the meta-properties of $P$: `RingHom.locally_respectsIso`, `RingHom.locally_stableUnderComposition`, `RingHom.locally_isStableUnderBaseChange` and `RingHom.locally_propertyIsLocal`.

**Flat and faithfully flat maps.** A ring homomorphism $f$ is flat, `RingHom.Flat`, when $S$ is a flat $R$-module. The file proves that the identity and every bijection are flat (`RingHom.Flat.id`, `RingHom.Flat.of_bijective`), that flat maps compose (`RingHom.Flat.comp`), and that flatness is local (`RingHom.Flat.propertyIsLocal`). The lemma `RingHom.Flat.localRingHom` gives a flat map $R_{\mathfrak{q}} \to S_{\mathfrak{P}}$ for each prime $\mathfrak{P}$ of $S$ over $\mathfrak{q}$. Every map out of a field is flat: this is `RingHom.Flat.of_isField`, because every module over a field is free. The lemma `RingHom.Flat.generalizingMap_comap` says that the map `PrimeSpectrum.comap f` of Section 3 lifts generalizations: this is the going down property of flat maps. A faithfully flat map, `RingHom.FaithfullyFlat`, is a flat map with a surjective map on spectra:
$$f \text{ faithfully flat} \iff f \text{ flat and } \operatorname{Spec} S \to \operatorname{Spec} R \text{ surjective}.$$
This is `RingHom.FaithfullyFlat.iff_flat_and_comap_surjective`. A faithfully flat map is injective, `RingHom.FaithfullyFlat.injective`.

**Unramified, smooth and étale maps.** The predicate `RingHom.FormallyUnramified` translates `Algebra.FormallyUnramified`: the module of Kähler differentials $\Omega_{S/R}$ is zero. A surjection is formally unramified, `RingHom.FormallyUnramified.of_surjective`, because for $S = R/I$ every element of $S$ is the image of an element of $R$, so every derivation $S \to M$ over $R$ is zero. The predicate `RingHom.Smooth` is the conjunction of formal smoothness and finite presentation, by `RingHom.smooth_def`. The predicate `RingHom.Etale` has the characterization
$$f \text{ étale} \iff f \text{ flat, formally unramified and of finite presentation},$$
which is `RingHom.Etale.iff_flat_and_formallyUnramified`. The lemma `RingHom.etale_iff_formallyUnramified_and_smooth` says that the étale maps are the smooth maps that are formally unramified.

**Standard smooth maps.** A standard smooth map is a map $R \to R[X_1, \ldots, X_n]/(f_1, \ldots, f_m)$ whose Jacobian determinant is invertible in the quotient. The file `Mathlib.RingTheory.RingHom.StandardSmooth` defines `RingHom.IsStandardSmooth` and `RingHom.IsStandardSmoothOfRelativeDimension`, with the relative dimension $n - m$ as a parameter. The lemma `RingHom.IsStandardSmooth.exists_etale_mvPolynomial` factors a standard smooth map through an étale map out of a polynomial ring. The file `Mathlib.RingTheory.RingHom.LocallyStandardSmooth` connects the two notions: `RingHom.IsStandardSmooth.smooth` says that a standard smooth map is smooth, and `RingHom.smooth_iff_locally_isStandardSmooth` says that a smooth map is locally standard smooth. The lemma `RingHom.etale_iff_isStandardSmoothOfRelativeDimension_zero` describes étale maps as the maps that are locally standard smooth of relative dimension zero.

**Standard open immersions.** A standard open immersion is a localization map $R \to R_r$ for some $r \in R$, up to isomorphism. The file `Mathlib.RingTheory.RingHom.OpenImmersion` defines the class `Algebra.IsStandardOpenImmersion` and the predicate `RingHom.IsStandardOpenImmersion`. The lemma `Algebra.isStandardOpenImmersion_iff` says that $S$ is a standard open immersion over $R$ exactly when `IsLocalization.Away r S` holds for some $r$. The class is stable under composition, `Algebra.IsStandardOpenImmersion.trans`, and under base change, `Algebra.IsStandardOpenImmersion.instTensorProduct`. On spectra, $R \to R_r$ is the inclusion of the basic open set $D(r)$ of Section 3, so these maps are the affine open immersions of algebraic geometry.

#### Common errors

1. A predicate on `R →+* S` and an algebra class are different objects. A goal `RingHom.Flat f` does not close with an instance of `Module.Flat` unless the algebra structure is `RingHom.toAlgebra f`. Use the lemmas on the structure map or the tactic algebraize to pass from one to the other.
2. The meta-properties quantify over all rings in one universe. A lemma such as `RingHom.locally_iff_finite` needs the two rings in the same universe, and a property stated for `Type*` must be used at a fixed universe.
3. `RingHom.OfLocalizationSpan` and `RingHom.OfLocalizationSpanTarget` are different conditions. The first localizes both rings at elements of $R$, the second localizes only $S$ at elements of $S$. Check which one a lemma needs before applying it.

### Exercises

1. (A) Prove that the identity of a ring $R$ is finite, flat and étale, and find the lemmas of the library that state these facts.
2. (A) Let $f : R \to S$ be surjective. Prove that $f$ is of finite type and formally unramified, and that it is flat when $R$ is a field.
3. (B) Let $f : R \to S$ be flat. Use the going down property `RingHom.Flat.generalizingMap_comap` to prove that the image of $\operatorname{Spec} S \to \operatorname{Spec} R$ is closed under generalization. Deduce that if $R$ is a domain and $S \neq 0$, then the zero ideal of $R$ is in the image.
4. (B) Prove that $\mathbb{Z} \to \mathbb{Z}[1/2] \times \mathbb{Z}_{(2)}$ is faithfully flat but not a localization of $\mathbb{Z}$ at one element.
5. (B) Show that `RingHom.Locally P` implies $P$ when $P$ satisfies `RingHom.OfLocalizationSpanTarget`, and give the proof of `RingHom.locally_of` in your own words.
6. (C) Prove that the map $\mathbb{Z} \to \mathbb{Z}[X]/(X^2 - 2)$ is not étale, and that $\mathbb{Z}[1/6] \to \mathbb{Z}[1/6][X]/(X^2 - 3)$ is étale. Use the characterization `RingHom.Etale.iff_flat_and_formallyUnramified`.

### Reference

<?reference?>
