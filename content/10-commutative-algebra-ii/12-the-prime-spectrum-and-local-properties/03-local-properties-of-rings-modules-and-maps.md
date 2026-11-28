---
title: Local properties of rings, modules and ring maps
kind: api
modules:
  - Mathlib.RingTheory.LocalProperties.Basic
  - Mathlib.RingTheory.LocalProperties.Submodule
  - Mathlib.RingTheory.LocalProperties.Exactness
  - Mathlib.RingTheory.LocalProperties.FinitePresentation
  - Mathlib.RingTheory.LocalProperties.Projective
  - Mathlib.RingTheory.LocalProperties.Injective
  - Mathlib.RingTheory.LocalProperties.ProjectiveDimension
  - Mathlib.RingTheory.LocalProperties.InjectiveDimension
  - Mathlib.RingTheory.LocalProperties.Reduced
  - Mathlib.RingTheory.LocalProperties.IntegrallyClosed
  - Mathlib.RingTheory.LocalProperties.Semilocal
  - Mathlib.RingTheory.RingHomProperties
  - Mathlib.RingTheory.LocalIso
  - Mathlib.RingTheory.SurjectiveOnStalks
explains:
  E2: [OfLocalizationMaximal, RingHom.PropertyIsLocal, RingHom.OfLocalizationSpanTarget, RingHom.RespectsIso, RingHom.IsStableUnderBaseChange, Submodule.mem_of_localization_maximal, exact_of_localized_maximal, Module.projective_of_localization_maximal, Algebra.IsLocalIso, RingHom.SurjectiveOnStalks]
  E1: auto
families: []
requires: [V09, V10.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Local properties of rings, modules and ring maps

### Overview

A property is local when it can be checked at each prime, or at each maximal ideal, or on a cover of $\operatorname{Spec} R$ by sets $D(f_i)$. Many properties are local in this sense. An element of a module is zero if it is zero in each $M_{\mathfrak m}$. A map is injective, surjective or exact if it is so after each localization at a maximal ideal. A finitely presented module is projective if it is free at each maximal ideal. A domain is integrally closed if each of its localizations is. For ring maps, the same idea gives the properties that algebraic geometry uses to glue local statements into global ones.

This section describes the local principle for elements, submodules and exact sequences, the local nature of finite presentation, projectivity and homological dimensions, the local properties of rings, the framework of properties of ring maps, local isomorphisms, and maps that are surjective on stalks.

### The library around it

#### Elements, submodules and exactness

The basic fact is that a module $M$ is zero if $M_{\mathfrak m} = 0$ for each maximal ideal $\mathfrak m$, `Module.subsingleton_of_localization_maximal` in `Mathlib.RingTheory.LocalProperties.Submodule`.

**Theorem.** Let $N$ be a submodule of $M$ and $m \in M$. If $m/1 \in N_{\mathfrak m}$ for each maximal ideal $\mathfrak m$, then $m \in N$. This is `Submodule.mem_of_localization_maximal`.

*Proof.* Put $I = \{r \in R : rm \in N\}$. This is an ideal. If $I \ne R$, then $I \subseteq \mathfrak m$ for a maximal ideal $\mathfrak m$. Since $m/1 \in N_{\mathfrak m}$, there are $n \in N$ and $s \notin \mathfrak m$ with $m/1 = n/s$, so $t(sm - n) = 0$ for some $t \notin \mathfrak m$. Then $tsm = tn \in N$ and $ts \in I \setminus \mathfrak m$, a contradiction. So $1 \in I$ and $m \in N$. $\square$

The companion forms are `Submodule.le_of_localization_maximal` for an inclusion of submodules and `Ideal.mem_of_localization_maximal` for ideals. The forms with the suffix isLocalized_span use a cover $D(f_i)$ in place of all maximal ideals, for instance `Submodule.mem_of_isLocalized_span`.

The module `Mathlib.RingTheory.LocalProperties.Exactness` proves the local nature of injectivity, surjectivity and exactness.

| Lean name | Statement |
|---|---|
| `injective_of_localized_maximal` | $f$ is injective if each $f_{\mathfrak m}$ is |
| `surjective_of_localized_maximal` | $f$ is surjective if each $f_{\mathfrak m}$ is |
| `bijective_of_localized_maximal` | the same for bijectivity |
| `exact_of_localized_maximal` | $M \to N \to L$ is exact if each localization is |
| `exact_of_localized_span` | the same on a cover $D(f_i)$ |
| `LinearIndependent.of_isLocalized_maximal` | linear independence is local |

Each result follows from the vanishing of a kernel, a cokernel or a homology module at each maximal ideal, since localization is exact.

#### Finiteness, projectivity and dimensions

1. `Module.FinitePresentation.of_localizationSpan` in `Mathlib.RingTheory.LocalProperties.FinitePresentation`: if $M_{f_i}$ is finitely presented over $R_{f_i}$ for a cover, then $M$ is finitely presented.
2. `Module.projective_of_localization_maximal` in `Mathlib.RingTheory.LocalProperties.Projective`: a finitely presented module whose localizations at maximal ideals are projective is projective. The proof uses `LinearMap.split_surjective_of_localization_maximal`: a surjection onto a finitely presented module splits if it splits at each maximal ideal.
3. `Module.injective_of_localization_maximal` in `Mathlib.RingTheory.LocalProperties.Injective`: over a Noetherian ring, a module whose localizations are injective is injective.
4. `ModuleCat.projectiveDimension_eq_iSup_localizedModule_prime` in `Mathlib.RingTheory.LocalProperties.ProjectiveDimension`: for a finitely generated module over a Noetherian ring, the projective dimension is the supremum of the projective dimensions of the localizations. The maximal form is `ModuleCat.projectiveDimension_eq_iSup_localizedModule_maximal`.
5. `ModuleCat.injectiveDimension_eq_iSup_localizedModule_prime` in `Mathlib.RingTheory.LocalProperties.InjectiveDimension`: the same for injective dimension over a Noetherian ring.

For a ring with finitely many maximal ideals, more properties are local. The module `Mathlib.RingTheory.LocalProperties.Semilocal` proves that a module is finitely generated, `Module.Finite.of_localized_maximal`, a ring is Noetherian, `IsNoetherianRing.of_isLocalization_maximal`, and a domain is a principal ideal ring, `isPrincipalIdealRing_of_isPrincipalIdealRing_isLocalization_maximal`, when this holds at each maximal ideal.

#### Properties of rings

The module `Mathlib.RingTheory.LocalProperties.Basic` defines predicates on properties $P$ of rings.

1. `LocalizationPreserves P`: $P$ passes from $R$ to each localization $S^{-1}R$.
2. `OfLocalizationMaximal P`: $P$ holds for $R$ if it holds for each $R_{\mathfrak m}$.

Reducedness has both properties, `isReduced_localizationPreserves` and `isReduced_ofLocalizationMaximal` in `Mathlib.RingTheory.LocalProperties.Reduced`. A domain is integrally closed if each localization at a maximal ideal is, `IsIntegrallyClosed.of_localization_maximal` in `Mathlib.RingTheory.LocalProperties.IntegrallyClosed`. The proof uses `IsIntegrallyClosed.of_iInf_eq_bot`: a domain that is the intersection of integrally closed subrings of its fraction field is integrally closed, and $R = \bigcap R_{\mathfrak m}$ in the fraction field.

#### Properties of ring maps

A property of ring maps is a predicate $P(f)$ for $f : R \to S$. The same module and `Mathlib.RingTheory.RingHomProperties` give the conditions that a good property satisfies.

| Lean name | Statement |
|---|---|
| `RingHom.RespectsIso` | $P$ is invariant under composition with isomorphisms |
| `RingHom.StableUnderComposition` | $P(f)$ and $P(g)$ give $P(g \circ f)$ |
| `RingHom.IsStableUnderBaseChange` | $P(R \to S)$ gives $P(T \to T \otimes_R S)$ |
| `RingHom.HoldsForLocalizationAway` | $P$ holds for $R \to R_r$ |
| `RingHom.LocalizationPreserves` | $P(f)$ gives $P(S^{-1}f)$ |
| `RingHom.OfLocalizationSpan` | $P$ holds if it holds for $R_{r_i} \to S_{r_i}$ for a cover of $\operatorname{Spec} R$ |
| `RingHom.OfLocalizationSpanTarget` | $P$ holds if it holds for $R \to S_{s_i}$ for a cover of $\operatorname{Spec} S$ |
| `RingHom.OfLocalizationPrime` | $P$ holds if it holds for $R_{\mathfrak p} \to S_{\mathfrak q}$ at all primes |
| `RingHom.CodescendsAlong` | $P$ descends from a base change along maps with another property $Q$ |

The structure `RingHom.PropertyIsLocal P` collects the conditions that make $P$ local on the source and on the target: it is preserved by localization, it holds when it holds on a cover of the source or of the target, and it is stable under composition with $S \to S_s$. In algebraic geometry, such a $P$ defines a property of morphisms of schemes that can be checked on affine open covers. The property of being of finite type is an example. The bridge to category theory is `RingHom.toMorphismProperty`.

#### Local isomorphisms

The class `Algebra.IsLocalIso R S` in `Mathlib.RingTheory.LocalIso` says that $\operatorname{Spec} S \to \operatorname{Spec} R$ is locally an open immersion. By `Algebra.isLocalIso_iff`, each prime $\mathfrak q$ of $S$ has $g \notin \mathfrak q$ such that $S_g$ is a standard open immersion over $R$, that is, $S_g \cong R_r$ for some $r$. The class is stable under composition, `Algebra.IsLocalIso.trans`, and it holds for finite products, `Algebra.IsLocalIso.pi_of_finite`.

#### Maps that are surjective on stalks

The predicate `RingHom.SurjectiveOnStalks f` in `Mathlib.RingTheory.SurjectiveOnStalks` says that $R_{\mathfrak p} \to S_{\mathfrak q}$ is surjective for each prime $\mathfrak q$ of $S$ over $\mathfrak p$. Surjections and localizations have the property, `RingHom.surjectiveOnStalks_of_surjective` and `RingHom.surjectiveOnStalks_of_isLocalization`. It is enough to check maximal ideals, `RingHom.surjectiveOnStalks_iff_forall_maximal`. The property is stable under composition, `RingHom.SurjectiveOnStalks.comp`, and base change, `RingHom.SurjectiveOnStalks.baseChange`. The prime spectrum of $S \otimes_R T$ embeds into the product of the spectra when $R \to T$ has this property, as in Section 2.

#### Common errors

1. `Module.projective_of_localization_maximal` needs `Module.FinitePresentation R M`. A module that is free at each maximal ideal need not be projective without it.
2. `Submodule.mem_of_localization_maximal` and the other lemmas with the suffix localization_maximal quantify over all maximal ideals. The lemmas with the suffix localized_span take a set that generates the unit ideal, for a finite cover by sets $D(f_i)$.
3. `RingHom.OfLocalizationSpan` localizes the source and the target at the same elements of $R$. `RingHom.OfLocalizationSpanTarget` localizes only the target, at elements of $S$.

### Exercises

1. (A) Show that an element $x$ of $R$ is $0$ if $x/1 = 0$ in $R_{\mathfrak m}$ for each maximal ideal $\mathfrak m$.
2. (A) Use `injective_of_localized_maximal` to show that a map of modules over a field that is injective after localization is injective, and explain why this case is trivial.
3. (B) Prove `surjective_of_localized_maximal` from the vanishing of the cokernel at each maximal ideal.
4. (B) Show that the property of being surjective respects isomorphisms, is stable under composition and is stable under base change.
5. (B) Let $R = \prod_{n \in \mathbb{N}} \mathbb{F}_2$. Show that each localization of $R$ at a maximal ideal is $\mathbb{F}_2$, and that $R$ is not Noetherian. Explain why this does not contradict `IsNoetherianRing.of_isLocalization_maximal`.
6. (C) Show that $\mathbb{Z} \to \mathbb{Z}[1/2] \times \mathbb{Z}[1/3]$ is a local isomorphism.

### Reference

<?reference?>
