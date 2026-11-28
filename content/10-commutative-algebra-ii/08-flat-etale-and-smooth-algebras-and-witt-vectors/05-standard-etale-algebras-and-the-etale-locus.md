---
title: Standard étale algebras, the étale locus and finite étale algebras
kind: api
modules:
  - Mathlib.RingTheory.Etale.Descent
  - Mathlib.RingTheory.Etale.Finite
  - Mathlib.RingTheory.Etale.Kaehler
  - Mathlib.RingTheory.Etale.Locus
  - Mathlib.RingTheory.Etale.Pi
  - Mathlib.RingTheory.Etale.QuasiFinite
  - Mathlib.RingTheory.Etale.StandardEtale
  - Mathlib.RingTheory.Etale.Weakly
explains:
  E2: [StandardEtalePair, StandardEtalePair.homEquiv, StandardEtalePair.existsUnique_hasMap_of_hasMap_quotient_of_sq_eq_bot, Algebra.etaleLocus_eq_unramifiedLocus_inter_smoothLocus, Algebra.isOpen_etaleLocus, KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale, Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat, Algebra.FormallyEtale.pi_iff, CommAlgCat.FiniteEtale.equivOfIsSepClosed]
  E1: auto
families: []
requires: [V10.C02, V11]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Standard étale algebras, the étale locus and finite étale algebras

### Overview

Section 2 of this chapter defines étale algebras by the infinitesimal lifting property: an $R$-algebra $A$ is formally étale when each $R$-algebra map $A \to B/I$, with $I^2 = 0$, has exactly one lift to $A \to B$. An étale algebra is formally étale and of finite presentation. That section proves the first examples: localizations and finite separable field extensions. This section describes the library that comes after the definition.

The first part is the standard étale algebra $(R[X]/(f))_g$, the local model of each étale algebra. Then come the étale locus, the set of primes where an algebra is étale, the behaviour of the Kähler differentials under an étale map, the descent of étaleness along faithfully flat maps, finite products, the étale neighbourhoods that split the fibers of a finite algebra, and the category of finite étale algebras with its fiber functor. Weakly étale algebras close the section.

### The library around it

#### Standard étale pairs

Let $f, g \in R[X]$ with $f$ monic. Suppose that $f'$ is invertible in $R[X]_g/(f)$. In polynomial terms this means $f' p_1 + f p_2 = g^n$ for some $p_1, p_2 \in R[X]$ and some $n$. Such a pair is a `StandardEtalePair R`, with fields `StandardEtalePair.f`, `StandardEtalePair.g`, `StandardEtalePair.monic_f` and `StandardEtalePair.cond`. Its ring `StandardEtalePair.Ring` is
$$R[X][Y]/(f, Yg - 1) \cong (R[X]/(f))_g \cong R[X]_g/(f),$$
and the three forms are `StandardEtalePair.equivPolynomialQuotient`, `StandardEtalePair.equivAwayAdjoinRoot` and `StandardEtalePair.equivAwayQuotient`. The class of $X$ is `StandardEtalePair.X`.

The ring has a clean universal property. For an $R$-algebra $S$, say that $x \in S$ has a map, `StandardEtalePair.HasMap`, when $f(x) = 0$ and $g(x)$ is a unit of $S$. Then `StandardEtalePair.homEquiv` is a bijection between the $R$-algebra maps from the ring to $S$ and the elements $x$ with a map. The map that belongs to $x$ is `StandardEtalePair.lift`, and `StandardEtalePair.hom_ext` says that a map is determined by the image of $X$. The proof is the universal property of a quotient and of a localization: $X \mapsto x$ kills $f$, and $g(x)$ is a unit, so $Y \mapsto g(x)^{-1}$ is forced.

**Theorem.** The ring of a standard étale pair is étale over $R$ (`StandardEtalePair.instEtaleRing`).

*Proof sketch.* The ring is of finite presentation, with two generators and two relations. For formal étaleness, take an $R$-algebra $S$, an ideal $I$ with $I^2 = 0$, and a map to $S/I$. By the universal property, the map is an element $\bar x$ of $S/I$ with $f(\bar x) = 0$ and $g(\bar x)$ a unit. Choose a lift $x \in S$. A lift of the map is an element $x + \varepsilon$, $\varepsilon \in I$, with $f(x + \varepsilon) = 0$. Since $\varepsilon^2 = 0$, Taylor expansion gives
$$f(x + \varepsilon) = f(x) + f'(x)\,\varepsilon.$$
The element $f'(x)$ is a unit: it is a unit modulo the nilpotent ideal $I$, by the condition on the pair. So $\varepsilon = -f(x)/f'(x)$ is the only solution. The element $g(x + \varepsilon)$ is a unit for the same reason. This is `StandardEtalePair.existsUnique_hasMap_of_hasMap_quotient_of_sq_eq_bot`. $\square$

An $R$-algebra $S$ with an isomorphism to such a ring is given by a `StandardEtalePresentation R S`, with the element `StandardEtalePresentation.x` and the isomorphism `StandardEtalePresentation.equivRing`. The class `Algebra.IsStandardEtale R S` says that a presentation exists. The instance `Algebra.instEtaleOfIsStandardEtale` makes such an algebra étale. The class is stable under base change, `Algebra.instIsStandardEtaleTensorProduct`, under localization at one element, `Algebra.IsStandardEtale.of_isLocalizationAway`, and under a surjection onto an étale algebra, `Algebra.IsStandardEtale.of_surjective`. A standard étale presentation is also a submersive presentation, `StandardEtalePresentation.toSubmersivePresentation`, whose Jacobian is $f'(x)\,g(x)$, by `StandardEtalePresentation.toSubmersivePresentation_jacobian`.

**Example.** Let $R = \mathbb{Z}$, $f = X^2 - 2$ and $g = 2X$. Then $f' = 2X = g$ is a unit in $\mathbb{Z}[X]_g/(f)$. The ring is $\mathbb{Z}[\sqrt 2, 1/(2\sqrt 2)] = \mathbb{Z}[\sqrt 2, 1/2]$, and it is étale over $\mathbb{Z}$.

#### The étale locus

Let $A$ be an $R$-algebra. The predicate `Algebra.IsEtaleAt R q` says that the localization $A_{\mathfrak q}$ is formally étale over $R$, for a prime $\mathfrak q$ of $A$. The étale locus `Algebra.etaleLocus R A` is the set of these primes in $\operatorname{Spec} A$, with `Algebra.mem_etaleLocus_iff`.

| Lean name | Statement |
|---|---|
| `Algebra.etaleLocus_eq_univ_iff` | the locus is all of $\operatorname{Spec} A$ if and only if $A$ is formally étale |
| `Algebra.etaleLocus_eq_univ_iff_etale` | for $A$ of finite presentation, the same with étale |
| `Algebra.basicOpen_subset_etaleLocus_iff` | $D(f)$ is in the locus if and only if $A_f$ is formally étale |
| `Algebra.etaleLocus_eq_unramifiedLocus_inter_smoothLocus` | étale locus $=$ unramified locus $\cap$ smooth locus |
| `Algebra.etaleLocus_eq_compl_support` | the locus is the complement of the supports of $\Omega_{A/R}$ and $H^1(L_{A/R})$ |
| `Algebra.isOpen_etaleLocus` | for $A$ of finite presentation, the locus is open |
| `Algebra.exists_etale_of_isEtaleAt` | if $A$ is étale at $\mathfrak q$, then $A_f$ is étale for some $f \notin \mathfrak q$ |

The openness follows from the description by supports. For $A$ of finite presentation, $\Omega_{A/R}$ and $H^1(L_{A/R})$ are finitely generated $A$-modules. The support of a finitely generated module is closed, so the complement of the union of the two supports is open. The lemma `Algebra.IsEtaleAt.comp` says that étaleness at primes composes along a tower.

#### Kähler differentials of an étale algebra

Let $R \to S \to T$ be a tower with $T$ formally étale over $S$. Then the differentials of $T$ over $R$ come from those of $S$: the map $T \otimes_S \Omega_{S/R} \to \Omega_{T/R}$ is an isomorphism, `KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale`. Proof sketch: the second exact sequence of Section 1 reads $T \otimes_S \Omega_{S/R} \to \Omega_{T/R} \to \Omega_{T/S} \to 0$. For $T$ formally étale over $S$, $\Omega_{T/S} = 0$, so the map is surjective. The sequence extends to the left by $H^1(L_{T/S}) \to T \otimes_S \Omega_{S/R}$, and $H^1(L_{T/S}) = 0$ for a formally étale algebra, so the map is also injective. The form `KaehlerDifferential.isBaseChange_of_formallyEtale` states this as an `IsBaseChange`. For a localization $T$ of $S$, the first homology of the cotangent complex also localizes: `Algebra.tensorH1CotangentOfIsLocalization` is the isomorphism $T \otimes_S H^1(L_{S/R}) \cong H^1(L_{T/R})$, and `KaehlerDifferential.isLocalizedModule_map` says that $\Omega_{T/R}$ is the localization of $\Omega_{S/R}$.

#### Descent and products

Let $T$ be a faithfully flat $R$-algebra. The module `Mathlib.RingTheory.Etale.Descent` proves that smoothness, unramifiedness and étaleness of an $R$-algebra $S$ can be checked after base change to $T$. The statements are `Algebra.Smooth.of_smooth_tensorProduct_of_faithfullyFlat`, `Algebra.Unramified.of_unramified_tensorProduct_of_faithfullyFlat`, `Algebra.FormallyUnramified.of_formallyUnramified_tensorProduct_of_faithfullyFlat` and `Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat`. Each one asks for the property of $T \otimes_R S$ over $T$. The forms for the framework of ring map properties are `RingHom.Etale.codescendsAlong_faithfullyFlat`, `RingHom.Smooth.codescendsAlong_faithfullyFlat` and `RingHom.FormallyUnramified.codescendsAlong_faithfullyFlat`.

For a finite family of $R$-algebras $A_i$, `Algebra.FormallyEtale.pi_iff` says that $\prod_i A_i$ is formally étale if and only if each $A_i$ is. The instance `Algebra.FormallyEtale.instEtaleForallOfFinite` gives the étale version. The proof splits formal étaleness into formal unramifiedness and formal smoothness, and uses the product results for these two properties.

#### Étale neighbourhoods of a fiber

Let $S$ be an $R$-algebra of finite type, $\mathfrak q$ a prime of $S$ over a prime $\mathfrak p$ of $R$, and suppose that $S$ is quasi-finite at $\mathfrak q$ (`Algebra.QuasiFiniteAt`). The lemma `Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq` builds an étale $R$-algebra $R'$ with a prime $\mathfrak P$ over $\mathfrak p$, with the same residue field, and an idempotent $e$ of $R' \otimes_R S$, such that the factor $(R' \otimes_R S)_e$ is finite over $R'$ and has exactly one prime over $\mathfrak P$, which lies over $\mathfrak q$. This is the algebraic form of the statement that a quasi-finite map is finite étale locally near a point. The lemma `Algebra.exists_etale_completeOrthogonalIdempotents_forall_liesOver_eq` is the version for a finite algebra that separates all the primes over $\mathfrak p$ at once. The equivalence `Ideal.fiberIsoOfBijectiveResidueField` identifies the fibers over $\mathfrak p$ and $\mathfrak P$ when the residue fields agree.

#### The category of finite étale algebras

The category `CommAlgCat.FiniteEtale R` has as objects the $R$-algebras that are finite as modules and étale, with the property `CommAlgCat.finiteEtale` of `CommAlgCat R`. An object is made with `CommAlgCat.FiniteEtale.of`, and an isomorphism from an algebra isomorphism with `CommAlgCat.FiniteEtale.isoMk`. Base change along $R \to S$ is the functor `CommAlgCat.FiniteEtale.baseChange`.

For an $R$-algebra $\Omega$ that is a separably closed field, the fiber functor `CommAlgCat.FiniteEtale.fiber R Ω` sends $S$ to the finite set of $R$-algebra maps $S \to \Omega$. This is the functor of the Galois theory of schemes.

**Theorem.** For a separably closed field $\Omega$, the category of finite étale $\Omega$-algebras is anti-equivalent to the category of finite sets (`CommAlgCat.FiniteEtale.equivOfIsSepClosed`).

*Proof sketch.* A finite étale algebra $S$ over a field is a finite product of finite separable field extensions, by Section 2. Over a separably closed field each of them is $\Omega$ itself, so $S \cong \Omega^n$. The functor sends $S$ to the finite set $\operatorname{Spec} S$, `CommAlgCat.FiniteEtale.finiteSpec`, with $n$ points. The inverse sends a finite set $X$ to the algebra $\Omega^X$ of functions on $X$. The maps $\Omega^X \to \Omega^Y$ of algebras are exactly the maps given by composition with a function $Y \to X$. $\square$

The isomorphism `CommAlgCat.FiniteEtale.fiberIsoFiniteSpec` says that over $\Omega$ the fiber functor and `CommAlgCat.FiniteEtale.finiteSpec` agree, and `CommAlgCat.FiniteEtale.fiberIsoComp` writes the fiber functor over $R$ as base change to $\Omega$ followed by this one.

#### Weakly étale algebras

An $R$-algebra $S$ is weakly étale, `Algebra.WeaklyEtale R S`, if $S$ is flat over $R$ and the multiplication $S \otimes_R S \to S$ is a flat ring map. This is `Algebra.weaklyEtale_iff`, with the fields `Algebra.WeaklyEtale.flat` and `Algebra.WeaklyEtale.flat_lmul'`. An étale algebra is weakly étale, `Algebra.WeaklyEtale.instOfEtale`, and the class is stable under base change, `Algebra.WeaklyEtale.instTensorProduct`, and composition, `Algebra.WeaklyEtale.trans`. The index of this edition has no declaration that a weakly étale algebra of finite presentation is étale.

#### Common errors

1. `Algebra.IsEtaleAt R q` is about the localization $A_{\mathfrak q}$ and asks only for formal étaleness. For an algebra that is not of finite presentation, a prime in the étale locus need not have an étale neighbourhood $D(f)$; `Algebra.exists_etale_of_isEtaleAt` needs `Algebra.FinitePresentation`.
2. `StandardEtalePair.Ring` is the quotient $R[X][Y]/(f, Yg - 1)$, not a localization type. To use the theory of localizations, transport along `StandardEtalePair.equivAwayAdjoinRoot`.
3. The fiber functor is contravariant: `CommAlgCat.FiniteEtale.fiber R Ω` is a functor from the opposite category to `FintypeCat`. A morphism $S \to T$ of algebras gives a map of fibers in the other direction.

### Exercises

1. (A) Show that $(f, g) = (X, 1)$ is a standard étale pair over each ring $R$, and that its ring is isomorphic to $R$.
2. (A) Let $R = \mathbb{Z}$ and $f = X^2 + 1$. Find $g$ such that $(f, g)$ is a standard étale pair, and describe the ring.
3. (B) Show that $\mathbb{Z}[i]$ is étale over $\mathbb{Z}$ exactly at the primes that do not contain $2$, with `Algebra.etaleLocus_eq_compl_support` and $\Omega_{\mathbb{Z}[i]/\mathbb{Z}} \cong \mathbb{Z}[i]/(2i)$.
4. (B) Use `Algebra.FormallyEtale.pi_iff` to show that $R^n$ is étale over $R$.
5. (B) Prove that the maps $\Omega^X \to \Omega$ of $\Omega$-algebras are the evaluations at the points of $X$, for a finite set $X$ and a field $\Omega$.
6. (C) Let $p$ be a prime and $f = X^p - X - a$ over $\mathbb{F}_p[a]$. Show that $(f, 1)$ is a standard étale pair, and explain why the extension is étale but not a localization.

### Reference

<?reference?>
