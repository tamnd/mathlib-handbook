---
title: Unramified and quasi-finite algebras
kind: api
modules:
  - Mathlib.RingTheory.Unramified.Field
  - Mathlib.RingTheory.Unramified.LocalRing
  - Mathlib.RingTheory.Unramified.Locus
  - Mathlib.RingTheory.Unramified.Finite
  - Mathlib.RingTheory.Unramified.Pi
  - Mathlib.RingTheory.Unramified.Dedekind
  - Mathlib.RingTheory.Unramified.LocalStructure
  - Mathlib.RingTheory.QuasiFinite.Basic
  - Mathlib.RingTheory.QuasiFinite.Weakly
  - Mathlib.RingTheory.QuasiFinite.Polynomial
  - Mathlib.RingTheory.ZariskisMainTheorem
  - Mathlib.RingTheory.TotallySplit
explains:
  E2: [Algebra.FormallyUnramified.iff_isSeparable, Algebra.FormallyUnramified.iff_map_maximalIdeal_eq, Algebra.unramifiedLocus, Algebra.unramifiedLocus_eq_compl_support, Algebra.FormallyUnramified.iff_exists_tensorProduct, Algebra.QuasiFinite, Algebra.QuasiFiniteAt, Algebra.ZariskisMainProperty, Algebra.ZariskisMainProperty.of_finiteType, Algebra.IsFiniteSplit]
  E1: auto
families: []
requires: [V10.C01, V10.C02, V10.C04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Unramified and quasi-finite algebras

### Overview

An algebra $S$ over $R$ is formally unramified when $\Omega_{S/R} = 0$, as in Section 2. For an extension of Dedekind domains this is the classical condition: each prime of $S$ has ramification index $1$ over its image, and the residue field extension is separable. An algebra is quasi-finite when each fiber is finite over its residue field, so each prime of $R$ has finitely many primes above it, and each of them is isolated in its fiber. An unramified algebra of finite type is quasi-finite.

This section describes unramified field extensions and local rings, the unramified locus, the diagonal idempotent of an unramified algebra, the local structure of unramified and étale maps, quasi-finite algebras, Zariski's main theorem, and totally split algebras.

### The library around it

#### Fields and local rings

The module `Mathlib.RingTheory.Unramified.Field` treats algebras over a field $K$.

1. `Algebra.FormallyUnramified.iff_isSeparable`: an essentially finite type field extension $L/K$ is formally unramified if and only if it is separable.
2. `Algebra.FormallyUnramified.isReduced_of_field`: an unramified algebra of essentially finite type over a field is reduced.
3. `Algebra.FormallyUnramified.range_eq_top_of_isPurelyInseparable`: an unramified purely inseparable extension is trivial.
4. `Algebra.FormallyUnramified.of_isSeparable` and `Algebra.FormallyUnramified.isSeparable` give the two directions of the first item.

**Theorem.** Let $R \to S$ be a local map of local rings with $S$ essentially of finite type. Then $S$ is formally unramified over $R$ if and only if $\mathfrak m_R S = \mathfrak m_S$ and $k_S / k_R$ is separable. This is `Algebra.FormallyUnramified.iff_map_maximalIdeal_eq` in `Mathlib.RingTheory.Unramified.LocalRing`.

*Proof sketch.* The fiber $S/\mathfrak m_R S$ is unramified over $k_R$ if and only if $\Omega_{S/R} \otimes k_S = 0$, and by Nakayama's lemma this is $\Omega_{S/R} = 0$. An unramified local algebra of finite type over a field is a finite separable field extension, since it is reduced and local of dimension zero. So the fiber is the field $k_S$, which means $\mathfrak m_R S = \mathfrak m_S$, and $k_S$ is separable over $k_R$. $\square$

The instances `Algebra.instIsSeparableResidueFieldOfIsUnramifiedAt` and `Algebra.instFiniteResidueFieldOfIsUnramifiedAt` give separability and finiteness of the residue field extension at an unramified prime. The lemmas `Localization.exists_awayMap_bijective_of_localRingHom_bijective` and `Localization.finite_of_primesOver_eq_singleton` spread a property of a local map to a neighborhood $D(r)$, for a prime with a single prime above it.

#### The unramified locus

The module `Mathlib.RingTheory.Unramified.Locus` defines `Algebra.unramifiedLocus R A`, the set of primes $\mathfrak q$ with $A_{\mathfrak q}$ formally unramified over $R$. The predicate `Algebra.IsUnramifiedAt R q` says that $\mathfrak q$ is in the locus, and `Algebra.IsUnramifiedIn A p` says that each prime of $A$ over $\mathfrak p$ is in the locus.

| Lean name | Statement |
|---|---|
| `Algebra.unramifiedLocus_eq_compl_support` | the locus is the complement of the support of $\Omega_{A/R}$ |
| `Algebra.isOpen_unramifiedLocus` | the locus is open for an essentially finite type algebra |
| `Algebra.unramifiedLocus_eq_univ_iff` | the locus is everything if and only if $A$ is formally unramified |
| `Algebra.basicOpen_subset_unramifiedLocus_iff` | $D(f)$ is in the locus if and only if $A_f$ is formally unramified |
| `Algebra.IsUnramifiedAt.comp` | unramified points compose in a tower |
| `Algebra.exists_unramified_of_isUnramifiedAt` | an unramified point has an unramified neighborhood $D(f)$ |

The first item is the reason for the openness: $\Omega_{A/R}$ is finitely generated over $A$, and the support of a finitely generated module is closed, as in Chapter 7.

#### The diagonal idempotent

Let $S$ be formally unramified and essentially of finite type over $R$. The kernel $I$ of the multiplication $S \otimes_R S \to S$ has $I/I^2 = \Omega_{S/R} = 0$. Since $I$ is finitely generated, it is generated by an idempotent. This idempotent is `Algebra.FormallyUnramified.elem R S`. The theorem `Algebra.FormallyUnramified.iff_exists_tensorProduct` says that $S$ is formally unramified if and only if there is $t \in S \otimes_R S$ with $\mu(t) = 1$ and $(1 \otimes s - s \otimes 1)t = 0$ for all $s$. Geometrically, the diagonal is open and closed in $\operatorname{Spec}(S \otimes_R S)$.

The module `Mathlib.RingTheory.Unramified.Finite` builds on this idempotent.

1. `Algebra.FormallyUnramified.sec` is an $S$-linear section $M \to S \otimes_R M$ of the action map, for each $S$-module $M$.
2. `Algebra.FormallyUnramified.flat_of_restrictScalars` and `Algebra.FormallyUnramified.projective_of_restrictScalars`: an $S$-module that is flat or projective over $R$ is flat or projective over $S$.
3. `Algebra.FormallyUnramified.finite_of_free`: a free unramified algebra of essentially finite type is finite.
4. `Algebra.FormallyUnramified.equalizerIdempotent f g` is an idempotent of $A$ that cuts out the locus where two algebra maps $f, g : S \to A$ agree. The idempotent `Algebra.FormallyUnramified.inertiaIdempotent` is the case of $g = \sigma \circ f$ for a group element $\sigma$.

The module `Mathlib.RingTheory.Unramified.Pi` has `Algebra.FormallyUnramified.pi_iff`: a finite product is formally unramified if and only if each factor is. The module `Mathlib.RingTheory.Unramified.Dedekind` proves `IsDedekindDomain.of_formallyUnramified`: a domain that is finite and unramified over a Dedekind domain is a Dedekind domain.

#### Local structure

The module `Mathlib.RingTheory.Unramified.LocalStructure` proves the local structure theorems.

1. `Algebra.IsUnramifiedAt.exists_hasStandardEtaleSurjectionOn`: near an unramified prime $\mathfrak q$ of a finite type algebra, there is $f \notin \mathfrak q$ such that $S_f$ is a quotient of a standard étale algebra, `HasStandardEtaleSurjectionOn`.
2. `Algebra.IsEtaleAt.exists_isStandardEtale`: near an étale prime, $S_f$ is standard étale.
3. `Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial`: near a smooth prime, $S_f$ is standard étale over a polynomial ring $R[x_1, \dots, x_n]$.

The standard étale algebras are in Section 5 and standard smooth algebras in Section 8. The instance `Algebra.IsUnramifiedAt.instQuasiFiniteOfEssFiniteTypeOfFormallyUnramified` says that an unramified algebra of essentially finite type is quasi-finite.

#### Quasi-finite algebras

The class `Algebra.QuasiFinite R S` in `Mathlib.RingTheory.QuasiFinite.Basic` says that each fiber $\kappa(\mathfrak p) \otimes_R S$ is a finite dimensional $\kappa(\mathfrak p)$-vector space, `Algebra.quasiFinite_iff`.

1. `Algebra.QuasiFinite.finite_primesOver`: each prime of $R$ has finitely many primes above it. For a finite type algebra this is a characterization, `Algebra.QuasiFinite.iff_finite_primesOver`.
2. `Algebra.QuasiFinite.iff_of_isArtinianRing`: over an Artinian ring, quasi-finite means finite.
3. `Algebra.QuasiFinite.trans` and `Algebra.QuasiFinite.baseChange`: the class is stable under composition and base change.
4. `Algebra.QuasiFinite.of_isIntegral_of_finiteType`: a localization $S_s$ of an integral algebra is quasi-finite when it is of finite type.

The pointwise form `Algebra.QuasiFiniteAt R q` is `Algebra.QuasiFinite R` of the localization $S_{\mathfrak q}$. For a finite type algebra, `Algebra.quasiFiniteAt_iff_isOpen_singleton_fiber` says that $\mathfrak q$ is quasi-finite if and only if it is an isolated point of its fiber. The weaker class `Algebra.WeaklyQuasiFiniteAt R q` in `Mathlib.RingTheory.QuasiFinite.Weakly` asks only that the fiber of $S_{\mathfrak q}$ is quasi-finite, `Algebra.weaklyQuasiFiniteAt_iff`. For finite type algebras the two agree, `Algebra.QuasiFiniteAt.of_weaklyQuasiFiniteAt`. The module `Mathlib.RingTheory.QuasiFinite.Polynomial` proves `Polynomial.not_quasiFiniteAt`: no prime of $R[x]$ is quasi-finite over $R$, since each fiber is a line.

#### Zariski's main theorem

The predicate `Algebra.ZariskisMainProperty R p` says that some $r \notin \mathfrak p$ is integral over $R$ and, for each $x \in S$, some $r^m x$ is integral over $R$, `Algebra.zariskisMainProperty_iff`. Then $S_r$ is a localization of the integral closure of $R$ in $S$.

**Theorem.** Let $S$ be of finite type over $R$ and $\mathfrak q$ a quasi-finite prime. Then $S$ has the Zariski main property at $\mathfrak q$. This is `Algebra.ZariskisMainProperty.of_finiteType` in `Mathlib.RingTheory.ZariskisMainTheorem`.

The geometric form says that a quasi-finite map is locally an open immersion into a finite map. In Lean, `Algebra.QuasiFiniteAt.exists_fg_and_exists_notMem_and_awayMap_bijective` gives a subalgebra $S'$ that is finite over $R$ and $r \in S'$, $r \notin \mathfrak q$, with $S'_r \cong S_r$. The proof is by induction on the number of generators. A key step is `Algebra.not_isStronglyTranscendental_of_quasiFiniteAt`: a generator at a quasi-finite prime is not strongly transcendental.

#### Totally split algebras

The class `Algebra.IsFiniteSplit R S` in `Mathlib.RingTheory.TotallySplit` says that $S \cong R^n$ as an $R$-algebra for some $n$, `Algebra.IsFiniteSplit.nonempty_algEquiv_fun`. A split algebra is étale, `Algebra.IsFiniteSplit.instEtale`, and over a field $k$ its algebra maps to $k$ are its primes, `Algebra.IsFiniteSplit.algHomEquivPrimeSpectrum`. Over a separably closed field every étale algebra of essentially finite type is split, by `Algebra.IsFiniteSplit.instOfIsSepClosedOfEssFiniteTypeOfFormallyEtale`. The main result is `Algebra.IsFiniteSplit.exists_tensorProduct_of_etale`: a finite étale algebra of constant rank $n$ becomes split after a finite, faithfully flat and étale base change.

#### Common errors

1. In `Algebra.FormallyUnramified.iff_isSeparable`, the class `Algebra.IsSeparable K L` asks that each element is algebraic and separable. So $\mathbb{Q}(x)/\mathbb{Q}$ is not unramified, and indeed $\Omega_{\mathbb{Q}(x)/\mathbb{Q}}$ is free on $dx$.
2. `Algebra.QuasiFinite R S` does not include finite type. With finite type, `Algebra.QuasiFinite.iff_finite_primesOver` gives the description by finite fibers.
3. `Algebra.IsUnramifiedAt R q` is a property of the prime $\mathfrak q$ of $S$. The property of a prime $\mathfrak p$ of $R$, that all primes above it are unramified, is `Algebra.IsUnramifiedIn S p`.

### Exercises

1. (A) Show that $\mathbb{Z}[i]$ is unramified over $\mathbb{Z}$ at every prime above an odd prime $p$, and not at the prime above $2$.
2. (A) Find the element of `Algebra.FormallyUnramified.iff_exists_tensorProduct` for $S = R \times R$.
3. (B) Show that $R[x]_x$ is not quasi-finite over $R$, and that $R[x]/(x^2 - a)$ is quasi-finite.
4. (B) Let $k$ be a field of characteristic $p$ and $S = k[x]/(x^p - a)$ with $a \in k$. Show that $S$ is not unramified over $k$, with `Algebra.FormallyUnramified.isReduced_of_field` or with $\Omega_{S/k}$.
5. (B) Let $S = k[x, y]/(xy - 1)$ over $R = k[x]$. Show that $S$ is quasi-finite over $R$, and find a finite $R$-algebra $S'$ and $r$ with $S'_r \cong S$, as in Zariski's main theorem.
6. (C) Let $L/K$ be a finite Galois extension of degree $n$. Show that $L \otimes_K L \cong L^n$, so that $L$ is split after the base change $K \to L$.

### Reference

<?reference?>
