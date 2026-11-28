---
title: Maps of spectra, the free locus and Chevalley's theorem
kind: api
modules:
  - Mathlib.RingTheory.Spectrum.Prime.RingHom
  - Mathlib.RingTheory.Spectrum.Prime.Polynomial
  - Mathlib.RingTheory.Spectrum.Prime.IsOpenComapC
  - Mathlib.RingTheory.Spectrum.Prime.TensorProduct
  - Mathlib.RingTheory.Spectrum.Prime.Module
  - Mathlib.RingTheory.Spectrum.Prime.FreeLocus
  - Mathlib.RingTheory.Spectrum.Prime.ConstructibleSet
  - Mathlib.RingTheory.Spectrum.Prime.Chevalley
  - Mathlib.RingTheory.Spectrum.Prime.ChevalleyComplexity
  - Mathlib.RingTheory.Spectrum.Maximal.Defs
  - Mathlib.RingTheory.Spectrum.Maximal.Basic
  - Mathlib.RingTheory.Spectrum.Maximal.Topology
  - Mathlib.RingTheory.Spectrum.Maximal.Localization
explains:
  E2: [PrimeSpectrum.comap, PrimeSpectrum.preimage_comap_zeroLocus, Ideal.primeSpectrumQuotientOrderIsoZeroLocus, Polynomial.isOpenMap_comap_C, Module.freeLocus, Module.isOpen_freeLocus, Module.rankAtStalk, PrimeSpectrum.isConstructible_comap_image, PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation, MaximalSpectrum]
  E1: auto
families: []
requires: [V09, V10.C01, V10.C07]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Maps of spectra, the free locus and Chevalley's theorem

### Overview

A ring map $f : R \to S$ gives a map $\operatorname{Spec} S \to \operatorname{Spec} R$ that sends a prime $\mathfrak q$ to $f^{-1}(\mathfrak q)$. This map is continuous, and $\operatorname{Spec}$ is a contravariant functor from rings to topological spaces. Quotients give closed embeddings, and localizations give embeddings onto sets of primes that avoid a multiplicative set. The image of the map is in general neither open nor closed. Chevalley's theorem says that for a finitely presented map the image of a constructible set is constructible.

This section describes the map of spectra and its first properties, the images for polynomial rings and tensor products, the support and the free locus of a module, constructible sets and Chevalley's theorem, and the maximal spectrum.

### The library around it

#### The map of spectra

The map `PrimeSpectrum.comap f` in `Mathlib.RingTheory.Spectrum.Prime.RingHom` sends $\mathfrak q$ to `Ideal.comap f q`, `PrimeSpectrum.comap_asIdeal`. It is functorial, `PrimeSpectrum.comap_id` and `PrimeSpectrum.comap_comp`, and a ring isomorphism gives the order isomorphism `PrimeSpectrum.comapEquiv`.

1. `PrimeSpectrum.preimage_comap_zeroLocus`: the preimage of $V(s)$ is $V(f(s))$. So the map is continuous, `PrimeSpectrum.continuous_comap`.
2. `PrimeSpectrum.mem_range_comap_iff`: $\mathfrak p$ is in the image if and only if $f^{-1}(f(\mathfrak p)S) = \mathfrak p$.
3. `Ideal.primeSpectrumQuotientOrderIsoZeroLocus`: the primes of $R/I$ are the primes of $V(I)$, and `PrimeSpectrum.isClosedEmbedding_comap_of_surjective` gives the closed embedding.
4. `PrimeSpectrum.localization_comap_range`: the image of $\operatorname{Spec} S^{-1}R$ is the set of primes disjoint from $S$, and `PrimeSpectrum.localization_comap_isEmbedding` says that the map is an embedding.
5. `PrimeSpectrum.residueField_comap`: the image of $\operatorname{Spec} \kappa(\mathfrak p)$ is $\{\mathfrak p\}$.
6. `PrimeSpectrum.sigmaToPi_bijective`: the spectrum of a finite product is the disjoint union of the spectra.

**Theorem.** A prime $\mathfrak p$ is in the image of $\operatorname{Spec} S$ if and only if $f^{-1}(f(\mathfrak p)S) = \mathfrak p$.

*Proof.* If $\mathfrak p = f^{-1}(\mathfrak q)$, then $f(\mathfrak p)S \subseteq \mathfrak q$, so $\mathfrak p \subseteq f^{-1}(f(\mathfrak p)S) \subseteq \mathfrak p$. Conversely, put $T = R \setminus \mathfrak p$. The ideal $f(\mathfrak p)S$ does not meet $f(T)$, since an element $f(t)$ in it would give $t \in f^{-1}(f(\mathfrak p)S) = \mathfrak p$. A prime $\mathfrak q \supseteq f(\mathfrak p)S$ disjoint from $f(T)$ exists, and $f^{-1}(\mathfrak q) = \mathfrak p$. $\square$

#### Polynomial rings and tensor products

The module `Mathlib.RingTheory.Spectrum.Prime.Polynomial` treats $C : R \to R[x]$.

1. `Polynomial.image_comap_C_basicOpen`: the image of $D(g)$ is the complement of $V$ of the coefficients of $g$.
2. `Polynomial.isOpenMap_comap_C`: so the map $\operatorname{Spec} R[x] \to \operatorname{Spec} R$ is open. The form for several variables is `MvPolynomial.isOpenMap_comap_C`.
3. `Polynomial.isCompact_image_comap_of_monic`: for a monic $g$, the image of $V(g) \setminus V(f)$ is compact, and `Polynomial.isOpen_image_comap_of_monic` says that it is open.
4. `PrimeSpectrum.exists_image_comap_of_finite_of_free`: for a finite free quotient, the image of $V(s) \setminus V(f)$ is open, by the characteristic polynomial criterion `isNilpotent_tensor_residueField_iff`.

The module `Mathlib.RingTheory.Spectrum.Prime.IsOpenComapC` has an older proof of the openness, with the set `AlgebraicGeometry.Polynomial.imageOfDf`. The module `Mathlib.RingTheory.Spectrum.Prime.TensorProduct` defines `PrimeSpectrum.tensorProductTo`, the map $\operatorname{Spec}(S \otimes_R T) \to \operatorname{Spec} S \times \operatorname{Spec} T$. It is continuous, and it is an embedding when $R \to T$ is surjective on stalks, `PrimeSpectrum.isEmbedding_tensorProductTo_of_surjectiveOnStalks`.

#### The support and the free locus

The support of Chapter 7 is a subset of the spectrum. The module `Mathlib.RingTheory.Spectrum.Prime.Module` proves its topological properties: it is stable under specialization, `Module.stableUnderSpecialization_support`, and closed for a finitely generated module, `Module.isClosed_support`. A nonzero finitely generated module over a local ring has the closed point in its support, `IsLocalRing.closedPoint_mem_support`.

The module `Mathlib.RingTheory.Spectrum.Prime.FreeLocus` defines `Module.freeLocus R M`, the set of primes $\mathfrak p$ with $M_{\mathfrak p}$ free over $R_{\mathfrak p}$, `Module.mem_freeLocus`. The function `Module.rankAtStalk M` sends $\mathfrak p$ to the rank of $M_{\mathfrak p}$, `Module.rankAtStalk_eq_finrank_tensorProduct`.

| Lean name | Statement |
|---|---|
| `Module.isOpen_freeLocus` | the free locus of a finitely presented module is open |
| `Module.freeLocus_eq_univ_iff` | it is everything if and only if $M$ is projective |
| `Module.basicOpen_subset_freeLocus_iff` | $D(f)$ is in the locus if and only if $M_f$ is projective |
| `Module.isLocallyConstant_rankAtStalk` | the rank of a finitely presented flat module is locally constant |
| `Module.rankAtStalk_eq_finrank_of_free` | for a free module the rank is the constant $\operatorname{rank} M$ |
| `Module.rankAtStalk_eq_zero_iff_notMem_support` | the rank is $0$ exactly outside the support |
| `Module.rankAtStalk_tensorProduct` | the rank of $M \otimes N$ is the product |
| `Module.rankAtStalk_baseChange` | the rank is stable under base change |

**Theorem.** The free locus of a finitely presented module is open. This is `Module.isOpen_freeLocus`.

*Proof sketch.* Let $M_{\mathfrak p}$ be free with basis the images of $m_1, \dots, m_n \in M$. The map $R^n \to M$ given by the $m_i$ has finitely generated kernel and cokernel, since $M$ is finitely presented. Both vanish at $\mathfrak p$, so both vanish on some $D(f)$ with $f \notin \mathfrak p$. Then $M_f \cong R_f^n$, and $D(f)$ is in the free locus. $\square$

The smooth locus of Chapter 8 is the free locus of $\Omega$ minus the support of $H_1$.

#### Constructible sets and Chevalley's theorem

A constructible set is a finite union of sets $V(I) \setminus V(J)$, in the sense of the predicate `Topology.IsConstructible`. The module `Mathlib.RingTheory.Spectrum.Prime.ConstructibleSet` gives the data `PrimeSpectrum.ConstructibleSetData R`, a finite set of basic pieces `PrimeSpectrum.BasicConstructibleSetData` with an element $f$ and elements $g_1, \dots, g_n$ for the set $V(g_1, \dots, g_n) \setminus V(f)$. The set is `PrimeSpectrum.ConstructibleSetData.toSet`, and a ring map moves the data by `PrimeSpectrum.ConstructibleSetData.map`.

**Theorem.** Let $f : R \to S$ be of finite presentation. The image of a constructible subset of $\operatorname{Spec} S$ is constructible. This is `PrimeSpectrum.isConstructible_comap_image` in `Mathlib.RingTheory.Spectrum.Prime.Chevalley`, and `PrimeSpectrum.isConstructible_range_comap` is the case of the whole space.

*Proof sketch.* A finitely presented algebra is a quotient of $R[x_1, \dots, x_n]$ by a finitely generated ideal, and a closed subset is constructible. So it is enough to treat $R \to R[x]$ and induct on $n$. For one variable, the image of $V(g_1, \dots, g_k) \setminus V(f)$ is computed by a division algorithm. One splits by the vanishing of leading coefficients, and in each case reduces to a monic polynomial, where the image of a basic piece is open in a closed set by `Polynomial.isOpen_image_comap_of_monic`. $\square$

The module `Mathlib.RingTheory.Spectrum.Prime.ChevalleyComplexity` proves a form with bounds. The theorem `ChevalleyThm.chevalley_polynomialC` controls the number of pieces and the coefficients of the image, and `chevalley_mvPolynomial_mvPolynomial` bounds the degrees for a map of polynomial rings, through `ChevalleyThm.numBound` and `ChevalleyThm.degBound`. Two consequences are the openness of maps: `PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation` for a finitely presented algebra with going down, as in Chapter 1, and `PrimeSpectrum.isOpenMap_comap_algebraMap_tensorProduct_of_field` for a base change $A \to A \otimes_K B$ over a field.

#### The maximal spectrum

The type `MaximalSpectrum R` in `Mathlib.RingTheory.Spectrum.Maximal.Defs` is the structure of maximal ideals, with `MaximalSpectrum.asIdeal`. The map `MaximalSpectrum.toPrimeSpectrum` is injective and continuous, and its image is the set of closed points, `MaximalSpectrum.toPrimeSpectrum_range` in `Mathlib.RingTheory.Spectrum.Maximal.Topology`. Two distinct maximal ideals are coprime, `MaximalSpectrum.isCoprime_of_ne`.

The module `Mathlib.RingTheory.Spectrum.Maximal.Localization` compares $R$ with the product of its localizations. The map `MaximalSpectrum.toPiLocalization R` from $R$ to $\prod_{\mathfrak m} R_{\mathfrak m}$ is injective, `MaximalSpectrum.toPiLocalization_injective`, since an element that vanishes at each maximal ideal is $0$. It is surjective only for finitely many maximal ideals, `MaximalSpectrum.finite_of_toPiLocalization_surjective`. For a domain with fraction field $K$, `MaximalSpectrum.iInf_localization_eq_bot` says that $R = \bigcap_{\mathfrak m} R_{\mathfrak m}$ inside $K$. The forms `PrimeSpectrum.toPiLocalization` and `PrimeSpectrum.piLocalizationToMaximal` use all primes.

#### Common errors

1. `PrimeSpectrum.comap f` goes from `PrimeSpectrum S` to `PrimeSpectrum R`, in the opposite direction to $f : R \to S$.
2. `Module.isOpen_freeLocus` needs `Module.FinitePresentation R M`. The proof spreads a basis from $\mathfrak p$ to $D(f)$, and this step uses a finitely generated kernel of $R^n \to M$. For a module that is only finitely generated, prove openness by other means or add the hypothesis.
3. `PrimeSpectrum.isConstructible_comap_image` needs a finitely presented ring map. The image of $\operatorname{Spec} \mathbb{Q} \to \operatorname{Spec} \mathbb{Z}$ is the generic point, which is not constructible.

### Exercises

1. (A) Find the image of $\operatorname{Spec} \mathbb{Z}[i] \to \operatorname{Spec} \mathbb{Z}$ and the fibers over $(2)$, $(3)$ and $(5)$.
2. (A) Show that the image of $D(f)$ under $\operatorname{Spec} R_f \to \operatorname{Spec} R$ is $D(f)$, with `PrimeSpectrum.localization_away_comap_range`.
3. (B) Show that the image of $\operatorname{Spec} k[x, y]/(xy - 1) \to \operatorname{Spec} k[x]$ is $D(x)$, and that it is open but not closed.
4. (B) Let $R = \mathbb{Z}$ and $M = \mathbb{Z} \oplus \mathbb{Z}/6$. Find the free locus and the function `Module.rankAtStalk M`.
5. (B) Find the image of $V(xy - t) \subseteq \operatorname{Spec} k[t][x, y]$ in $\operatorname{Spec} k[t]$, and of $V(tx - 1)$.
6. (C) Prove that the image of $\operatorname{Spec} R[x] \to \operatorname{Spec} R$ of $D(g)$ is the complement of the zero locus of the coefficients of $g$.

### Reference

<?reference?>
