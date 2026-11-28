---
title: The prime spectrum and the Zariski topology
kind: api
modules:
  - Mathlib.RingTheory.Spectrum.Prime.Defs
  - Mathlib.RingTheory.Spectrum.Prime.Basic
  - Mathlib.RingTheory.Spectrum.Prime.Topology
  - Mathlib.RingTheory.Spectrum.Prime.Noetherian
  - Mathlib.RingTheory.Spectrum.Prime.Homeomorph
  - Mathlib.RingTheory.Spectrum.Prime.LTSeries
  - Mathlib.RingTheory.Spectrum.Prime.Jacobson
explains:
  E2: [PrimeSpectrum, PrimeSpectrum.zeroLocus, PrimeSpectrum.vanishingIdeal, PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical, PrimeSpectrum.basicOpen, PrimeSpectrum.isTopologicalBasis_basic_opens, PrimeSpectrum.isClosed_singleton_iff_isMaximal, PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime, PrimeSpectrum.isIdempotentElemEquivClopens, PrimeSpectrum.isJacobsonRing_iff_jacobsonSpace]
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

## The prime spectrum and the Zariski topology

### Overview

The prime spectrum $\operatorname{Spec} R$ of a commutative ring is the set of its prime ideals. Its closed sets are the sets $V(I)$ of primes that contain an ideal $I$. This is the Zariski topology. It is far from Hausdorff: the closure of a point $\mathfrak p$ is $V(\mathfrak p)$, so the closed points are the maximal ideals. The space is still compact and sober, and the basic open sets $D(f)$, where $f$ does not vanish, form a basis of compact open sets.

This section describes the type of primes, the zero locus and the vanishing ideal, the basic open sets, the topological properties of the spectrum, the clopen sets and idempotents, and three results on chains of primes, homeomorphisms and Jacobson rings.

### The library around it

#### Points, zero loci and vanishing ideals

The type `PrimeSpectrum R` in `Mathlib.RingTheory.Spectrum.Prime.Defs` is a structure with an ideal `PrimeSpectrum.asIdeal` and a proof that it is prime. It is ordered by inclusion of ideals, `PrimeSpectrum.asIdeal_le_asIdeal`. The module `Mathlib.RingTheory.Spectrum.Prime.Basic` defines the two maps of the Galois connection.

1. `PrimeSpectrum.zeroLocus s` is the set $V(s)$ of primes that contain the set $s \subseteq R$, `PrimeSpectrum.mem_zeroLocus`.
2. `PrimeSpectrum.vanishingIdeal t` is the ideal $I(t)$ of elements that are in each prime of $t$, `PrimeSpectrum.mem_vanishingIdeal`.
3. `PrimeSpectrum.gc` says that $V$ and $I$ form a Galois connection between ideals and sets of primes, with the reverse order.

**Theorem.** For an ideal $I$, the vanishing ideal of $V(I)$ is the radical of $I$. This is `PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical`.

*Proof.* An element of $\sqrt I$ has a power in $I$, so it is in each prime that contains $I$. Conversely, the radical of $I$ is the intersection of the primes that contain $I$, by Krull's theorem on the existence of primes outside a multiplicative set. $\square$

The rules for $V$ are the usual ones: `PrimeSpectrum.zeroLocus_span` replaces a set by its ideal, `PrimeSpectrum.zeroLocus_radical` replaces an ideal by its radical, `PrimeSpectrum.zeroLocus_mul` and `PrimeSpectrum.zeroLocus_inf` say that $V(IJ) = V(I \cap J) = V(I) \cup V(J)$, and `PrimeSpectrum.zeroLocus_iSup` says that $V(\sum I_i) = \bigcap V(I_i)$. The empty set is $V(1)$, `PrimeSpectrum.zeroLocus_empty_iff_eq_top`, and the whole space is $V(I)$ exactly for $I$ in the nilradical, `PrimeSpectrum.zeroLocus_eq_univ_iff`. The nilradical is the intersection of all primes, `PrimeSpectrum.nilradical_eq_iInf`. The spectrum of a product is the disjoint union, `PrimeSpectrum.primeSpectrumProd`.

#### The topology and the basic open sets

The instance `PrimeSpectrum.zariskiTopology` in `Mathlib.RingTheory.Spectrum.Prime.Topology` makes the closed sets the zero loci, `PrimeSpectrum.isClosed_iff_zeroLocus`. The basic open set `PrimeSpectrum.basicOpen f` is the complement of $V(f)$, `PrimeSpectrum.basicOpen_eq_zeroLocus_compl`.

| Lean name | Statement |
|---|---|
| `PrimeSpectrum.isTopologicalBasis_basic_opens` | the sets $D(f)$ form a basis |
| `PrimeSpectrum.basicOpen_mul` | $D(fg) = D(f) \cap D(g)$ |
| `PrimeSpectrum.basicOpen_le_basicOpen_iff` | $D(f) \subseteq D(g)$ if and only if $f \in \sqrt{(g)}$ |
| `PrimeSpectrum.isCompact_basicOpen` | each $D(f)$ is compact |
| `PrimeSpectrum.compactSpace` | the spectrum is compact |
| `PrimeSpectrum.iSup_basicOpen_eq_top_iff` | the $D(f_i)$ cover if and only if the $f_i$ generate $R$ |
| `PrimeSpectrum.localization_away_comap_range` | $D(f)$ is the image of $\operatorname{Spec} R_f$ |
| `PrimeSpectrum.isCompact_isOpen_iff` | an open set is compact if and only if it is $D(f_1) \cup \dots \cup D(f_n)$ |

The compactness of $D(f)$ is the algebraic fact that $1 \in (g_i)$ in $R_f$ uses finitely many $g_i$. With compactness and the other properties, the spectrum is a spectral space, by the instance `PrimeSpectrum.instSpectralSpace`.

#### Points, closures and irreducible sets

**Theorem.** The closure of $\{\mathfrak p\}$ is $V(\mathfrak p)$. So $\mathfrak p$ specializes to $\mathfrak q$ if and only if $\mathfrak p \subseteq \mathfrak q$, and a point is closed if and only if it is maximal. These are `PrimeSpectrum.closure_singleton`, `PrimeSpectrum.le_iff_specializes` and `PrimeSpectrum.isClosed_singleton_iff_isMaximal`.

*Proof.* The closure of a set is $V$ of its vanishing ideal, `PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure`. The vanishing ideal of $\{\mathfrak p\}$ is $\mathfrak p$. So the closure is $V(\mathfrak p)$, the primes that contain $\mathfrak p$. It is $\{\mathfrak p\}$ if and only if no prime is larger, that is, $\mathfrak p$ is maximal among primes, which is maximal. $\square$

A closed set is irreducible if and only if its vanishing ideal is prime, `PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime`. So the points of the spectrum are the irreducible closed sets, by the order isomorphism `PrimeSpectrum.pointsEquivIrreducibleCloseds`, and the spectrum is sober, `PrimeSpectrum.quasiSober`. The irreducible components are the sets $V(\mathfrak p)$ for the minimal primes, `PrimeSpectrum.zeroLocus_minimalPrimes`. A Noetherian ring has finitely many minimal primes, `PrimeSpectrum.finite_setOfPred_isMin` in `Mathlib.RingTheory.Spectrum.Prime.Noetherian`. For a domain, the spectrum is $T_1$ only for a field, `PrimeSpectrum.t1Space_iff_isField`, and it is discrete if and only if it is finite and $R$ has dimension zero, `PrimeSpectrum.discreteTopology_iff_finite_and_krullDimLE_zero`. For a local ring, `IsLocalRing.closedPoint` is the maximal ideal.

#### Clopen sets and idempotents

**Theorem.** The clopen subsets of $\operatorname{Spec} R$ correspond to the idempotents of $R$. The idempotent $e$ gives $D(e) = V(1 - e)$. This is the order isomorphism `PrimeSpectrum.isIdempotentElemEquivClopens`.

*Proof sketch.* For an idempotent $e$, every prime contains exactly one of $e$ and $1 - e$, since $e(1 - e) = 0$ and $e + (1 - e) = 1$. So $D(e)$ and $D(1 - e)$ are disjoint open sets that cover the space. Conversely, a clopen set $U$ and its complement are closed, say $V(I)$ and $V(J)$, with $V(I + J) = \emptyset$ and $V(IJ) = \operatorname{Spec} R$. So $I + J = R$ and $IJ$ is nilpotent. Write $1 = a + b$ with $a \in I$, $b \in J$, and lift the idempotent of $R/IJ$ given by the Chinese remainder theorem to $R$. $\square$

The forms with two elements are `PrimeSpectrum.isClopen_iff_mul_add` and `PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen`. So the spectrum is connected if and only if $R$ has no idempotents other than $0$ and $1$.

#### Chains, homeomorphisms and Jacobson rings

The module `Mathlib.RingTheory.Spectrum.Prime.LTSeries` proves a step of the theory of dimension. For a Noetherian ring and primes $\mathfrak p_0 \subsetneq \mathfrak p_1 \subsetneq \mathfrak p_2$ with $x \in \mathfrak p_2$, there is a prime $\mathfrak q$ with $x \in \mathfrak q$ and $\mathfrak p_0 \subsetneq \mathfrak q \subsetneq \mathfrak p_2$, `PrimeSpectrum.exist_mem_one_of_mem_two`. By induction, `PrimeSpectrum.exist_ltSeries_mem_one_of_mem_last` moves an element of the last prime of a chain into the second prime. This is used for the dimension of $R/(x)$ in Chapter 7.

The module `Mathlib.RingTheory.Spectrum.Prime.Homeomorph` gives criteria for the map of spectra to be a homeomorphism. By `PrimeSpectrum.isHomeomorph_comap`, this holds for $f : R \to S$ when the kernel is nil and each element of $S$ has a power in the image. A purely inseparable extension $K/k$ gives a homeomorphism $\operatorname{Spec}(R \otimes_k K) \to \operatorname{Spec} R$, `PrimeSpectrum.isHomeomorph_comap_of_isPurelyInseparable`.

The module `Mathlib.RingTheory.Spectrum.Prime.Jacobson` translates the Jacobson property. A ring is Jacobson if and only if its spectrum is a Jacobson space, in which the closed points are dense in each closed set, `PrimeSpectrum.isJacobsonRing_iff_jacobsonSpace`. In a Jacobson ring each nonempty open set has a closed point, `PrimeSpectrum.exists_isClosed_singleton_of_isJacobsonRing`.

#### Common errors

1. `PrimeSpectrum R` is a structure, not a subtype of `Ideal R`. Use `PrimeSpectrum.asIdeal` to get the ideal, and `PrimeSpectrum.equivSubtype` to change between the two forms.
2. The order on `PrimeSpectrum R` is inclusion of ideals. So a closed point is a maximal element, and the closure of a point is the set of points above it, not below it.
3. `PrimeSpectrum.zeroLocus` takes a set of elements, not an ideal. For an ideal write `PrimeSpectrum.zeroLocus (I : Set R)`, and use `PrimeSpectrum.zeroLocus_span` to pass between the two.

### Exercises

1. (A) Describe $\operatorname{Spec} \mathbb{Z}$, its closed points, and the closure of the point $(0)$.
2. (A) Show that $D(f) = \emptyset$ if and only if $f$ is nilpotent, with `PrimeSpectrum.basicOpen_eq_bot_iff`.
3. (B) Show that $\operatorname{Spec} R$ and $\operatorname{Spec} R/\sqrt 0$ are homeomorphic, with `PrimeSpectrum.isHomeomorph_comap`.
4. (B) Let $R = k[x, y]/(xy)$. Find the irreducible components of $\operatorname{Spec} R$ and show that the spectrum is connected.
5. (B) Show that $\operatorname{Spec}(R \times S)$ is disconnected for nonzero rings $R$ and $S$, and find the idempotent that gives the clopen set $\operatorname{Spec} R$.
6. (C) Prove that $D(f)$ is compact. Hint: reduce a cover by sets $D(g_i)$ to the statement that $f^n \in (g_i)$ for some $n$.

### Reference

<?reference?>
