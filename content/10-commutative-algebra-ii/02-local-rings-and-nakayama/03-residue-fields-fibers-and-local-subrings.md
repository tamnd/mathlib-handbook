---
title: Residue fields, fibers and local subrings
kind: api
modules:
  - Mathlib.RingTheory.LocalRing.ResidueField.Basic
  - Mathlib.RingTheory.LocalRing.ResidueField.Ideal
  - Mathlib.RingTheory.LocalRing.ResidueField.Fiber
  - Mathlib.RingTheory.LocalRing.ResidueField.Instances
  - Mathlib.RingTheory.LocalRing.ResidueField.Polynomial
  - Mathlib.RingTheory.LocalRing.ResidueField.Separable
  - Mathlib.RingTheory.LocalRing.Quotient
  - Mathlib.RingTheory.LocalRing.Etale
  - Mathlib.RingTheory.LocalRing.LocalSubring
  - Mathlib.RingTheory.LocalRing.Subring
  - Mathlib.RingTheory.LocalRing.Pullback
  - Mathlib.RingTheory.LocalRing.NonLocalRing
explains:
  E2: [IsLocalRing.ResidueField.map, Ideal.ResidueField, Ideal.bijective_algebraMap_quotient_residueField, Ideal.Fiber, PrimeSpectrum.preimageHomeomorphFiber, IsLocalRing.finite_quotient_iff, LocalSubring, RingHom.isLocalRing_pullback, IsLocalRing.not_isLocalRing_tfae]
  E1: auto
families: []
requires: [V06, V09]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Residue fields, fibers and local subrings

### Overview

Section 1 defines the residue field $k = R/\mathfrak m$ of a local ring and the local homomorphisms. This section collects the library that works with residue fields in practice. A local homomorphism induces a map of residue fields. Each prime $\mathfrak p$ of any ring has a residue field $\kappa(\mathfrak p)$, the residue field of the localization $R_{\mathfrak p}$. The fiber of an algebra $S$ over $\mathfrak p$ is the $\kappa(\mathfrak p)$-algebra $\kappa(\mathfrak p) \otimes_R S$, and its primes are the primes of $S$ over $\mathfrak p$.

The section also treats some constructions that produce local rings or show that a ring is not local: local subrings of a ring, subrings in which each non-zero-divisor is a unit, pullbacks of rings, and products.

### The library around it

#### The residue field of a local ring

For a local ring $R$, `IsLocalRing.residue R : R →+* ResidueField R` is the quotient map. The module `Mathlib.RingTheory.LocalRing.ResidueField.Basic` gives its basic API.

| Lean name | Statement |
|---|---|
| `IsLocalRing.ker_residue` | the kernel of the residue map is $\mathfrak m$ |
| `IsLocalRing.residue_eq_zero_iff` | $\bar x = 0$ if and only if $x \in \mathfrak m$ |
| `IsLocalRing.residue_ne_zero_iff_isUnit` | $\bar x \ne 0$ if and only if $x$ is a unit |
| `IsLocalRing.residue_surjective` | the residue map is surjective |
| `IsLocalRing.ResidueField.algebraMap_eq` | the algebra map $R \to k$ is the residue map |

A local homomorphism $f : R \to S$ maps $\mathfrak m_R$ into $\mathfrak m_S$, so it induces a ring map `IsLocalRing.ResidueField.map f` of residue fields, with `IsLocalRing.ResidueField.map_residue` as its defining equation. The map is functorial: `IsLocalRing.ResidueField.map_id`, `IsLocalRing.ResidueField.map_comp` and `IsLocalRing.ResidueField.map_map`. An isomorphism gives `IsLocalRing.ResidueField.mapEquiv`, and the group of ring automorphisms acts through `IsLocalRing.ResidueField.mapAut`. For algebras over a third ring there are `IsLocalRing.ResidueField.mapAlgHom` and `IsLocalRing.ResidueField.mapAlgEquiv`. A group that acts on $R$ acts on $k$, by `IsLocalRing.ResidueField.instMulSemiringAction` and `IsLocalRing.ResidueField.residue_smul`.

When $S$ is a local $R$-algebra with a local structure map, the instance `IsLocalRing.ResidueField.instAlgebra` makes $k_S$ an algebra over $k_R$. The instance `IsLocalRing.ResidueField.finite_of_module_finite` says that $k_S$ is finite over $k_R$ when $S$ is a finite $R$-module, and `IsLocalRing.ResidueField.finite_of_finite` transfers the finiteness of the residue field. The module `Mathlib.RingTheory.LocalRing.ResidueField.Instances` adds the algebra `IsLocalRing.ResidueField.algebraOfIsIntegral` from $k_R$ to a field $k$ over an integral $R$-algebra, and `Algebra.isSeparable_residueField_iff` compares separability of residue fields with separability of quotients.

#### The residue field at a prime

Let $\mathfrak p$ be a prime of a ring $R$. The module `Mathlib.RingTheory.LocalRing.ResidueField.Ideal` defines `Ideal.ResidueField p` as the residue field of `Localization.AtPrime p`, the field $\kappa(\mathfrak p) = R_{\mathfrak p}/\mathfrak p R_{\mathfrak p}$. It is also the fraction field of the domain $R/\mathfrak p$.

| Lean name | Statement |
|---|---|
| `Ideal.ker_algebraMap_residueField` | the kernel of $R \to \kappa(\mathfrak p)$ is $\mathfrak p$ |
| `Ideal.algebraMap_residueField_eq_zero` | $x \mapsto 0$ if and only if $x \in \mathfrak p$ |
| `Ideal.injective_algebraMap_quotient_residueField` | $R/\mathfrak p \to \kappa(\mathfrak p)$ is injective |
| `Ideal.bijective_algebraMap_quotient_residueField` | this map is bijective when $\mathfrak p$ is maximal |
| `Ideal.algEquivResidueFieldOfField` | for a field $k$, $\kappa(0) \cong k$ |
| `Ideal.ResidueField.ringHom_ext` | two maps out of $\kappa(\mathfrak p)$ agree if they agree on $R$ |

A ring map $f : R \to S$ and a prime $\mathfrak q$ of $S$ with $\mathfrak p = f^{-1}(\mathfrak q)$ give `Ideal.ResidueField.map p q f h`, a map $\kappa(\mathfrak p) \to \kappa(\mathfrak q)$. The hypothesis `h : p = q.comap f` is an explicit argument. The algebra form is `Ideal.ResidueField.mapₐ`, and an isomorphism gives `Ideal.residueFieldRingEquiv`. The universal property is `Ideal.ResidueField.lift`: a map $f : R \to S$ that kills $\mathfrak p$ and sends the complement of $\mathfrak p$ to units factors through $\kappa(\mathfrak p)$. The lemma `RingHom.SurjectiveOnStalks.residueFieldMap_bijective` says that the induced maps of residue fields are bijective for a map that is surjective on stalks.

#### Fibers

Let $S$ be an $R$-algebra and $\mathfrak p$ a prime of $R$. The fiber `p.Fiber S` is the tensor product $\kappa(\mathfrak p) \otimes_R S$, an abbreviation in `Mathlib.RingTheory.LocalRing.ResidueField.Fiber`.

**Theorem.** The primes of $S$ over $\mathfrak p$ correspond to the primes of the fiber, and the correspondence is a homeomorphism for the Zariski topologies. This is `PrimeSpectrum.preimageHomeomorphFiber`.

*Proof sketch.* The fiber is the localization of $S/\mathfrak p S$ at the image of $R \setminus \mathfrak p$, by `Ideal.Fiber.algEquivQuotient`. The primes of a quotient are the primes that contain the ideal, and the primes of a localization are the primes that miss the multiplicative set. So the primes of the fiber are the primes $\mathfrak q$ of $S$ that contain $\mathfrak p S$ and meet the image of $R$ in a subset of $\mathfrak p$, that is, the $\mathfrak q$ with $\mathfrak q \cap R = \mathfrak p$. $\square$

The same correspondence is an equivalence `PrimeSpectrum.preimageEquivFiber`, an order isomorphism `PrimeSpectrum.preimageOrderIsoFiber`, and `PrimeSpectrum.primesOverOrderIsoFiber` in the language of `Ideal.primesOver`. The lemma `Ideal.Fiber.exists_smul_eq_one_tmul` says that each element of the fiber becomes a pure tensor $1 \otimes s$ after multiplication by some $r \notin \mathfrak p$.

The module `Mathlib.RingTheory.LocalRing.ResidueField.Polynomial` computes fibers of quotients of $R[X]$. If $S = R[X]/I$, then `Polynomial.fiberEquivQuotient` identifies the fiber with $\kappa(\mathfrak p)[X]/I\kappa(\mathfrak p)[X]$. For the extended prime $\mathfrak p R[X]$, `Polynomial.residueFieldMapCAlgEquiv` identifies its residue field with the field of rational functions `RatFunc` over $\kappa(\mathfrak p)$.

The module `Mathlib.RingTheory.LocalRing.ResidueField.Separable` defines the class `Algebra.HasSeparableResidueFieldsAt A B p`: for each prime $\mathfrak q$ of $B$ over $\mathfrak p$, the extension $\kappa(\mathfrak q)/\kappa(\mathfrak p)$ is separable. It holds for integral algebras over a prime with a perfect residue field, and it passes to the two halves of a tower by `Algebra.HasSeparableResidueFieldsAt.tower_top` and `Algebra.HasSeparableResidueFieldsAt.tower_bot`.

#### Quotients of local rings and finite étale extensions

Let $(R, \mathfrak m, k)$ be local. The module `Mathlib.RingTheory.LocalRing.Quotient` relates a finite free $R$-algebra $S$ to the $k$-algebra $S/\mathfrak m S$. A basis of $S$ over $R$ reduces to a basis of $S/\mathfrak m S$ over $k$, `IsLocalRing.basisQuotient`, so the ranks agree, `IsLocalRing.finrank_quotient_map`. The lemma `IsLocalRing.quotient_span_eq_top_iff_span_eq_top` is Nakayama's lemma in this setting.

**Theorem.** Let $R$ be a Noetherian local ring with finite residue field, and $I$ an ideal. Then $R/I$ is finite if and only if $\mathfrak m^n \subseteq I$ for some $n$. This is `IsLocalRing.finite_quotient_iff`.

*Proof sketch.* If $\mathfrak m^n \subseteq I$, then $R/I$ is a quotient of $R/\mathfrak m^n$. This ring has the filtration by the $\mathfrak m^i/\mathfrak m^{i+1}$, and each factor is a finite dimensional vector space over the finite field $k$, since $\mathfrak m$ is finitely generated. So $R/\mathfrak m^n$ is finite. Conversely, a finite ring $R/I$ is Artinian, and its maximal ideal $\mathfrak m/I$ is nilpotent, by `IsLocalRing.exists_maximalIdeal_pow_le_of_isArtinianRing_quotient`. $\square$

The module `Mathlib.RingTheory.LocalRing.Etale` treats a finite étale extension $S$ of local rings. It is monogenic: `IsLocalRing.exists_adjoin_eq_top` gives $\beta$ with $S = R[\beta]$, already for a formally unramified finite extension. For such $\beta$ the value of the derivative of the minimal polynomial at $\beta$ is a unit, `IsLocalRing.isUnit_aeval_derivative_minpoly_of_adjoin_eq_top`. The minimal polynomial reduces to the minimal polynomial of $\bar\beta$ over $k$, `IsLocalRing.minpoly_map_residue`, and the rank of $S$ over $R$ is the degree of the residue field extension, `IsLocalRing.finrank_eq_finrank_residueField`.

#### Local subrings

The structure `LocalSubring R` in `Mathlib.RingTheory.LocalRing.LocalSubring` is a subring of $R$ that is a local ring. Its order is domination: $A \le B$ means $A \subseteq B$ and the inclusion is a local homomorphism, so $\mathfrak m_B \cap A = \mathfrak m_A$. This is `LocalSubring.le_def`. The function `LocalSubring.toSubring` is monotone and injective. The constructions are `LocalSubring.map` along a ring map, `LocalSubring.range` of a local map, and `LocalSubring.ofPrime A P`, the localization of a subring $A$ of a field at a prime $P$, with `LocalSubring.le_ofPrime` and `LocalSubring.ofPrimeEquiv`. The valuation rings of a field are the maximal elements for domination; see Chapter 3.

The module `Mathlib.RingTheory.LocalRing.Subring` gives a criterion. Let $S$ be local and $R$ a subring of $S$ in which each non-zero-divisor is a unit. Then $R$ is local, `IsLocalRing.of_subring`, and `IsLocalRing.of_injective` is the form for an injective map.

#### Pullbacks and non-local rings

For ring maps $f : R \to T$ and $g : S \to T$ the pullback `f.pullback g` is the subring $\{(r, s) \mid f(r) = g(s)\}$ of $R \times S$, with projections `RingHom.pullbackFst` and `RingHom.pullbackSnd` and the commuting square `RingHom.pullback_comm_sq`. An element is a unit if and only if both coordinates are units, `RingHom.isUnit_pullback_mk_iff`. Then `RingHom.isLocalRing_pullback` says that the pullback is local when $R$ is local and $g$ is a local homomorphism. The `AlgHom` versions are `AlgHom.pullback` and `AlgHom.isLocalRing_pullback`. A special case is `RingHom.isLocalRing_eqLocus`.

The module `Mathlib.RingTheory.LocalRing.NonLocalRing` collects criteria for a ring not to be local. The lemma `IsLocalRing.not_isLocalRing_tfae` says that for a nontrivial ring the following are equivalent: $R$ is not local, its maximal spectrum has two points, and $R$ has two different maximal ideals. A product of two nontrivial rings is not local, `IsLocalRing.not_isLocalRing_of_prod_of_nontrivial`, since $(1, 0) + (0, 1) = 1$ is a sum of two non-units, as in `IsLocalRing.not_isLocalRing_def`. A non-local ring maps onto a product of two fields, by the Chinese remainder theorem for two maximal ideals: `IsLocalRing.exists_surjective_of_not_isLocalRing`.

#### Common errors

1. `Ideal.ResidueField p` is the residue field of the localization, not the quotient `R ⧸ p`. The two agree only for a maximal ideal, and then the isomorphism comes from `Ideal.bijective_algebraMap_quotient_residueField`.
2. `IsLocalRing.ResidueField.map f` needs `[IsLocalHom f]`. For a map that is not local, use `Ideal.ResidueField.map` with explicit primes.
3. The order on `LocalSubring R` is domination, so `A ≤ B` is stronger than the inclusion of subrings.

### Exercises

1. (A) Let $R = \mathbb{Z}_{(p)}$. Show that `IsLocalRing.ResidueField R` is isomorphic to $\mathbb{F}_p$, and compute the map of residue fields for $\mathbb{Z}_{(p)} \to \mathbb{Z}_p$.
2. (A) Compute the fiber of $\mathbb{Z}[i]$ over the primes $(2)$, $(3)$ and $(5)$ of $\mathbb{Z}$, and count its primes.
3. (B) Show that $\kappa(\mathfrak p)$ is the fraction field of $R/\mathfrak p$, and describe $\kappa((X))$ for $R = k[X, Y]$.
4. (B) Let $k$ be a field. Show that the pullback of $k[[X]] \to k$ and $k[[Y]] \to k$ is the local ring $k[[X, Y]]/(XY)$.
5. (B) Show that $\mathbb{Z}/6\mathbb{Z}$ is not local in two ways: by two maximal ideals and by a sum of two non-units equal to $1$.
6. (C) Let $R = \mathbb{Z}_p$ and $S = \mathbb{Z}_p[\zeta]$ with $\zeta$ a primitive root of unity of order prime to $p$. Show that $S$ is finite étale and local over $R$, and find a generator as in `IsLocalRing.exists_adjoin_eq_top`.

### Reference

<?reference?>
