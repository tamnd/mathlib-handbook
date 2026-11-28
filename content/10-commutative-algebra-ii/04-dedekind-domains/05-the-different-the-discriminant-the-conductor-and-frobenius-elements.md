---
title: The different, the discriminant, the conductor and Frobenius elements
kind: api
modules:
  - Mathlib.RingTheory.Discriminant
  - Mathlib.RingTheory.Complex
  - Mathlib.RingTheory.DedekindDomain.Different
  - Mathlib.RingTheory.DedekindDomain.LinearDisjoint
  - Mathlib.RingTheory.Conductor
  - Mathlib.RingTheory.FractionalIdeal.Extended
  - Mathlib.RingTheory.FractionalIdeal.Norm
  - Mathlib.RingTheory.DedekindDomain.Instances
  - Mathlib.RingTheory.Frobenius
explains:
  E2: [Algebra.discr, Algebra.discr_of_matrix_mulVec, Algebra.discr_powerBasis_eq_prod, Submodule.traceDual, FractionalIdeal.dual, differentIdeal, not_dvd_differentIdeal_iff, conductor_mul_differentIdeal, FractionalIdeal.extendedHom_injective, AlgHom.IsArithFrobAt]
  E1: auto
families: []
requires: [V10.C01, V10.C03, V11]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The different, the discriminant, the conductor and Frobenius elements

### Overview

Let $A \subseteq B$ be an extension of Dedekind domains, with fraction fields $K \subseteq L$ and $L/K$ finite and separable. Section 3 describes how a prime $\mathfrak{p}$ of $A$ factors in $B$, with ramification indices and residue degrees. This section collects the invariants of the extension that detect the ramified primes, and the tools that compute the factorization. The discriminant of a basis is an element of $K$; the different is an ideal of $B$ whose prime factors are exactly the ramified primes of $B$. The conductor of an element $x$ measures how far $A[x]$ is from $B$, and it controls when the factorization of $\mathfrak{p}B$ can be read off from the minimal polynomial of $x$.

The section also treats the extension of fractional ideals from $A$ to $B$, the absolute norm of a fractional ideal, the instances for localizations of an extension at a prime, and the Frobenius element of a prime with a finite residue field. These are the inputs of the arithmetic of number fields in Volume 12. The trace and the norm of a finite extension are in Volume 11.

### The library around it

#### The discriminant

Let $B$ be an $A$-algebra and $b = (b_1, \dots, b_n)$ a family in $B$. The discriminant of $b$ is
$$\mathrm{disc}(b) = \det\big(\mathrm{Tr}_{B/A}(b_ib_j)\big)_{i,j}.$$
This is `Algebra.discr A b`, and `Algebra.discr_def` unfolds it to the determinant of `Algebra.traceMatrix A b`. The definition makes sense for every algebra, but the trace `Algebra.trace` is zero when $B$ is not a free finite $A$-module, so the discriminant is useful only for a free algebra.

**Proposition.** For a matrix $P$ over $A$, $\mathrm{disc}(Pb) = \det(P)^2 \, \mathrm{disc}(b)$.

*Proof.* The trace is $A$-linear, so the trace matrix of $Pb$ is $P\,T\,P^{t}$, where $T$ is the trace matrix of $b$. Take determinants. $\square$

This is `Algebra.discr_of_matrix_mulVec`, with the companion `Algebra.discr_of_matrix_vecMul` for the action on the other side. A change of basis over $\mathbb{Z}$ has $\det P = \pm 1$, so two $\mathbb{Z}$-bases of a ring have the same discriminant: `Algebra.discr_eq_discr`. The discriminant does not change under reindexing, `Algebra.discr_reindex`, or under an isomorphism of algebras, `Algebra.discr_eq_discr_of_algEquiv`.

Over fields the discriminant detects bases. For $L/K$ finite and separable, `Algebra.discr_not_zero_of_basis` says that the discriminant of a basis is not zero, because the trace form is nondegenerate. If $b$ is not linearly independent, `Algebra.discr_zero_of_not_linearIndependent` says that the discriminant is zero. Let $E$ be an algebraically closed field over $K$, and let $\sigma_1, \dots, \sigma_n$ be the $K$-embeddings of $L$ into $E$. Then `Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two` says $\mathrm{disc}(b) = \det(\sigma_j(b_i))^2$. For a power basis $1, \alpha, \dots, \alpha^{n-1}$, the matrix is a Vandermonde matrix, and:

| Lean name | Statement |
|---|---|
| `Algebra.discr_powerBasis_eq_prod` | $\mathrm{disc} = \prod_{i<j} (\sigma_j\alpha - \sigma_i\alpha)^2$ |
| `Algebra.discr_powerBasis_eq_prod'` | the same product with the signs $-(\sigma_j\alpha - \sigma_i\alpha)(\sigma_i\alpha - \sigma_j\alpha)$ |
| `Algebra.discr_powerBasis_eq_prod''` | $\mathrm{disc} = (-1)^{n(n-1)/2} \prod_{i<j} (\sigma_j\alpha - \sigma_i\alpha)(\sigma_i\alpha - \sigma_j\alpha)$ |
| `Algebra.discr_powerBasis_eq_norm` | $\mathrm{disc} = (-1)^{n(n-1)/2} N_{L/K}(f'(\alpha))$, with $f$ the minimal polynomial of $\alpha$ |
| `Algebra.discr_isIntegral` | the discriminant of a family of integral elements is integral |
| `Algebra.discr_mul_isIntegral_mem_adjoin` | $\mathrm{disc}(\alpha) \cdot z \in A[\alpha]$ for each integral $z \in L$ |

The last line is the classical bound on the ring of integers: if $\alpha$ is integral and generates $L$, then $\mathcal{O}_L \subseteq \mathrm{disc}(\alpha)^{-1} A[\alpha]$. The discriminant of a number field, `NumberField.discr`, is built from `Algebra.discr` in Volume 12. The small module `Mathlib.RingTheory.Complex` computes the trace and the norm of $\mathbb{C}$ over $\mathbb{R}$: `Algebra.trace_complex_apply` gives $\mathrm{Tr}(z) = 2\,\mathrm{Re}\,z$, `Algebra.norm_complex_apply` gives $N(z) = |z|^2$ as `Complex.normSq z`, and `Algebra.leftMulMatrix_complex` gives the matrix of multiplication by $z$ in the basis $1, i$.

#### The trace dual and the different

Let $I$ be a $B$-submodule of $L$. Its trace dual is
$$I^\vee = \{ x \in L \mid \mathrm{Tr}_{L/K}(xa) \in A \text{ for all } a \in I \}.$$
This is `Submodule.traceDual A K I`, with membership lemma `Submodule.mem_traceDual`. The dual reverses inclusions, `Submodule.le_traceDual_comm`, and $I \subseteq I^{\vee\vee}$, `Submodule.le_traceDual_traceDual`. The key rule is `Submodule.le_traceDual`: $I \subseteq J^\vee$ if and only if $IJ \subseteq B^\vee$. If $I$ has an $A$-basis $b$, then $I^\vee$ has the dual basis for the trace form, `Submodule.traceDual_span_of_basis` with `Module.Basis.traceDual`.

For a nonzero fractional ideal $I$ of the Dedekind domain $B$, the dual is again a fractional ideal, `FractionalIdeal.dual A K I`. The rule above gives $I^\vee = B^\vee I^{-1}$, which is `FractionalIdeal.dual_eq_mul_inv`. So the dual is determined by the inverse different $B^\vee$, and:

| Lean name | Statement |
|---|---|
| `FractionalIdeal.dual_dual` | $I^{\vee\vee} = I$ |
| `FractionalIdeal.dual_involutive` | the dual is an involution |
| `FractionalIdeal.dual_le_dual` | $I^\vee \subseteq J^\vee \iff J \subseteq I$ for nonzero $I$, $J$ |
| `FractionalIdeal.dual_mul_self` | $I^\vee I = B^\vee$ |
| `FractionalIdeal.dual_inv` | $(I^{-1})^\vee = B^\vee I$ |
| `FractionalIdeal.one_le_dual_one` | $B \subseteq B^\vee$ |
| `FractionalIdeal.dual_eq_dual_mul_dual` | the inverse different of a tower is the product of the inverse differents |

The different ideal is the inverse of the trace dual of $B$:
$$\mathfrak{D}_{B/A} = (B^\vee)^{-1}.$$
Since $B \subseteq B^\vee$, it is an integral ideal of $B$. This is `differentIdeal A B`, and `coeIdeal_differentIdeal` states the defining identity in fractional ideals. It is nonzero, `differentIdeal_ne_bot`, when the extension of fraction fields is separable.

**Theorem.** A prime $P$ of $B$ divides $\mathfrak{D}_{B/A}$ if and only if $P$ is ramified over $A$.

The Lean form is `not_dvd_differentIdeal_iff`, with `Algebra.IsUnramifiedAt A P` for "unramified at $P$", and `dvd_differentIdeal_iff` is the negated form. The proof goes through local statements. If $P^e$ divides $\mathfrak{p}B$, then $P^{e-1}$ divides the different, `pow_sub_one_dvd_differentIdeal`. If the residue extension at $P$ is not separable, then $P$ divides the different, `dvd_differentIdeal_of_not_isSeparable`. If $\mathfrak{p}B = PQ$ and some $x \in Q$ has trace not in $\mathfrak{p}$, then $P$ does not divide the different, `not_dvd_differentIdeal_of_intTrace_notMem`. The different is multiplicative in towers $A \subseteq B \subseteq C$: $\mathfrak{D}_{C/A} = \mathfrak{D}_{C/B} \cdot \mathfrak{D}_{B/A}C$, which is `differentIdeal_eq_differentIdeal_mul_differentIdeal`.

#### The conductor and the different of a generator

For $x \in S$ in an $R$-algebra $S$, the conductor of $x$ is the largest ideal of $S$ contained in $R[x]$:
$$\mathfrak{f}(x) = \{ y \in S \mid yS \subseteq R[x] \}.$$
This is `conductor R x`, with `mem_conductor_iff` and `conductor_subset_adjoin`. It is all of $S$ exactly when $R[x] = S$: `conductor_eq_top_iff_adjoin_eq_top`, and `conductor_eq_top_of_powerBasis` for a power basis.

The conductor is the hypothesis of the Kummer-Dedekind theorem. If $\mathfrak{f}(x) \cap R$ and the ideal $I$ of $R$ are coprime, and $R[x] \to S$ is injective, then `quotAdjoinEquivQuotMap` is a ring isomorphism $R[x]/IR[x] \cong S/IS$. So the factorization of $IS$ can be computed in $R[x] = R[X]/(f)$, that is, by factoring $f$ modulo $I$. The factorization itself is `KummerDedekind.normalizedFactorsMapEquivNormalizedFactorsMinPolyMk`, outside this section. The related lemma `comap_map_eq_map_adjoin_of_coprime_conductor` compares the extended ideals, and `Localization.localRingHom_bijective_of_not_conductor_le` says that $R[x]$ and $S$ have the same localization at a prime that does not contain the conductor.

For $x \in B$ with $K(x) = L$ and minimal polynomial $f$ over $A$, the conductor and the different are linked:
$$\mathfrak{f}(x) \cdot \mathfrak{D}_{B/A} = (f'(x)).$$
This is `conductor_mul_differentIdeal`. In particular $f'(x) \in \mathfrak{D}_{B/A}$, `aeval_derivative_mem_differentIdeal`, and the different is $(f'(x))$ when $B = A[x]$. The base of the proof is Euler's lemma, `traceForm_dualSubmodule_adjoin`: the trace dual of $A[x]$ is $f'(x)^{-1}A[x]$.

The module `Mathlib.RingTheory.DedekindDomain.LinearDisjoint` treats a compositum. Let $A \subseteq R_1, R_2 \subseteq B$ with fraction fields $F_1$, $F_2$ that are linearly disjoint over $K$ and generate $L$. If the differents of $R_1/A$ and $R_2/A$ are coprime, then `IsDedekindDomain.differentIdeal_eq_differentIdeal_mul_differentIdeal_of_isCoprime` gives $\mathfrak{D}_{B/A} = \mathfrak{D}_{R_1/A}\mathfrak{D}_{R_2/A}$, the construction `Module.Basis.ofIsCoprimeDifferentIdeal` gives an $R_1$-basis of $B$ from an $A$-basis of $R_2$, and `IsDedekindDomain.range_sup_range_eq_top_of_isCoprime_differentIdeal` says that $R_1$ and $R_2$ generate $B$. This is the abstract form of the fact that the ring of integers of $\mathbb{Q}(\zeta_m, \zeta_n)$ is generated by $\zeta_m$ and $\zeta_n$ when $m$ and $n$ are coprime.

#### Extension and norm of fractional ideals

A ring map $f : A \to B$ that sends a submonoid $M$ into a submonoid $N$ extends fractional ideals: `FractionalIdeal.extended L hf I` is the $B$-submodule generated by the image of $I$, by `FractionalIdeal.coeToSubmodule_extended_eq_span`. It respects sums and products, `FractionalIdeal.extended_add` and `FractionalIdeal.extended_mul`, and is the ring map `FractionalIdeal.extendedHom'`. For an extension of domains, `FractionalIdeal.extendedHom L B` is the map on fractional ideals of the fraction fields, and `FractionalIdeal.extendedHom_coeIdeal_eq_map` says that it extends $I \mapsto IB$.

**Proposition.** For an integral extension $A \subseteq B$ of Dedekind domains, the map $I \mapsto IB$ on fractional ideals is injective.

*Proof.* The map is a group homomorphism on nonzero fractional ideals, so it suffices to show that $IB = B$ implies $I = A$. The lemma `FractionalIdeal.le_one_of_extendedHom_le_one` gives $IB \subseteq B \Rightarrow I \subseteq A$: an element of $I$ lies in $K$, and its image lies in $B$, so it is integral over $A$; since $A$ is integrally closed, it lies in $A$. Apply it to $I$ and to $I^{-1}$. $\square$

This is `FractionalIdeal.extendedHom_injective`, and the class group map `ClassGroup.extendedHom` of Chapter 5 is built on it. For a Dedekind domain $R$ that is free and finite over $\mathbb{Z}$, `FractionalIdeal.absNorm` extends `Ideal.absNorm` to fractional ideals with values in $\mathbb{Q}$. If $I = J/d$ with $J$ an ideal and $d \in R$, then $N(I) = N(J)/|N(d)|$, `FractionalIdeal.absNorm_eq`. The norm of a principal fractional ideal is $|N_{K/\mathbb{Q}}(x)|$, `FractionalIdeal.absNorm_span_singleton`, and `FractionalIdeal.coeIdeal_absNorm` checks the agreement with `Ideal.absNorm`.

#### Localization at a prime of the base

A proof about $A \subseteq B$ often localizes at a prime $\mathfrak{p}$ of $A$, so that $A_{\mathfrak{p}}$ is a discrete valuation ring and $B_{\mathfrak{p}} = (A \setminus \mathfrak{p})^{-1}B$ is a semilocal Dedekind domain. The module `Mathlib.RingTheory.DedekindDomain.Instances` gives the instances for this square of rings. The localization `Localization (Algebra.algebraMapSubmonoid B P.primeCompl)` is a Dedekind domain, a finite $A_{\mathfrak{p}}$-module when $B$ is finite over $A$, a principal ideal ring when $B$ is finite over $A$ and $\mathfrak{p} \neq 0$, and torsion free over $A_{\mathfrak{p}}$. Its fraction field is the fraction field of $B$, and the extension of fraction fields stays separable, `FractionRing.isSeparable_of_isLocalization`. The definitions `Localization.AtPrime.liftAlgebra` and `Localization.AtPrime.algebra_localization_localization` are the algebra structures over the localization, for the fraction field of $B$ and for a third ring $T$ over $B$. They are definitions and not instances, because as instances they create diamonds with other algebra structures.

#### Frobenius elements

Let $\varphi : S \to S$ be an $R$-algebra map and $Q$ a prime of $S$, with $\mathfrak{p} = Q \cap R$ and $R/\mathfrak{p}$ finite of order $q$. Then $\varphi$ is an arithmetic Frobenius at $Q$ if
$$\varphi(x) \equiv x^q \pmod Q \quad \text{for all } x \in S.$$
This is `AlgHom.IsArithFrobAt φ Q`, and `AlgHom.IsArithFrobAt.mk_apply` is the congruence. Such a $\varphi$ maps $Q$ into $Q$, `AlgHom.IsArithFrobAt.le_comap`, and it induces the $q$-power map on $S/Q$, `AlgHom.IsArithFrobAt.restrict_apply`. On a root of unity $\zeta$ of order $m$ prime to the residue characteristic, $\varphi(\zeta) = \zeta^q$, `AlgHom.IsArithFrobAt.apply_of_pow_eq_one`: the powers of $\zeta$ are distinct modulo $Q$, so the congruence fixes the root.

For a finite group $G$ acting on $S$ with fixed ring $R$, written `Algebra.IsInvariant R S G`, the predicate is `IsArithFrobAt R σ Q` for $\sigma \in G$. The main results:

1. `IsArithFrobAt.exists_of_isInvariant`: a Frobenius element exists at each prime $Q$ with $S/Q$ finite, and `arithFrobAt R G Q` chooses one.
2. `IsArithFrobAt.mem_stabilizer`: a Frobenius element at $Q$ fixes $Q$.
3. `IsArithFrobAt.mul_inv_mem_inertia`: two Frobenius elements at $Q$ differ by an element of the inertia group `Ideal.inertia G Q`.
4. `IsArithFrobAt.conj`: if $\sigma$ is a Frobenius at $Q$, then $\tau\sigma\tau^{-1}$ is a Frobenius at $\tau Q$.
5. `isConj_arithFrobAt`: the Frobenius elements at two primes over the same $\mathfrak{p}$ are conjugate.

So at an unramified prime, where the inertia group is trivial, the Frobenius element is unique, and its conjugacy class depends only on $\mathfrak{p}$. For a Galois extension of number fields, this is the Frobenius class of Volume 12. The existence uses the surjectivity of the decomposition group onto the automorphisms of the residue field extension, from the theory of invariant rings.

#### Common errors

1. `Algebra.discr A b` is defined for every family, and it is zero when $B$ is not free over $A$, because the trace is zero then. A result about a discriminant needs a basis, or a field as base.
2. `differentIdeal A B` is an ideal of $B$, while `FractionalIdeal.dual A K 1` is the inverse different, a fractional ideal of $L$. The identity `coeIdeal_differentIdeal` relates the two, with an inverse.
3. `AlgHom.IsArithFrobAt` is a predicate on a map, while `arithFrobAt` is a choice in $G$. A statement about the Frobenius element must assume that it is unique, for example at an unramified prime, or must hold for every choice.

### Exercises

1. (A) Compute the discriminant of the basis $1, i$ of $\mathbb{C}$ over $\mathbb{R}$ with `Algebra.trace_complex_apply`, and compare it with the discriminant of $1, i$ in $\mathbb{Z}[i]$ over $\mathbb{Z}$.
2. (A) Show that the conductor of $x$ is an ideal of $S$ contained in $R[x]$, and that it is the whole ring when $x$ generates $S$.
3. (B) For $B = \mathbb{Z}[\sqrt{d}]$ with $d$ squarefree and $d \equiv 2, 3 \pmod 4$, compute $\mathfrak{D}_{B/\mathbb{Z}}$ with `conductor_mul_differentIdeal`, and find the primes that divide it.
4. (B) Show that $\mathrm{disc}(1, \alpha, \alpha^2) = -4a^3 - 27b^2$ for a root $\alpha$ of $X^3 + aX + b$, with `Algebra.discr_powerBasis_eq_norm`.
5. (B) Prove that a Frobenius element at $Q$ is unique when the inertia group at $Q$ is trivial.
6. (C) Use the conductor of $\sqrt{-3}$ in $\mathbb{Z}[(1 + \sqrt{-3})/2]$ to find the primes $p$ for which the factorization of $p$ can be read from $X^2 + 3$ modulo $p$.

### Reference

<?reference?>
