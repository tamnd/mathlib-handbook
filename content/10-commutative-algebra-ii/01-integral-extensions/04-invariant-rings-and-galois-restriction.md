---
title: Invariant rings and the restriction of Galois actions
kind: api
modules:
  - Mathlib.RingTheory.Invariant.Defs
  - Mathlib.RingTheory.Invariant.Basic
  - Mathlib.RingTheory.Invariant.Galois
  - Mathlib.RingTheory.Invariant.Profinite
  - Mathlib.RingTheory.IntegralClosure.IntegralRestrict
explains:
  E2: [Algebra.IsInvariant, Algebra.IsInvariant.isIntegral, Algebra.IsInvariant.exists_smul_of_under_eq, Algebra.IsInvariant.orbit_eq_primesOver, Ideal.Quotient.stabilizerHom_surjective, Algebra.isInvariant_of_isGalois, galRestrict, Algebra.intNorm, Algebra.algebraMap_intNorm_of_isGalois]
  E1: auto
families: []
requires: [V06, V07, V09]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Invariant rings and the restriction of Galois actions

### Overview

Let a finite group $G$ act on a commutative ring $B$ by ring automorphisms, and let $A$ be the ring of invariants $B^G$. Then $B$ is integral over $A$, and $G$ acts transitively on the primes of $B$ over a given prime of $A$. These two facts are the base of the theory of decomposition and inertia groups. The main example is the ring of integers $B$ of a Galois extension $L/K$ of number fields, with $A$ the ring of integers of $K$ and $G = \operatorname{Gal}(L/K)$.

This section describes the class that says that $A$ is the ring of invariants, the results on primes, the decomposition group and the inertia group, and the restriction of field automorphisms, traces and norms to the integral closure. It uses the integral elements of Section 1 and the primes over a prime of Section 3.

### The library around it

#### The invariant class

The module `Mathlib.RingTheory.Invariant.Defs` defines the class `Algebra.IsInvariant A B G`. Here $B$ is an $A$-algebra, and $G$ acts on $B$ through `MulSemiringAction G B`. The class says that every $b \in B$ with $g \cdot b = b$ for all $g \in G$ is the image of an element of $A$. The map $A \to B$ need not be injective, so $A$ need not be equal to $B^G$, but its image is $B^G$ when the action fixes $A$. The lemma `Algebra.isInvariant_iff` unfolds the class. Most results also ask for `SMulCommClass G A B`, which says that the action of $G$ is $A$-linear.

#### Integrality and the characteristic polynomial

For a finite group $G$ and $b \in B$ the module `Mathlib.RingTheory.Invariant.Basic` defines `MulSemiringAction.charpoly G b`, the polynomial

$$\chi_b(X) = \prod_{g \in G} (X - g \cdot b).$$

| Lean name | Statement |
|---|---|
| `MulSemiringAction.charpoly_eq` | $\chi_b = \prod_g (X - g \cdot b)$ |
| `MulSemiringAction.monic_charpoly` | $\chi_b$ is monic |
| `MulSemiringAction.eval_charpoly` | $\chi_b(b) = 0$ |
| `MulSemiringAction.smul_charpoly` | $g \cdot \chi_b = \chi_b$ |
| `MulSemiringAction.smul_coeff_charpoly` | each coefficient of $\chi_b$ is fixed by $G$ |
| `MulSemiringAction.splits_charpoly` | $\chi_b$ splits over $B$ |
| `Algebra.IsInvariant.charpoly_mem_lifts` | $\chi_b$ comes from a polynomial over $A$ |

**Theorem.** If $G$ is finite and `Algebra.IsInvariant A B G` holds, then $B$ is integral over $A$. This is `Algebra.IsInvariant.isIntegral`.

*Proof.* Let $b \in B$. A $g \in G$ permutes the factors of $\chi_b$, so $g \cdot \chi_b = \chi_b$ and each coefficient is invariant. By the class each coefficient comes from $A$. So $\chi_b$ is the image of a monic polynomial over $A$, and $b$ is a root of it. $\square$

#### The action on primes

Let $P$ be a prime of $A$. The group $G$ acts on the set `P.primesOver B` of primes of $B$ over $P$.

**Theorem (transitivity).** Let $G$ be finite, and let $P, Q$ be primes of $B$ with $P \cap A = Q \cap A$. Then $Q = g \cdot P$ for some $g \in G$. This is `Algebra.IsInvariant.exists_smul_of_under_eq`, and `Algebra.IsInvariant.orbit_eq_primesOver` says that the orbit of a prime over $P$ is the whole set of primes over $P$.

*Proof sketch.* Suppose $Q \ne g \cdot P$ for all $g$. Since $B$ is integral over $A$, incomparability gives $Q \not\subseteq g \cdot P$ for all $g$. By prime avoidance there is $x \in Q$ with $x \notin g \cdot P$ for all $g$. The product $y = \prod_g g \cdot x$ is invariant, so it lies in $Q \cap A = P \cap A \subseteq P$. Since $P$ is prime, some factor $g \cdot x$ lies in $P$, so $x \in g^{-1} \cdot P$, a contradiction. $\square$

The lemma `Algebra.IsInvariant.mem_map_under` says that an invariant element of an ideal $I$ of $B$ lies in the extension of $I \cap A$.

#### Decomposition and inertia

Let $Q$ be a prime of $B$ over $P$. The decomposition group is the stabilizer `MulAction.stabilizer G Q`, and the inertia group `Ideal.inertia G Q` is the subgroup of the $g$ that act trivially on $B/Q$. An element of the stabilizer induces an automorphism of $B/Q$ over $A/P$, and `Ideal.Quotient.stabilizerHom` is this map.

1. For maximal $P$ and $Q$, `Ideal.Quotient.normal` says that the residue extension $(B/Q)/(A/P)$ is normal, and `Ideal.Quotient.finite_of_isInvariant` says that it is finite when it is separable. For primes that are not maximal, `Ideal.IsFractionRing.normal` and `Ideal.IsFractionRing.finite_of_isInvariant` give the same results for the fraction fields of $A/P$ and $B/Q$.
2. `Ideal.Quotient.stabilizerHom_surjective` says that every automorphism of $B/Q$ over $A/P$ comes from the decomposition group.
3. `Ideal.Quotient.stabilizerQuotientInertiaEquiv` is the isomorphism of the decomposition group modulo inertia with the group of automorphisms of $B/Q$ over $A/P$.
4. `IsFractionRing.stabilizerHom` and `IsFractionRing.stabilizerQuotientInertiaEquiv` are the same maps with values in `Gal(L/K)` for the fraction fields $K$ and $L$ of $A/P$ and $B/Q$, and `IsFractionRing.ker_stabilizerHom` says that the kernel is the inertia group.

The surjectivity is the step that gives Frobenius elements in number theory: for a finite residue field the automorphism $x \mapsto x^q$ lifts to the decomposition group. The lemmas `Ideal.stabilizer_quotient`, `Ideal.inertia_quotient`, `Ideal.map_stabilizer_of_surjective` and `Ideal.map_inertia_of_surjective` compare these groups for $G$ and for a quotient $G/H$ acting on $B^H$.

#### The Galois case

The module `Mathlib.RingTheory.Invariant.Galois` treats the main example. Let $A$ be an integrally closed domain with fraction field $K$, let $L/K$ be a finite Galois extension, and let $B$ be the integral closure of $A$ in $L$. The action of `Gal(L/K)` on $L$ restricts to $B$, by `IsIntegralClosure.MulSemiringAction`, and `Algebra.isInvariant_of_isGalois` says that $A$ is the ring of invariants. So the results above apply to rings of integers. The converse direction is `IsFractionRing.isInvariant`: if $A$ is invariant in $B$, then $K$ is invariant in $L$.

The module `Mathlib.RingTheory.Invariant.Profinite` removes finiteness of $G$ for a profinite group whose action is continuous, with $B$ having the discrete topology. The results are `Algebra.IsInvariant.isIntegral_of_profinite`, `Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite` and `Ideal.Quotient.stabilizerHom_surjective_of_profinite`. The proof passes to the finite quotients $G/N$ for open normal subgroups $N$ and takes a limit of nonempty finite sets.

#### Restriction to the integral closure

The module `Mathlib.RingTheory.IntegralClosure.IntegralRestrict` works in the AKLB setup of the library: $A$ is an integrally closed domain, $K$ its fraction field, $L/K$ a finite extension and $B$ the integral closure of $A$ in $L$. An automorphism of $L$ over $K$ maps integral elements to integral elements, so it restricts to $B$.

| Lean name | Statement |
|---|---|
| `galRestrict A K L B` | the isomorphism `Gal(L/K) ≃* (B ≃ₐ[A] B)` |
| `galRestrictHom A K L B` | the same for algebra endomorphisms, `(L →ₐ[K] L) ≃* (B →ₐ[A] B)` |
| `galRestrict'` | restriction of a map $L \to L_2$ to a map $B \to B_2$ |
| `galLift` | extension of a map $B \to B_2$ to the fraction fields |
| `galLift_galRestrict'` | the two maps are inverse |
| `algebraMap_galRestrict_apply` | $\sigma|_B(x) = \sigma(x)$ inside $L$ |
| `prod_galRestrict_eq_norm` | $\prod_\sigma \sigma|_B(x)$ is the norm of $x$ |

The trace and the norm of $L/K$ map $B$ to $A$, so they restrict. `Algebra.intTrace A B` is the $A$-linear map $B \to A$, and `Algebra.intNorm A B` is the multiplicative map $B \to A$. The lemmas `Algebra.algebraMap_intTrace` and `Algebra.algebraMap_intNorm` say that they agree with `Algebra.trace` and `Algebra.norm` after the map to $K$. For a free extension they are the usual trace and norm, by `Algebra.intTrace_eq_trace` and `Algebra.intNorm_eq_norm`. The norm has the expected properties: `Algebra.intNorm_eq_zero` says that $N(x) = 0$ if and only if $x = 0$, `Algebra.intNorm_intNorm` is transitivity in a tower, and `Algebra.dvd_algebraMap_intNorm_self` says that $x$ divides $N(x)$ in $B$. In the Galois case `Algebra.algebraMap_intNorm_of_isGalois` gives $N(x) = \prod_{\sigma} \sigma(x)$. The lemmas `Algebra.intTrace_eq_of_isLocalization` and `Algebra.intNorm_eq_of_isLocalization` say that both maps commute with localization.

#### Common errors

1. `Algebra.IsInvariant A B G` does not say that $G$ fixes $A$. Add `SMulCommClass G A B` when a result needs it.
2. `galRestrict` needs the full AKLB context, including `IsIntegralClosure B A L` and the scalar towers. A missing instance gives an error at `galRestrict`, not at its use.
3. `Algebra.intNorm A B` is a monoid map, not a linear map. Use `map_mul` and `map_one` with it, and `Algebra.intTrace A B` with `map_add`.

### Exercises

1. (A) Let $G = \{1, \tau\}$ act on $\mathbb{Z}[i]$ by complex conjugation. Compute `MulSemiringAction.charpoly G (a + bi)` and check that it has integer coefficients.
2. (A) Use `Algebra.IsInvariant.orbit_eq_primesOver` to show that the primes of $\mathbb{Z}[i]$ over $(5)$ are $(2 + i)$ and $(2 - i)$, and that conjugation swaps them.
3. (B) Let $k$ be a field and let the symmetric group $S_n$ act on $k[X_1, \dots, X_n]$. Show that the ring of symmetric polynomials satisfies `Algebra.IsInvariant`, and deduce that the polynomial ring is integral over it.
4. (B) Show that the decomposition group of a prime $Q$ over $P$ has index equal to the number of primes over $P$.
5. (B) In the AKLB setup with $L/K$ Galois, prove that $x \mid N(x)$ in $B$ from the product formula for the norm.
6. (C) Let $Q$ be a prime over $P$ with finite residue fields of size $q$ and $q^f$. Use `Ideal.Quotient.stabilizerHom_surjective` to construct an element $\sigma$ of the decomposition group with $\sigma(x) \equiv x^q \pmod Q$ for all $x \in B$.

### Reference

<?reference?>
