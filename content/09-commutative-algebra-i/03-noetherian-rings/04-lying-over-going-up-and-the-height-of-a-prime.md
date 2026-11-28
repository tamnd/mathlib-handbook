---
title: Lying over, going up and the height of a prime
kind: api
modules:
  - Mathlib.RingTheory.Ideal.Over
  - Mathlib.RingTheory.Ideal.GoingUp
  - Mathlib.RingTheory.Ideal.GoingDown
  - Mathlib.RingTheory.Ideal.HasGoingUp
  - Mathlib.RingTheory.Ideal.Quotient.Over
  - Mathlib.RingTheory.Ideal.Height
  - Mathlib.RingTheory.Ideal.KrullsHeightTheorem
  - Mathlib.RingTheory.Ideal.UFD
explains:
  E2: [Ideal.exists_ideal_over_prime_of_isIntegral, Ideal.IsIntegral.under_lt_under, Ideal.isMaximal_of_isIntegral_of_isMaximal_comap, Ideal.exists_ideal_ge_liesOver_of_le, Ideal.height_eq_zero_iff, Ideal.height_add_one_le_of_lt_of_isPrime]
  E1: auto
families: []
requires: [V06.C02, V09.C01, V09.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Lying over, going up and the height of a prime

### Overview

Let $R \to S$ be a ring homomorphism, given in Mathlib as an algebra `[Algebra R S]`. Each prime $Q$ of $S$ contracts to a prime $Q \cap R$ of $R$. This section studies the opposite direction: given a prime $p$ of $R$, is there a prime $Q$ of $S$ with $Q \cap R = p$, and how do chains of primes of $R$ lift to chains of primes of $S$? The classical answers are the theorems of lying over, going up, incomparability and going down. They hold when $S$ is integral over $R$, that is, when each element of $S$ is a root of a monic polynomial with coefficients in $R$. Going down holds when $S$ is flat over $R$. A later volume studies integral extensions in depth. Here only the statements about primes are needed.

The second half of the section measures primes. The height of a prime $p$ is the supremum of the lengths $n$ of chains $p_0 < p_1 < \dots < p_n = p$ of primes. In a Noetherian ring the height of each prime is finite, and Krull's height theorem bounds it by the number of generators of an ideal that $p$ is minimal over. The section ends with the criterion of the library for a Noetherian domain to be a unique factorization domain: each prime of height one is principal. The ideals of Chapter 1, contraction along a homomorphism, and the minimal primes of Section 3.3 are the tools.

### The library around it

#### Ideals over ideals

The module `Mathlib.RingTheory.Ideal.Over` fixes the language. For an ideal $P$ of $S$, `Ideal.under R P` is the contraction $P \cap R$. It is an abbreviation for `Ideal.comap (algebraMap R S) P`, and `Ideal.under_def` states this equality. The class `Ideal.LiesOver P p` says that $p$ is the contraction of $P$. The lemma `Ideal.over_def` extracts the equation $p = $ `Ideal.under R P` from an instance. The set `Ideal.primesOver p S` is the set of primes of $S$ that lie over $p$. Because `Ideal.LiesOver` is a class, the library finds facts about it by instance search. For example `Ideal.IsPrime.under` gives that the contraction of a prime is prime, and `Ideal.LiesOver.trans` handles a tower $R \to S \to T$. The definition `Ideal.Quotient.stabilizerHom` sends an element $\sigma$ of a group that acts on $S$ and fixes $P$ to the induced automorphism of $S/P$ over $R/p$. It is the first step to decomposition groups in algebraic number theory.

#### Lying over and incomparability

The module `Mathlib.RingTheory.Ideal.GoingUp` proves the theorems of Cohen and Seidenberg type for an integral algebra, that is, under the hypothesis `[Algebra.IsIntegral R S]`.

| Lean name | Statement |
|---|---|
| `Ideal.exists_ideal_over_prime_of_isIntegral` | for $p$ prime and $I \subseteq S$ with $I \cap R \subseteq p$, there is a prime $Q \supseteq I$ with $Q \cap R = p$ |
| `Ideal.exists_ideal_over_maximal_of_isIntegral` | for $p$ maximal with $\ker(R \to S) \subseteq p$, there is a maximal $Q$ over $p$ |
| `Ideal.IsIntegral.under_lt_under` | if $I$ is prime and $I < J$, then $I \cap R < J \cap R$ |
| `Ideal.isMaximal_of_isIntegral_of_isMaximal_comap` | a prime $Q$ whose contraction is maximal is maximal |
| `Ideal.IsMaximal.under` | the contraction of a maximal ideal is maximal |
| `Ideal.under_ne_bot_of_integral_mem` | in a domain $S$, a nonzero ideal that has a nonzero integral element contracts to a nonzero ideal |

The proof of lying over is short with the tools of Chapter 2. Replace $S$ by $S/I$ and localize at $p$: the ring $S_p$ is integral over the local ring $R_p$, and the map $R_p \to S_p$ is injective after a reduction by the kernel. The key point is that the extension $p S_p$ is a proper ideal. If $1 = \sum a_i s_i$ with $a_i \in p R_p$, then the subring $S' = R_p[s_1, \dots, s_n]$ is a finite $R_p$-module with $p S' = S'$, so $S' = 0$ by Nakayama's lemma (Chapter 4), which is false. A maximal ideal of $S_p$ above $p S_p$ contracts to a maximal ideal of $R_p$ by the next argument, so it contracts to $p R_p$, and its preimage in $S$ lies over $p$.

The maximality statement has a three line proof. Let $Q$ be prime with $Q \cap R$ maximal. Then $R/(Q \cap R)$ is a field $k$ and $S/Q$ is a domain that is integral over $k$. Take $x \ne 0$ in $S/Q$ and a monic equation $x^n + c_{n-1} x^{n-1} + \dots + c_0 = 0$ of least degree. Then $c_0 \ne 0$ because $S/Q$ is a domain and the degree is least, so $x \cdot (x^{n-1} + \dots + c_1) = -c_0$ is a unit, and $x$ is invertible. Incomparability is the same argument in $S/I$: an element $x \in J \setminus I$ is a nonzero element of the domain $S/I$, the constant term $c_0$ of its least monic equation is a nonzero element of $J/I$ that comes from $R$, and so $J \cap R$ is strictly bigger than $I \cap R$. The lemma `Ideal.coeff_zero_mem_comap_of_root_mem` records the step that $c_0$ lies in $J \cap R$.

#### Going up and going down as classes

The module `Mathlib.RingTheory.Ideal.HasGoingUp` turns going up into a property of the algebra. The class `Algebra.HasGoingUp R S` says that for primes $p \le q$ of $R$ and a prime $P$ of $S$ over $p$ there is a prime $Q \ge P$ over $q$. The instance `Algebra.HasGoingUp.of_isIntegral` gives it for each integral algebra, and `Algebra.HasGoingUp.trans` composes it along a tower. The main lemmas are `Ideal.exists_ideal_ge_liesOver_of_le` and its strict form `Ideal.exists_ideal_gt_liesOver_of_lt`. The lemma `Ideal.exists_ltSeries_of_hasGoingUp` lifts a whole chain of primes of $R$, given as an `LTSeries` of `PrimeSpectrum R`, to a chain of the same length in $S$ that starts at a given prime. For an integral algebra the proof of going up is lying over applied to $R/p \to S/P$, which is again integral.

The module `Mathlib.RingTheory.Ideal.GoingDown` is the mirror image. The class `Algebra.HasGoingDown R S` says that for primes $p \le q$ of $R$ and a prime $Q$ of $S$ over $q$ there is a prime $P \le Q$ over $p$. The instance `Algebra.HasGoingDown.of_flat` gives it for each flat algebra. The lemmas `Ideal.exists_ideal_le_liesOver_of_le`, `Ideal.exists_ideal_lt_liesOver_of_lt` and `Ideal.exists_ltSeries_of_hasGoingDown` correspond to the lemmas of going up. Both classes have a topological form: `Algebra.HasGoingUp.iff_specializingMap_primeSpectrumComap` says that going up holds if and only if the map $\operatorname{Spec} S \to \operatorname{Spec} R$ lifts specializations.

The small module `Mathlib.RingTheory.Ideal.Quotient.Over` counts primes. If $S \to T$ is a surjective map of $R$-algebras whose kernel is not contained in a prime $P'$ over $P$, and the set of primes of $S$ over $P$ is finite, then `Ideal.ncard_primesOver_lt_of_not_le` says that $T$ has strictly fewer primes over $P$. It is a tool for induction on the number of primes over $P$.

#### Height

The module `Mathlib.RingTheory.Ideal.Height` defines `Ideal.height`, with values in `ℕ∞`. For a prime $p$ it is the order height of $p$ in the poset of primes (`PrimeSpectrum.height_eq_orderHeight`). For an arbitrary ideal $I$ it is the infimum of the heights of the minimal primes over $I$ (`Ideal.height_eq_inf_minimalPrimes`). The class `Ideal.FiniteHeight` says that the height is finite, and the instance `Ideal.finiteHeight_of_isNoetherianRing` gives it in a Noetherian ring.

| Lean name | Statement |
|---|---|
| `Ideal.height_eq_zero_iff` | a prime has height $0$ if and only if it is a minimal prime of $R$ |
| `Ideal.height_eq_zero_iff_eq_bot` | in a domain, $\operatorname{ht} I = 0$ if and only if $I = 0$ |
| `Ideal.height_mono` | $I \le J$ implies $\operatorname{ht} I \le \operatorname{ht} J$ |
| `Ideal.height_add_one_le_of_lt_of_isPrime` | for primes $I < J$, $\operatorname{ht} I + 1 \le \operatorname{ht} J$ |
| `Ideal.sup_height_eq_ringKrullDim` | the supremum of the heights of the proper ideals is the Krull dimension |
| `IsLocalRing.maximalIdeal_height_eq_ringKrullDim` | in a local ring, $\operatorname{ht} \mathfrak m = \dim R$ |
| `IsLocalization.AtPrime.ringKrullDim_eq_height` | $\dim R_p = \operatorname{ht} p$ |

The height-one-step lemma has a one line proof: a chain of length $n$ that ends at $I$, followed by $I < J$, is a chain of length $n + 1$ that ends at $J$. The statement on height zero is the definition: a prime has no strictly smaller prime exactly when it is minimal. The Krull dimension `ringKrullDim R` takes values in `WithBot ℕ∞`, so the equalities above carry a coercion from `ℕ∞`.

#### Krull's height theorem

The module `Mathlib.RingTheory.Ideal.KrullsHeightTheorem` proves the main theorems of dimension theory for a Noetherian ring. They are stated here without proof. The proof of the principal ideal theorem uses Artinian rings and symbolic powers, which are not in this chapter.

1. `Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes`: if $I = (a)$ is principal, then each minimal prime over $I$ has height at most $1$. This is Krull's principal ideal theorem.
2. `Ideal.height_le_card_of_mem_minimalPrimes_span_finset`: if $p$ is minimal over the ideal generated by a finite set $s$, then $\operatorname{ht} p \le |s|$. This is Krull's height theorem.
3. `Ideal.exists_finset_card_eq_height_of_isNoetherianRing`: conversely, each prime $p$ is minimal over an ideal generated by $\operatorname{ht} p$ elements.
4. `Ideal.height_le_spanFinrank` and `ringKrullDim_le_spanFinrank_maximalIdeal`: a proper ideal has height at most its minimal number of generators, and a Noetherian local ring has finite dimension, bounded by the number of generators of $\mathfrak m$.

The module also compares heights along an algebra. For primes $P$ over $p$ in Noetherian rings, `Ideal.height_le_height_add_of_liesOver` gives $\operatorname{ht} P \le \operatorname{ht} p + \operatorname{ht}(P/pS)$, and `Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown` gives equality when going down holds, for example for a flat algebra.

#### Height one primes and factorization

The module `Mathlib.RingTheory.Ideal.UFD` gives a criterion. `UniqueFactorizationMonoid.iff_forall_isPrincipal_of_height_eq_one` says that a Noetherian domain is a unique factorization domain if and only if each prime of height $1$ is principal. One direction is short. In a unique factorization domain, a prime $p$ of height $1$ is nonzero, so it holds a nonzero element, and so one of its prime factors $\pi$. Then $0 < (\pi) \le p$, and $(\pi)$ is prime, so $(\pi) = p$ because the height is $1$. The converse uses the principal ideal theorem. The lemma `UniqueFactorizationMonoid.iff_localizationAway_of_prime` reduces the property to a localization $R[1/\pi]$ at a prime element.

#### Common errors

1. The two directions of `Ideal.LiesOver`: `Ideal.LiesOver P p` has the ideal of the big ring first. Many lemmas take this as an instance argument, so after a destructuring of the result of lying over, the equation `Ideal.under R Q = P` must be turned into an instance with `⟨h.symm⟩` or by `Ideal.liesOver_iff`.
2. Lying over needs a hypothesis on the kernel. A prime $p$ of $R$ that does not contain $\ker(R \to S)$ has no prime above it. In `Ideal.exists_ideal_over_prime_of_isIntegral` the hypothesis is `Ideal.under R I ≤ P`, and $I = \bot$ gives exactly the kernel condition.
3. `Ideal.height` is in `ℕ∞` and `ringKrullDim` is in `WithBot ℕ∞`. A goal that mixes them needs a cast, and arithmetic such as $\operatorname{ht} I + 1$ happens in `ℕ∞`, where $\top + 1 = \top$.

### Exercises

1. (A) Use `Ideal.isMaximal_of_isIntegral_of_isMaximal_comap` and `Ideal.IsMaximal.under` to prove that for an integral algebra $R \to S$ a prime $Q$ of $S$ is maximal if and only if $Q \cap R$ is maximal.
2. (A) Show that in $\mathbb Z[i]$ the primes over $(5)$ are $(2 + i)$ and $(2 - i)$, and that the only prime over $(3)$ is $(3)$. State the facts with `Ideal.primesOver`.
3. (B) Prove that an integral extension $R \subseteq S$ has $\dim R = \dim S$. Use going up for one inequality and incomparability for the other.
4. (B) Show that the prime $(X, Y)$ of $k[X, Y]$ has height $2$. For the upper bound use `Ideal.height_le_card_of_mem_minimalPrimes_span_finset`.
5. (B) Show that in $\mathbb Z[\sqrt{-5}]$ the prime $(2, 1 + \sqrt{-5})$ has height $1$ and is not principal, and conclude with `UniqueFactorizationMonoid.iff_forall_isPrincipal_of_height_eq_one` that the ring is not a unique factorization domain.
6. (C) Prove that a domain in which each nonzero prime contains a prime element is a unique factorization domain. Then use it and the principal ideal theorem to prove the hard direction of `UniqueFactorizationMonoid.iff_forall_isPrincipal_of_height_eq_one`.

### Reference

<?reference?>
