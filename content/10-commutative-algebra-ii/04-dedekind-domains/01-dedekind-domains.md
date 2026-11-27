---
title: Dedekind domains
kind: theory
modules:
  - Mathlib.RingTheory.DedekindDomain.Basic
  - Mathlib.RingTheory.DedekindDomain.Dvr
  - Mathlib.RingTheory.DedekindDomain.IntegralClosure
explains:
  E3: [IsDedekindDomain, Ring.DimensionLEOne, isDedekindDomain_iff_isDiscreteValuationRing_atPrime, integralClosure.isDedekindDomain]
  E2: [IsDedekindRing, isDedekindDomain_iff, Ideal.IsPrime.isMaximal, IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain, IsLocalization.isDedekindDomain, Ring.DimensionLEOne.of_isIntegral, IsIntegralClosure.isDedekindDomain, integralClosure.isNoetherianRing, IsIntegralClosure.isNoetherianRing]
  E1: auto
families: []
requires: [V10.C01, V10.C02, V10.C03]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Dedekind domains

### Overview

A Dedekind domain is a Noetherian domain that is integrally closed and in which every nonzero prime ideal is maximal. The three conditions are the local conditions of Chapter 3 put together: at each nonzero prime the localization is a Noetherian local domain of dimension $1$ that is integrally closed, so it is a discrete valuation ring. So a Dedekind domain is a ring that looks like $\mathbb{Z}_{(p)}$ near each of its primes.

This section gives the definition, the characterization by localizations, and the theorem that makes the definition useful in number theory and geometry: the integral closure of a Dedekind domain in a finite separable extension of its fraction field is again a Dedekind domain. So the ring of integers of a number field is Dedekind.

### Definitions

**Definition (Dimension at most one).** A commutative ring $R$ has dimension at most one if every nonzero prime ideal of $R$ is maximal.

For a domain this means that the chains of primes have the form $0 \subsetneq \mathfrak p$, or $0$ alone. Krull dimension in general is in Chapter 7.

::: mathlib
`Ring.DimensionLEOne` · `Mathlib.RingTheory.DedekindDomain.Basic`

`Ring.DimensionLEOne R` is a class with the field `maximalOfPrime : p ≠ ⊥ → p.IsPrime → p.IsMaximal`. The lemma `Ideal.IsPrime.isMaximal` applies it to a given prime. The class is stated without the Krull dimension of Chapter 7, so it can be used before dimension theory.

<?decl Ring.DimensionLEOne?>
:::

**Definition (Dedekind domain).** A Dedekind domain is a domain $A$ that is Noetherian, integrally closed in its field of fractions, and of dimension at most one.

A field is a Dedekind domain by this definition. Some books exclude fields. Every PID is a Dedekind domain: it is Noetherian, a UFD and so integrally closed (Volume 9), and a nonzero prime $(p)$ is maximal since $(p) \subseteq (q)$ means $q \mid p$, so $q$ is a unit or an associate of $p$.

::: mathlib
`IsDedekindDomain` · `Mathlib.RingTheory.DedekindDomain.Basic`

`IsDedekindDomain A` is a class that extends `IsDomain A` and `IsDedekindRing A`, and `IsDedekindRing A` extends `IsNoetherianRing A`, `Ring.DimensionLEOne A` and `IsIntegralClosure A A (FractionRing A)`. The definition uses the fraction field `FractionRing A`. The lemma `isDedekindDomain_iff` states the definition for any fraction field `K`, so that the choice does not matter. Fields are Dedekind domains in Mathlib.

<?decl IsDedekindDomain?>
:::

### Theorems and proofs

**Theorem (Dedekind domains by localization).** Let $A$ be a Noetherian domain. Then $A$ is a Dedekind domain if and only if $A_{\mathfrak p}$ is a discrete valuation ring for every nonzero prime $\mathfrak p$.

*Proof.* Assume $A$ is Dedekind and let $\mathfrak p \ne 0$ be prime. The ring $A_{\mathfrak p}$ is a local domain, Noetherian since localizations of Noetherian rings are Noetherian (Volume 9). Its primes correspond to the primes of $A$ inside $\mathfrak p$ (Chapter 2, Section 1, Exercise 8), and these are $0$ and $\mathfrak p$, since $\mathfrak p$ is maximal and every nonzero prime is maximal. So $A_{\mathfrak p}$ has exactly one nonzero prime. It is integrally closed, since localization keeps integral closedness (Chapter 1, Section 2). It is not a field, since $\mathfrak p A_{\mathfrak p} \ne 0$. By condition 4 of the characterization of discrete valuation rings (Chapter 3, Section 3), $A_{\mathfrak p}$ is a DVR.

Conversely, assume each $A_{\mathfrak p}$ is a DVR. Dimension: let $0 \ne \mathfrak q \subseteq \mathfrak p$ be primes, with $\mathfrak p$ maximal. Then $\mathfrak q A_{\mathfrak p}$ and $\mathfrak p A_{\mathfrak p}$ are nonzero primes of the DVR $A_{\mathfrak p}$, which has only one, so $\mathfrak q = \mathfrak p$. Every nonzero prime lies in a maximal ideal, so every nonzero prime is maximal. Integral closure: let $x \in K$ be integral over $A$. Then $x$ is integral over each $A_{\mathfrak m}$, which is integrally closed, so $x \in A_{\mathfrak m}$ for every maximal ideal $\mathfrak m$. The ideal $J = \{a \in A : ax \in A\}$ is then not inside any maximal ideal: $x = b/s$ with $s \notin \mathfrak m$ gives $s \in J$. So $J = A$, $1 \in J$ and $x \in A$. If $A$ is a field there is nothing to prove. $\square$

The argument shows a general principle: $A = \bigcap_{\mathfrak m} A_{\mathfrak m}$ inside $K$, for any domain $A$.

::: mathlib
`isDedekindDomain_iff_isDiscreteValuationRing_atPrime` · `Mathlib.RingTheory.DedekindDomain.Dvr`

For a domain `A`: `IsDedekindDomain A ↔ IsNoetherian A A ∧ ∀ P ≠ ⊥, P.IsPrime → IsDiscreteValuationRing (Localization.AtPrime P)`. The forward direction for any localization at a nonzero prime is `IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain`, and `IsLocalization.isDedekindDomain` says that a localization of a Dedekind domain is Dedekind.

<?decl isDedekindDomain_iff_isDiscreteValuationRing_atPrime?>
:::

**Theorem (Integral closure in a finite separable extension).** Let $A$ be a Dedekind domain with fraction field $K$, $L/K$ a finite separable extension, and $B$ the integral closure of $A$ in $L$. Then $B$ is a Dedekind domain with fraction field $L$, and $B$ is a finitely generated $A$-module.

*Proof.* Integrally closed: an element of $L$ integral over $B$ is integral over $A$, by transitivity of integrality (Chapter 1, Section 1), so it lies in $B$. Fraction field: every $x \in L$ satisfies an equation over $K$, and clearing denominators gives $d \in A \setminus 0$ with $dx$ integral over $A$, so $x = (dx)/d$.

Dimension: let $0 \ne \mathfrak Q$ be a prime of $B$, and $\mathfrak p = \mathfrak Q \cap A$. A nonzero $y \in \mathfrak Q$ satisfies $y^n + a_{n-1}y^{n-1} + \cdots + a_0 = 0$ with $a_i \in A$ and $n$ least, so $a_0 \ne 0$, and $a_0 \in \mathfrak Q \cap A = \mathfrak p$. So $\mathfrak p \ne 0$, and $\mathfrak p$ is maximal in $A$. Over a maximal ideal, the primes of an integral extension are maximal (Chapter 1, Section 3). So $\mathfrak Q$ is maximal.

Noetherian: since $L/K$ is separable, the trace form $(x, y) \mapsto \operatorname{Tr}_{L/K}(xy)$ is nondegenerate (Volume 11). Take a basis $b_1, \ldots, b_n$ of $L/K$ inside $B$ and its dual basis $b_1^*, \ldots, b_n^*$ for the trace form. For $x \in B$, write $x = \sum c_i b_i^*$, with $c_i = \operatorname{Tr}(x b_i)$. The trace of an integral element is integral over $A$ and lies in $K$, so it lies in $A$. So $B \subseteq A b_1^* + \cdots + A b_n^*$, a finitely generated $A$-module. Since $A$ is Noetherian, $B$ is a finitely generated $A$-module, and every ideal of $B$ is a finitely generated $A$-module, so $B$ is Noetherian. $\square$

::: mathlib
`integralClosure.isDedekindDomain` · `Mathlib.RingTheory.DedekindDomain.IntegralClosure`

For a Dedekind domain `A` with fraction field `K` and a finite separable extension `L` of `K`: `IsDedekindDomain (integralClosure A L)`. The version for any ring with `IsIntegralClosure B A L` is `IsIntegralClosure.isDedekindDomain`. The Noetherian part is `integralClosure.isNoetherianRing`, and the finiteness as a module is `IsIntegralClosure.finite`.

<?decl integralClosure.isDedekindDomain?>
:::

The trace argument is where separability enters. The theorem stays true without separability, by the Krull-Akizuki theorem, but the proof is harder, and the index of this edition has no declaration for the Krull-Akizuki theorem.

::: mathlib
`NumberField.RingOfIntegers` · `Mathlib.NumberTheory.NumberField.Basic`

The ring of integers `𝓞 K` of a number field `K`, the integral closure of `ℤ` in `K`. Mathlib has an instance that it is a Dedekind domain, by the theorem above with $A = \mathbb{Z}$. The number theory is in Volume 12.

<?decl NumberField.RingOfIntegers?>
:::

### Examples

**Example (PIDs).** The rings $\mathbb{Z}$, $k[X]$, $\mathbb{Z}[i]$ and every DVR are Dedekind domains. For a PID the theory of the chapter reduces to unique factorization of elements: every ideal is $(a)$, and its prime factorization is the factorization of $a$.

**Example (Quadratic rings of integers).** For a squarefree integer $d \equiv 2, 3 \pmod 4$, the ring of integers of $\mathbb{Q}(\sqrt d)$ is $\mathbb{Z}[\sqrt d]$ (Chapter 1, Section 2), so it is a Dedekind domain by the theorem. For $d = -5$ the ring $\mathbb{Z}[\sqrt{-5}]$ is Dedekind and not a UFD, since $2 \cdot 3 = (1 + \sqrt{-5})(1 - \sqrt{-5})$ are two factorizations into irreducibles. A Dedekind domain is a UFD if and only if it is a PID, a fact of Chapter 5.

**Example (Not integrally closed).** The ring $\mathbb{Z}[\sqrt{-3}]$ is Noetherian of dimension $1$, as a finite extension of $\mathbb{Z}$, but not integrally closed: $\omega = (1 + \sqrt{-3})/2$ satisfies $\omega^2 - \omega + 1 = 0$. So it is not Dedekind. Its localization at the prime $\mathfrak p = (2, 1 + \sqrt{-3})$ is not a DVR, and the ideal $\mathfrak p$ satisfies $\mathfrak p^2 = 2\mathfrak p$ without being principal, so the cancellation law of Section 2 fails. Its integral closure $\mathbb{Z}[\omega]$ is a PID.

**Example (Curves).** Let $k$ be a field of characteristic not $2$ and $A = k[X, Y]/(Y^2 - X^3 + X)$, the coordinate ring of an affine elliptic curve. It is a free $k[X]$-module with basis $1, y$, so it is integral and finite over $k[X]$, Noetherian, and of dimension $1$ by Chapter 1, Section 3. At each point the maximal ideal is principal in the local ring: at $(a, b)$ with $b \ne 0$ it is generated by $x - a$, and at $(a, 0)$ by $y$, because the curve is smooth. So every localization at a maximal ideal is a DVR, and $A$ is Dedekind. On the other hand $k[X, Y]$ has dimension $2$, and $k[X, Y]/(Y^2 - X^3)$ is not integrally closed (Chapter 3, Section 3), so neither is Dedekind.

### The library around it

The file `DedekindDomain/Basic.lean` has the classes and the definition through a fraction field. `DedekindDomain/Dvr.lean` has the characterization by localizations, and `DedekindDomain/IntegralClosure.lean` the theorem on integral closures, with the trace argument stated in `integralClosure_le_span_dualBasis`. `Ring.DimensionLEOne.of_isIntegral` transfers the dimension condition along integral extensions. The file `DedekindDomain/PID.lean` proves that a Dedekind domain with finitely many primes is a PID. Section 2 gives the inverse ideals.

Common errors of a learner:

- `IsDedekindDomain A` includes `IsDomain A`. Do not add a second `[IsDomain A]` argument, which creates two instance paths.
- `IsNoetherian A A` and `IsNoetherianRing A` are the same notion with different names. The characterization uses the first.
- The theorem on integral closures needs `[Algebra.IsSeparable K L]`, a finite dimensional extension, and the scalar tower `A → K → L`.

### Exercises

1. (A) Show that a Dedekind domain with exactly one nonzero prime is a DVR.
2. (A) Show that $\mathbb{Z}[X]$ is not Dedekind, by a chain of primes $0 \subsetneq (X) \subsetneq (2, X)$.
3. (A) Show that $\mathbb{Z}[\sqrt{-3}]$ has dimension $1$.
4. (B) Show that every localization $S^{-1}A$ of a Dedekind domain $A$, with $0 \notin S$, is Dedekind.
5. (B) Show that a domain $A$ equals the intersection of the localizations $A_{\mathfrak m}$ at its maximal ideals, inside its fraction field.
6. (B) Show that the ring of integers of $\mathbb{Q}(\sqrt{-3})$ is $\mathbb{Z}[\omega]$ with $\omega = (1 + \sqrt{-3})/2$, and that it is Euclidean for the norm.
7. (B) Show that a Dedekind domain that is semilocal, with finitely many maximal ideals, is a PID. Use the Chinese remainder theorem to find a generator of each prime.
8. (C) Let $A = k[X, Y]/(Y^2 - X^3 + X)$ as in the example. Show that the maximal ideal $(x, y)$ at the origin is not principal in $A$ itself, although it becomes principal in $A_{(x, y)}$.

### Notes and history

Dedekind developed the theory of ideals in rings of algebraic integers in the supplements to Dirichlet's *Vorlesungen über Zahlentheorie* (1871 and later editions), building on Kummer's ideal numbers. Emmy Noether gave the abstract characterization by the three conditions of this section in 1927. The characterization by localizations is in Atiyah and Macdonald, Theorem 9.3.

### Reference

<?reference?>
