---
title: Ideals of a localization and local rings
kind: theory
modules:
  - Mathlib.RingTheory.Localization.Ideal
  - Mathlib.RingTheory.Localization.AtPrime.Basic
  - Mathlib.RingTheory.ZMod.LocalRing
explains:
  E3: [IsLocalization.orderIsoOfPrime, IsLocalization.isPrime_iff_isPrime_disjoint, Localization.AtPrime.isLocalRing]
  E2: [IsLocalization.map_under, IsLocalization.under_map_of_isPrime_disjoint, IsLocalization.isPrime_of_isPrime_disjoint, IsLocalization.mem_map_algebraMap_iff, IsLocalization.map_algebraMap_ne_top_iff_disjoint, "IsLocalization.mk'_mem_iff", IsLocalization.disjoint_under_iff, IsLocalization.AtPrime.isLocalRing, IsLocalization.AtPrime.map_eq_maximalIdeal, IsLocalization.AtPrime.to_map_mem_maximal_iff, IsLocalization.AtPrime.isUnit_to_map_iff, IsLocalization.AtPrime.orderIsoOfPrime, IsLocalization.AtPrime.equivQuotMaximalIdeal, IsLocalization.map_radical, IsLocalization.instQuotientIdealAlgebraMapSubmonoidMapRingHomAlgebraMap, nonunits, Ideal.under]
  E1: auto
families: []
requires: [V09.C01, V06.C02, V06.C03]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Ideals of a localization and local rings

### Overview

The map $\iota : R \to S^{-1} R$ of Section 1 gives extension and contraction of ideals, as in Chapter 1, Section 1. Every ideal of $S^{-1} R$ is extended from $R$, and the prime ideals of $S^{-1} R$ correspond to the prime ideals of $R$ that miss $S$. So $R_{\mathfrak{p}}$ has exactly one maximal ideal: it is a local ring. The section ends with localization of quotients and the residue field of $R_{\mathfrak{m}}$.

Throughout, $S$ is a multiplicative subset of $R$, $\iota : R \to S^{-1} R$ is the localization map, and $I^e = S^{-1} I$ and $J^c = \iota^{-1}(J)$ are taken along $\iota$.

### Definitions

**Definition (Saturated ideal).** An ideal $I$ of $R$ is $S$-saturated if $u r \in I$ with $u \in S$ implies $r \in I$.

**Definition (Local ring).** A ring $R$ is local if it has exactly one maximal ideal $\mathfrak{m}$. The field $R/\mathfrak{m}$ is its residue field.

**Definition (Nonunits).** The set of nonunits of $R$ is $R \setminus R^\times$.

::: mathlib
`IsLocalRing` · `Mathlib.RingTheory.LocalRing.Defs`

The class `IsLocalRing R` says that `R` is nontrivial and that `a + b = 1` forces `IsUnit a` or `IsUnit b`. The constructors `IsLocalRing.of_unique_max_ideal` and `IsLocalRing.of_nonunits_add` give the other definitions of the theorem below. The maximal ideal `IsLocalRing.maximalIdeal R` has as members the elements of `nonunits R`. Volume 10 develops this API.

<?decl IsLocalRing?>
:::

### Theorems and proofs

**Theorem (Extended ideals).** Let $I$ be an ideal of $R$.

1. $S^{-1} I = \{ a/s : a \in I, s \in S \}$.
2. $(S^{-1} I)^c = \{ r \in R : u r \in I \text{ for some } u \in S \}$.
3. $S^{-1} I = S^{-1} R$ if and only if $I \cap S \ne \emptyset$.

*Proof.* (1) Let $T$ be the set of the $a/s$ with $a \in I$. It lies in $S^{-1} I$, since $a/s = \iota(a) \cdot (1/s)$. It is an ideal: $a/s + b/t = (a t + b s)/(s t)$ and $(r/t)(a/s) = (r a)/(t s)$ have numerators in $I$. It contains $\iota(I)$. So $S^{-1} I \subseteq T$.

(2) Let $r/1 \in S^{-1} I$. By (1), $r/1 = a/s$ with $a \in I$, so $v (r s - a) = 0$ for some $v \in S$. Then $(v s) r = v a \in I$ and $v s \in S$. Conversely, if $u r \in I$, then $r/1 = (u r)/u \in S^{-1} I$.

(3) $S^{-1} I = S^{-1} R$ means $1 \in (S^{-1} I)^c$, that is, $u \in I$ for some $u \in S$ by (2). $\square$

**Theorem (Ideals of $S^{-1} R$).** Each ideal $J$ of $S^{-1} R$ satisfies $J = (J^c)^e$. The maps $J \mapsto J^c$ and $I \mapsto S^{-1} I$ are inverse bijections between the ideals of $S^{-1} R$ and the $S$-saturated ideals of $R$, and they preserve inclusion.

*Proof.* $(J^c)^e \subseteq J$ by the Galois connection. If $a/s \in J$, then $\iota(a) = (a/s)(s/1) \in J$, so $a \in J^c$ and $a/s \in (J^c)^e$ by part (1) above. By part (2), $I = I^{ec}$ holds exactly when $I$ is $S$-saturated. So the contracted ideals of $R$ are the $S$-saturated ideals. The bijection follows from Chapter 1, Section 1. $\square$

::: mathlib
`IsLocalization.map_under` · `Mathlib.RingTheory.Localization.Ideal`

The equation $J = J^{ce}$ as `Ideal.map (algebraMap R S) (Ideal.under R J) = J`. Here `Ideal.under R J` is the contraction `Ideal.comap (algebraMap R S) J`. Part (1) of the previous theorem is `IsLocalization.mem_map_algebraMap_iff`, and part (3) is `IsLocalization.map_algebraMap_ne_top_iff_disjoint`, in the form `≠ ⊤ ↔ Disjoint ↑M ↑I`. By `IsLocalization.mk'_mem_iff`, membership does not see the denominator.

<?decl IsLocalization.map_under?>
:::

**Theorem (Prime ideals of $S^{-1} R$).** The maps $Q \mapsto Q^c$ and $P \mapsto S^{-1} P$ are inverse bijections, preserving inclusion, between the prime ideals of $S^{-1} R$ and the prime ideals $P$ of $R$ with $P \cap S = \emptyset$.

*Proof.* Let $Q$ be prime. Then $Q^c$ is prime (Chapter 1, Section 1). If $s \in Q^c \cap S$, then the unit $\iota(s)$ lies in $Q$, which is impossible. So $Q^c \cap S = \emptyset$, and $Q = Q^{ce}$ by the previous theorem.

Let $P$ be prime with $P \cap S = \emptyset$. If $u r \in P$ with $u \in S$, then $u \notin P$, so $r \in P$. So $P$ is $S$-saturated and $P^{ec} = P$. The ideal $S^{-1} P$ is proper by part (3) of the theorem on extended ideals. If $(a/s)(b/t) \in S^{-1} P$, then $\iota(a b) = (a/s)(b/t) \cdot \iota(s t) \in S^{-1} P$, so $a b \in P^{ec} = P$. Hence $a \in P$ or $b \in P$, and $a/s$ or $b/t$ lies in $S^{-1} P$. $\square$

::: mathlib
`IsLocalization.orderIsoOfPrime` · `Mathlib.RingTheory.Localization.Ideal`

The theorem as an order isomorphism `{p : Ideal S // p.IsPrime} ≃o {p : Ideal R // p.IsPrime ∧ Disjoint ↑M ↑p}`. The two halves are `IsLocalization.isPrime_iff_isPrime_disjoint`, which says that `J` is prime exactly when its contraction is prime and misses `M`, and `IsLocalization.isPrime_of_isPrime_disjoint` with `IsLocalization.under_map_of_isPrime_disjoint` for the other direction. `IsLocalization.disjoint_under_iff` says that the contraction of `J` misses `M` exactly when `J ≠ ⊤`.

<?decl IsLocalization.orderIsoOfPrime?>
:::

**Theorem (Local rings).** For a nonzero ring $R$, the following are equivalent:

1. $R$ is local;
2. the nonunits of $R$ form an ideal;
3. for each $a \in R$, $a$ or $1 - a$ is a unit.

If they hold, the maximal ideal is the set of nonunits.

*Proof.* (1) implies (2). Each nonunit $a$ generates a proper ideal, which lies in a maximal ideal (Volume 6, Chapter 2), so $a \in \mathfrak{m}$. Conversely $\mathfrak{m}$ contains no unit. So the nonunits form the ideal $\mathfrak{m}$.

(2) implies (3). If $a$ and $1 - a$ are nonunits, so is their sum $1$, a contradiction.

(3) implies (2). Let $N$ be the set of nonunits. Then $0 \in N$ since $R \ne 0$. If $a \in N$, then $r a \in N$, since $r a v = 1$ would make $a$ a unit. Let $a, b \in N$ and suppose $a + b = u$ is a unit. Then $a u^{-1} + b u^{-1} = 1$ with $a u^{-1} \in N$, so $b u^{-1} = 1 - a u^{-1}$ is a unit by (3), and $b$ is a unit, a contradiction.

(2) implies (1). $N$ is a proper ideal, and each proper ideal lies in $N$, since it contains no unit. So $N$ is the only maximal ideal. $\square$

**Corollary ($R_{\mathfrak{p}}$ is local).** For a prime ideal $\mathfrak{p}$, the ring $R_{\mathfrak{p}}$ is local with maximal ideal $\mathfrak{p} R_{\mathfrak{p}}$. An element $a/s$ is a unit exactly when $a \notin \mathfrak{p}$.

*Proof.* If $a \notin \mathfrak{p}$, then $a/s$ has inverse $s/a$. If $a \in \mathfrak{p}$, then $a/s \in \mathfrak{p} R_{\mathfrak{p}}$, a proper ideal by part (3) of the theorem on extended ideals, so $a/s$ is not a unit. So the nonunits form the ideal $\mathfrak{p} R_{\mathfrak{p}}$, and $R_{\mathfrak{p}}$ is local by the theorem. $\square$

By the theorem on primes, the primes of $R_{\mathfrak{p}}$ correspond to the primes of $R$ contained in $\mathfrak{p}$.

::: mathlib
`Localization.AtPrime.isLocalRing` · `Mathlib.RingTheory.Localization.AtPrime.Basic`

The instance `IsLocalRing (Localization.AtPrime P)`. For any model there is `IsLocalization.AtPrime.isLocalRing`. Then `IsLocalization.AtPrime.map_eq_maximalIdeal` says that $\mathfrak{p} R_{\mathfrak{p}}$ is the maximal ideal, `IsLocalization.AtPrime.isUnit_to_map_iff` and `IsLocalization.AtPrime.to_map_mem_maximal_iff` describe units and nonunits among the $\iota(x)$, and `IsLocalization.AtPrime.orderIsoOfPrime` is the bijection with the primes inside `P`.

<?decl Localization.AtPrime.isLocalRing?>
:::

**Theorem (Quotients and residue fields).** Let $I$ be an ideal of $R$ and $\bar S$ the image of $S$ in $R/I$.

1. The map $g : R/I \to S^{-1} R / S^{-1} I$, $r + I \mapsto \iota(r) + S^{-1} I$, is a localization at $\bar S$.
2. For a maximal ideal $\mathfrak{m}$, the map $R/\mathfrak{m} \to R_{\mathfrak{m}}/\mathfrak{m} R_{\mathfrak{m}}$ is an isomorphism.

*Proof.* (1) The map $g$ is well defined since $\iota(I) \subseteq S^{-1} I$. Check the three conditions of Section 1. The images of $s \in S$ are units, since $\iota(s)$ is. Each class $a/s + S^{-1} I$ equals $g(a + I) g(s + I)^{-1}$. If $g(a + I) = 0$, then $a \in (S^{-1} I)^c$, so $u a \in I$ for some $u \in S$, that is, $(u + I)(a + I) = 0$. Since $g$ is additive, this kernel condition gives condition (3).

(2) The composite $R \to R_{\mathfrak{m}} \to R_{\mathfrak{m}}/\mathfrak{m} R_{\mathfrak{m}}$ has kernel $(\mathfrak{m} R_{\mathfrak{m}})^c = \mathfrak{m}$, by the theorem on primes. It is surjective: let $a/s$ with $s \notin \mathfrak{m}$. Since $R/\mathfrak{m}$ is a field, $s t - 1 \in \mathfrak{m}$ for some $t$. Then
$$\frac{a}{s} - \frac{a t}{1} = \frac{a (1 - s t)}{s} \in \mathfrak{m} R_{\mathfrak{m}}.$$
So the class of $a/s$ is the image of $a t$. $\square$

::: mathlib
`IsLocalization.AtPrime.equivQuotMaximalIdeal` · `Mathlib.RingTheory.Localization.AtPrime.Basic`

Part (2) as `R ⧸ p ≃ₐ[R] Rₚ ⧸ IsLocalRing.maximalIdeal Rₚ` for a maximal `p`. Part (1) is the instance `IsLocalization.instQuotientIdealAlgebraMapSubmonoidMapRingHomAlgebraMap`, which states `IsLocalization (Algebra.algebraMapSubmonoid (R ⧸ I) M) (S ⧸ I.map (algebraMap R S))`. The compatibility with radicals of Exercise 4 is `IsLocalization.map_radical`.

<?decl IsLocalization.AtPrime.equivQuotMaximalIdeal?>
:::

### Examples

**Example (Ideals of $\mathbb{Z}_{(p)}$).** Every ideal of $\mathbb{Z}_{(p)}$ is $S^{-1}(n)$ for some $n \ge 0$. Write $n = p^k m$ with $p \nmid m$. Then $m$ is a unit of $\mathbb{Z}_{(p)}$, so $S^{-1}(n) = (p^k)$. So the ideals are $0$ and $(p^k)$ for $k \ge 0$, and the primes are $0$ and $(p)$, which correspond to the primes $0$ and $(p)$ of $\mathbb{Z}$ inside $(p)$. The residue field is $\mathbb{Z}/p$.

**Counterexample (Not every ideal is contracted).** Let $S = \{1, 2, 4, \dots\} \subseteq \mathbb{Z}$ and $I = (6)$. Then $(S^{-1} I)^c = \{ r : 2^k r \in (6) \text{ for some } k \} = (3) \ne (6)$. The ideal $(6)$ is not $S$-saturated: $2 \cdot 3 \in (6)$ and $3 \notin (6)$.

**Counterexample (Only complements of primes give local rings).** Let $S = \mathbb{Z} \setminus ((2) \cup (3))$, a multiplicative set. The primes of $S^{-1} \mathbb{Z}$ correspond to the primes of $\mathbb{Z}$ inside $(2) \cup (3)$. By prime avoidance (Chapter 1, Section 3) such a prime lies in $(2)$ or in $(3)$, so it is $0$, $(2)$ or $(3)$. Hence $S^{-1} \mathbb{Z}$ has the two maximal ideals $2 S^{-1} \mathbb{Z}$ and $3 S^{-1} \mathbb{Z}$, and it is not local.

### The library around it

The module `Mathlib.RingTheory.ZMod.LocalRing` gives a small example of a local ring. For $r \neq 0$ the reduction $\mathbb{Z}/n^r \to \mathbb{Z}/n$ is a local homomorphism, `ZMod.isLocalHom_castHom_pow`, and so `ZMod (p ^ r)` is a local ring for a prime $p$, by the instance `ZMod.instIsLocalRingHPowNatOfFactPrimeOfNeZero`. Its maximal ideal is $(p)$.

`Mathlib.RingTheory.Localization.Ideal` holds the correspondence of ideals, and `Mathlib.RingTheory.Localization.AtPrime.Basic` the local ring $R_{\mathfrak{p}}$. Common errors:

- `Localization.AtPrime P` needs the instance `[P.IsPrime]`, since the submonoid `P.primeCompl` exists only for a prime.
- The contraction `Ideal.under R J` abbreviates `Ideal.comap (algebraMap R S) J`. Both forms appear in lemma names.
- `IsLocalRing.maximalIdeal R` is a definition, not a field of the class. To show that an ideal is the maximal ideal, use an equality lemma such as `IsLocalization.AtPrime.map_eq_maximalIdeal`.

### Exercises

1. (A) List the ideals of $\mathbb{Z}_{(3)}$ and the prime ideals of $\mathbb{Z}[1/6]$.
2. (A) For $I = (12)$ in $\mathbb{Z}$, compute $(S^{-1} I)^c$ for $S = \{2^k\}$ and for $S = \mathbb{Z} \setminus (2)$.
3. (A) Show that $\mathbb{Z}/p^n$ is local for a prime $p$, and that $\mathbb{Z}/n$ for $n > 1$ is local only if $n$ is a prime power.
4. (B) Show $S^{-1} \sqrt{I} = \sqrt{S^{-1} I}$, and deduce that the nilradical of $S^{-1} R$ is $S^{-1} \mathfrak{N}(R)$. Hint: from $u a^n \in I$ get $(u a)^n \in I$.
5. (B) Show $S^{-1}(I \cap J) = S^{-1} I \cap S^{-1} J$, $S^{-1}(I + J) = S^{-1} I + S^{-1} J$ and $S^{-1}(I J) = (S^{-1} I)(S^{-1} J)$.
6. (B) For a prime $\mathfrak{p}$, show that $R_{\mathfrak{p}}/\mathfrak{p} R_{\mathfrak{p}}$ is the field of fractions of $R/\mathfrak{p}$. Hint: apply part (1) of the last theorem with $I = \mathfrak{p}$.
7. (C) Let $\mathfrak{p}_1, \dots, \mathfrak{p}_n$ be primes, none contained in another, and $S = R \setminus (\mathfrak{p}_1 \cup \dots \cup \mathfrak{p}_n)$. Show that $S^{-1} R$ has exactly $n$ maximal ideals. Hint: use prime avoidance.

### Notes and history

Local rings go back to Krull, who called them Stellenringe. The proofs here follow Atiyah and Macdonald, Chapter 3.

### Reference

<?reference?>
