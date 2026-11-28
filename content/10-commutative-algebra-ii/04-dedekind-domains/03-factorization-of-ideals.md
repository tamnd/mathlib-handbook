---
title: Factorization of ideals
kind: theory
modules:
  - Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
  - Mathlib.RingTheory.DedekindDomain.Factorization
  - Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
  - Mathlib.RingTheory.RamificationInertia.Ramification
  - Mathlib.RingTheory.RamificationInertia.Basic
  - Mathlib.RingTheory.RamificationInertia.Inertia
explains:
  E3: [Ideal.uniqueFactorizationMonoid, Ideal.dvd_iff_le, IsDedekindDomain.HeightOneSpectrum, IsDedekindDomain.HeightOneSpectrum.intValuation, Ideal.ramificationIdx]
  E2: [Ideal.prod_normalizedFactors_eq_self, Ideal.isPrime_of_prime, Ideal.prime_of_isPrime, Ideal.finprod_heightOneSpectrum_factorization, IsDedekindDomain.HeightOneSpectrum.maxPowDividing, IsDedekindDomain.quotientEquivPiFactors, IsDedekindDomain.exists_eq_span_pair, IsDedekindDomain.HeightOneSpectrum.valuation, IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_dvd, Ideal.inertiaDeg, Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count, Ideal.sum_ramification_inertia_eq_finrank]
  E1: auto
families: []
requires: [V10.C01, V10.C03]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Factorization of ideals

### Overview

In a Dedekind domain every nonzero ideal is a product of prime ideals, in a unique way up to order. This is the theorem that Dedekind proved for rings of integers, and it replaces unique factorization of elements, which fails in rings such as $\mathbb{Z}[\sqrt{-5}]$. The proof uses the cancellation law of Section 2 and the rule "to contain is to divide": $I \mid J$ if and only if $J \subseteq I$.

The exponent of a prime $\mathfrak p$ in the factorization of $(x)$ defines a valuation $v_{\mathfrak p}$ on the fraction field, the $\mathfrak p$-adic valuation, which is the valuation of the DVR $A_{\mathfrak p}$. For an extension $A \subseteq B$ of Dedekind domains, the factorization of $\mathfrak p B$ defines the ramification indices and residue degrees. The section ends with the factorization of $(6)$ in $\mathbb{Z}[\sqrt{-5}]$.

### Definitions

Let $A$ be a Dedekind domain with fraction field $K$.

**Definition (Divisibility of ideals).** For ideals $I, J$ of $A$, $I$ divides $J$, written $I \mid J$, if $J = IC$ for an ideal $C$.

Always $IC \subseteq I$, so $I \mid J$ implies $J \subseteq I$. The converse is the first theorem below.

**Definition (Height one spectrum).** The height one spectrum of $A$ is the set of nonzero prime ideals of $A$. For a Dedekind domain that is not a field these are the maximal ideals.

::: mathlib
`IsDedekindDomain.HeightOneSpectrum` · `Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas`

A term `v : HeightOneSpectrum R` is a structure with an ideal `v.asIdeal`, a proof that it is prime, and a proof that it is not `⊥`. The name comes from algebraic geometry: the nonzero primes of a Dedekind domain are its primes of height one (Chapter 7). The adic valuations and the adeles of Volume 12 are indexed by this type.

<?decl IsDedekindDomain.HeightOneSpectrum?>
:::

**Definition ($\mathfrak p$-adic valuation).** For a nonzero prime $\mathfrak p$ and $x \in A$, $x \ne 0$, $v_{\mathfrak p}(x)$ is the exponent of $\mathfrak p$ in the factorization of $(x)$. For $x/y \in K^\times$, $v_{\mathfrak p}(x/y) = v_{\mathfrak p}(x) - v_{\mathfrak p}(y)$.

::: mathlib
`IsDedekindDomain.HeightOneSpectrum.intValuation` · `Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation`

`v.intValuation : Valuation R ℤᵐ⁰`, in the multiplicative form of Chapter 3: an element `r ≠ 0` has value `exp (-n)`, with `n` the exponent of `v.asIdeal` in `(r)`. The criterion is `intValuation_le_pow_iff_dvd`: the value is at most `exp (-n)` if and only if `v.asIdeal ^ n ∣ span {r}`. The extension to the fraction field is `IsDedekindDomain.HeightOneSpectrum.valuation K v`.

<?decl IsDedekindDomain.HeightOneSpectrum.intValuation?>
:::

### Theorems and proofs

**Theorem (To contain is to divide).** Let $I, J$ be ideals of a Dedekind domain with $I \ne 0$. Then $I \mid J$ if and only if $J \subseteq I$.

*Proof.* If $J \subseteq I$, let $C = I^{-1}J$. It is a fractional ideal with $C \subseteq I^{-1}I = A$, so $C$ is an ideal, and $IC = II^{-1}J = J$ by Section 2. $\square$

::: mathlib
`Ideal.dvd_iff_le` · `Mathlib.RingTheory.DedekindDomain.Ideal.Basic`

`I ∣ J ↔ J ≤ I` in a Dedekind domain. Since `Ideal A` is a commutative monoid, `∣` is the divisibility of any monoid.

<?decl Ideal.dvd_iff_le?>
:::

As a consequence, the prime elements of the monoid of ideals are the nonzero prime ideals: $\mathfrak p \mid IJ$ means $IJ \subseteq \mathfrak p$, which gives $I \subseteq \mathfrak p$ or $J \subseteq \mathfrak p$.

**Theorem (Unique factorization of ideals).** Let $A$ be a Dedekind domain and $I \ne 0$ an ideal. Then $I = \mathfrak p_1^{e_1} \cdots \mathfrak p_r^{e_r}$ with distinct nonzero primes $\mathfrak p_i$ and $e_i \ge 1$, and the primes and exponents are unique.

*Proof.* Existence. Assume some nonzero ideal has no factorization. Since $A$ is Noetherian, there is a maximal such ideal $I$. Then $I \ne A$, which is the empty product, so $I \subseteq \mathfrak p$ for a maximal ideal $\mathfrak p$, and $I = \mathfrak p C$ by the previous theorem. Since $\mathfrak p^{-1} \not\subseteq A$ (otherwise $A = \mathfrak p\mathfrak p^{-1} \subseteq \mathfrak p$), cancellation shows that $C = \mathfrak p^{-1} I \supsetneq I$: indeed $C = I$ would give $\mathfrak p I = I$, and cancelling $I$ gives $\mathfrak p = A$. By maximality, $C$ has a factorization, and so has $I = \mathfrak p C$. This is a contradiction.

Uniqueness. Let $\mathfrak p_1 \cdots \mathfrak p_n = \mathfrak q_1 \cdots \mathfrak q_m$ be two products of nonzero primes. Then $\mathfrak q_1 \cdots \mathfrak q_m \subseteq \mathfrak p_1$, so some $\mathfrak q_j \subseteq \mathfrak p_1$, and $\mathfrak q_j = \mathfrak p_1$ since $\mathfrak q_j$ is maximal. Cancel $\mathfrak p_1$ in the group of fractional ideals and use induction on $n$. $\square$

::: mathlib
`Ideal.uniqueFactorizationMonoid` · `Mathlib.RingTheory.DedekindDomain.Ideal.Basic`

The instance `UniqueFactorizationMonoid (Ideal A)` for a Dedekind domain. All the factorization theory of Volume 9 applies to ideals: `UniqueFactorizationMonoid.normalizedFactors I` is the multiset of prime factors, and `Ideal.prod_normalizedFactors_eq_self` says that their product is `I`. The form with the height one spectrum is `Ideal.finprod_heightOneSpectrum_factorization`: `I = ∏ᶠ v, v.maxPowDividing I`, where `v.maxPowDividing I` is the largest power of `v.asIdeal` that divides `I`. The prime elements of `Ideal A` are the nonzero primes, by `Ideal.prime_of_isPrime` and `Ideal.isPrime_of_prime`.

<?decl Ideal.uniqueFactorizationMonoid?>
:::

**Corollary (Operations through exponents).** Write $v_{\mathfrak p}(I)$ for the exponent of $\mathfrak p$ in $I$. Then $v_{\mathfrak p}(IJ) = v_{\mathfrak p}(I) + v_{\mathfrak p}(J)$, $I \subseteq J \iff v_{\mathfrak p}(I) \ge v_{\mathfrak p}(J)$ for all $\mathfrak p$, $v_{\mathfrak p}(I + J) = \min$ and $v_{\mathfrak p}(I \cap J) = \max$.

*Proof.* The first is unique factorization. The second is "to contain is to divide". The ideal $I + J$ is the smallest ideal containing both, so it is the largest common divisor, with exponents the minima, and $I \cap J$ is the least common multiple. $\square$

**Theorem (Chinese remainder theorem for a Dedekind domain).** Let $I = \mathfrak p_1^{e_1} \cdots \mathfrak p_r^{e_r}$. Then $A/I \cong A/\mathfrak p_1^{e_1} \times \cdots \times A/\mathfrak p_r^{e_r}$.

*Proof.* For $i \ne j$, $\mathfrak p_i^{e_i} + \mathfrak p_j^{e_j}$ has all exponents $0$, so it equals $A$. The Chinese remainder theorem for pairwise comaximal ideals (Volume 6) applies, and the product of the $\mathfrak p_i^{e_i}$ equals their intersection. $\square$

::: mathlib
`IsDedekindDomain.quotientEquivPiFactors` · `Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas`

The ring isomorphism `R ⧸ I ≃+* ((P : factors I) → R ⧸ P ^ count P (factors I))` for `I ≠ ⊥`. A consequence proved with the same tool is `IsDedekindDomain.exists_eq_span_pair`: every ideal containing a nonzero `x` is `span {x, y}` for some `y`, so every ideal of a Dedekind domain is generated by two elements.

<?decl IsDedekindDomain.quotientEquivPiFactors?>
:::

**Theorem (The $\mathfrak p$-adic valuation).** For each nonzero prime $\mathfrak p$, $v_{\mathfrak p}$ is a discrete valuation on $K$, and it is the valuation of the DVR $A_{\mathfrak p}$. Every $x \in K^\times$ has $v_{\mathfrak p}(x) = 0$ for all but finitely many $\mathfrak p$, and $x \in A$ if and only if $v_{\mathfrak p}(x) \ge 0$ for all $\mathfrak p$.

*Proof.* $v_{\mathfrak p}(xy) = v_{\mathfrak p}(x) + v_{\mathfrak p}(y)$ by the corollary, since $(xy) = (x)(y)$. For sums, $(x + y) \subseteq (x) + (y)$ gives $v_{\mathfrak p}(x + y) \ge \min$. In $A_{\mathfrak p}$, the factorization of $(x)$ becomes $\mathfrak p^{v_{\mathfrak p}(x)} A_{\mathfrak p}$, since the other primes become the unit ideal, so $v_{\mathfrak p}$ is the valuation of the DVR $A_{\mathfrak p}$. Finiteness: $(x)$ has finitely many prime factors. Last claim: $x = a/b$ lies in $A$ iff $(b) \mid (a)$ iff the exponents of $(a)$ dominate those of $(b)$. $\square$

### Examples

**Example (Factorization of $(6)$ in $\mathbb{Z}[\sqrt{-5}]$).** Let $A = \mathbb{Z}[\sqrt{-5}]$, and
$$\mathfrak p = (2, 1 + \sqrt{-5}), \quad \mathfrak q = (3, 1 + \sqrt{-5}), \quad \mathfrak q' = (3, 1 - \sqrt{-5}).$$
These are maximal: $A/\mathfrak p \cong \mathbb{F}_2$ and $A/\mathfrak q \cong A/\mathfrak q' \cong \mathbb{F}_3$, since $A \cong \mathbb{Z}[X]/(X^2 + 5)$, and $A/\mathfrak q \cong \mathbb{F}_3[X]/(X^2 + 5, X + 1) = \mathbb{F}_3$ because $(-1)^2 + 5 = 6 \equiv 0$. Section 2 computed $\mathfrak p^2 = (2)$. Next,
$$\mathfrak q \mathfrak q' = (9,\ 3(1 - \sqrt{-5}),\ 3(1 + \sqrt{-5}),\ 6) = (3),$$
since all generators are multiples of $3$ and $9 - 6 = 3$. Similarly $\mathfrak p\mathfrak q = (1 + \sqrt{-5})$: the generators of $\mathfrak p\mathfrak q$ are $6$, $2 + 2\sqrt{-5}$, $3 + 3\sqrt{-5}$ and $(1 + \sqrt{-5})^2 = -4 + 2\sqrt{-5}$, all multiples of $1 + \sqrt{-5}$ (note $6 = (1 + \sqrt{-5})(1 - \sqrt{-5})$), and $(3 + 3\sqrt{-5}) - (2 + 2\sqrt{-5}) = 1 + \sqrt{-5}$. In the same way $\mathfrak p\mathfrak q' = (1 - \sqrt{-5})$. So
$$(6) = \mathfrak p^2 \mathfrak q \mathfrak q', \qquad (2)(3) = \mathfrak p^2 \cdot \mathfrak q\mathfrak q', \qquad (1 + \sqrt{-5})(1 - \sqrt{-5}) = \mathfrak p\mathfrak q \cdot \mathfrak p\mathfrak q'.$$
The two factorizations of the element $6$ group the same four prime ideals in two ways. None of $\mathfrak p$, $\mathfrak q$, $\mathfrak q'$ is principal: a generator would have norm $2$ or $3$, and $a^2 + 5b^2$ takes neither value.

**Example (Valuations in $\mathbb{Z}[\sqrt{-5}]$).** With the primes of the previous example, $v_{\mathfrak p}(6) = 2$, $v_{\mathfrak q}(6) = v_{\mathfrak q'}(6) = 1$, and $v_{\mathfrak p}(1 + \sqrt{-5}) = 1$, $v_{\mathfrak q}(1 + \sqrt{-5}) = 1$, $v_{\mathfrak q'}(1 + \sqrt{-5}) = 0$. The element $x = 2/(1 + \sqrt{-5})$ has $v_{\mathfrak p}(x) = 2 - 1 = 1$ and $v_{\mathfrak q}(x) = -1$, so $x \notin A$.

**Example (Ramification in $\mathbb{Z}[i]$).** Let $B = \mathbb{Z}[i]$ over $A = \mathbb{Z}$. Then $2B = (1 + i)^2$, since $(1 + i)^2 = 2i$; $5B = (2 + i)(2 - i)$; and $3B$ is prime, since $X^2 + 1$ is irreducible mod $3$. For a prime $\mathfrak Q$ of $B$ over $p$, the ramification index $e$ is the exponent of $\mathfrak Q$ in $pB$, and the residue degree $f$ is $[B/\mathfrak Q : \mathbb{F}_p]$. For $p = 2$: one prime, $e = 2$, $f = 1$. For $p = 5$: two primes, $e = f = 1$. For $p = 3$: one prime, $e = 1$, $f = 2$. In each case $\sum e_i f_i = 2 = [\mathbb{Q}(i) : \mathbb{Q}]$.

::: mathlib
`Ideal.ramificationIdx` · `Mathlib.RingTheory.RamificationInertia.Ramification`

`P.ramificationIdx R` is the ramification index of a prime `P` of `S` over its contraction to `R`, the exponent of `P` in the extended ideal. `Ideal.inertiaDeg` is the residue degree. For Dedekind domains, `Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count` identifies the index with a multiplicity in the factorization, and `Ideal.sum_ramification_inertia_eq_finrank` proves $\sum e_i f_i = \operatorname{rank}_R S$ for a finite flat extension.

<?decl Ideal.ramificationIdx?>
:::

### The library around it

The theory is spread over `DedekindDomain/Ideal/Basic.lean` (inverses, the monoid structure, "to contain is to divide"), `DedekindDomain/Ideal/Lemmas.lean` (factors, the Chinese remainder theorem, the height one spectrum), `DedekindDomain/Factorization.lean` (factorization of ideals and fractional ideals as finite products over the height one spectrum, with `FractionalIdeal.count` for the exponents), and `DedekindDomain/AdicValuation/` (the valuations and the completions, used for the adeles of Volume 12). Ramification and inertia are in `Mathlib/RingTheory/RamificationInertia/`.

The module `Mathlib.RingTheory.RamificationInertia.Inertia` has the residue degree. For a prime `q` of `S`, `q.inertiaDeg R` is the degree of the residue field of `q` over the residue field of the prime `Ideal.under R q`, by `Ideal.inertiaDeg_def`. It is $0$ when `q` is not prime, `Ideal.inertiaDeg_of_not_isPrime`. When the primes are maximal, `Ideal.inertiaDeg_eq_of_isMaximal` gives the degree of $S/q$ over $R/p$, and `Ideal.inertiaDeg_eq_of_isFractionRing` treats the zero ideal through fraction fields. The degree is multiplicative in a tower, `Ideal.inertiaDeg_tower`, and the degree in a tower divides the total degree, `Ideal.inertiaDeg_below_dvd` and `Ideal.inertiaDeg_above_dvd`. It is invariant under a group action, `Ideal.inertiaDeg_smul`. For finite residue fields, `Ideal.absNorm_pow_inertiaDeg` says that $N(p)^f = N(q)$, and `Ideal.pow_inertiaDeg` is the case $R = \mathbb{Z}$, where $N(q) = p^f$.

Common errors of a learner:

- In `Ideal A`, multiplication is the product of ideals and `≤` is inclusion, so `I ∣ J` corresponds to `J ≤ I`, with the order reversed.
- `normalizedFactors` returns a multiset, and the exponent of `P` is `Multiset.count P (normalizedFactors I)`. The ideal `I` must be nonzero.
- The valuation `intValuation` is multiplicative, so a larger exponent gives a smaller value.

### Exercises

1. (A) Factor $(10)$ and $(2 + \sqrt{-5})$ in $\mathbb{Z}[\sqrt{-5}]$.
2. (A) Factor $(2)$, $(3)$, $(5)$, $(7)$ and $(13)$ in $\mathbb{Z}[i]$, and give $e$ and $f$ for each.
3. (A) Show that in a Dedekind domain, $I + J = A$ if and only if $I$ and $J$ have no common prime factor.
4. (B) Show that a Dedekind domain with finitely many prime ideals is a PID. Choose $x_i \in \mathfrak p_i \setminus \mathfrak p_i^2$ and use the Chinese remainder theorem to get an element with prescribed valuations.
5. (B) Let $I \ne 0$ be an ideal of a Dedekind domain and $x \in I$ nonzero. Show that there is $y$ with $I = (x, y)$.
6. (B) Show that a Dedekind domain is a UFD if and only if it is a PID.
7. (B) Let $p$ be an odd prime. Show that $p$ ramifies in $\mathbb{Z}[\sqrt{-5}]$ if and only if $p = 5$, and that $p$ splits into two primes if and only if $-5$ is a square mod $p$.
8. (C) Let $A$ be a Dedekind domain and $I \ne 0$ an ideal. Show that $A/I$ is a principal ideal ring, and that every ideal of $A/I$ is generated by one element.

### Notes and history

Kummer introduced "ideal numbers" in the 1840s to restore unique factorization in cyclotomic rings, in connection with Fermat's Last Theorem. Dedekind defined ideals as sets and proved the unique factorization of ideals in rings of integers of number fields in 1871. The rule "to contain is to divide" is a classical name for the theorem of this section. The relation $\sum e_i f_i = n$ is the fundamental identity of algebraic number theory.

### Reference

<?reference?>
