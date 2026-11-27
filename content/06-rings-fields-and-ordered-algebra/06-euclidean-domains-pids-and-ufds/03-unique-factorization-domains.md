---
title: Unique factorization domains
kind: theory
modules: []
explains:
  E1: [Irreducible, Prime, Associated, Prime.irreducible, irreducible_iff_prime, DvdNotUnit, WfDvdMonoid, WfDvdMonoid.exists_factors, UniqueFactorizationMonoid, UniqueFactorizationMonoid.irreducible_iff_prime, UniqueFactorizationMonoid.factors, UniqueFactorizationMonoid.factors_prod, UniqueFactorizationMonoid.factors_unique, UniqueFactorizationMonoid.of_exists_prime_factors, PrincipalIdealRing.isNoetherianRing, IsNoetherianRing.wfDvdMonoid, PrincipalIdealRing.to_uniqueFactorizationMonoid, Polynomial.uniqueFactorizationMonoid]
families: []
requires: [V06.C02, V06.C03, V06.C05]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Unique factorization domains

### Overview

The fundamental theorem of arithmetic says that every integer $n > 1$ is a product of primes, and that the factors are unique up to their order. This section states the same property for an integral domain and proves that every PID has it. The proof splits into two parts, and each part has its own hypothesis. Existence of a factorization needs a finiteness condition, the ascending chain condition on principal ideals. Uniqueness needs that every irreducible element is prime. A PID has both properties. The section also shows where each part fails: in $\mathbb{Z}[\sqrt{-5}]$ factorizations exist but are not unique, and in the ring $\mathbb{Z} + X\mathbb{Q}[X]$ the element $X$ has no factorization at all.

### Definitions

In this section $R$ is an integral domain.

**Definition (Associates).** Two elements $a, b \in R$ are associates, written $a \sim b$, if $a = ub$ for a unit $u$. In a domain this holds if and only if $a \mid b$ and $b \mid a$, if and only if $(a) = (b)$.

The last equivalence was proved in Section 1. In $\mathbb{Z}$ the associates of $n$ are $\pm n$, and in $K[X]$ the associates of $f$ are the $cf$ with $c \in K^\times$.

**Definition (Irreducible element).** An element $p \in R$ is irreducible if $p$ is not zero and not a unit, and $p = ab$ implies that $a$ or $b$ is a unit.

**Definition (Prime element).** An element $p \in R$ is prime if $p$ is not zero and not a unit, and $p \mid ab$ implies $p \mid a$ or $p \mid b$.

So $p$ is prime if and only if $(p)$ is a nonzero prime ideal. The two definitions agree in $\mathbb{Z}$, but in general they differ.

**Definition (Unique factorization domain).** An integral domain $R$ is a unique factorization domain, or UFD, if:

1. every nonzero nonunit $a \in R$ is a product $a = p_1 \cdots p_n$ of irreducible elements, and
2. the factorization is unique up to order and associates: if $p_1 \cdots p_n = q_1 \cdots q_m$ with all $p_i$ and $q_j$ irreducible, then $n = m$ and there is a permutation $\sigma$ with $p_i \sim q_{\sigma(i)}$ for all $i$.

**Definition (ACCP).** The domain $R$ satisfies the ascending chain condition on principal ideals if every chain $(a_1) \subseteq (a_2) \subseteq (a_3) \subseteq \cdots$ of principal ideals is eventually constant.

A strict inclusion $(a) \subsetneq (b)$ with $a \ne 0$ means $a = bc$ with $c$ not a unit: $b$ is a strict divisor of $a$. So ACCP says that there is no infinite sequence $a_1, a_2, \dots$ in which each $a_{k+1}$ is a strict divisor of $a_k$.

::: mathlib
`Irreducible` · `Mathlib.Algebra.Group.Irreducible.Defs`

A structure with the fields `not_isUnit` and `isUnit_or_isUnit : p = a * b → IsUnit a ∨ IsUnit b`, for any monoid. It has no field `p ≠ 0`: in a nontrivial monoid with zero, $0 = 0 \cdot 0$ with $0$ not a unit, so $0$ is not irreducible anyway, and `Irreducible.ne_zero` records it.

<?decl Irreducible?>
:::

::: mathlib
`Prime` · `Mathlib.Algebra.Prime.Defs`

The definition `p ≠ 0 ∧ ¬IsUnit p ∧ ∀ a b, p ∣ a * b → p ∣ a ∨ p ∣ b`, in a `CommMonoidWithZero`. The predicate on natural numbers is `Nat.Prime`, and `Nat.prime_iff` connects the two.

<?decl Prime?>
:::

::: mathlib
`Associated` · `Mathlib.Algebra.GroupWithZero.Associated`

`Associated a b` means `∃ u : Mˣ, a * u = b`, with the notation `a ~ᵤ b`. The lemma `associated_of_dvd_dvd` gives it from divisibility both ways.

<?decl Associated?>
:::

::: mathlib
`DvdNotUnit` · `Mathlib.Algebra.GroupWithZero.Divisibility`

Strict divisibility: `DvdNotUnit a b` means `a ≠ 0 ∧ ∃ x, ¬IsUnit x ∧ b = a * x`. ACCP is the statement that this relation is well-founded.

<?decl DvdNotUnit?>
:::

::: mathlib
`WfDvdMonoid` · `Mathlib.RingTheory.UniqueFactorizationDomain.Defs`

An abbreviation for `WellFounded DvdNotUnit`: every nonempty set has an element with no strict divisor in the set. For a domain it is equivalent to ACCP.

<?decl WfDvdMonoid?>
:::

### Theorems and proofs

**Theorem (Prime implies irreducible).** In an integral domain every prime element is irreducible.

*Proof.* Let $p$ be prime and $p = ab$. Then $p \mid ab$, so $p \mid a$ or $p \mid b$. Say $p \mid a$, so $a = pc$. Then $p = pcb$, and cancellation of $p \ne 0$ gives $cb = 1$. So $b$ is a unit. The case $p \mid b$ is the same with $a$ and $b$ exchanged. $\square$

::: mathlib
`Prime.irreducible` · `Mathlib.Algebra.Prime.Defs`

The theorem, with the hypothesis `[IsCancelMulZero M]` in place of a domain: the proof uses only cancellation.

<?decl Prime.irreducible?>
:::

**Theorem (Irreducible implies prime in a PID).** Let $R$ be a PID and $p$ irreducible. Then $(p)$ is a maximal ideal, and $p$ is prime.

*Proof.* Let $(p) \subseteq (m)$. Then $p = ma$ for some $a$. Since $p$ is irreducible, $m$ or $a$ is a unit. If $m$ is a unit, then $(m) = R$. If $a$ is a unit, then $m = a^{-1}p$ and $(m) = (p)$. Every ideal of $R$ is principal, so no ideal lies strictly between $(p)$ and $R$. Also $(p) \ne R$, since $p$ is not a unit. So $(p)$ is maximal. A maximal ideal is prime (Chapter 2), so $p$ is prime. $\square$

::: mathlib
`irreducible_iff_prime` · `Mathlib.Algebra.Prime.Defs`

The equivalence of the two notions under `[IsCancelMulZero M] [DecompositionMonoid M]`. Every PID is a decomposition monoid, through the GCD domains.

<?decl irreducible_iff_prime?>
:::

**Theorem (ACCP in a PID).** Every PID satisfies the ascending chain condition on principal ideals. In fact every ascending chain of ideals is eventually constant.

*Proof.* Let $I_1 \subseteq I_2 \subseteq \cdots$ be ideals, and $I = \bigcup_k I_k$. Then $I$ is an ideal: it contains $0$; for $x \in I_j$ and $y \in I_k$ both lie in $I_{\max(j,k)}$, so $x - y \in I$; and $rx \in I_j$ for $r \in R$. By hypothesis $I = (d)$. Then $d \in I_n$ for some $n$. For $k \ge n$,
$$I = (d) \subseteq I_n \subseteq I_k \subseteq I,$$
so $I_k = I_n$. $\square$

So a PID is a Noetherian ring, a notion of Volume 9.

**Theorem (Existence of factorizations).** Let $R$ be a domain with ACCP. Then every nonzero nonunit of $R$ is a product of irreducible elements.

*Proof.* Call a nonzero nonunit bad if it is not a product of irreducibles. Assume a bad element $a_1$ exists. It is not irreducible, since an irreducible element is a product of one irreducible. So $a_1 = bc$ with $b$ and $c$ not units, and $b, c \ne 0$. If $b$ and $c$ were both products of irreducibles, then so would be $a_1$. So one of them is bad. Call it $a_2$. Then $a_1 = a_2 c'$ with $c'$ not a unit, so $(a_1) \subsetneq (a_2)$: equality would make $a_1$ and $a_2$ associates, and $c'$ a unit by cancellation.

Repeat with $a_2$ in place of $a_1$. This gives a sequence of bad elements with
$$(a_1) \subsetneq (a_2) \subsetneq (a_3) \subsetneq \cdots,$$
a chain that is never constant. This contradicts ACCP. So no bad element exists. $\square$

::: mathlib
`WfDvdMonoid.exists_factors` · `Mathlib.RingTheory.UniqueFactorizationDomain.Defs`

The theorem: `a ≠ 0 → ∃ f : Multiset α, (∀ b ∈ f, Irreducible b) ∧ Associated f.prod a`. A factorization is a multiset, and its product is only associated to `a`.

<?decl WfDvdMonoid.exists_factors?>
:::

**Theorem (Uniqueness of factorizations).** Let $R$ be a domain in which every irreducible element is prime. If $p_1 \cdots p_n \sim q_1 \cdots q_m$ with all $p_i$ and $q_j$ irreducible, then $n = m$, and after a renumbering $p_i \sim q_i$ for all $i$.

*Proof.* Induction on $n$. If $n = 0$, the product $q_1 \cdots q_m$ is associate to $1$, so it is a unit. Then each $q_j$ divides a unit and is a unit itself, which is false for an irreducible. So $m = 0$.

Let $n \ge 1$. The element $p_n$ is prime by hypothesis, and it divides $q_1 \cdots q_m$, since $p_1 \cdots p_n = u\, q_1 \cdots q_m$ with $u$ a unit. So $m \ge 1$, and by induction on the number of factors, a prime that divides a product divides one of the factors: $p_n \mid q_j$ for some $j$. Renumber the $q_j$ so that $j = m$. Then $q_m = p_n v$, and $q_m$ is irreducible and $p_n$ is not a unit, so $v$ is a unit and $p_n \sim q_m$. Now
$$p_1 \cdots p_{n-1} p_n = u\, q_1 \cdots q_{m-1} \, v p_n.$$
Cancel $p_n \ne 0$: $p_1 \cdots p_{n-1} = uv\, q_1 \cdots q_{m-1}$. By the induction hypothesis $n - 1 = m - 1$, and after a renumbering $p_i \sim q_i$ for $i < n$. $\square$

**Theorem (A PID is a UFD).** Every principal ideal domain is a unique factorization domain.

*Proof.* A PID satisfies ACCP, so factorizations exist by the theorem on existence. In a PID every irreducible element is prime, so factorizations are unique by the theorem on uniqueness. $\square$

With Section 1: $\mathbb{Z}$, $K[X]$ and $\mathbb{Z}[i]$ are UFDs.

**Theorem (Irreducible implies prime in a UFD).** In a UFD every irreducible element is prime. So the two conditions of the last proof are also necessary: a domain is a UFD if and only if it satisfies ACCP and every irreducible element is prime.

*Proof.* Let $p$ be irreducible and $p \mid ab$, with $ab = pc$. If $a = 0$, then $p \mid a$, and if $b = 0$, then $p \mid b$. If $a$ is a unit, then $b = a^{-1} p c$ and $p \mid b$, and the same for $b$. So let $a$ and $b$ be nonzero nonunits, with factorizations $a = a_1 \cdots a_k$ and $b = b_1 \cdots b_l$. Then $c \ne 0$. Write $c = u c_1 \cdots c_r$ with $u$ a unit and $c_1, \dots, c_r$ irreducible, where $r = 0$ if $c$ is a unit. Then
$$a_1 \cdots a_k\, b_1 \cdots b_l = (up)\, c_1 \cdots c_r$$
are two factorizations of $ab$ into irreducibles, since $up$ is irreducible. By uniqueness $p$ is associate to some $a_i$ or to some $b_j$, so $p \mid a$ or $p \mid b$.

For the converse statement, the existence part of a UFD gives ACCP: the number of irreducible factors of a nonzero element is well defined by uniqueness, and it drops strictly when one passes to a strict divisor, so a strictly ascending chain $(a_1) \subsetneq (a_2) \subsetneq \cdots$ would give a strictly decreasing sequence of natural numbers. $\square$

::: mathlib
`UniqueFactorizationMonoid` · `Mathlib.RingTheory.UniqueFactorizationDomain.Defs`

Mathlib defines a UFD by the characterization of the last theorem, not by the textbook definition: the class extends `IsCancelMulZero α`, with the fields `WellFounded DvdNotUnit` and `irreducible_iff_prime`. It is stated for a `CommMonoidWithZero`, so `ℕ` is an instance too. A UFD domain is `[CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]`.

<?decl UniqueFactorizationMonoid?>
:::

::: mathlib
`UniqueFactorizationMonoid.irreducible_iff_prime` · `Mathlib.RingTheory.UniqueFactorizationDomain.Defs`

The field of the class: in a UFD, `Irreducible a ↔ Prime a`.

<?decl UniqueFactorizationMonoid.irreducible_iff_prime?>
:::

::: mathlib
`UniqueFactorizationMonoid.factors` · `Mathlib.RingTheory.UniqueFactorizationDomain.Defs`

A chosen factorization of `a` as a `Multiset`, with the junk value `factors 0 = 0`. Its elements are irreducible, and `UniqueFactorizationMonoid.factors_prod` gives `a ≠ 0 → Associated (factors a).prod a`.

<?decl UniqueFactorizationMonoid.factors?>
:::

::: mathlib
`UniqueFactorizationMonoid.factors_prod` · `Mathlib.RingTheory.UniqueFactorizationDomain.Defs`

The product of the factors of a nonzero `a` is associated to `a`, not equal: in `ℤ`, the factors of `-6` multiply to $6$ or to $-6$, depending on the choice.

<?decl UniqueFactorizationMonoid.factors_prod?>
:::

::: mathlib
`UniqueFactorizationMonoid.factors_unique` · `Mathlib.RingTheory.UniqueFactorizationDomain.Basic`

The uniqueness theorem: two multisets of irreducibles with associated products satisfy `Multiset.Rel Associated f g`, a matching of the elements by associates. This relation is the formal form of "after a renumbering, $p_i \sim q_i$".

<?decl UniqueFactorizationMonoid.factors_unique?>
:::

::: mathlib
`UniqueFactorizationMonoid.of_exists_prime_factors` · `Mathlib.RingTheory.UniqueFactorizationDomain.Basic`

A third characterization: a cancellative monoid in which every nonzero element is associated to a product of primes is a UFD.

<?decl UniqueFactorizationMonoid.of_exists_prime_factors?>
:::

::: mathlib
`PrincipalIdealRing.to_uniqueFactorizationMonoid` · `Mathlib.RingTheory.PrincipalIdealDomain`

The theorem that a PID is a UFD, as an instance for `[CommRing R] [IsDomain R] [IsPrincipalIdealRing R]`. Its proof is the two lines of the proof above, with the next two boxes for ACCP.

<?decl PrincipalIdealRing.to_uniqueFactorizationMonoid?>
:::

::: mathlib
`PrincipalIdealRing.isNoetherianRing` · `Mathlib.RingTheory.PrincipalIdealDomain`

A principal ideal ring is Noetherian, since every ideal is generated by one element and so is finitely generated. This is the theorem on ACCP in a PID.

<?decl PrincipalIdealRing.isNoetherianRing?>
:::

::: mathlib
`IsNoetherianRing.wfDvdMonoid` · `Mathlib.RingTheory.Noetherian.UniqueFactorizationDomain`

A Noetherian domain satisfies ACCP, as the instance `WfDvdMonoid R`. With the last box it gives the existence of factorizations in a PID.

<?decl IsNoetherianRing.wfDvdMonoid?>
:::

### Examples

**Example (Factorizations in $\mathbb{Z}$, $\mathbb{Z}[i]$ and $\mathbb{Q}[X]$).** In $\mathbb{Z}$, $-360 = -1 \cdot 2^3 \cdot 3^2 \cdot 5$, and the factorization $(-2) \cdot 2 \cdot 2 \cdot 3 \cdot 3 \cdot 5$ is the same up to associates. In $\mathbb{Q}[X]$,
$$X^4 - 1 = (X - 1)(X + 1)(X^2 + 1).$$
The factor $X^2 + 1$ is irreducible over $\mathbb{Q}$: a factorization into two factors of degree $1$ would give a rational root, and $x^2 + 1 > 0$ for $x \in \mathbb{Q}$. Over $\mathbb{F}_5$ the same polynomial splits into four linear factors, $X^4 - 1 = (X - 1)(X - 2)(X - 3)(X - 4)$, since every element of $\mathbb{F}_5^\times$ satisfies $x^4 = 1$. So irreducibility depends on the ring.

**Counterexample ($\mathbb{Z}[\sqrt{-5}]$ is not a UFD).** Let $R = \mathbb{Z}[\sqrt{-5}]$ with the multiplicative norm $N(a + b\sqrt{-5}) = a^2 + 5b^2$. In $R$,
$$6 = 2 \cdot 3 = (1 + \sqrt{-5})(1 - \sqrt{-5}).$$
The norms of the four factors are $N(2) = 4$, $N(3) = 9$ and $N(1 \pm \sqrt{-5}) = 1 + 5 = 6$. The units are the elements of norm $1$, namely $\pm 1$. No element has norm $2$ or $3$: for $b \ne 0$ the norm is at least $5$, and for $b = 0$ it is a square $a^2$. Now each factor is irreducible. A factorization $\alpha\beta$ of a factor with $\alpha$ and $\beta$ not units has $N(\alpha), N(\beta) > 1$ and $N(\alpha)N(\beta) \in \{4, 9, 6\}$, so one of $N(\alpha), N(\beta)$ is $2$ or $3$, which is impossible. The element $2$ is not associate to $1 \pm \sqrt{-5}$, since the norms differ. So $6$ has two factorizations into irreducibles that do not match. In terms of primes: $2$ divides $(1 + \sqrt{-5})(1 - \sqrt{-5})$ but neither factor, since $(1 \pm \sqrt{-5})/2 \notin R$. So $2$ is irreducible and not prime, $R$ is not a UFD, and by the theorem of this section $R$ is not a PID. Factorizations do exist in $R$, since the norm drops strictly on strict divisors and so ACCP holds.

**Counterexample (A domain without ACCP).** Let $R = \mathbb{Z} + X\mathbb{Q}[X]$ be the ring of polynomials with rational coefficients and integer constant term. It is a subring of $\mathbb{Q}[X]$, so it is a domain. Its units are $\pm 1$: if $fg = 1$, then $f$ and $g$ are constants, integers with product $1$. For each $n$ the element $X/2^n$ is in $R$, and
$$\frac{X}{2^n} = 2 \cdot \frac{X}{2^{n+1}}, \qquad \text{so} \qquad (X) \subsetneq \left(\frac{X}{2}\right) \subsetneq \left(\frac{X}{4}\right) \subsetneq \cdots.$$
Each inclusion is strict: $X/2^{n+1} = h \cdot X/2^n$ forces $h = \tfrac12 \notin R$. So ACCP fails. The element $X$ has no factorization into irreducibles. In a product $X = f_1 \cdots f_k$ in $R$ the degrees add to $1$, so one factor has degree $1$ and the others are nonzero integer constants. The constant terms multiply to $0$, so the factor of degree $1$ is $qX$ with $q \in \mathbb{Q}$. But $qX = 2 \cdot (q/2)X$ with two nonunits, so $qX$ is not irreducible. The theorem on existence shows why: such an $X$ yields exactly the chain above.

**Remark ($\mathbb{Z}[X]$).** If $R$ is a UFD, then $R[X]$ is a UFD, by the lemma of Gauss (Volume 9). So $\mathbb{Z}[X]$ is a UFD, and it is not a PID by Section 1: the second implication of this chapter does not reverse.

::: mathlib
`Polynomial.uniqueFactorizationMonoid` · `Mathlib.RingTheory.Polynomial.UniqueFactorization`

The instance `UniqueFactorizationMonoid D → UniqueFactorizationMonoid D[X]` for a commutative ring `D`. Instance search then finds a UFD structure on `ℤ[X]`.

<?decl Polynomial.uniqueFactorizationMonoid?>
:::

### The library around it

The definitions are in `Mathlib.RingTheory.UniqueFactorizationDomain.Defs`, and the theory, with multiplicities and normalized factors, is in the folder `Mathlib/RingTheory/UniqueFactorizationDomain/`. With a `NormalizationMonoid`, a choice of one element in each class of associates, the function `UniqueFactorizationMonoid.normalizedFactors` gives a factorization that is unique as a multiset, not only up to associates: in `ℤ` it picks the positive primes, and in `K[X]` the monic irreducibles.

Common errors of a learner:

- `Nat.Prime p` and `Prime p` are different predicates, linked by `Nat.prime_iff`. For integers `Int.prime_iff_natAbs_prime` is the link.
- `UniqueFactorizationMonoid` does not imply `IsDomain`. A theorem about a UFD ring often needs both classes.
- The function `factors` is `noncomputable`, since its definition uses choice.

### Exercises

1. (A) Show that in a domain, $a \sim b$ is an equivalence relation, and that $p \sim q$ with $p$ irreducible implies $q$ irreducible.
2. (A) Factor $X^4 + 4$ in $\mathbb{Q}[X]$ and in $\mathbb{Z}[i][X]$. Hint: $X^4 + 4 = (X^2 + 2)^2 - (2X)^2$.
3. (A) In $\mathbb{Z}[\sqrt{-5}]$, show that $3$ and $2 + \sqrt{-5}$ are irreducible, and find two factorizations of $9$.
4. (B) Show that the ideal $(2, 1 + \sqrt{-5})$ of $\mathbb{Z}[\sqrt{-5}]$ is not principal, and that its square is $(2)$.
5. (B) Show that in a UFD any two elements have a greatest common divisor, computed from the factorizations with the minimum of the exponents.
6. (B) Show that $\mathbb{Z}[\sqrt{-3}]$ satisfies ACCP but is not a UFD. Hint: the counterexample of Section 2 and the norm.
7. (B) Let $R$ be a UFD and $p$ irreducible. Show that the number $v_p(a)$ of factors associate to $p$ in a factorization of $a \ne 0$ is well defined and satisfies $v_p(ab) = v_p(a) + v_p(b)$.
8. (C) Show that in a UFD every nonzero prime ideal $P$ contains a prime element. Deduce that if every nonzero prime ideal of a UFD is maximal, then every nonzero prime ideal is principal. Hint: factor a nonzero element of $P$.

### Notes and history

Unique factorization in $\mathbb{Z}$ is implicit in Euclid, *Elements* VII.30 (a prime dividing a product divides a factor), and Gauss stated and proved it in full in the *Disquisitiones Arithmeticae* (1801), article 16. In 1847 Lamé announced a proof of Fermat's last theorem that assumed unique factorization in the rings $\mathbb{Z}[\zeta_p]$, and Liouville pointed out the gap. Kummer had already found that the property fails for $p = 23$, and he introduced ideal numbers to restore it. Dedekind (1871) turned ideal numbers into ideals, and proved unique factorization of ideals in rings of integers, the subject of Volume 12.

In Mathlib, the theory of unique factorization monoids is due to Johannes Hölzl, Jens Wagemaker and Aaron Anderson. Its definition by well-foundedness and `irreducible_iff_prime` avoids lists and permutations.

### Reference

<?reference?>
