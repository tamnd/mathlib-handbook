---
title: Integral closure and integrally closed domains
kind: theory
modules:
  - Mathlib.RingTheory.IntegralClosure.Algebra.Basic
  - Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Defs
  - Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
  - Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
explains:
  E3: [integralClosure, IsIntegralClosure, IsIntegrallyClosed, isIntegrallyClosed_of_isLocalization]
  E2: [mem_integralClosure_iff, integralClosure_idem, integralClosure.isIntegralClosure, IsIntegralClosure.equiv, IsIntegrallyClosedIn, isIntegrallyClosed_iff, IsIntegrallyClosed.isIntegral_iff, integralClosure.isIntegrallyClosedOfFiniteExtension, Field.instIsIntegrallyClosed]
  E1: auto
families: []
requires: [V06, V07]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Integral closure and integrally closed domains

### Overview

Section 1 proved that the elements of $A$ that are integral over $R$ are closed under sums and products. So they form a subring, the integral closure of $R$ in $A$. When $R$ is a domain and $A$ is its field of fractions, the question is whether the closure is larger than $R$. If it is not, $R$ is integrally closed. The integers are integrally closed in $\mathbb{Q}$, and the ring $\mathbb{Z}[\sqrt{-3}]$ is not: the element $(1 + \sqrt{-3})/2$ of its fraction field is a root of $X^2 - X + 1$.

The section proves three results. A unique factorization domain is integrally closed, by the argument of the rational root test. A localization of an integrally closed domain is integrally closed. The integral closure of $\mathbb{Z}$ in a quadratic field $\mathbb{Q}(\sqrt{d})$ is $\mathbb{Z}[\sqrt{d}]$ or $\mathbb{Z}[(1 + \sqrt{d})/2]$, according to $d$ modulo $4$. The last computation gives the rings of integers that Chapters 4 and 5 use as examples.

### Definitions

**Definition (Integral closure).** The integral closure of $R$ in $A$ is the set of the elements of $A$ that are integral over $R$. It is an $R$-subalgebra of $A$, by the theorem on sums and products of Section 1. The ring $R$ is integrally closed in $A$ if the integral closure is the image of $R$.

**Definition (Integrally closed domain).** A domain $R$ with field of fractions $K$ is integrally closed, or normal, if $R$ is integrally closed in $K$: every $x \in K$ that is integral over $R$ lies in $R$.

*Remarks.* The word normal comes from algebraic geometry, where a variety is normal if its local rings are integrally closed domains. For a domain, "integrally closed" without a ring named always means in the field of fractions. A field is integrally closed, since every element of $K$ lies in $K$.

The integral closure is closed under itself: the integral closure of $\overline{R}$ in $A$, where $\overline{R}$ is the integral closure of $R$ in $A$, is $\overline{R}$. Indeed, an element integral over $\overline{R}$ is integral over $R$ by transitivity (Section 1).

::: mathlib
`integralClosure` · `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`

`integralClosure R A : Subalgebra R A`, with carrier `{r | IsIntegral R r}`, for `[CommRing R] [CommRing A] [Algebra R A]`. Membership is `mem_integralClosure_iff`. The idempotence of the remark is `integralClosure_idem`: the closure of the closure, as a subalgebra over the closure, is `⊥`, the image of the base.

<?decl integralClosure?>
:::

**Definition (Integral closure, as a property).** Let $R \to B$ and $C \to B$ be ring maps. Then $C$ is an integral closure of $R$ in $B$ if $C \to B$ is injective and its image is the set of the elements of $B$ integral over $R$.

This form says what a ring is, not how it is built. The ring of integers of a number field $L$ is a type in Mathlib with its own name. It is not literally the subalgebra `integralClosure ℤ L`, but it is an integral closure of $\mathbb{Z}$ in $L$ in this sense, and every theorem about integral closures applies to it.

::: mathlib
`IsIntegralClosure` · `Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Defs`

`IsIntegralClosure A R B` is a class with two fields: `algebraMap A B` is injective, and `x : B` is integral over `R` if and only if `x` is in the range of `algebraMap A B`. The instance `integralClosure.isIntegralClosure` says that the subalgebra `integralClosure R B` satisfies it, and `IsIntegralClosure.equiv` gives the unique isomorphism between two integral closures. This is the "characteristic predicate" pattern that Mathlib also uses for localizations (`IsLocalization`) and fields of fractions (`IsFractionRing`).

<?decl IsIntegralClosure?>
:::

::: mathlib
`IsIntegrallyClosed` · `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`

`IsIntegrallyClosed R` is an abbreviation for `IsIntegrallyClosedIn R (FractionRing R)`, and `IsIntegrallyClosedIn R A` says that `R` is its own integral closure in `A`. The definition uses the canonical fraction field `FractionRing R`. For any other field of fractions `K`, with `[IsFractionRing R K]`, the lemma `isIntegrallyClosed_iff K` gives the textbook form: every `x : K` integral over `R` is `algebraMap R K y` for some `y`. The class does not ask that `R` is a domain; a theorem that needs it adds `[IsDomain R]`.

<?decl IsIntegrallyClosed?>
:::

### Theorems and proofs

**Theorem (A UFD is integrally closed).** Let $R$ be a unique factorization domain with field of fractions $K$. Then $R$ is integrally closed.

*Proof.* Let $x \in K$ be integral over $R$, with
$$x^n + c_{n-1}x^{n-1} + \cdots + c_1 x + c_0 = 0, \qquad c_i \in R.$$
Write $x = a/b$ with $a, b \in R$, $b \ne 0$, and with no prime element dividing both $a$ and $b$. This is possible in a UFD: cancel the common prime factors (Volume 6, Chapter 6). Multiply the equation by $b^n$:
$$a^n = -b\left(c_{n-1}a^{n-1} + c_{n-2}a^{n-2}b + \cdots + c_0 b^{n-1}\right).$$
Assume that $b$ is not a unit. Then $b$ has a prime factor $p$. The equation shows $p \mid a^n$, and since $p$ is prime, $p \mid a$. This contradicts the choice of $a$ and $b$. So $b$ is a unit, and $x = ab^{-1} \in R$. $\square$

So $\mathbb{Z}$, $k[X_1, \dots, X_n]$ for a field $k$, and every PID are integrally closed. For $R = \mathbb{Z}$ the proof is the rational root test: a rational root of a monic integer polynomial is an integer.

::: mathlib
`UniqueFactorizationMonoid.instIsIntegrallyClosed` · `Mathlib.RingTheory.Polynomial.RationalRoot`

The theorem is an instance, in the file of the rational root theorem of Volume 9, Commutative algebra I. So instance search proves `IsIntegrallyClosed ℤ` and `IsIntegrallyClosed (MvPolynomial σ k)` without help. A more general instance says that a GCD domain is integrally closed.

<?decl UniqueFactorizationMonoid.instIsIntegrallyClosed?>
:::

**Theorem (Localization).** Let $R$ be an integrally closed domain and $S \subseteq R \setminus \{0\}$ a multiplicative set. Then $S^{-1}R$ is an integrally closed domain.

*Proof.* The ring $S^{-1}R$ is a domain with the same field of fractions $K$ as $R$ (Volume 9, Commutative algebra I). Let $x \in K$ be integral over $S^{-1}R$:
$$x^n + \frac{r_{n-1}}{s_{n-1}}x^{n-1} + \cdots + \frac{r_0}{s_0} = 0, \qquad r_i \in R,\ s_i \in S.$$
Put $s = s_0 s_1 \cdots s_{n-1} \in S$. Multiply the equation by $s^n$:
$$(sx)^n + \frac{s r_{n-1}}{s_{n-1}}(sx)^{n-1} + \frac{s^2 r_{n-2}}{s_{n-2}}(sx)^{n-2} + \cdots + \frac{s^n r_0}{s_0} = 0.$$
Each coefficient $s^k r_{n-k}/s_{n-k}$ lies in $R$, since $s_{n-k}$ divides $s$. So $sx$ is integral over $R$, and $sx \in R$ because $R$ is integrally closed. Then $x = (sx)/s \in S^{-1}R$. $\square$

In particular, the local ring $R_{\mathfrak p}$ at a prime ideal of an integrally closed domain is integrally closed. Chapter 3 uses this with Dedekind domains, whose local rings turn out to be discrete valuation rings.

::: mathlib
`isIntegrallyClosed_of_isLocalization` · `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`

Stated for any `S` with `[IsLocalization M S]` and the hypothesis `M ≤ nonZeroDivisors R`, which is the condition $0 \notin S$ of the text. The more general fact that integral closure commutes with localization is `IsLocalization.integralClosure`, in a module of Volume 9.

<?decl isIntegrallyClosed_of_isLocalization?>
:::

**Theorem (Integers of a quadratic field).** Let $d \ne 0, 1$ be a squarefree integer and $L = \mathbb{Q}(\sqrt{d})$. The integral closure $\mathcal{O}_L$ of $\mathbb{Z}$ in $L$ is
$$\mathcal{O}_L = \begin{cases} \mathbb{Z}[\sqrt{d}] & \text{if } d \equiv 2, 3 \pmod 4, \\ \mathbb{Z}\left[\tfrac{1 + \sqrt{d}}{2}\right] & \text{if } d \equiv 1 \pmod 4. \end{cases}$$

*Proof.* Let $\sigma$ be the automorphism of $L$ with $\sigma(\sqrt{d}) = -\sqrt{d}$. Let $x = a + b\sqrt{d}$ with $a, b \in \mathbb{Q}$.

Step 1: $x$ is integral if and only if $2a \in \mathbb{Z}$ and $a^2 - db^2 \in \mathbb{Z}$. The element $x$ is a root of $X^2 - 2aX + (a^2 - db^2)$, so the condition is sufficient. Conversely, let $x$ be integral, with equation $p(x) = 0$, $p$ monic in $\mathbb{Z}[X]$. Apply $\sigma$: $p(\sigma x) = 0$, so $\sigma x$ is integral. Then $x + \sigma x = 2a$ and $x \cdot \sigma x = a^2 - db^2$ are integral, and they are rational. A rational number integral over $\mathbb{Z}$ is an integer, because $\mathbb{Z}$ is integrally closed.

Step 2: the conditions in Step 1 force $2b \in \mathbb{Z}$. Put $A = 2a \in \mathbb{Z}$. Then $4(a^2 - db^2) = A^2 - 4db^2$ is an integer, so $4db^2 \in \mathbb{Z}$. Write $b = u/v$ in lowest terms with $v > 0$. Then $v^2 \mid 4du^2$ and $\gcd(u, v) = 1$, so $v^2 \mid 4d$. An odd prime $p \mid v$ gives $p^2 \mid d$, and $4 \mid v$ gives $4 \mid d$. Both contradict that $d$ is squarefree. So $v \in \{1, 2\}$, and $B = 2b \in \mathbb{Z}$.

Step 3: the congruence. With $a = A/2$ and $b = B/2$, the condition $a^2 - db^2 \in \mathbb{Z}$ reads $A^2 \equiv dB^2 \pmod 4$. A square is $0$ or $1$ modulo $4$, and it is $1$ exactly for an odd number.

If $d \equiv 2$ or $3 \pmod 4$ and $B$ is odd, then $dB^2 \equiv d \pmod 4$ is $2$ or $3$, and it is not a square modulo $4$. So $B$ is even, then $A^2 \equiv 0$, and $A$ is even. So $a, b \in \mathbb{Z}$, and $\mathcal{O}_L = \mathbb{Z}[\sqrt{d}]$.

If $d \equiv 1 \pmod 4$, the condition reads $A^2 \equiv B^2 \pmod 4$, that is, $A \equiv B \pmod 2$. Then
$$x = \frac{A + B\sqrt{d}}{2} = \frac{A - B}{2} + B \cdot \frac{1 + \sqrt{d}}{2}$$
with $(A - B)/2 \in \mathbb{Z}$, so $x \in \mathbb{Z}[(1 + \sqrt{d})/2]$. Conversely every element of this ring has $A \equiv B \pmod 2$. $\square$

### Examples

**Example ($\mathbb{Z}[\sqrt{-3}]$ is not integrally closed).** Here $d = -3 \equiv 1 \pmod 4$. The element $\omega = (1 + \sqrt{-3})/2$ lies in the fraction field $\mathbb{Q}(\sqrt{-3})$ of $\mathbb{Z}[\sqrt{-3}]$, and $\omega^2 = (-2 + 2\sqrt{-3})/4 = \omega - 1$. So $\omega$ is a root of $X^2 - X + 1$ and is integral, but $\omega \notin \mathbb{Z}[\sqrt{-3}]$. The integral closure is $\mathbb{Z}[\omega]$, the Eisenstein integers. By the theorem on UFDs, $\mathbb{Z}[\sqrt{-3}]$ is not a UFD, which Volume 6, Chapter 6 showed by the factorization $4 = 2 \cdot 2 = (1 + \sqrt{-3})(1 - \sqrt{-3})$.

**Example (The converse fails).** Here $d = -5 \equiv 3 \pmod 4$, so $\mathbb{Z}[\sqrt{-5}]$ is integrally closed. It is not a UFD, since $6 = 2 \cdot 3 = (1 + \sqrt{-5})(1 - \sqrt{-5})$. So "integrally closed" is strictly weaker than "UFD". Chapter 4 shows that $\mathbb{Z}[\sqrt{-5}]$ is a Dedekind domain, and Chapter 5 that its class group has order $2$.

**Example (A cusp).** Let $k$ be a field and $R = k[t^2, t^3] \subseteq k[t]$, the ring of polynomials with no term of degree $1$. Its field of fractions is $k(t)$, since $t = t^3/t^2$. The element $t$ is a root of $X^2 - t^2 \in R[X]$, so it is integral over $R$, and $t \notin R$. So $R$ is not integrally closed. Its integral closure is $k[t]$: the ring $k[t]$ is integral over $R$ because it is generated by $t$, and it is integrally closed as a UFD. Geometrically, $R$ is the ring of the cuspidal cubic $y^2 = x^3$ with $x = t^2$, $y = t^3$, and $k[t]$ is the ring of its normalization, a line.

**Example (The golden ratio).** For $d = 5$ the ring of integers is $\mathbb{Z}[\tau]$ with $\tau = (1 + \sqrt{5})/2$, and $\mathbb{Z}[\sqrt{5}]$ is a subring of index $2$. For $d = -1$ and $d = 2$ the rings of integers are $\mathbb{Z}[i]$ and $\mathbb{Z}[\sqrt{2}]$.

### The library around it

The files `Mathlib/RingTheory/IntegralClosure/IsIntegralClosure/` and `IntegrallyClosed.lean` contain the theory. The lemma `IsIntegrallyClosed.isIntegral_iff` is the form to use in a proof: under `[IsIntegrallyClosed R]` and `[IsFractionRing R K]`, an element `x : K` is integral if and only if it comes from `R`. The instance `Field.instIsIntegrallyClosed` says that a field is integrally closed. The theorem `integralClosure.isIntegrallyClosedOfFiniteExtension` says that the integral closure of a domain in a finite extension of its fraction field is integrally closed. The proof is the idempotence of the closure, together with the fact that the closure has the large field as its field of fractions.

The ring of integers of a number field is `NumberField.RingOfIntegers K`, written `𝓞 K`, in Volume 12, Number theory. It has an instance of `IsIntegralClosure (𝓞 K) ℤ K`.

Common errors of a learner:

- `integralClosure R A` is a subalgebra, so its elements are pairs of an element and a proof. To use it as a ring, Lean coerces it to a type `↥(integralClosure R A)`.
- `IsIntegrallyClosed R` does not include `IsDomain R`.
- To show that a concrete ring is integrally closed, prefer an instance (UFD, GCD domain, Dedekind domain) to a direct proof.

### Exercises

1. (A) Show that the integral closure of $\mathbb{R}$ in $\mathbb{C}$ is $\mathbb{C}$, and that the integral closure of $\mathbb{Z}$ in $\mathbb{Q}(i)$ is $\mathbb{Z}[i]$.
2. (A) Compute the ring of integers of $\mathbb{Q}(\sqrt{-7})$, $\mathbb{Q}(\sqrt{6})$ and $\mathbb{Q}(\sqrt{13})$.
3. (A) Show that $\mathbb{Z}[\sqrt{8}]$ is not integrally closed, and find its integral closure.
4. (B) Let $R \subseteq A$ and let $\overline{R}$ be the integral closure of $R$ in $A$. Show that for a multiplicative set $S \subseteq R$, the integral closure of $S^{-1}R$ in $S^{-1}A$ is $S^{-1}\overline{R}$.
5. (B) Let $k$ be a field of characteristic not $2$. Show that $k[x, y]/(y^2 - x^2(x + 1))$ is a domain that is not integrally closed. Hint: consider $y/x$.
6. (B) Let $R$ be an integrally closed domain with fraction field $K$, and let $L/K$ be a finite extension. Show that $x \in L$ is integral over $R$ if and only if the minimal polynomial of $x$ over $K$ has coefficients in $R$. Hint: the roots of the minimal polynomial in a splitting field are integral.
7. (C) Let $\zeta = e^{2\pi i/3}$. Show that $\mathbb{Z}[\zeta]$ is a Euclidean domain for the norm $N(a + b\zeta) = a^2 - ab + b^2$, and deduce once more that it is integrally closed.

### Notes and history

The computation of the integers of a quadratic field is classical. It appears in Dedekind's supplements to Dirichlet's lectures on number theory, where the ring of algebraic integers of a number field was first defined. Zariski used the integral closure, under the name of normalization, in his work on the resolution of singularities of algebraic surfaces around 1939. A standard reference is Atiyah and Macdonald, Chapter 5, and for the quadratic fields Marcus, *Number Fields*, Chapter 2.

### Reference

<?reference?>
