---
title: Euclidean domains and principal ideal domains
kind: theory
modules: []
explains:
  E1: [EuclideanDomain, EuclideanDomain.r, EuclideanDomain.remainder_lt, EuclideanDomain.mul_left_not_lt, Int.euclideanDomain, IsPrincipalIdealRing, Submodule.IsPrincipal.generator, EuclideanDomain.instIsPrincipalIdealRing, EuclideanDomain.gcd, EuclideanDomain.gcd_val, EuclideanDomain.gcd_eq_gcd_ab, IsPrime.to_maximal_ideal, Ideal.span_singleton_prime, IsBezout]
families: []
requires: [V06.C02, V06.C03, V06.C05]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Euclidean domains and principal ideal domains

### Overview

Division with remainder is the one tool behind the arithmetic of the integers. It gives the Euclidean algorithm, the greatest common divisor, the identity of Bezout, and in the end the unique factorization into primes. Chapter 5 proved division with remainder for polynomials over a field, with the degree as the measure of size. A Euclidean domain is an integral domain with such a division and such a measure. This section defines Euclidean domains and principal ideal domains, the domains in which every ideal has one generator, and proves the main theorem: every Euclidean domain is a principal ideal domain. It then shows that greatest common divisors exist in a principal ideal domain, that the Euclidean algorithm computes them, and that a nonzero prime ideal of a principal ideal domain is maximal. The last part shows that $\mathbb{Z}[X]$ and $K[X, Y]$ are not principal ideal domains.

### Definitions

In this section all rings are commutative with $1 \ne 0$.

**Definition (Euclidean domain).** A Euclidean domain is an integral domain $R$ with a function $N : R \setminus \{0\} \to \mathbb{N}$, the Euclidean function, such that for all $a, b \in R$ with $b \ne 0$ there are $q, r \in R$ with
$$a = qb + r, \qquad r = 0 \text{ or } N(r) < N(b).$$

The elements $q$ and $r$ need not be unique. Some books also ask that $N(a) \le N(ab)$ for $a, b \ne 0$. That condition is not needed for the theorems below, and every Euclidean domain has a function with it.

**Definition (Principal ideal).** An ideal $I$ of $R$ is principal if $I = (d) = \{ rd : r \in R \}$ for some $d \in R$. The element $d$ is a generator of $I$.

**Definition (Principal ideal domain).** A principal ideal domain, or PID, is an integral domain in which every ideal is principal.

Two generators of the same ideal differ by a unit. If $(d) = (d') \ne 0$, then $d = u d'$ and $d' = v d$, so $d = uvd$, and $uv = 1$ by cancellation in a domain.

**Definition (Greatest common divisor).** Let $a, b \in R$. An element $d \in R$ is a greatest common divisor of $a$ and $b$ if $d \mid a$, $d \mid b$, and every common divisor $c$ of $a$ and $b$ divides $d$.

A greatest common divisor is unique up to a unit when it exists: two of them divide each other. In $\mathbb{Z}$ the convention picks the one that is not negative, and in $K[X]$ the monic one.

::: mathlib
`EuclideanDomain` · `Mathlib.Algebra.EuclideanDomain.Defs`

The class extends `CommRing R` and `Nontrivial R`. Its fields are a quotient and a remainder, the identity `b * quotient a b + remainder a b = a`, and, in place of a function to $\mathbb{N}$, a well-founded relation `r` with `remainder_lt : b ≠ 0 → r (a % b) b` and `mul_left_not_lt : b ≠ 0 → ¬ r (a * b) a`. A function $N$ gives the relation $N(x) < N(y)$, and a well-founded relation is the general form, so Mathlib covers the transfinite Euclidean domains too. The class does not ask for a domain. The second axiom proves it, and the instance `EuclideanDomain.instIsDomain` records it.

<?decl EuclideanDomain?>
:::

::: mathlib
`EuclideanDomain.r` · `Mathlib.Algebra.EuclideanDomain.Defs`

The relation of the class, a field that reads "is smaller than". For the integers, the instance `Int.euclideanDomain` sets `r a b` to `a.natAbs < b.natAbs`, with the usual `/` and `%` of `Int`.

<?decl EuclideanDomain.r?>
:::

::: mathlib
`EuclideanDomain.remainder_lt` · `Mathlib.Algebra.EuclideanDomain.Defs`

The axiom that the remainder is smaller than the divisor. The form with the notation `%` is `EuclideanDomain.mod_lt`.

<?decl EuclideanDomain.remainder_lt?>
:::

::: mathlib
`EuclideanDomain.mul_left_not_lt` · `Mathlib.Algebra.EuclideanDomain.Defs`

The axiom `¬ r (a * b) a` for `b ≠ 0`: a product is not smaller than a factor. It plays the role of $N(a) \le N(ab)$, and it rules out zero divisors.

<?decl EuclideanDomain.mul_left_not_lt?>
:::

::: mathlib
`Int.euclideanDomain` · `Mathlib.Algebra.EuclideanDomain.Int`

The instance for $\mathbb{Z}$, with the Euclidean function $|a|$ as the relation on `natAbs`.

<?decl Int.euclideanDomain?>
:::

::: mathlib
`IsPrincipalIdealRing` · `Mathlib.RingTheory.Ideal.Span`

The class with one field, `principal : ∀ S : Ideal R, S.IsPrincipal`. It does not include the domain hypothesis, so a PID in Mathlib is `[CommRing R] [IsDomain R] [IsPrincipalIdealRing R]`. The ring `ZMod 4` is a principal ideal ring that is not a domain.

<?decl IsPrincipalIdealRing?>
:::

::: mathlib
`Submodule.IsPrincipal.generator` · `Mathlib.LinearAlgebra.Span.Defs`

A chosen generator of a principal ideal, with `Submodule.IsPrincipal.span_singleton_generator : span {generator S} = S`. An ideal is a submodule of the ring, so the notion of a principal submodule applies.

<?decl Submodule.IsPrincipal.generator?>
:::

### Theorems and proofs

**Theorem (A Euclidean domain is a PID).** Let $R$ be a Euclidean domain. Every ideal of $R$ is principal.

*Proof.* The plan: a nonzero ideal is generated by an element of least size, because the remainder of any element on division by it lies in the ideal and is smaller.

Let $I$ be an ideal. If $I = 0$, then $I = (0)$. Otherwise the set $\{ N(x) : x \in I, x \ne 0 \}$ is a nonempty set of natural numbers. It has a least element, so there is $b \in I$ with $b \ne 0$ and $N(b) \le N(x)$ for all nonzero $x \in I$.

Since $b \in I$, the ideal $(b)$ is contained in $I$. For the converse, let $a \in I$. Divide: $a = qb + r$ with $r = 0$ or $N(r) < N(b)$. Then $r = a - qb$, and both $a$ and $qb$ are in $I$, so $r \in I$. If $r \ne 0$, then $N(r) < N(b)$ contradicts the choice of $b$. So $r = 0$, $a = qb$, and $a \in (b)$. So $I = (b)$. $\square$

::: mathlib
`EuclideanDomain.instIsPrincipalIdealRing` · `Mathlib.RingTheory.PrincipalIdealDomain`

The theorem as an instance. The proof in Mathlib is the proof above: it takes a minimal element of the nonzero elements of `S` with `WellFounded.has_min` for the relation `r`, and shows that `x % m` is zero with `EuclideanDomain.mod_mem_iff`. So `Polynomial K` for a field `K`, `ℤ` and `GaussianInt` are principal ideal rings by instance search.

<?decl EuclideanDomain.instIsPrincipalIdealRing?>
:::

**Theorem (Greatest common divisors in a PID).** Let $R$ be a PID and $a, b \in R$. Let $(a, b) = (d)$. Then $d$ is a greatest common divisor of $a$ and $b$, and there are $x, y \in R$ with
$$d = ax + by.$$

*Proof.* The ideal $(a, b) = \{ax + by : x, y \in R\}$ is principal by hypothesis, so $(a, b) = (d)$ for some $d$. Since $d \in (a, b)$, there are $x$ and $y$ with $d = ax + by$. Since $a \in (d)$ and $b \in (d)$, the element $d$ divides $a$ and $b$. If $c \mid a$ and $c \mid b$, then $c \mid ax + by = d$. $\square$

The identity $d = ax + by$ is the identity of Bezout. A domain in which every ideal with two generators is principal is a Bezout domain. Every PID is one, and the proof above uses only this weaker property.

**Theorem (The Euclidean algorithm).** Let $R$ be a Euclidean domain and $a, b \in R$ with $b \ne 0$. Let $a = qb + r$. Then $(a, b) = (b, r)$, so $a, b$ and $b, r$ have the same greatest common divisors. The sequence $r_0 = a$, $r_1 = b$, and $r_{k+1}$ the remainder of $r_{k-1}$ on division by $r_k$, reaches $0$ after finitely many steps. The last nonzero term is a greatest common divisor of $a$ and $b$.

*Proof.* Since $r = a - qb$, the element $r$ is in $(a, b)$, so $(b, r) \subseteq (a, b)$. Since $a = qb + r$, the element $a$ is in $(b, r)$, so $(a, b) \subseteq (b, r)$. The common divisors of two elements are the divisors of every element of the ideal they generate, so the two pairs have the same common divisors, and the same greatest common divisors.

As long as $r_k \ne 0$, the remainder satisfies $r_{k+1} = 0$ or $N(r_{k+1}) < N(r_k)$. A strictly decreasing sequence of natural numbers is finite, so some $r_{n+1} = 0$ with $r_n \ne 0$. Then $(a, b) = (r_0, r_1) = \dots = (r_n, r_{n+1}) = (r_n, 0) = (r_n)$, and $r_n$ is a greatest common divisor by the previous theorem. $\square$

Each step writes $r_{k+1} = r_{k-1} - q_k r_k$. Substitution from the last step back to the first writes $r_n$ as $ax + by$, the extended Euclidean algorithm.

::: mathlib
`EuclideanDomain.gcd` · `Mathlib.Algebra.EuclideanDomain.Defs`

The Euclidean algorithm as a definition, for `[DecidableEq R]`. It is defined by well-founded recursion on `r`, with `gcd 0 b = b`.

<?decl EuclideanDomain.gcd?>
:::

::: mathlib
`EuclideanDomain.gcd_val` · `Mathlib.Algebra.EuclideanDomain.Basic`

The recursion step `gcd a b = gcd (b % a) a`. Mathlib divides the second argument by the first, the reverse of the order of the theorem above.

<?decl EuclideanDomain.gcd_val?>
:::

::: mathlib
`EuclideanDomain.gcd_eq_gcd_ab` · `Mathlib.Algebra.EuclideanDomain.Basic`

The identity of Bezout, `gcd a b = a * gcdA a b + b * gcdB a b`. The coefficients come from the extended algorithm `EuclideanDomain.xgcd`.

<?decl EuclideanDomain.gcd_eq_gcd_ab?>
:::

::: mathlib
`IsBezout` · `Mathlib.RingTheory.PrincipalIdealDomain`

The class of rings in which every finitely generated ideal is principal. The instance `IsBezout.of_isPrincipalIdealRing` gives it for every principal ideal ring.

<?decl IsBezout?>
:::

**Theorem (Nonzero prime ideals of a PID are maximal).** Let $R$ be a PID and let $P$ be a nonzero prime ideal. Then $P$ is maximal. A nonzero element $p$ generates a prime ideal if and only if it is a prime element.

*Proof.* Write $P = (p)$ with $p \ne 0$. Let $J$ be an ideal with $P \subseteq J$, and write $J = (m)$. Since $p \in (m)$, there is $a$ with $p = ma$. Then $ma \in P$, and $P$ is prime, so $m \in P$ or $a \in P$. If $m \in P$, then $J = (m) \subseteq P$, so $J = P$. If $a \in P$, then $a = pc$ for some $c$, so $p = mpc$. Cancel $p \ne 0$ in the domain $R$: $1 = mc$. So $m$ is a unit and $J = R$. So $P$ is maximal.

The second claim is the definition of a prime element in terms of ideals: $p$ is prime when it is not zero and not a unit, and $p \mid xy$ implies $p \mid x$ or $p \mid y$. These are the conditions $(p) \ne R$ and $xy \in (p) \Rightarrow x \in (p) \text{ or } y \in (p)$. $\square$

So in a PID every nonzero prime ideal gives a field $R/P$. For $R = \mathbb{Z}$ these are the fields $\mathbb{Z}/p$ of Chapter 4. For $R = K[X]$ and an irreducible $f$ they are the fields $K[X]/(f)$ of Volume 11.

::: mathlib
`IsPrime.to_maximal_ideal` · `Mathlib.RingTheory.PrincipalIdealDomain`

The theorem, for `[IsDomain R] [IsPrincipalIdealRing R]`: `S ≠ ⊥ → S.IsMaximal` with `[S.IsPrime]` as an instance argument. The name is in the root namespace, not in `Ideal`.

<?decl IsPrime.to_maximal_ideal?>
:::

::: mathlib
`Ideal.span_singleton_prime` · `Mathlib.RingTheory.Ideal.Maximal`

The second claim, `p ≠ 0 → ((span {p}).IsPrime ↔ Prime p)`, in any commutative semiring.

<?decl Ideal.span_singleton_prime?>
:::

### Examples

**Example (Three Euclidean domains).** The integers with $N(a) = |a|$: for $b \ne 0$ the division $a = qb + r$ with $0 \le r < |b|$ gives $|r| < |b|$. The ring $K[X]$ over a field with $N(f) = \deg f$: this is the division of Chapter 5, and $r = 0$ or $\deg r < \deg g$. The Gaussian integers $\mathbb{Z}[i]$ with $N(a + bi) = a^2 + b^2$, by the theorem of Section 2. A field is a Euclidean domain with $N = 0$, since $a = (ab^{-1}) b + 0$. Every one of these rings is a PID by the theorem.

**Example (The Euclidean algorithm in $\mathbb{Z}$).** Take $a = 1071$ and $b = 462$:
$$1071 = 2 \cdot 462 + 147, \qquad 462 = 3 \cdot 147 + 21, \qquad 147 = 7 \cdot 21 + 0.$$
So $\gcd(1071, 462) = 21$. Back substitution gives
$$21 = 462 - 3 \cdot 147 = 462 - 3(1071 - 2 \cdot 462) = 7 \cdot 462 - 3 \cdot 1071.$$
Check: $7 \cdot 462 = 3234$, $3 \cdot 1071 = 3213$, and $3234 - 3213 = 21$.

**Example (The Euclidean algorithm in $\mathbb{Q}[X]$).** Take $f = X^3 - 1$ and $g = X^2 - 1$. Then
$$X^3 - 1 = X(X^2 - 1) + (X - 1), \qquad X^2 - 1 = (X + 1)(X - 1) + 0.$$
So $\gcd(f, g) = X - 1$, and $X - 1 = f - X g$. The answer agrees with the factorizations $X^3 - 1 = (X - 1)(X^2 + X + 1)$ and $X^2 - 1 = (X - 1)(X + 1)$.

**Example (The Euclidean algorithm in $\mathbb{Z}[i]$).** Take $a = 9 + 2i$ and $b = 3 + 2i$, with norms $85$ and $13$. Section 2 divides by rounding the exact quotient in $\mathbb{Q}(i)$:
$$\frac{a}{b} = \frac{(9 + 2i)(3 - 2i)}{13} = \frac{31 - 12i}{13} \approx 2.38 - 0.92i.$$
Round to $q = 2 - i$. Then $qb = (2 - i)(3 + 2i) = 8 + i$ and $r = a - qb = 1 + i$, of norm $2 < 13$. Next, $b/(1 + i) = (3 + 2i)(1 - i)/2 = (5 - i)/2$. Take $q = 2$: then $r = (3 + 2i) - 2(1 + i) = 1$, of norm $1 < 2$. The last step divides $1 + i$ by $1$ with remainder $0$. So $\gcd(a, b) = 1$ up to a unit. Back substitution gives
$$1 = b - 2(1 + i) = b - 2(a - (2 - i) b) = (5 - 2i) b - 2a.$$
Check: $(5 - 2i)(3 + 2i) = 19 + 4i$ and $2a = 18 + 4i$.

**Counterexample ($\mathbb{Z}[X]$ is not a PID).** Let $I = (2, X) \subseteq \mathbb{Z}[X]$, the polynomials with even constant term. Assume $I = (d)$. Since $2 \in (d)$, $d \mid 2$, and the degree formula over the domain $\mathbb{Z}$ gives $\deg d = 0$. So $d$ is an integer dividing $2$, one of $\pm 1, \pm 2$. Since $X \in (d)$, $X = d g$ for some $g \in \mathbb{Z}[X]$. The coefficient of $X$ gives $1 = d g_1$ with $g_1 \in \mathbb{Z}$, so $d = \pm 1$. Then $1 \in I$, so $1 = 2f + Xg$ for some $f, g$. The constant terms give $1 = 2 f(0)$ in $\mathbb{Z}$, which is false. So $I$ is not principal. The ring $\mathbb{Z}[X]$ is a domain, so it is not a PID, and by the theorem it is not a Euclidean domain for any function $N$. The quotient $\mathbb{Z}[X]/(2, X) \cong \mathbb{F}_2$ is a field, so $I$ is maximal. The ideal $(X)$ is a nonzero prime ideal, since $\mathbb{Z}[X]/(X) \cong \mathbb{Z}$ is a domain, and it is not maximal, since $(X) \subsetneq I$. This is the conclusion of the last theorem failing.

**Counterexample ($K[X, Y]$ is not a PID).** Let $K$ be a field and $I = (X, Y) \subseteq K[X, Y]$. Assume $I = (d)$. View $K[X, Y]$ as $K[X][Y]$, polynomials in $Y$ over the domain $K[X]$. Then $X = dg$ gives $\deg_Y d + \deg_Y g = 0$, so $\deg_Y d = 0$. In the same way $Y = dh$ gives $\deg_X d = 0$. So $d$ is a nonzero constant, a unit, and $I = K[X, Y]$. But every element of $I$ has value $0$ at $(0, 0)$, and $1$ does not. So $I$ is not principal.

**Remark (A PID that is not Euclidean).** The ring $\mathbb{Z}[\alpha]$ with $\alpha = (1 + \sqrt{-19})/2$ is a PID, and it is not a Euclidean domain for any function $N$. The statement is due to Motzkin (1949). His proof shows that a Euclidean domain that is not a field has an element $u$, not zero and not a unit, such that every class of $R/(u)$ contains $0$ or a unit. In $\mathbb{Z}[\alpha]$ the only units are $\pm 1$, and no such $u$ exists. The proof that the ring is a PID uses the class number of Volume 12. So the first implication of this chapter does not reverse.

### The library around it

The definitions are in `Mathlib.Algebra.EuclideanDomain.Defs`, and the gcd theory is in `Mathlib.Algebra.EuclideanDomain.Basic`. The file `Mathlib.RingTheory.PrincipalIdealDomain` proves the PID results: the instance from Euclidean domains, the instance `PrincipalIdealRing.isNoetherianRing`, the lemma `PrincipalIdealRing.isMaximal_of_irreducible`, and the route to unique factorization of Section 3. The membership lemma `Ideal.mem_span_singleton : x ∈ span {y} ↔ y ∣ x` turns statements about principal ideals into statements about divisibility, and `Ideal.span_singleton_le_span_singleton : span {x} ≤ span {y} ↔ y ∣ x` compares two of them. Note the reversal: the larger ideal has the smaller generator.

Common errors of a learner:

- `EuclideanDomain.gcd` needs `[DecidableEq R]`, since the algorithm tests for zero. For `ℤ` and `ℕ` the library also has `Int.gcd` and `Nat.gcd`, which are different functions with their own lemmas.
- `IsPrincipalIdealRing R` alone does not give a domain. Add `[IsDomain R]`.
- In a Euclidean domain the quotient and the remainder are not unique in general. In $\mathbb{Z}$ Mathlib picks the remainder with `0 ≤ a % b`, and in $\mathbb{Z}[i]$ a specific rounding. A proof must not assume more than the axioms.
- The ideal `span {a, b}` uses the set `{a, b}`. Its membership lemma is `Ideal.mem_span_pair : x ∈ span {a, b} ↔ ∃ c d, c * a + d * b = x`.

### Exercises

1. (A) Compute $\gcd(2024, 1001)$ with the Euclidean algorithm and write it as $2024x + 1001y$.
2. (A) Compute the monic $\gcd$ of $X^4 - 1$ and $X^3 + X^2 + X + 1$ in $\mathbb{Q}[X]$.
3. (A) Show that the units of a Euclidean domain are exactly the nonzero $u$ with $N(u) = N(1)$, if $N(a) \le N(ab)$ for all nonzero $a, b$. Hint: first show $N(1) \le N(a)$ for all $a \ne 0$, then divide $1$ by $u$.
4. (B) Show that $(2, 1 + \sqrt{-3})$ is not principal in $\mathbb{Z}[\sqrt{-3}]$. Hint: use the norm $a^2 + 3b^2$; a generator has norm dividing $4$.
5. (B) Show that in a PID every nonempty set of ideals has a maximal element. Hint: the union of a chain of ideals is an ideal.
6. (B) Let $R$ be a PID and $a, b$ coprime. Show that $R/(ab) \cong R/(a) \times R/(b)$. Hint: Bezout and the Chinese remainder theorem of Chapter 2.
7. (B) Show that a subring of $\mathbb{Q}$ that contains $\mathbb{Z}$ is a PID.
8. (C) Show that $\mathbb{Z}[\sqrt 2]$ is a Euclidean domain with $N(a + b\sqrt 2) = |a^2 - 2b^2|$. Hint: round the coordinates of $a/b$ in $\mathbb{Q}(\sqrt 2)$ and bound $|x^2 - 2y^2|$ for $|x|, |y| \le 1/2$.
9. (C) Let $R$ be a domain such that $R[X]$ is a PID. Show that $R$ is a field. Hint: for $a \ne 0$ study the ideal $(a, X)$ as in the counterexample.

### Notes and history

The Euclidean algorithm is Propositions VII.1 and VII.2 of Euclid's *Elements*, about 300 BC, stated for lengths and numbers. The identity $d = ax + by$ for integers is in Bachet de Méziriac (1624), and Bezout proved the analogue for polynomials in the eighteenth century. Gauss used the Euclidean algorithm in $\mathbb{Z}[i]$ in his work on biquadratic residues (1832). The notion of an ideal is due to Dedekind (1871), and the abstract definitions of this section come from the school of Emmy Noether in the 1920s. Motzkin, "The Euclidean algorithm" (1949), gave the criterion that shows that $\mathbb{Z}[(1 + \sqrt{-19})/2]$ is not Euclidean. A clear textbook account is Dummit and Foote, *Abstract Algebra*, Chapter 8.

In Mathlib, the class `EuclideanDomain` is due to Louis Carlin and Mario Carneiro. Its docstring cites Motzkin and Nagata, and explains the choice of a well-founded relation in place of a function to $\mathbb{N}$. The file on principal ideal domains is due to Chris Hughes and Morenikeji Neri.

### Reference

<?reference?>
