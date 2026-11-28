---
title: Gauss's lemma
kind: theory
modules:
  - Mathlib.RingTheory.Polynomial.Content
  - Mathlib.RingTheory.Polynomial.ContentIdeal
  - Mathlib.RingTheory.Polynomial.GaussLemma
  - Mathlib.RingTheory.Polynomial.UniqueFactorization
  - Mathlib.RingTheory.Polynomial.IrreducibleRing
explains:
  E3: [Polynomial.IsPrimitive.mul, Polynomial.IsPrimitive.irreducible_iff_irreducible_map_fraction_map, Polynomial.uniqueFactorizationMonoid, Polynomial.content]
  E2: [Polynomial.IsPrimitive, Polynomial.primPart, Polynomial.isPrimitive_primPart, Polynomial.content_mul, Polynomial.isPrimitive_iff_content_eq_one, Polynomial.Monic.isPrimitive, Polynomial.isPrimitive_of_dvd, Polynomial.content_primPart, Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast, Polynomial.IsPrimitive.dvd_iff_fraction_map_dvd_fraction_map, Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map, MvPolynomial.uniqueFactorizationMonoid, Polynomial.wfDvdMonoid, Polynomial.exists_irreducible_of_degree_pos, Polynomial.normalizedGcdMonoid]
  E1: [NormalizedGCDMonoid, GCDMonoid, UniqueFactorizationMonoid, ufm_of_decomposition_of_wfDvdMonoid, Polynomial.IsPrimitive.dvd_of_fraction_map_dvd_fraction_map, Polynomial.IsPrimitive.irreducible_of_irreducible_map_of_injective]
families: []
requires: [V06.C05, V06.C06, V09.C01]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Gauss's lemma

### Overview

Let $R$ be a unique factorization domain with field of fractions $K$. The ring $K[X]$ has unique factorization, as a principal ideal domain. The ring $R[X]$ is in general not a principal ideal domain, but this section proves that it still has unique factorization.

The proof compares $R[X]$ with $K[X]$. The content separates the constant factors from the factors of positive degree, and Gauss's lemma controls the content of a product.

### Definitions

**Definition (Content).** Let $f = a_n X^n + \dots + a_1 X + a_0 \in R[X]$. The content $c(f)$ of $f$ is a greatest common divisor of $a_0, \dots, a_n$, defined up to a unit of $R$.

**Definition (Primitive polynomial).** A polynomial $f \in R[X]$ is primitive if every $r \in R$ that divides all the coefficients of $f$ is a unit. Equivalently, $c(f)$ is a unit, or no prime element of $R$ divides all the coefficients of $f$.

A monic polynomial is primitive, $2X + 3 \in \mathbb{Z}[X]$ is primitive but not monic, and $2X + 4$ is not primitive.

**Definition (Primitive part).** Let $f \in R[X]$ be nonzero. The primitive part of $f$ is the polynomial $\operatorname{pp}(f)$ with $f = c(f) \operatorname{pp}(f)$. Its coefficients $a_i / c(f)$ lie in $R$ and have no common prime factor, so $\operatorname{pp}(f)$ is primitive.

::: mathlib
`Polynomial.content` · `Mathlib.RingTheory.Polynomial.Content`

`p.content` is `p.support.gcd p.coeff`. It needs `[NormalizedGCDMonoid R]`, a chosen `gcd` with normalized values, so the content is a definite element of `R`. The instance `Polynomial.normalizedGcdMonoid` makes `R[X]` a ring of the same kind.

<?decl Polynomial.content?>
:::

::: mathlib
`Polynomial.IsPrimitive` · `Mathlib.RingTheory.Polynomial.Content`

`p.IsPrimitive` says `∀ r : R, C r ∣ p → IsUnit r`. `isPrimitive_iff_content_eq_one` gives the form with the content. `p.primPart` is the primitive part, with `content_primPart`, and the junk value `primPart 0 = 1` lets `isPrimitive_primPart` have no hypothesis. See also `Monic.isPrimitive` and `isPrimitive_of_dvd`.

<?decl Polynomial.IsPrimitive?>
:::

### Theorems and proofs

**Lemma (Reduction modulo a prime).** Let $p$ be a prime element of $R$. The map $R[X] \to (R/(p))[X]$ that reduces each coefficient modulo $p$ is a surjective ring homomorphism with kernel $p R[X]$. The ring $(R/(p))[X]$ is a domain. So $p$ is a prime element of $R[X]$.

*Proof.* The map is the extension of $R \to R/(p)$ with $X \mapsto X$ (Volume 6, Chapter 5). Coefficients lift, so it is surjective, and its kernel is the set of polynomials with all coefficients in $(p)$, that is, $pR[X]$. The ring $R/(p)$ is a domain, so $(R/(p))[X]$ is a domain by the formula $\deg(gh) = \deg g + \deg h$. So $R[X]/pR[X] \cong (R/(p))[X]$ is a domain, and $pR[X]$ is a prime ideal. $\square$

**Theorem (Gauss's lemma).** Let $f, g \in R[X]$ be primitive. Then $fg$ is primitive. More generally, $c(fg) = c(f) c(g)$ up to a unit for all $f, g \in R[X]$.

*Proof.* If $fg$ is not primitive, a prime $p$ of $R$ divides all its coefficients. Let $\bar f, \bar g$ be the reductions modulo $p$. Then $\bar f \bar g = \overline{fg} = 0$ in $(R/(p))[X]$. This ring is a domain by the lemma, so $\bar f = 0$ or $\bar g = 0$. Then $p$ divides all coefficients of $f$ or of $g$, against the hypothesis.

For the general statement, let $f, g \ne 0$ and write $f = c(f) f_1$ and $g = c(g) g_1$ with $f_1, g_1$ primitive. Then $fg = c(f) c(g) f_1 g_1$ with $f_1 g_1$ primitive. For $a \in R$ and $h$ primitive, $c(ah) = a$ up to a unit, since $\gcd(a b_0, \dots, a b_m) = a \gcd(b_0, \dots, b_m)$. So $c(fg) = c(f) c(g)$ up to a unit. $\square$

**Lemma (Clearing denominators).** Each nonzero $h \in K[X]$ can be written $h = a h_0$ with $a \in K$ nonzero and $h_0 \in R[X]$ primitive. If also $h = b h_1$ with $b \in K$ and $h_1 \in R[X]$ primitive, then $b = u a$ and $h_1 = u^{-1} h_0$ for a unit $u$ of $R$.

*Proof.* Let $d \in R$ be the product of the denominators of the coefficients of $h$. Then $0 \ne dh \in R[X]$. Put $h_0 = \operatorname{pp}(dh)$ and $a = c(dh)/d$.

For the uniqueness, choose $s \in R$ nonzero with $sa \in R$ and $sb \in R$. Then $(sa) h_0 = (sb) h_1$ in $R[X]$. The contents give $sa = u \cdot sb$ for a unit $u$ of $R$. So $a = ub$, and $b h_1 = ub h_0$ gives $h_1 = u h_0$. Rename $u^{-1}$ as $u$. $\square$

**Theorem (Irreducibility over $R$ and over $K$).** Let $f \in R[X]$ be primitive of positive degree. Then $f$ is irreducible in $R[X]$ if and only if $f$ is irreducible in $K[X]$.

*Proof.* Suppose first that $f$ is irreducible in $K[X]$, and let $f = gh$ with $g, h \in R[X]$. In $K[X]$ one factor is a unit, so a nonzero constant, say $g = c \in R$. Then $c$ divides every coefficient of $f$, so $c$ is a unit of $R$. Also $f$ is not a unit, since its degree is positive. So $f$ is irreducible in $R[X]$.

Now suppose that $f$ is irreducible in $R[X]$, and assume that $f = GH$ in $K[X]$ with $\deg G \ge 1$ and $\deg H \ge 1$. By the clearing lemma write $G = a g_0$ and $H = b h_0$ with $g_0, h_0 \in R[X]$ primitive. Then $f = (ab) g_0 h_0$ with $g_0 h_0$ primitive by Gauss's lemma, and also $f = 1 \cdot f$. The uniqueness in the clearing lemma makes $ab$ a unit $u$ of $R$. So $f = (u g_0) h_0$ in $R[X]$ with two factors of positive degree, a contradiction. Finally, $f$ is not a unit of $K[X]$, since its degree is positive. $\square$

**Lemma (Divisibility over $R$ and over $K$).** Let $q \in R[X]$ be primitive and $g \in R[X]$. If $q \mid g$ in $K[X]$, then $q \mid g$ in $R[X]$.

*Proof.* The case $g = 0$ is clear, so assume $g \ne 0$. Write $g = qH$ with $H \in K[X]$, and $H = a h_0$ as in the clearing lemma. Then $g = a (q h_0)$, and $q h_0$ is primitive by Gauss's lemma. Write $a = r/s$ with $r, s \in R$ and $s \ne 0$. Then $s g = r q h_0$, and the contents give $s \, c(g) = r$ up to a unit. So $s$ divides $r$ in $R$, and $a \in R$. Hence $a h_0 \in R[X]$ and $g = q \cdot (a h_0)$. $\square$

**Theorem (Polynomial rings over a unique factorization domain).** If $R$ is a unique factorization domain, then $R[X]$ is a unique factorization domain.

*Proof.* By Volume 6, Chapter 6, Section 3, a domain is a unique factorization domain if each nonzero nonunit is a product of irreducible elements and each irreducible element is prime. The domain $R[X]$ has both properties.

*Existence.* Let $f \in R[X]$ be nonzero and not a unit. Write $f = c(f) \operatorname{pp}(f)$. The content is a unit times a product of irreducible elements of $R$. These stay irreducible in $R[X]$, since a factorization of a constant has constant factors and the units of $R[X]$ are those of $R$. It remains to factor a primitive $f$ of positive degree, by induction on the degree. If $f = gh$ with $g, h$ not units, then neither factor is constant, since a constant factor of a primitive polynomial is a unit. So $g$ and $h$ have smaller positive degree, they are primitive, and the induction hypothesis factors them.

*Irreducible elements are prime.* Let $q$ be irreducible in $R[X]$. If $\deg q = 0$, then $q$ is a prime element of $R$, and so prime in $R[X]$ by the first lemma. If $\deg q \ge 1$, then $c(q)$ is a unit, since $\operatorname{pp}(q)$ is not a unit. So $q$ is primitive and irreducible in $K[X]$, hence prime in the principal ideal domain $K[X]$. If $q \mid gh$ in $R[X]$, then $q \mid g$ or $q \mid h$ in $K[X]$, and the divisibility lemma moves this to $R[X]$. $\square$

**Corollary (Several variables).** If $R$ is a unique factorization domain, then $R[x_1, \dots, x_n]$ is a unique factorization domain. In particular $\mathbb{Z}[x_1, \dots, x_n]$ and $k[x_1, \dots, x_n]$ for a field $k$ are unique factorization domains.

*Proof.* Induction on $n$, with $R[x_1, \dots, x_n] \cong R[x_1, \dots, x_{n-1}][x_n]$ (Chapter 6, Section 1). $\square$

::: mathlib
`Polynomial.IsPrimitive.mul` · `Mathlib.RingTheory.Polynomial.Content`

`hp.mul hq : (p * q).IsPrimitive` over a `NormalizedGCDMonoid`. `content_mul` states `(p * q).content = p.content * q.content` under `StrongNormalizedGCDMonoid`.

<?decl Polynomial.IsPrimitive.mul?>
:::

::: mathlib
`Polynomial.IsPrimitive.irreducible_iff_irreducible_map_fraction_map` · `Mathlib.RingTheory.Polynomial.GaussLemma`

For `hp : p.IsPrimitive` this is `Irreducible p ↔ Irreducible (p.map (algebraMap R K))`, with `[IsFractionRing R K]` and `[IsGCDMonoid R]`. The case of `ℤ` is `IsPrimitive.Int.irreducible_iff_irreducible_map_cast`, and `Monic.irreducible_iff_irreducible_map_fraction_map` treats monic polynomials over an integrally closed domain.

<?decl Polynomial.IsPrimitive.irreducible_iff_irreducible_map_fraction_map?>
:::

::: mathlib
`Polynomial.uniqueFactorizationMonoid` · `Mathlib.RingTheory.Polynomial.UniqueFactorization`

An instance for a domain `D` with unique factorization. Its proof has the two parts of the text: `Polynomial.wfDvdMonoid` gives existence, and `ufm_of_decomposition_of_wfDvdMonoid` adds the `gcd` structure. `MvPolynomial.uniqueFactorizationMonoid` covers several variables.

<?decl Polynomial.uniqueFactorizationMonoid?>
:::

### Examples

**Example (A content and a primitive part).** Let $f = 6X^3 + 4X^2 - 10 \in \mathbb{Z}[X]$. The gcd of $6, 4, 0, -10$ is $2$, so $c(f) = 2$ and $\operatorname{pp}(f) = 3X^3 + 2X^2 - 5$. As $\operatorname{pp}(f)(1) = 0$, it is $(X - 1)(3X^2 + 5X + 5)$, and the quadratic is primitive with discriminant $-35$, so irreducible in $\mathbb{Q}[X]$ and in $\mathbb{Z}[X]$. So $f = 2 (X - 1)(3X^2 + 5X + 5)$ in $\mathbb{Z}[X]$, and in $\mathbb{Q}[X]$ the factor $2$ is a unit.

**Counterexample (The primitive hypothesis is needed).** The polynomial $f = 2X + 2 \in \mathbb{Z}[X]$ has degree $1$, so it is irreducible in $\mathbb{Q}[X]$. In $\mathbb{Z}[X]$ it is $2 \cdot (X + 1)$, a product of two non-units, since the units of $\mathbb{Z}[X]$ are $\pm 1$. Here $c(f) = 2$.

**Counterexample (Gauss's lemma fails without unique factorization).** Let $R = \mathbb{Z}[\sqrt{-3}]$ and $s = \sqrt{-3}$. The norm $N(a + bs) = a^2 + 3b^2$ is multiplicative. Let $f = 2X - (1 + s)$ and $g = 2X - (1 - s)$. A common divisor $d$ of $2$ and $1 + s$ has norm dividing $4$. No element has norm $2$, and $N(d) = 4$ would make $d$ an associate of $2$, since $d \mid 2$, but $(1 + s)/2 \notin R$. So $d = \pm 1$, and $f$ and likewise $g$ are primitive. But $fg = (2X - 1)^2 - s^2 = 4X^2 - 4X + 4$ is not primitive. The proof breaks because $2$ is irreducible in $R$ but not prime: $2 \mid (1 + s)(1 - s)$.

### The library around it

`Polynomial.exists_irreducible_of_degree_pos` gives an irreducible factor of a polynomial of positive degree. `IsPrimitive.dvd_iff_fraction_map_dvd_fraction_map` is the divisibility lemma of the text.

The content and the primitive part live in `Mathlib.RingTheory.Polynomial.Content`. Its lemmas follow the names of the objects: `Polynomial.content_C`, `Polynomial.content_X`, `Polynomial.content_mul`, `Polynomial.content_primPart`, `Polynomial.isPrimitive_primPart`, `Polynomial.primPart_dvd`. The multiplicativity `Polynomial.content_mul` needs a `StrongNormalizedGCDMonoid`; with only a `NormalizedGCDMonoid` the library gives `Polynomial.associated_content_mul`, equality up to a unit. Divisibility splits into two parts, `Polynomial.dvd_iff_content_dvd_content_and_primPart_dvd_primPart`, and the module puts a `NormalizedGCDMonoid` on $R[X]$, `Polynomial.normalizedGcdMonoid`. For rings without a gcd, `Mathlib.RingTheory.Polynomial.ContentIdeal` defines the content ideal `Polynomial.contentIdeal`, the ideal generated by the coefficients. A polynomial over a Bezout domain is primitive exactly when its content ideal is the unit ideal, `Polynomial.isPrimitive_iff_contentIdeal_eq_top`. For any commutative ring the content ideals satisfy $c(p) c(q) \subseteq \sqrt{c(pq)}$, `Polynomial.mul_contentIdeal_le_radical_contentIdeal_mul`, and so the product of two polynomials with unit content ideal has unit content ideal, `Polynomial.contentIdeal_mul_eq_top_of_contentIdeal_eq_top`. This is a form of Gauss's lemma that needs no factorization. The module `Mathlib.RingTheory.Polynomial.GaussLemma` holds the comparison with the field of fractions: `Polynomial.IsPrimitive.irreducible_iff_irreducible_map_fraction_map`, its case over $\mathbb{Z}$, `Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast`, and the monic version `Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map` for an integrally closed domain. The converse holds: `Polynomial.isIntegrallyClosed_iff'` says that a domain is integrally closed exactly when a monic polynomial is irreducible over $R$ only if it is irreducible over $K$. The module `Mathlib.RingTheory.Polynomial.UniqueFactorization` gives the instances `Polynomial.uniqueFactorizationMonoid` and `MvPolynomial.uniqueFactorizationMonoid`, and `Polynomial.wfDvdMonoid` for the weaker condition that divisibility is well founded. The one lemma of `Mathlib.RingTheory.Polynomial.IrreducibleRing`, `Polynomial.Monic.irreducible_of_irreducible_map_of_isPrime_nilradical`, lifts irreducibility of a monic polynomial along any map to a domain, when the nilradical of $R$ is prime.

A common error of a learner: `NormalizedGCDMonoid` is not inferred from `UniqueFactorizationMonoid`, since a normalization is extra data. For `ℤ` and fields the instance exists.

### Exercises

1. (A) Compute the content and the primitive part of $12X^4 - 18X^2 + 30 \in \mathbb{Z}[X]$ and of $(1 + i)X^2 + 2X + 2i \in \mathbb{Z}[i][X]$. Hint: in $\mathbb{Z}[i]$ the element $1 + i$ is prime and $2 = -i(1 + i)^2$.
2. (A) Show that a polynomial $f \in R[X]$ of degree $1$ is irreducible if and only if it is primitive.
3. (B) Show that the units of $R[X]$ are the units of $R$ when $R$ is a domain, and give an example of a commutative ring $R$ for which $R[X]$ has a unit of positive degree. Hint: $(1 + 2X)(1 - 2X)$ in $(\mathbb{Z}/4)[X]$.
4. (B) Let $f \in \mathbb{Z}[X]$ be monic and let $g \in \mathbb{Q}[X]$ be a monic divisor of $f$ in $\mathbb{Q}[X]$. Show that $g \in \mathbb{Z}[X]$. Hint: write $f = gh$, clear the denominators of $g$ and $h$ and use Gauss's lemma.
5. (C) Show that $x^2 + y^2 - 1$ is irreducible in $\mathbb{Q}[x, y]$. Hint: view it as a monic polynomial in $y$ over the unique factorization domain $\mathbb{Q}[x]$ and look for a root in $\mathbb{Q}(x)$.

### Notes and history

Gauss proved the case of the integers in the *Disquisitiones Arithmeticae* (1801), in the form of Exercise 4. The library works with GCD domains, a class larger than the unique factorization domains.

### Reference

<?reference?>
