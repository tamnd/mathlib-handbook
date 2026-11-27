---
title: The minimal polynomial
kind: theory
modules:
  - Mathlib.FieldTheory.Minpoly.Basic
  - Mathlib.FieldTheory.Minpoly.Field
  - Mathlib.FieldTheory.Minpoly.MinpolyDiv
  - Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
  - Mathlib.FieldTheory.Minpoly.Finite
  - Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
  - Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
  - Mathlib.RingTheory.PowerBasis
explains:
  E3: [minpoly, minpoly.irreducible, minpoly.dvd, IntermediateField.adjoin.finrank, IntermediateField.adjoin.powerBasis, IntermediateField.adjoinRootEquivAdjoin, PowerBasis]
  E2: [minpoly.monic, minpoly.aeval, minpoly.unique, minpoly.min, minpoly.ne_zero, minpoly.dvd_iff, minpoly.ker_aeval_eq_span_minpoly, minpoly.degree_dvd, minpoly.natDegree_le, minpoly.natDegree_eq_one_iff, minpoly.dvd_map_of_isScalarTower, "minpoly.isIntegrallyClosed_eq_field_fractions'", minpoly.zero, IntermediateField.finrank_eq_one_iff, IntermediateField.isSimpleOrder_of_finrank_prime, IntermediateField.mem_adjoin_simple_iff, IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic, PowerBasis.finrank, IntermediateField.adjoin.powerBasis_dim, Polynomial.Irreducible.natDegree_dvd_finrank]
  E1: auto
families: []
requires: [V11.C01, V06.C05, V06.C06]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The minimal polynomial

### Overview

An algebraic element $\alpha$ is a root of many polynomials. Among them is one monic polynomial of least degree, and it divides all the others. This minimal polynomial $m_\alpha$ determines the field $K(\alpha)$ up to isomorphism: $K(\alpha) \cong K[X]/(m_\alpha)$, and $[K(\alpha):K] = \deg m_\alpha$. So the degree of a simple extension is the degree of one polynomial, and the tower law of Chapter 1 turns into a tool to compute.

To use this, one must recognise the minimal polynomial. A monic polynomial with root $\alpha$ is the minimal polynomial exactly when it is irreducible. So the section also proves three tests for irreducibility over $\mathbb{Q}$: the rational root test, the criterion of Eisenstein and reduction modulo a prime.

The section needs Section 1, Chapter 1, polynomials from Volume 6, Chapter 5, and principal ideal domains and irreducible elements from Volume 6, Chapter 6.

### Definitions

**Definition (Minimal polynomial).** Let $L/K$ be an extension and $\alpha \in L$ algebraic over $K$. The minimal polynomial $m_\alpha = m_{\alpha,K}$ is the monic polynomial of least degree in $K[X]$ with $m_\alpha(\alpha) = 0$.

The theorem below shows that $m_\alpha$ exists and is unique. The degree of $\alpha$ over $K$ is $\deg m_\alpha$.

::: mathlib
`minpoly` · `Mathlib.FieldTheory.Minpoly.Basic`

`minpoly A x : A[X]` is defined for any commutative ring `A` and any `A`-algebra. If `x` is integral, it is a monic polynomial of least degree with root `x`, chosen by well founded minimality. If `x` is not integral, it is the junk value `0`. So `minpoly ℚ Real.pi = 0`. Lemmas take `hx : IsIntegral A x`, which over a field is `IsAlgebraic`. The basic facts are `minpoly.aeval : aeval x (minpoly A x) = 0`, which holds always, `minpoly.monic hx`, `minpoly.ne_zero hx` and `minpoly.min`, the minimality of the degree.

<?decl minpoly?>
:::

### Theorems and proofs

**Theorem (Minimal polynomial).** Let $\alpha \in L$ be algebraic over $K$. The set $I = \{p \in K[X] : p(\alpha) = 0\}$ is the ideal $(m_\alpha)$. The polynomial $m_\alpha$ is irreducible, and it is the only monic irreducible polynomial with root $\alpha$.

*Proof.* The set $I$ is the kernel of the evaluation map $K[X] \to L$, so it is an ideal. It is nonzero, since $\alpha$ is algebraic. The ring $K[X]$ is a principal ideal domain (Volume 6, Chapter 6), so $I = (m)$ for a nonzero $m$, which can be taken monic. Each nonzero element of $I$ is a multiple of $m$, so it has degree at least $\deg m$. So $m$ is a monic element of $I$ of least degree. If $m'$ is another, then $m - m' \in I$ has smaller degree, so $m - m' = 0$. Thus $m = m_\alpha$ is unique.

Suppose $m_\alpha = gh$ with $g, h$ of positive degree. Then $g(\alpha)h(\alpha) = 0$ in the field $L$, so $g(\alpha) = 0$ or $h(\alpha) = 0$. Either factor lies in $I$ and has smaller degree than $m_\alpha$, a contradiction. So $m_\alpha$ is irreducible.

Let $p$ be monic irreducible with $p(\alpha) = 0$. Then $m_\alpha \mid p$. Since $p$ is irreducible and $\deg m_\alpha \geq 1$, the quotient is a unit, a constant. Both are monic, so $p = m_\alpha$. $\square$

::: mathlib
`minpoly.irreducible` · `Mathlib.FieldTheory.Minpoly.Basic`

`minpoly.irreducible hx : Irreducible (minpoly A x)` under `[IsDomain A] [IsDomain B]`. The ideal form over a field is `minpoly.ker_aeval_eq_span_minpoly`. The uniqueness is `minpoly.unique`: a monic `p` with root `x` and least degree among monic polynomials with root `x` is `minpoly A x`.

<?decl minpoly.irreducible?>
:::

::: mathlib
`minpoly.dvd` · `Mathlib.FieldTheory.Minpoly.Field`

`minpoly.dvd A x : aeval x p = 0 → minpoly A x ∣ p`, for a field `A`. The converse is part of `minpoly.dvd_iff`. To show that a monic irreducible `p` with root `x` is the minimal polynomial, apply `minpoly.dvd` and then use the irreducibility of `p`, as in the proof. For a tower `A → K → R`, `minpoly.dvd_map_of_isScalarTower` says that the minimal polynomial over the larger field `K` divides the one over `A`.

<?decl minpoly.dvd?>
:::

**Theorem (Structure of a simple algebraic extension).** Let $\alpha$ be algebraic over $K$ with minimal polynomial $m$ of degree $n$. Then evaluation at $\alpha$ induces an isomorphism $K[X]/(m) \cong K(\alpha)$, and $1, \alpha, \dots, \alpha^{n-1}$ is a basis of $K(\alpha)$ over $K$. In particular $[K(\alpha):K] = n$.

*Proof.* Evaluation $K[X] \to L$ has the kernel $(m)$ and the image $K[\alpha]$. By the isomorphism theorem $K[X]/(m) \cong K[\alpha]$. Section 1 shows $K[\alpha] = K(\alpha)$. The elements $1, \alpha, \dots, \alpha^{n-1}$ span $K[\alpha]$ by division with remainder, as in Section 1. They are independent: a relation $\sum_{i<n} c_i\alpha^i = 0$ gives a polynomial of degree less than $n$ in $(m)$, which must be $0$. $\square$

**Corollary (Degree divides).** If $L/K$ is finite and $\alpha \in L$, then $\deg m_\alpha$ divides $[L:K]$. If $\deg m_\alpha = 1$, then $\alpha \in K$.

*Proof.* By the tower law $[L:K] = [L:K(\alpha)]\,[K(\alpha):K]$. If $m_\alpha = X - a$, then $\alpha = a$. $\square$

::: mathlib
`IntermediateField.adjoin.finrank` · `Mathlib.FieldTheory.IntermediateField.Adjoin.Basic`

The statement is `IsIntegral K x → finrank K K⟮x⟯ = (minpoly K x).natDegree`. The divisibility is `minpoly.degree_dvd`, and the case of degree one is `minpoly.natDegree_eq_one_iff`. The lemma `minpoly.natDegree_le` gives `natDegree ≤ finrank` in a finite extension. The degree one criterion of Chapter 1 is `IntermediateField.finrank_eq_one_iff`, and the prime degree criterion is `IntermediateField.isSimpleOrder_of_finrank_prime`.

<?decl IntermediateField.adjoin.finrank?>
:::

::: mathlib
`IntermediateField.adjoinRootEquivAdjoin` · `Mathlib.FieldTheory.IntermediateField.Adjoin.Basic`

`adjoinRootEquivAdjoin F hα : AdjoinRoot (minpoly F α) ≃ₐ[F] F⟮α⟯`. Here `AdjoinRoot f` is the quotient `K[X]/(f)`, built in `Mathlib.RingTheory.AdjoinRoot`, with the class of `X` as `AdjoinRoot.root f`. It is a field when `f` is irreducible. Chapter 3 uses it to build roots. The lemma `IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic` states $K[\alpha] = K(\alpha)$ as `F⟮α⟯.toSubalgebra = F[α]`, and `IntermediateField.mem_adjoin_simple_iff` describes the elements as quotients.

<?decl IntermediateField.adjoinRootEquivAdjoin?>
:::

::: mathlib
`PowerBasis` · `Mathlib.RingTheory.PowerBasis`

A `pb : PowerBasis R S` has a generator `pb.gen`, a dimension `pb.dim` and a basis `pb.basis` whose `i`-th vector is `pb.gen ^ i`. It is the right structure for $1, \alpha, \dots, \alpha^{n-1}$. `PowerBasis.finrank` gives `finrank R S = pb.dim`. For `hx : IsIntegral K x`, `IntermediateField.adjoin.powerBasis hx : PowerBasis K K⟮x⟯` has the generator `x`, and `IntermediateField.adjoin.powerBasis_dim` gives `dim = (minpoly K x).natDegree`.

<?decl IntermediateField.adjoin.powerBasis?>

<?decl PowerBasis?>
:::

**Theorem (Rational root test).** Let $f = a_nX^n + \dots + a_0 \in \mathbb{Z}[X]$ with $a_n \neq 0$, and let $r = a/b$ be a rational root with $\gcd(a, b) = 1$. Then $a \mid a_0$ and $b \mid a_n$.

*Proof.* Multiply $f(a/b) = 0$ by $b^n$: $a_na^n + a_{n-1}a^{n-1}b + \dots + a_0b^n = 0$. Each term except the last is a multiple of $a$, so $a \mid a_0b^n$. Since $\gcd(a, b^n) = 1$, $a \mid a_0$. In the same way $b \mid a_na^n$, so $b \mid a_n$. $\square$

A polynomial of degree $2$ or $3$ over a field is irreducible exactly when it has no root there, since a factorization has a factor of degree $1$.

**Theorem (Eisenstein).** Let $f = a_nX^n + \dots + a_0 \in \mathbb{Z}[X]$, $n \geq 1$, and $p$ a prime with $p \nmid a_n$, $p \mid a_i$ for $i < n$, and $p^2 \nmid a_0$. Then $f$ is irreducible in $\mathbb{Q}[X]$.

*Proof.* By the lemma of Gauss (below), if $f$ factors in $\mathbb{Q}[X]$ into factors of positive degree, then $f = gh$ in $\mathbb{Z}[X]$ with $\deg g = k \geq 1$ and $\deg h = n - k \geq 1$. Reduce modulo $p$. Then $\bar g \bar h = \bar f = \bar a_n X^n$ in $\mathbb{F}_p[X]$, with $\bar a_n \neq 0$. Since $\mathbb{F}_p[X]$ has unique factorization and $X$ is prime, $\bar g = cX^i$ and $\bar h = dX^j$ with $i + j = n$. Also $i \leq k$ and $j \leq n - k$, so $i = k \geq 1$ and $j \geq 1$. So $p$ divides the constant terms $g_0$ and $h_0$, and $p^2 \mid g_0h_0 = a_0$, a contradiction. $\square$

**Theorem (Reduction modulo a prime).** Let $f \in \mathbb{Z}[X]$ be monic and $p$ a prime. If the reduction $\bar f \in \mathbb{F}_p[X]$ is irreducible, then $f$ is irreducible in $\mathbb{Q}[X]$.

*Proof.* If $f$ factors over $\mathbb{Q}$, then by Gauss $f = gh$ with monic $g, h \in \mathbb{Z}[X]$ of positive degree. Reduction keeps the degrees of monic polynomials, so $\bar f = \bar g \bar h$ is a factorization of $\bar f$ into factors of positive degree. $\square$

The lemma of Gauss says: a primitive $f \in \mathbb{Z}[X]$ is irreducible in $\mathbb{Z}[X]$ if and only if it is irreducible in $\mathbb{Q}[X]$, and a factorization over $\mathbb{Q}$ gives one over $\mathbb{Z}$ with the same degrees. Volume 9 proves it in full for each unique factorization domain. In Mathlib it is `Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast`. The two tests are `Polynomial.irreducible_of_eisenstein_criterion` and `Polynomial.Monic.irreducible_of_irreducible_map`, and `minpoly.isIntegrallyClosed_eq_field_fractions'` says that the minimal polynomial over $\mathbb{Q}$ of an algebraic integer has integer coefficients.

### Examples

**Example (The minimal polynomial of $\sqrt 2 + \sqrt 3$).** Let $\theta = \sqrt 2 + \sqrt 3$. Then $\theta^2 = 5 + 2\sqrt 6$, so $(\theta^2 - 5)^2 = 24$, that is
$$\theta^4 - 10\theta^2 + 1 = 0.$$
By Chapter 1, Section 1, $\mathbb{Q}(\theta) = \mathbb{Q}(\sqrt 2, \sqrt 3)$, and by Chapter 1, Section 2, this field has degree $4$. So $\deg m_\theta = 4$, and $m_\theta = X^4 - 10X^2 + 1$, since $m_\theta$ divides this monic quartic. The polynomial has the four roots $\pm\sqrt 2 \pm \sqrt 3$. Reduction modulo a prime cannot prove this result: one can show that $X^4 - 10X^2 + 1$ is reducible modulo every prime.

**Example (The minimal polynomial depends on the base).** Over $K = \mathbb{Q}(\sqrt 2)$, the same $\theta$ satisfies $(\theta - \sqrt 2)^2 = 3$, so it is a root of $X^2 - 2\sqrt 2 X - 1 \in K[X]$. This polynomial has no root in $K$, because a root would give $\sqrt 3 \in K$. So it is irreducible, and it is $m_{\theta, K}$. Its degree is $2 = [K(\theta):K]$, which matches the tower law $4 = 2 \cdot 2$. And it divides $X^4 - 10X^2 + 1$ in $K[X]$, as `minpoly.dvd_map_of_isScalarTower` predicts. Over $\mathbb{R}$, the polynomial is $X - \theta$.

**Example (Eisenstein and cube roots).** $X^3 - 2$ is Eisenstein at $p = 2$, so it is $m_c$ for $c = \sqrt[3]{2}$, and $[\mathbb{Q}(c):\mathbb{Q}] = 3$ with the basis $1, c, c^2$. In the same way $X^n - 2$ is irreducible for each $n$. The polynomial $X^4 + 4$ has no rational root but is reducible: $X^4 + 4 = (X^2 + 2X + 2)(X^2 - 2X + 2)$. So the root criterion needs degree at most $3$.

### The library around it

`Polynomial.Irreducible.natDegree_dvd_finrank` gives the corollary for a polynomial: if an irreducible `f` splits in `L`, then its degree divides `finrank K L`. `minpoly.zero` gives `minpoly A 0 = X`.

**Common errors of a learner.** The first error is to forget the junk value: `(minpoly ℚ x).natDegree = 0` does not say that $x \in \mathbb{Q}$. It may say that $x$ is transcendental. The second error is to prove `minpoly K x = p` from `aeval x p = 0` alone: monic and irreducible are both needed.

### Exercises

1. (A) Find the minimal polynomial of $1 + \sqrt[3]{2}$ over $\mathbb{Q}$. Hint: $(\alpha - 1)^3 = 2$.

2. (A) Show that $X^5 - 6X + 3$ and $X^4 + 10X + 5$ are irreducible over $\mathbb{Q}$. Hint: Eisenstein at $3$ and at $5$.

3. (A) Find the minimal polynomial of $i$ over $\mathbb{Q}$, over $\mathbb{R}$ and over $\mathbb{C}$. Hint: the degree of the extension generated.

4. (B) Show that $f(X)$ is irreducible if and only if $f(X + 1)$ is. Use this to show that $X^{p-1} + \dots + X + 1$ is irreducible for a prime $p$. Hint: multiply by $X - 1$, shift, and apply Eisenstein at $p$.

5. (B) Show that $\sqrt[3]{2} \notin \mathbb{Q}(\sqrt[4]{2})$. Hint: degrees $3$ and $4$.

6. (B) Let $\alpha$ have odd degree over $K$. Show that $K(\alpha) = K(\alpha^2)$. Hint: $[K(\alpha):K(\alpha^2)] \leq 2$ and divides an odd number.

7. (B) Show that $X^4 + 1$ is irreducible over $\mathbb{Q}$ and find its factors over $\mathbb{Q}(\sqrt 2)$. Hint: substitute $X + 1$; over $\mathbb{Q}(\sqrt 2)$ use $X^4 + 1 = (X^2 + 1)^2 - 2X^2$.

8. (C) Let $p$ be prime, $K$ a field, and $a \in K$ not a $p$-th power. Show that $X^p - a$ is irreducible over $K$. Hint: a monic factor of degree $k$ with $0 < k < p$ has constant term $\pm\beta$ with $\beta^p = a^k$ in a field where $X^p - a$ splits, and $\gcd(k, p) = 1$.

### Notes and history

The criterion of Eisenstein was published by Eisenstein in 1850. Schönemann published an equivalent criterion a few years earlier, and the result is also called the criterion of Schönemann and Eisenstein. The construction of $K(\alpha)$ as $K[X]/(m)$ goes back to Kronecker.

### Reference

<?reference?>
