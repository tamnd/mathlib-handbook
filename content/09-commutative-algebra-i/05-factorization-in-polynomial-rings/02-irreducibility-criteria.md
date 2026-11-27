---
title: Irreducibility criteria
kind: theory
modules: []
explains:
  E3: [Polynomial.IsEisensteinAt, Polynomial.IsEisensteinAt.irreducible, Polynomial.Monic.irreducible_of_irreducible_map, num_dvd_of_is_root]
  E2: [Polynomial.isEisensteinAt_iff, Polynomial.irreducible_of_eisenstein_criterion, Polynomial.generalizedEisenstein, Polynomial.Monic.isEisensteinAt_of_mem_of_notMem, Polynomial.IsWeaklyEisensteinAt, cyclotomic_comp_X_add_one_isEisensteinAt, Polynomial.cyclotomic_prime, Polynomial.cyclotomic.irreducible_rat, den_dvd_of_is_root, isInteger_of_is_root_of_monic, Polynomial.irreducible_of_degree_le_three_of_not_isRoot, Polynomial.Monic.irreducible_iff_roots_eq_zero_of_degree_le_three, Polynomial.taylor, Polynomial.taylor_apply, Polynomial.taylor_mul]
  E1: [Polynomial.Monic.irreducible_of_irreducible_map_of_isPrime_nilradical, Polynomial.IsPrimitive.irreducible_of_irreducible_map_of_injective, Polynomial.map, Polynomial.IsPrimitive]
families: []
requires: [V06.C05, V06.C06, V09.C01]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Irreducibility criteria

### Overview

Section 1 turns irreducibility over $\mathbb{Q}$ into irreducibility over $\mathbb{Z}$. This section gives three tests for it. The rational root test finds the factors of degree $1$. Reduction modulo a prime moves the question to the finite field $\mathbb{F}_p$. The criterion of Eisenstein treats polynomials of a special shape, which a change of variable $X \mapsto X + a$ often gives. The tests are sufficient and not necessary: $X^4 + 1$ is irreducible over $\mathbb{Q}$ and reducible modulo every prime.

### Definitions

Throughout, $R$ is a domain with field of fractions $K$. For a ring homomorphism $\varphi \colon R \to S$ and $f = \sum a_i X^i$ write $\varphi(f) = \sum \varphi(a_i) X^i \in S[X]$, a ring homomorphism in $f$.

**Definition (Eisenstein polynomial).** Let $P$ be an ideal of $R$. A polynomial $f = a_n X^n + \dots + a_0 \in R[X]$ of degree $n$ is Eisenstein at $P$ if

1. $a_n \notin P$,
2. $a_i \in P$ for $0 \le i < n$,
3. $a_0 \notin P^2$.

For $R = \mathbb{Z}$ and $P = (p)$ the conditions read: $p \nmid a_n$, $p \mid a_i$ for $i < n$, and $p^2 \nmid a_0$.

::: mathlib
`Polynomial.IsEisensteinAt` · `Mathlib.RingTheory.Polynomial.Eisenstein.Basic`

`f.IsEisensteinAt P` is a structure with the three fields `leading : f.leadingCoeff ∉ P`, `mem : ∀ {n}, n < f.natDegree → f.coeff n ∈ P` and `notMem : f.coeff 0 ∉ P ^ 2`. See `isEisensteinAt_iff`, `IsWeaklyEisensteinAt` (only the second field) and, for monic `f`, `Monic.isEisensteinAt_of_mem_of_notMem`.

<?decl Polynomial.IsEisensteinAt?>
:::

### Theorems and proofs

**Theorem (Rational root test).** Let $R$ be a unique factorization domain and $f = a_n X^n + \dots + a_0 \in R[X]$ with $a_n \ne 0$. Let $r/s \in K$ be a root of $f$ with $r, s \in R$ coprime. Then $r \mid a_0$ and $s \mid a_n$. In particular a root in $K$ of a monic polynomial over $R$ lies in $R$.

*Proof.* Multiply $f(r/s) = 0$ by $s^n$:
$$a_n r^n + a_{n-1} r^{n-1} s + \dots + a_1 r s^{n-1} + a_0 s^n = 0.$$
Every term except $a_0 s^n$ is divisible by $r$, so $r \mid a_0 s^n$. The elements $r$ and $s^n$ have no common prime factor, so $r \mid a_0$. In the same way every term except $a_n r^n$ is divisible by $s$, so $s \mid a_n r^n$ and $s \mid a_n$. If $a_n = 1$, then $s$ is a unit and $r/s \in R$. $\square$

**Theorem (Reduction modulo a prime).** Let $R$ be a unique factorization domain, $\varphi \colon R \to F$ a ring homomorphism to a field, and $f \in R[X]$ primitive with $\varphi(a_n) \ne 0$ for the leading coefficient $a_n$. If $\varphi(f)$ is irreducible in $F[X]$, then $f$ is irreducible in $R[X]$ and in $K[X]$. For $R = \mathbb{Z}$: if $p \nmid a_n$ and $f \bmod p$ is irreducible in $\mathbb{F}_p[X]$, then $f$ is irreducible in $\mathbb{Q}[X]$.

*Proof.* As $\varphi(a_n) \ne 0$, $\deg \varphi(f) = n$, and $n \ge 1$ since $\varphi(f)$ is not a unit. Suppose $f = gh$ in $R[X]$ with $g, h$ not units. Neither factor is constant, because $f$ is primitive. The leading coefficients $b$ of $g$ and $c$ of $h$ satisfy $\varphi(b) \varphi(c) = \varphi(a_n) \ne 0$, so $\deg \varphi(g) = \deg g \ge 1$ and $\deg \varphi(h) = \deg h \ge 1$. Then $\varphi(f) = \varphi(g) \varphi(h)$ is a product of two non-units of $F[X]$, a contradiction. So $f$ is irreducible in $R[X]$, and in $K[X]$ by Section 1.

For $R = \mathbb{Z}$ and a polynomial $f$ that is not primitive, write $f = c \cdot f_0$ with $c = c(f)$. Since $c \mid a_n$ and $p \nmid a_n$, also $p \nmid c$. So $f_0 \bmod p$ is a unit multiple of $f \bmod p$ and is irreducible, and the leading coefficient of $f_0$ is not divisible by $p$. The first part shows that $f_0$ is irreducible in $\mathbb{Q}[X]$, and $f = c f_0$ with $c$ a unit of $\mathbb{Q}$. $\square$

::: mathlib
`Polynomial.Monic.irreducible_of_irreducible_map` · `Mathlib.Algebra.Polynomial.Eval.Irreducible`

The form in the library is `(φ : R →+* S) (f : R[X]) : f.Monic → Irreducible (f.map φ) → Irreducible f`, for domains `R` and `S`. The index of this edition has no declaration for the form with a primitive polynomial whose leading coefficient survives in `S`. `IsPrimitive.irreducible_of_irreducible_map_of_injective` treats an injective `φ`, for example `ℤ → ℚ`.

<?decl Polynomial.Monic.irreducible_of_irreducible_map?>
:::

**Theorem (Eisenstein's criterion).** Let $R$ be a domain, $P$ a prime ideal of $R$, and $f \in R[X]$ of degree $n \ge 1$, Eisenstein at $P$. If $f = gh$ in $R[X]$, then $\deg g = 0$ or $\deg h = 0$. So $f$ is irreducible in $R[X]$ if $f$ is primitive. If $R$ is a unique factorization domain, then $f$ is irreducible in $K[X]$.

*Proof.* Suppose $f = gh$ with $g = b_r X^r + \dots + b_0$ and $h = c_s X^s + \dots + c_0$ of degrees $r, s \ge 1$. Reduce modulo $P$ and write $\bar u$ for the image in $(R/P)[X]$. Conditions 1 and 2 give $\bar f = \bar a_n X^n$ with $\bar a_n \ne 0$. The ring $R/P$ is a domain. Let $L$ be its field of fractions. In $L[X]$ the element $X$ is prime, and $\bar g \bar h = \bar a_n X^n$ with $\bar a_n$ a unit of $L$. By unique factorization in $L[X]$, $\bar g = u X^k$ and $\bar h = v X^{n-k}$ with units $u, v \in L$. Also $\bar b_r \bar c_s = \bar a_n \ne 0$, so $\deg \bar g = r$ and $\deg \bar h = s$. Hence $k = r \ge 1$ and $n - k = s \ge 1$. Then the constant terms $\bar b_0$ and $\bar c_0$ vanish, that is, $b_0, c_0 \in P$. So $a_0 = b_0 c_0 \in P^2$, against condition 3.

If $f$ is primitive and $f = gh$, then one factor is a constant that divides all coefficients of $f$, so it is a unit. Also $f$ is not a unit, since $n \ge 1$. So $f$ is irreducible in $R[X]$.

Let $R$ be a unique factorization domain, and write $f = c f_0$ with $c = c(f)$ and $f_0$ primitive. Then $c \mid a_n$ and $a_n \notin P$, so $c \notin P$. Each coefficient $a_i = c a'_i$ with $i < n$ lies in $P$, and $P$ is prime, so $a'_i \in P$. Also $a'_n \notin P$, and $a'_0 \notin P^2$, since otherwise $a_0 = c a'_0 \in P^2$. So $f_0$ is primitive and Eisenstein at $P$, hence irreducible in $R[X]$, and in $K[X]$ by Section 1. Then $f = c f_0$ is irreducible in $K[X]$, since $c$ is a unit of $K$. $\square$

::: mathlib
`Polynomial.IsEisensteinAt.irreducible` · `Mathlib.RingTheory.Polynomial.Eisenstein.Basic`

`hf.irreducible hP hu hn : Irreducible f` for `hf : f.IsEisensteinAt P`, `hP : P.IsPrime`, `hu : f.IsPrimitive` and `hn : 0 < f.natDegree`. `irreducible_of_eisenstein_criterion` spells out the conditions, and `generalizedEisenstein` allows a power of an irreducible $q$ in place of $X^n$.

<?decl Polynomial.IsEisensteinAt.irreducible?>
:::

**Lemma (Change of variable).** Let $a \in R$. The map $\tau_a \colon R[X] \to R[X]$, $f(X) \mapsto f(X + a)$, is a ring automorphism that preserves the degree. So $f$ is irreducible if and only if $f(X + a)$ is irreducible.

*Proof.* $\tau_a$ is the ring homomorphism with $X \mapsto X + a$, and $\tau_{-a}$ is its inverse, since both composites fix $X$. The leading term of $(X + a)^n$ is $X^n$, so $\tau_a$ preserves the degree. A ring automorphism preserves units and factorizations. $\square$

::: mathlib
`Polynomial.taylor` · `Mathlib.Algebra.Polynomial.Taylor`

`taylor r : R[X] →ₗ[R] R[X]` sends `f` to `f.comp (X + C r)` (`taylor_apply`). It is bundled as a linear map, and `taylor_mul` gives multiplicativity.

<?decl Polynomial.taylor?>
:::

### Examples

**Example ($X^n - p$).** Let $p$ be a prime number and $n \ge 1$. The polynomial $X^n - p$ is monic and Eisenstein at $(p)$, since $p \mid -p$ and $p^2 \nmid p$. So $X^n - p$ is irreducible over $\mathbb{Q}$, and $\mathbb{Q}[X]$ has irreducible polynomials of every degree.

**Example (The cyclotomic polynomial $\Phi_p$).** Let $p$ be prime and $\Phi_p = X^{p-1} + \dots + X + 1 = (X^p - 1)/(X - 1)$. Then
$$\Phi_p(X + 1) = \frac{(X + 1)^p - 1}{X} = \sum_{k = 1}^{p} \binom{p}{k} X^{k-1} = X^{p-1} + p X^{p-2} + \dots + \binom{p}{2} X + p.$$
The binomial coefficients $\binom{p}{k}$ for $0 < k < p$ are divisible by $p$, since $p$ divides $p!$ but not $k!(p-k)!$. The constant term is $p$. So $\Phi_p(X + 1)$ is monic and Eisenstein at $(p)$, and $\Phi_p$ is irreducible over $\mathbb{Q}$ by the lemma on the change of variable.

**Example ($X^4 + 1$ over $\mathbb{Q}$).** Put $f = X^4 + 1$. Then
$$f(X + 1) = X^4 + 4X^3 + 6X^2 + 4X + 2,$$
which is monic and Eisenstein at $(2)$: the coefficients $4, 6, 4, 2$ are even and $4 \nmid 2$. So $f$ is irreducible over $\mathbb{Q}$.

**Counterexample ($X^4 + 1$ is reducible modulo every prime).** Let $p$ be prime and $\bar f = X^4 + 1 \in \mathbb{F}_p[X]$. For $p = 2$, $\bar f = (X + 1)^4$. Let $p$ be odd. The squaring map on $\mathbb{F}_p^\times$ is a homomorphism with kernel $\{\pm 1\}$, so the squares form a subgroup $Q$ of index $2$. The quotient $\mathbb{F}_p^\times / Q$ has order $2$, so the product of two non-squares is a square. Hence one of $-1$, $2$, $-2$ is a square in $\mathbb{F}_p$: if $-1$ and $2$ are non-squares, then $-2$ is a square. In the three cases:

- $-1 = a^2$: $\bar f = X^4 - a^2 = (X^2 - a)(X^2 + a)$.
- $2 = b^2$: $\bar f = (X^2 + 1)^2 - 2X^2 = (X^2 - bX + 1)(X^2 + bX + 1)$.
- $-2 = c^2$: $\bar f = (X^2 - 1)^2 + 2X^2 = (X^2 - 1)^2 - c^2 X^2 = (X^2 - cX - 1)(X^2 + cX - 1)$.

So $\bar f$ is reducible for every $p$. For $p = 7$: $2 = 3^2$, and $(X^2 - 3X + 1)(X^2 + 3X + 1) = X^4 - 7X^2 + 1 = X^4 + 1$ in $\mathbb{F}_7[X]$.

**Counterexample (The hypotheses of the tests).** In the reduction test the leading coefficient matters: $2X^2 + X = X(2X + 1)$ is reducible over $\mathbb{Q}$, but its reduction modulo $2$ is the irreducible $X$, as the degree drops. In the criterion of Eisenstein condition 3 matters: $X^2 - 4 = (X - 2)(X + 2)$ satisfies conditions 1 and 2 at $(2)$.

### The library around it

Over a field, a polynomial of degree $2$ or $3$ is irreducible if and only if it has no root: `irreducible_of_degree_le_three_of_not_isRoot` and `Monic.irreducible_iff_roots_eq_zero_of_degree_le_three`. The computation for $\Phi_p$ is `cyclotomic_comp_X_add_one_isEisensteinAt`, with `cyclotomic_prime` for the sum. `cyclotomic.irreducible_rat` proves that every cyclotomic polynomial is irreducible over $\mathbb{Q}$, with the roots of unity of Volume 11.

::: mathlib
`num_dvd_of_is_root` · `Mathlib.RingTheory.Polynomial.RationalRoot`

For a unique factorization domain `A` with fraction field `K` and `aeval r p = 0`, it gives `IsFractionRing.num A r ∣ p.coeff 0`. `den_dvd_of_is_root` divides the leading coefficient, and `isInteger_of_is_root_of_monic` treats a monic `p`.

<?decl num_dvd_of_is_root?>
:::

### Exercises

1. (A) Find all rational roots of $2X^3 - 3X^2 - 3X + 2$ and factor it in $\mathbb{Z}[X]$.
2. (A) Show that $X^3 - 3X - 1$ is irreducible over $\mathbb{Q}$ in two ways: by the rational root test, and by reduction modulo $2$.
3. (A) Show that $X^5 + 21X^3 - 6X + 15$ is irreducible over $\mathbb{Q}$.
4. (B) Show that $X^5 + X^2 + 1$ is irreducible in $\mathbb{F}_2[X]$, and deduce that $X^5 - 4X^4 + 2X^3 + 7X^2 + 1$ is irreducible over $\mathbb{Q}$. Hint: a reducible quintic has a factor of degree $1$ or $2$.
5. (B) Let $p$ be prime. Show that $\Phi_{p^2} = \Phi_p(X^p)$ is irreducible over $\mathbb{Q}$. Hint: compute $\Phi_{p^2}(X + 1)$ modulo $p$, using $(X + 1)^{p^2} \equiv X^{p^2} + 1$.
6. (C) Show that $y^3 + x^2 y + x$ is irreducible in $\mathbb{Q}[x, y]$. Hint: Eisenstein in $(\mathbb{Q}[x])[y]$ at the prime $x$.

### Notes and history

Eisenstein published the criterion in 1850. Schönemann had found an equivalent form a few years before, and some texts use both names.

### Reference

<?reference?>
