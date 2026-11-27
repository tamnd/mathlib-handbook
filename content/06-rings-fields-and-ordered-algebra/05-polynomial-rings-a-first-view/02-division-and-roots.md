---
title: Division with remainder and roots
kind: theory
modules: []
explains:
  E1: [Polynomial.modByMonic, Polynomial.divByMonic, Polynomial.modByMonic_add_div, Polynomial.degree_modByMonic_lt, Polynomial.instEuclideanDomain, Polynomial.modByMonic_X_sub_C_eq_C_eval, Polynomial.dvd_iff_isRoot, Polynomial.mul_divByMonic_eq_iff_isRoot, Polynomial.IsRoot, Polynomial.roots, Polynomial.card_roots', Polynomial.zero_of_eval_zero, Polynomial.funext, isCyclic_subgroup_units, isCyclic_of_card_pow_eq_one_le]
families: []
requires: [V06.C03, V06.C04]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Division with remainder and roots

### Overview

The integers have division with remainder: for $a$ and $b > 0$ there are $q$ and $r$ with $a = qb + r$ and $0 \le r < b$. Polynomials have the same tool, with the degree in place of the size. Over any commutative ring one can divide by a monic polynomial, and over a field one can divide by any nonzero polynomial. This section proves the division theorem and draws three consequences. The remainder theorem says that the remainder of $f$ on division by $X - a$ is the value $f(a)$. The factor theorem says that $a$ is a root of $f$ exactly when $X - a$ divides $f$. The root bound says that a nonzero polynomial of degree $n$ over an integral domain has at most $n$ roots.

The root bound has an application to group theory, which ends the section: every finite subgroup of the group of units of an integral domain is cyclic. In particular the group $\mathbb{F}_p^\times$ is cyclic, so each prime $p$ has a primitive root. Chapter 6 uses the division theorem again, to show that $K[X]$ is a Euclidean domain.

### Definitions

In this section $R$ is a commutative ring with $1 \ne 0$, and $K$ is a field.

**Definition (Root).** Let $f \in R[X]$. An element $a \in R$ is a root of $f$ if $f(a) = 0$.

**Definition (Quotient and remainder).** Let $f, g \in R[X]$ with $g$ monic. A pair $(q, r)$ of polynomials with
$$f = q g + r, \qquad \deg r < \deg g$$
is a division of $f$ by $g$. The polynomial $q$ is the quotient and $r$ is the remainder. The next theorem shows that the pair exists and is unique.

::: mathlib
`Polynomial.modByMonic` · `Mathlib.Algebra.Polynomial.Div`

The remainder `p %ₘ q`. It is defined for every `q`, with the junk value `p %ₘ q = p` when `q` is not monic. The lemmas about it then assume `q.Monic`. The definition is stated for a `Ring`, not only a commutative ring.

<?decl Polynomial.modByMonic?>
:::

::: mathlib
`Polynomial.divByMonic` · `Mathlib.Algebra.Polynomial.Div`

The quotient `p /ₘ q`, with the junk value `0` when `q` is not monic.

<?decl Polynomial.divByMonic?>
:::

::: mathlib
`Polynomial.IsRoot` · `Mathlib.Algebra.Polynomial.Eval.Defs`

`p.IsRoot a` is the proposition `p.eval a = 0`. It is a definition, not a notation, so `simp` needs `Polynomial.IsRoot.def` to unfold it.

<?decl Polynomial.IsRoot?>
:::

### Theorems and proofs

**Theorem (Division by a monic polynomial).** Let $f, g \in R[X]$ with $g$ monic of degree $m$. There are unique $q, r \in R[X]$ with $f = qg + r$ and $\deg r < m$.

*Proof.* The plan: existence by strong induction on the degree of $f$, removing the leading term of $f$ with a multiple of $g$; uniqueness by the degree formula for a monic factor.

Existence. If $\deg f < m$, take $q = 0$ and $r = f$. This covers $f = 0$. Now let $\deg f = n \ge m$, and assume the claim for all polynomials of degree less than $n$. Let $a$ be the leading coefficient of $f$ and put
$$f_1 = f - a X^{n-m} g.$$
The polynomial $a X^{n - m} g$ has degree at most $n$, and its coefficient of $X^n$ is $a \cdot 1 = a$, since $g$ is monic of degree $m$. So the coefficients of $X^n$ in $f$ and in $a X^{n-m} g$ cancel, and $\deg f_1 < n$. By the induction hypothesis $f_1 = q_1 g + r$ with $\deg r < m$. Then
$$f = (q_1 + a X^{n-m}) g + r,$$
and $(q_1 + aX^{n-m}, r)$ is a division of $f$ by $g$.

Uniqueness. Let $f = qg + r = q'g + r'$ with $\deg r < m$ and $\deg r' < m$. Then $(q - q') g = r' - r$. Assume $q \ne q'$. The leading coefficient of $g$ is $1$, and $1 \cdot c = c \ne 0$ for the leading coefficient $c$ of $q - q'$. So the remark after the degree formula of Section 1 gives
$$\deg((q - q') g) = \deg(q - q') + m \ge m.$$
But $\deg(r' - r) \le \max(\deg r', \deg r) < m$. This is a contradiction. So $q = q'$, and then $r = f - qg = r'$. $\square$

The proof is the long division of school. It is an algorithm: each step subtracts one multiple $a X^{n-m} g$ and lowers the degree.

**Corollary (Division over a field).** Let $f, g \in K[X]$ with $g \ne 0$. There are unique $q, r \in K[X]$ with $f = qg + r$ and $\deg r < \deg g$.

*Proof.* Let $c$ be the leading coefficient of $g$. It is nonzero, so it has an inverse, and $c^{-1} g$ is monic of the same degree. Divide $f$ by $c^{-1} g$: $f = q_1 (c^{-1} g) + r$. Then $q = c^{-1} q_1$ works. For uniqueness, a division $f = qg + r$ gives the division $f = (cq)(c^{-1}g) + r$ by the monic polynomial, so $cq$ and $r$ are unique, and so is $q$. $\square$

::: mathlib
`Polynomial.modByMonic_add_div` · `Mathlib.Algebra.Polynomial.Div`

The identity `p %ₘ q + q * (p /ₘ q) = p`. It holds for every `q`, because of the junk values: if `q` is not monic, it reads `p + q * 0 = p`. So the hypothesis `q.Monic` appears only in the degree bound.

<?decl Polynomial.modByMonic_add_div?>
:::

::: mathlib
`Polynomial.degree_modByMonic_lt` · `Mathlib.Algebra.Polynomial.Div`

The degree bound of the theorem, `q.Monic → (p %ₘ q).degree < q.degree`, over a nontrivial ring. The uniqueness is `Polynomial.div_modByMonic_unique`.

<?decl Polynomial.degree_modByMonic_lt?>
:::

::: mathlib
`Polynomial.instEuclideanDomain` · `Mathlib.Algebra.Polynomial.FieldDivision`

Over a field, Mathlib packs the corollary into an instance of `EuclideanDomain K[X]`, with `p / q` and `p % q` from `Polynomial.div` and `Polynomial.mod`. These divide by the monic polynomial `q * C (q.leadingCoeff)⁻¹` and correct the quotient, exactly as in the proof above. The class `EuclideanDomain` is the subject of Chapter 6.

<?decl Polynomial.instEuclideanDomain?>
:::

**Theorem (Remainder theorem).** Let $f \in R[X]$ and $a \in R$. The remainder of $f$ on division by $X - a$ is the constant $f(a)$. So $f = (X - a) q + f(a)$ for a unique $q \in R[X]$.

*Proof.* The polynomial $X - a$ is monic of degree $1$. Divide: $f = q(X - a) + r$ with $\deg r < 1$, so $r$ is a constant $c$. Evaluation at $a$ is a ring homomorphism by the universal property of Section 1. Apply it: $f(a) = q(a)(a - a) + c = c$. $\square$

**Corollary (Factor theorem).** An element $a \in R$ is a root of $f$ if and only if $X - a$ divides $f$. The kernel of the evaluation map $R[X] \to R$, $f \mapsto f(a)$, is the principal ideal $(X - a)$.

*Proof.* If $f(a) = 0$, the remainder theorem gives $f = (X - a)q$. Conversely, if $f = (X - a) q$, then $f(a) = 0 \cdot q(a) = 0$. The second claim restates the first: $f$ is in the kernel exactly when $X - a$ divides $f$. $\square$

::: mathlib
`Polynomial.modByMonic_X_sub_C_eq_C_eval` · `Mathlib.Algebra.Polynomial.Div`

The remainder theorem: `p %ₘ (X - C a) = C (p.eval a)`. Note that Mathlib writes $X - a$ as `X - C a`.

<?decl Polynomial.modByMonic_X_sub_C_eq_C_eval?>
:::

::: mathlib
`Polynomial.dvd_iff_isRoot` · `Mathlib.Algebra.Polynomial.Div`

The factor theorem, `X - C a ∣ p ↔ p.IsRoot a`. The form with the quotient written out is `Polynomial.mul_divByMonic_eq_iff_isRoot`.

<?decl Polynomial.dvd_iff_isRoot?>
:::

::: mathlib
`Polynomial.mul_divByMonic_eq_iff_isRoot` · `Mathlib.Algebra.Polynomial.Div`

`(X - C a) * (p /ₘ (X - C a)) = p ↔ p.IsRoot a`. This is the form to use when the proof needs the cofactor $q$ itself, as in the root bound below.

<?decl Polynomial.mul_divByMonic_eq_iff_isRoot?>
:::

**Theorem (Root bound).** Let $R$ be an integral domain and let $f \in R[X]$ be nonzero of degree $n$. Then $f$ has at most $n$ distinct roots in $R$.

*Proof.* Induction on $n$. If $n = 0$, then $f$ is a nonzero constant and has no root. Let $n \ge 1$ and assume the claim for degree $n - 1$. If $f$ has no root, there is nothing to prove. Otherwise let $a$ be a root. By the factor theorem $f = (X - a) q$. The degree formula over a domain gives $\deg q = n - 1$, and $q \ne 0$. Let $b$ be a root of $f$ with $b \ne a$. Then
$$0 = f(b) = (b - a)\, q(b).$$
Here $b - a \ne 0$, and $R$ has no zero divisors, so $q(b) = 0$. So each root of $f$ is $a$ or a root of $q$. By the induction hypothesis $q$ has at most $n - 1$ roots, and $f$ has at most $1 + (n - 1) = n$ roots. $\square$

The proof uses the domain hypothesis twice: in the degree formula, and in the step from $(b - a)q(b) = 0$ to $q(b) = 0$. The examples below show that the theorem fails without it.

**Corollary (Polynomial functions over an infinite domain).** Let $R$ be an infinite integral domain and let $f, g \in R[X]$. If $f(x) = g(x)$ for all $x \in R$, then $f = g$.

*Proof.* Each $x \in R$ is a root of $f - g$. If $f - g \ne 0$, it has at most $\deg(f - g)$ roots, but it has infinitely many. So $f - g = 0$. $\square$

::: mathlib
`Polynomial.roots` · `Mathlib.Algebra.Polynomial.Roots`

The roots of `p` over a domain, as a `Multiset R`: each root appears as often as its multiplicity. The junk value is `roots 0 = 0`, the empty multiset, although every element is a root of `0`. Membership is `Polynomial.mem_roots : p ≠ 0 → (a ∈ p.roots ↔ p.IsRoot a)`.

<?decl Polynomial.roots?>
:::

::: mathlib
`Polynomial.card_roots'` · `Mathlib.Algebra.Polynomial.Roots`

The root bound with multiplicities, `p.roots.card ≤ p.natDegree`. Because roots are counted with multiplicity, it is stronger than the theorem above. The form with `degree` is `Polynomial.card_roots`, which needs `p ≠ 0`.

<?decl Polynomial.card_roots'?>
:::

::: mathlib
`Polynomial.funext` · `Mathlib.Algebra.Polynomial.Roots`

The corollary, with `[IsDomain R] [Infinite R]`. The special case for one polynomial is `Polynomial.zero_of_eval_zero`.

<?decl Polynomial.funext?>
:::

**Theorem (Finite subgroups of the units are cyclic).** Let $R$ be an integral domain and let $G$ be a finite subgroup of $R^\times$. Then $G$ is cyclic. In particular, for a finite field $\mathbb{F}$, the group $\mathbb{F}^\times$ is cyclic.

*Proof.* The plan: count the elements of each order $d$ and compare with the cyclic group of the same order, using the root bound and Euler's function $\varphi$.

Let $|G| = n$. Each element of $G$ has an order $d$ that divides $n$, by Lagrange (Volume 5). For $d \mid n$ let $\psi(d)$ be the number of elements of order $d$ in $G$. Then
$$\sum_{d \mid n} \psi(d) = n. \tag{1}$$

Step 1: $\psi(d) \le \varphi(d)$ for each $d \mid n$. If $\psi(d) = 0$ this holds. Otherwise let $x \in G$ have order $d$. The $d$ elements $1, x, \dots, x^{d-1}$ are distinct, and each is a root of $X^d - 1$, since $(x^k)^d = (x^d)^k = 1$. The polynomial $X^d - 1$ is nonzero of degree $d$, so by the root bound it has no other roots in $R$. So each $y \in G$ with $y^d = 1$ lies in the cyclic group $\langle x \rangle$. In particular each element of order $d$ lies in $\langle x \rangle$. A cyclic group of order $d$ has exactly $\varphi(d)$ elements of order $d$, namely the $x^k$ with $\gcd(k, d) = 1$ (Volume 5). So $\psi(d) = \varphi(d)$ in this case.

Step 2: $\sum_{d \mid n} \varphi(d) = n$. Consider the $n$ fractions $k/n$ for $k = 1, \dots, n$. Write each in lowest terms as $a/d$. Then $d \mid n$, $1 \le a \le d$ and $\gcd(a, d) = 1$. Conversely, for $d \mid n$ and such an $a$, the fraction $a/d = (a n/d)/n$ is one of the $n$ fractions. So the fractions with denominator $d$ in lowest terms are counted by $\varphi(d)$, and the total is $n$.

Step 3. By (1), Step 2 and Step 1,
$$\sum_{d \mid n} \psi(d) = n = \sum_{d \mid n} \varphi(d), \qquad \psi(d) \le \varphi(d) \text{ for each } d.$$
So $\psi(d) = \varphi(d)$ for every $d \mid n$. In particular $\psi(n) = \varphi(n) \ge 1$. An element of order $n$ generates $G$. $\square$

::: mathlib
`isCyclic_subgroup_units` · `Mathlib.RingTheory.IntegralDomain`

The theorem as an instance: for `[CommRing R] [IsDomain R]` and a subgroup `S` of `Rˣ` with `[Finite S]`, instance search finds `IsCyclic S`. The same file has an unnamed instance `[Finite Rˣ] : IsCyclic Rˣ` for the full unit group, which covers a finite field.

<?decl isCyclic_subgroup_units?>
:::

::: mathlib
`isCyclic_of_card_pow_eq_one_le` · `Mathlib.GroupTheory.SpecificGroups.Cyclic`

The group theory half of the proof: a finite group in which, for each $n > 0$, at most $n$ elements satisfy $x^n = 1$ is cyclic. Mathlib proves it by the counting argument of Steps 1 to 3. The ring theory half is the root bound applied to $X^n - 1$.

<?decl isCyclic_of_card_pow_eq_one_le?>
:::

### Examples

**Example (A long division).** Divide $f = X^4 + 1$ by $g = X^2 + X + 1$ in $\mathbb{Q}[X]$. The first step removes $X^4$ with $X^2 g = X^4 + X^3 + X^2$, and leaves $-X^3 - X^2 + 1$. The second step removes $-X^3$ with $-X g = -X^3 - X^2 - X$, and leaves $X + 1$, of degree $1 < 2$. So
$$X^4 + 1 = (X^2 - X)(X^2 + X + 1) + (X + 1).$$
Check: $(X^2 - X)(X^2 + X + 1) = X^4 + X^3 + X^2 - X^3 - X^2 - X = X^4 - X$, and $X^4 - X + X + 1 = X^4 + 1$. The divisor is monic, so the same division holds in $\mathbb{Z}[X]$.

**Example (The remainder theorem).** Let $f = X^3 - 2X + 5 \in \mathbb{Z}[X]$. Then $f(2) = 8 - 4 + 5 = 9$, so the remainder on division by $X - 2$ is $9$. Indeed $(X - 2)(X^2 + 2X + 2) = X^3 - 2X - 4$, and
$$X^3 - 2X + 5 = (X - 2)(X^2 + 2X + 2) + 9.$$
The coefficients $1, 2, 2$ of the quotient are the numbers of Horner's scheme: $1$, then $1 \cdot 2 + 0 = 2$, then $2 \cdot 2 - 2 = 2$, and the last step $2 \cdot 2 + 5 = 9$ gives the value.

**Counterexample (The root bound needs a domain).** Over $\mathbb{Z}/8$ the polynomial $X^2 - 1$ has degree $2$ and the four roots $1, 3, 5, 7$: $1^2 = 1$, $3^2 = 9 = 1$, $5^2 = 25 = 1$ and $7^2 = 49 = 1$. It also has two different factorizations into monic linear factors:
$$X^2 - 1 = (X - 1)(X + 1) = (X - 3)(X + 3),$$
since $(X - 3)(X + 3) = X^2 - 9 = X^2 - 1$. The proof of the root bound fails at the root $b = 3$ of $(X - 1)(X + 1)$: here $(b - 1)(b + 1) = 2 \cdot 4 = 0$ with both factors nonzero. The unit group $(\mathbb{Z}/8)^\times = \{1, 3, 5, 7\}$ has four elements, each of order at most $2$, so it is not cyclic. The theorem on finite subgroups needs the domain hypothesis for the same reason.

**Counterexample (The root bound needs commutativity).** In the quaternions $\mathbb{H}$, a division ring that is not commutative, the polynomial $X^2 + 1$ has the roots $i$, $j$, $k$, and in fact every $bi + cj + dk$ with $b^2 + c^2 + d^2 = 1$. So a polynomial of degree $2$ has infinitely many roots. The proof fails at the remainder theorem, because evaluation at a point that does not commute with the coefficients is not a ring homomorphism (Section 1).

**Counterexample (Division needs a monic divisor).** In $\mathbb{Z}[X]$, try to divide $X$ by $2X$. A division $X = q \cdot 2X + r$ with $\deg r < 1$ would have $r$ constant, and the coefficients of $X$ would give $1 = 2 q_0 + 0$ in $\mathbb{Z}$, with $q_0$ the constant term of $q$. This is impossible. Over $\mathbb{Q}$ the division exists, $X = \tfrac{1}{2} \cdot 2X$.

**Counterexample (The corollary needs an infinite ring).** Over $\mathbb{F}_p$ the polynomial $X^p - X$ is nonzero, and by Fermat's little theorem of Chapter 4 every $a \in \mathbb{F}_p$ is a root of it. So it has exactly $p$ roots, the most that the root bound allows, and it defines the zero function. By the factor theorem applied $p$ times,
$$X^p - X = \prod_{a \in \mathbb{F}_p} (X - a).$$

**Example (A primitive root modulo $7$).** The group $\mathbb{F}_7^\times$ has order $6$, so it is cyclic by the theorem. The powers of $3$ are $3, 2, 6, 4, 5, 1$, so $3$ is a generator. The powers of $2$ are $2, 4, 1$, so $2$ has order $3$ and is not a generator. The counts of the proof are $\psi(1) = 1$, $\psi(2) = 1$ (the element $6 = -1$), $\psi(3) = 2$ (the elements $2, 4$) and $\psi(6) = 2$ (the elements $3, 5$), equal to $\varphi(1), \varphi(2), \varphi(3), \varphi(6)$.

### The library around it

The division lemmas for a monic divisor are in `Mathlib.Algebra.Polynomial.Div`, and they work over any ring, even a noncommutative one. Over a field the operations `/` and `%` of the class `EuclideanDomain` apply directly, with `EuclideanDomain.mod_add_div` as the division identity and `EuclideanDomain.mod_lt` as the degree bound. The roots of a polynomial over a domain form the multiset `p.roots`, with the multiplicity `Polynomial.rootMultiplicity a p`, and the lemma `Polynomial.card_roots_sub_C` counts the solutions of $p(x) = a$. The finite set of distinct roots is `p.roots.toFinset`.

Common errors of a learner:

- `p %ₘ q` with a non-monic `q` is `p`, not an error. A proof that forgets `q.Monic` gets stuck at the degree bound, not at the definition.
- `Polynomial.roots 0 = 0`. A statement about all roots of `p` usually needs `p ≠ 0`.
- `p.roots` counts multiplicities. The number of distinct roots is `p.roots.toFinset.card`.
- The root bound needs `IsDomain R`. Over `ZMod 8` the lemma does not apply, and the counterexample above shows that it must not.

### Exercises

1. (A) Divide $X^5 - 1$ by $X^2 - 1$ in $\mathbb{Z}[X]$. Hint: the remainder is $X - 1$.
2. (A) Find the remainder of $X^{100}$ on division by $X - 1$ and by $X + 1$, without long division.
3. (A) Show that $X^2 + X + 1$ has no root in $\mathbb{F}_2$ and two roots in $\mathbb{F}_7$. Hint: try all elements.
4. (B) Find the remainder of $X^{100}$ on division by $X^2 - 1$. Hint: the remainder is $aX + b$; evaluate at $1$ and $-1$.
5. (B) Let $K$ be a field and $a_1, \dots, a_n \in K$ distinct. Show that a polynomial of degree less than $n$ is determined by its values at $a_1, \dots, a_n$, and write the Lagrange polynomial with given values.
6. (B) Find all roots of $X^2 - 1$ in $\mathbb{Z}/15$ and explain the count with the Chinese remainder theorem of Chapter 4.
7. (B) Find a generator of $\mathbb{F}_{13}^\times$ and list the elements of each order. Hint: try $2$.
8. (C) Show Wilson's theorem $(p - 1)! \equiv -1 \pmod p$ from the factorization $X^{p-1} - 1 = \prod_{a \ne 0} (X - a)$ in $\mathbb{F}_p[X]$. Hint: compare the constant terms.
9. (C) Show that $-1$ is a square in $\mathbb{F}_p$ for a prime $p \equiv 1 \pmod 4$, from the cyclicity of $\mathbb{F}_p^\times$. Hint: if $g$ generates, try $g^{(p-1)/4}$.

### Notes and history

Division of polynomials is as old as algebra with symbols. The remainder theorem and the factor theorem are in Descartes, *La Géométrie* (1637), Book III. The bound on the number of roots was used by Lagrange (1770) for polynomials over $\mathbb{F}_p$, which gave him the theorem of Wilson. The cyclicity of $\mathbb{F}_p^\times$, the existence of primitive roots, was stated by Euler and Lambert, and the first complete proof is in Gauss, *Disquisitiones Arithmeticae* (1801), articles 52 to 55, with an argument close to the counting proof above. A modern account is in Ireland-Rosen, *A Classical Introduction to Modern Number Theory*, Chapter 4.

In Mathlib, the division by a monic polynomial is in `Mathlib/Algebra/Polynomial/Div.lean` and the roots in `Mathlib/Algebra/Polynomial/Roots.lean`, both with the authors Chris Hughes, Johannes Hölzl, Kim Morrison and Jens Wagemaker. The theorem on finite subgroups of units is in `Mathlib/RingTheory/IntegralDomain.lean`, by Johan Commelin and Chris Hughes.

### Reference

<?reference?>
