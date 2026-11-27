---
title: The Gaussian integers
kind: theory
modules: []
explains:
  E1: [GaussianInt, Zsqrtd, Zsqrtd.norm, Zsqrtd.norm_mul, Zsqrtd.norm_eq_one_iff, GaussianInt.toComplex, GaussianInt.instEuclideanDomain, GaussianInt.div_def, GaussianInt.norm_mod_lt, GaussianInt.sq_add_sq_of_nat_prime_of_not_irreducible, GaussianInt.prime_iff_mod_four_eq_three_of_nat_prime, Nat.Prime.sq_add_sq, ZMod.exists_sq_eq_neg_one_iff, ZMod.wilsons_lemma]
families: []
requires: [V06.C02, V06.C03, V06.C05]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The Gaussian integers

### Overview

The Gaussian integers are the complex numbers $a + bi$ with $a, b \in \mathbb{Z}$. They form a ring $\mathbb{Z}[i]$, the first example beyond $\mathbb{Z}$ and $K[X]$ in which the theory of Section 1 gives new arithmetic. This section defines the norm $N(a + bi) = a^2 + b^2$, proves that it is multiplicative, finds the units, and proves that $\mathbb{Z}[i]$ is a Euclidean domain with the norm as the Euclidean function. Section 1 then makes $\mathbb{Z}[i]$ a PID. The PID property proves a theorem of Fermat: an odd prime $p$ is a sum of two squares if and only if $p \equiv 1 \pmod 4$. The section ends with the list of all Gaussian primes.

### Definitions

**Definition (Gaussian integers).** The Gaussian integers are the set
$$\mathbb{Z}[i] = \{ a + bi : a, b \in \mathbb{Z} \} \subseteq \mathbb{C}.$$
It contains $1$ and is closed under subtraction and under the product $(a + bi)(c + di) = (ac - bd) + (ad + bc)i$. So it is a subring of $\mathbb{C}$, and in particular an integral domain. Complex conjugation $\overline{a + bi} = a - bi$ maps $\mathbb{Z}[i]$ to itself and is a ring automorphism of it.

**Definition (Norm).** The norm of $\alpha = a + bi \in \mathbb{Z}[i]$ is
$$N(\alpha) = \alpha \overline{\alpha} = a^2 + b^2 = |\alpha|^2.$$
It is a natural number, and $N(\alpha) = 0$ only for $\alpha = 0$. The same formula defines $N$ on the field $\mathbb{Q}(i) = \{x + yi : x, y \in \mathbb{Q}\}$, with values in $\mathbb{Q}_{\ge 0}$.

::: mathlib
`GaussianInt` · `Mathlib.NumberTheory.Zsqrtd.GaussianInt`

The Gaussian integers, with the notation `ℤ[i]`. It is an abbreviation for `ℤ√(-1)`, the ring `Zsqrtd (-1)`, so an element is a structure with an integer field `re` and an integer field `im`. It is not defined as a subring of `ℂ`; the map to `ℂ` is the ring homomorphism `GaussianInt.toComplex`.

<?decl GaussianInt?>
:::

::: mathlib
`Zsqrtd` · `Mathlib.NumberTheory.Zsqrtd.Basic`

The ring $\mathbb{Z}[\sqrt d] = \{a + b\sqrt d\}$ for an integer `d`, with the product $(a + b\sqrt d)(c + e \sqrt d) = (ac + d b e) + (ae + bc)\sqrt d$. The same type gives $\mathbb{Z}[\sqrt 2]$, $\mathbb{Z}[\sqrt{-3}]$ and $\mathbb{Z}[\sqrt{-5}]$ of the examples of this chapter.

<?decl Zsqrtd?>
:::

::: mathlib
`GaussianInt.toComplex` · `Mathlib.NumberTheory.Zsqrtd.GaussianInt`

The injective ring homomorphism `ℤ[i] →+* ℂ`, which is also a coercion. Its injectivity is `GaussianInt.toComplex_injective`.

<?decl GaussianInt.toComplex?>
:::

::: mathlib
`Zsqrtd.norm` · `Mathlib.NumberTheory.Zsqrtd.Basic`

The norm `n.re * n.re - d * n.im * n.im`, with values in `ℤ`, not in `ℕ`. For `d = -1` it is $a^2 + b^2$. Proofs about size often use `(Zsqrtd.norm x).natAbs`.

<?decl Zsqrtd.norm?>
:::

### Theorems and proofs

**Theorem (The norm is multiplicative).** For $\alpha, \beta \in \mathbb{Q}(i)$, $N(\alpha \beta) = N(\alpha) N(\beta)$.

*Proof.* Conjugation is multiplicative, so $N(\alpha\beta) = \alpha\beta\,\overline{\alpha\beta} = \alpha\overline{\alpha}\,\beta\overline{\beta} = N(\alpha)N(\beta)$. $\square$

In coordinates, with $\alpha = a + bi$ and $\beta = c + di$, the theorem is the identity of Diophantus
$$(a^2 + b^2)(c^2 + d^2) = (ac - bd)^2 + (ad + bc)^2.$$
So a product of two sums of two squares is a sum of two squares.

**Corollary (Units).** An element $\alpha \in \mathbb{Z}[i]$ is a unit if and only if $N(\alpha) = 1$. The units are $1, -1, i, -i$. If $\alpha \mid \beta$ in $\mathbb{Z}[i]$, then $N(\alpha) \mid N(\beta)$ in $\mathbb{Z}$.

*Proof.* If $\alpha\beta = 1$, then $N(\alpha) N(\beta) = N(1) = 1$ in $\mathbb{N}$, so $N(\alpha) = 1$. Conversely, if $N(\alpha) = 1$, then $\alpha \overline{\alpha} = 1$ and $\overline{\alpha} \in \mathbb{Z}[i]$ is an inverse. The solutions of $a^2 + b^2 = 1$ in integers are $(\pm 1, 0)$ and $(0, \pm 1)$. The last claim follows from $\beta = \alpha\gamma$ and $N(\beta) = N(\alpha)N(\gamma)$. $\square$

The associates of $\alpha$ are $\alpha$, $-\alpha$, $i\alpha$ and $-i\alpha$. Multiplication by $i$ turns the point $(a, b)$ of the plane by a right angle to $(-b, a)$.

::: mathlib
`Zsqrtd.norm_mul` · `Mathlib.NumberTheory.Zsqrtd.Basic`

The theorem, `(n * m).norm = n.norm * m.norm`, for every `d`.

<?decl Zsqrtd.norm_mul?>
:::

::: mathlib
`Zsqrtd.norm_eq_one_iff` · `Mathlib.NumberTheory.Zsqrtd.Basic`

The first claim of the corollary in the form `x.norm.natAbs = 1 ↔ IsUnit x`, for every `d`. The `natAbs` matters for `d > 0`, where the norm can be $-1$.

<?decl Zsqrtd.norm_eq_one_iff?>
:::

**Theorem ($\mathbb{Z}[i]$ is Euclidean).** For $\alpha, \beta \in \mathbb{Z}[i]$ with $\beta \ne 0$ there are $\kappa, \rho \in \mathbb{Z}[i]$ with
$$\alpha = \kappa\beta + \rho, \qquad N(\rho) \le \tfrac12 N(\beta) < N(\beta).$$
So $\mathbb{Z}[i]$ is a Euclidean domain with the norm as the Euclidean function, and it is a PID.

*Proof.* The plan: divide in the field $\mathbb{Q}(i)$, round the quotient to the nearest Gaussian integer, and bound the error with the multiplicative norm.

The quotient $\alpha/\beta = \alpha\overline{\beta}/N(\beta)$ is an element $x + yi$ of $\mathbb{Q}(i)$. Choose integers $m$ and $n$ with $|x - m| \le \tfrac12$ and $|y - n| \le \tfrac12$, the nearest integers. Put $\kappa = m + ni$ and $\rho = \alpha - \kappa\beta$. Then $\rho \in \mathbb{Z}[i]$, since $\alpha$ and $\kappa\beta$ are. In $\mathbb{Q}(i)$,
$$\rho = \beta\left(\frac{\alpha}{\beta} - \kappa\right) = \beta\big((x - m) + (y - n)i\big).$$
The norm is multiplicative on $\mathbb{Q}(i)$, so
$$N(\rho) = N(\beta)\big((x - m)^2 + (y - n)^2\big) \le N(\beta)\left(\tfrac14 + \tfrac14\right) = \tfrac12 N(\beta).$$
Since $N(\beta) \ge 1$, $\tfrac12 N(\beta) < N(\beta)$. The theorem of Section 1 then makes $\mathbb{Z}[i]$ a PID. $\square$

Geometrically, the multiples of $\beta$ form a square lattice in the plane, and every point of the plane lies at distance at most $|\beta|/\sqrt 2$ from a lattice point, the half diagonal of a square of side $|\beta|$.

::: mathlib
`GaussianInt.instEuclideanDomain` · `Mathlib.NumberTheory.Zsqrtd.GaussianInt`

The instance `EuclideanDomain ℤ[i]`, with the relation `r` given by `Int.natAbs ∘ norm`. Instance search then finds `IsPrincipalIdealRing ℤ[i]` by `EuclideanDomain.instIsPrincipalIdealRing`.

<?decl GaussianInt.instEuclideanDomain?>
:::

::: mathlib
`GaussianInt.div_def` · `Mathlib.NumberTheory.Zsqrtd.GaussianInt`

The quotient is the rounding of the proof: the real and the imaginary part of `x * star y` are divided by the norm of `y` in `ℚ` and rounded with `round`. The remainder is `x - y * (x / y)`, by `GaussianInt.mod_def`.

<?decl GaussianInt.div_def?>
:::

::: mathlib
`GaussianInt.norm_mod_lt` · `Mathlib.NumberTheory.Zsqrtd.GaussianInt`

The bound `norm (x % y) < norm y` for `y ≠ 0`. The form with `natAbs` that the instance uses is `GaussianInt.natAbs_norm_mod_lt`.

<?decl GaussianInt.norm_mod_lt?>
:::

**Lemma (Irreducible elements of a PID are prime).** Let $R$ be a PID and $\pi \in R$ irreducible: not zero, not a unit, and $\pi = \alpha\beta$ implies that $\alpha$ or $\beta$ is a unit. If $\pi \mid \alpha\beta$, then $\pi \mid \alpha$ or $\pi \mid \beta$.

*Proof.* Let $\pi \mid \alpha\beta$ and $\pi \nmid \alpha$. Write $(\pi, \alpha) = (\delta)$. Then $\delta \mid \pi$, so $\pi = \delta\gamma$, and $\delta$ or $\gamma$ is a unit. If $\gamma$ is a unit, then $\pi$ and $\delta$ are associates, and $\delta \mid \alpha$ gives $\pi \mid \alpha$, which is false. So $\delta$ is a unit, and $1 \in (\pi, \alpha)$: $1 = \pi x + \alpha y$. Multiply by $\beta$: $\beta = \pi\beta x + \alpha\beta y$. Both terms are divisible by $\pi$, so $\pi \mid \beta$. $\square$

Section 3 returns to this lemma as one step of unique factorization.

**Lemma ($-1$ is a square modulo $p$).** Let $p$ be a prime with $p \equiv 1 \pmod 4$ and let $x = \left(\tfrac{p-1}{2}\right)!$. Then $x^2 \equiv -1 \pmod p$.

*Proof.* Wilson's theorem of Chapter 4 says $(p - 1)! \equiv -1 \pmod p$. Pair the factor $k$ with the factor $p - k \equiv -k$ for $k = 1, \dots, \tfrac{p - 1}{2}$:
$$-1 \equiv (p-1)! = \prod_{k=1}^{(p-1)/2} k (p - k) \equiv \prod_{k=1}^{(p-1)/2} (-k^2) = (-1)^{(p-1)/2} x^2 \pmod p.$$
Since $p \equiv 1 \pmod 4$, the exponent $\tfrac{p-1}{2}$ is even, and $-1 \equiv x^2$. $\square$

**Theorem (Fermat, sums of two squares).** Let $p$ be an odd prime. Then $p = a^2 + b^2$ for some integers $a, b$ if and only if $p \equiv 1 \pmod 4$.

*Proof.* The plan: a square root of $-1$ modulo $p$ shows that $p$ is not prime in $\mathbb{Z}[i]$; the PID property then splits $p$, and the norm of a factor is $p$.

If $p = a^2 + b^2$: a square is $0$ or $1$ modulo $4$, so $a^2 + b^2$ is $0$, $1$ or $2$ modulo $4$. An odd $p$ is $1$ or $3$ modulo $4$, so $p \equiv 1 \pmod 4$.

Conversely, let $p \equiv 1 \pmod 4$. By the lemma there is $x \in \mathbb{Z}$ with $p \mid x^2 + 1$. In $\mathbb{Z}[i]$,
$$x^2 + 1 = (x + i)(x - i).$$
So $p \mid (x + i)(x - i)$ in $\mathbb{Z}[i]$. But $p \nmid x + i$: the quotient $(x + i)/p = x/p + (1/p)i$ has the imaginary part $1/p \notin \mathbb{Z}$. In the same way $p \nmid x - i$. So $p$ is not a prime element of $\mathbb{Z}[i]$. The ring $\mathbb{Z}[i]$ is a PID, so by the first lemma $p$ is not irreducible. It is not zero, and it is not a unit, since $N(p) = p^2 \ne 1$. So $p = \alpha\beta$ with $\alpha$ and $\beta$ not units. Then
$$N(\alpha)N(\beta) = N(p) = p^2, \qquad N(\alpha) \ne 1, \quad N(\beta) \ne 1.$$
So $N(\alpha) = p$. Write $\alpha = a + bi$: then $a^2 + b^2 = p$. $\square$

The proof does not find $a$ and $b$ by search. The Euclidean algorithm finds them: $\alpha$ is a greatest common divisor of $p$ and $x + i$, as the example of $13$ below shows.

::: mathlib
`ZMod.wilsons_lemma` · `Mathlib.NumberTheory.Wilson`

Wilson's theorem, `((p - 1)! : ZMod p) = -1`, for `[Fact p.Prime]`.

<?decl ZMod.wilsons_lemma?>
:::

::: mathlib
`ZMod.exists_sq_eq_neg_one_iff` · `Mathlib.NumberTheory.LegendreSymbol.Basic`

The criterion `IsSquare (-1 : ZMod p) ↔ p % 4 ≠ 3`. It includes $p = 2$, where $-1 = 1$ is a square.

<?decl ZMod.exists_sq_eq_neg_one_iff?>
:::

::: mathlib
`GaussianInt.sq_add_sq_of_nat_prime_of_not_irreducible` · `Mathlib.NumberTheory.Zsqrtd.GaussianInt`

The second half of the proof: if the prime `p` is not irreducible in `ℤ[i]`, then `∃ a b, a ^ 2 + b ^ 2 = p`, by the norm argument above.

<?decl GaussianInt.sq_add_sq_of_nat_prime_of_not_irreducible?>
:::

::: mathlib
`GaussianInt.prime_iff_mod_four_eq_three_of_nat_prime` · `Mathlib.NumberTheory.Zsqrtd.QuadraticReciprocity`

The rational prime `p` is prime in `ℤ[i]` if and only if `p % 4 = 3`. One direction is the first half of the proof, from a square root of $-1$.

<?decl GaussianInt.prime_iff_mod_four_eq_three_of_nat_prime?>
:::

::: mathlib
`Nat.Prime.sq_add_sq` · `Mathlib.NumberTheory.SumTwoSquares`

Fermat's theorem: `p % 4 ≠ 3 → ∃ a b : ℕ, a ^ 2 + b ^ 2 = p`. The proof in Mathlib is three lines, and it follows the proof above: `irreducible_iff_prime` in the UFD `ℤ[i]`, then the two lemmas before this box.

<?decl Nat.Prime.sq_add_sq?>
:::

**Theorem (Gaussian primes).** Up to multiplication by a unit, the prime elements of $\mathbb{Z}[i]$ are:

1. $1 + i$, of norm $2$;
2. the rational primes $p$ with $p \equiv 3 \pmod 4$, of norm $p^2$;
3. the elements $a + bi$ and $a - bi$ with $a^2 + b^2 = p$ for a prime $p \equiv 1 \pmod 4$, of norm $p$. These two are not associates.

*Proof.* First, every element in the list is prime. In a PID prime and irreducible agree, by the first lemma and by Section 3. An element $\pi$ with $N(\pi)$ a prime number is irreducible: if $\pi = \alpha\beta$, then $N(\alpha)N(\beta)$ is prime, so $N(\alpha) = 1$ or $N(\beta) = 1$. This covers types 1 and 3. For a prime $p \equiv 3 \pmod 4$: if $p = \alpha\beta$ with neither a unit, then $N(\alpha) = p$ as in Fermat's proof, so $p$ is a sum of two squares, against Fermat's theorem. So $p$ is irreducible.

Next, every prime $\pi$ is in the list. Since $\pi \mid \pi\overline{\pi} = N(\pi)$ and $N(\pi) > 1$ is a product of rational primes, the prime $\pi$ divides one rational prime $p$. Then $N(\pi) \mid N(p) = p^2$, so $N(\pi) = p$ or $N(\pi) = p^2$. If $N(\pi) = p$, then $\pi = a + bi$ with $a^2 + b^2 = p$, and $p = 2$ or $p \equiv 1 \pmod 4$. For $p = 2$ the solutions $(\pm 1, \pm 1)$ are the associates of $1 + i$. If $N(\pi) = p^2$, then $p = \pi\gamma$ with $N(\gamma) = 1$, so $\pi$ is an associate of $p$ and $p$ is prime in $\mathbb{Z}[i]$. This excludes $p = 2 = -i(1 + i)^2$ and $p \equiv 1 \pmod 4$, where $p = (a + bi)(a - bi)$. So $p \equiv 3 \pmod 4$.

Last, for $p$ odd, $a + bi$ and $a - bi$ are not associates. The associates of $a + bi$ are $a + bi$, $-a - bi$, $-b + ai$ and $b - ai$. Equality of $a - bi$ with one of them gives $b = 0$, $a = 0$, $a = -b$ or $a = b$. Then $p = a^2 + b^2$ is a square or twice a square, which is false for an odd prime. $\square$

### Examples

**Example (A division).** Divide $\alpha = 7 + 5i$ by $\beta = 2 + 3i$, with $N(\beta) = 13$. The exact quotient is
$$\frac{(7 + 5i)(2 - 3i)}{13} = \frac{29 - 11i}{13} \approx 2.23 - 0.85i.$$
Round to $\kappa = 2 - i$. Then $\kappa\beta = (2 - i)(2 + 3i) = 7 + 4i$, and $\rho = \alpha - \kappa\beta = i$. So $7 + 5i = (2 - i)(2 + 3i) + i$ with $N(i) = 1 \le 13/2$.

**Example (Small rational primes).** The prime $2$ ramifies: $2 = (1 + i)(1 - i) = -i(1 + i)^2$, since $(1 + i)^2 = 2i$, and $1 - i = -i(1 + i)$ is an associate of $1 + i$. The prime $5$ splits: $5 = (2 + i)(2 - i)$, with two primes of norm $5$ that are not associates. The prime $3$ stays prime: $3 \equiv 3 \pmod 4$ and $3$ is not a sum of two squares. So the Gaussian factorization of $30$ is
$$30 = 2 \cdot 3 \cdot 5 = -i (1 + i)^2 \cdot 3 \cdot (2 + i)(2 - i).$$

**Example (Fermat's theorem for $p = 13$, by computation).** The lemma gives $x = 6! = 720$. Since $720 = 55 \cdot 13 + 5$, $x \equiv 5$, and indeed $5^2 + 1 = 26 = 2 \cdot 13$. Now run the Euclidean algorithm on $13$ and $5 + i$. First,
$$\frac{13}{5 + i} = \frac{13(5 - i)}{26} = \frac{5 - i}{2} = 2.5 - 0.5i.$$
Round to $\kappa = 2$. The remainder is $13 - 2(5 + i) = 3 - 2i$, of norm $13 < 26$. Next,
$$\frac{5 + i}{3 - 2i} = \frac{(5 + i)(3 + 2i)}{13} = \frac{13 + 13i}{13} = 1 + i,$$
with remainder $0$. So $3 - 2i$ is a greatest common divisor, with norm $9 + 4 = 13$. So $13 = 3^2 + 2^2 = (3 - 2i)(3 + 2i)$.

**Counterexample (Rounding fails in $\mathbb{Z}[\sqrt{-3}]$).** In $R = \mathbb{Z}[\sqrt{-3}]$ the norm is $N(a + b\sqrt{-3}) = a^2 + 3b^2$, and the proof of the Euclidean property breaks: rounding each coordinate gives the bound $\tfrac14 + 3 \cdot \tfrac14 = 1$, not less than $1$. The bound is reached. Divide $1 + \sqrt{-3}$ by $2$: the quotient $\tfrac12 + \tfrac12\sqrt{-3}$ has norm distance $(\tfrac12 - m)^2 + 3(\tfrac12 - n)^2 \ge 1$ from every $m + n\sqrt{-3}$, so every remainder has norm at least $N(2) = 4$. The ring is not a PID for any Euclidean function: it has two different factorizations
$$4 = 2 \cdot 2 = (1 + \sqrt{-3})(1 - \sqrt{-3}).$$
All three factors have norm $4$, and no element has norm $2$, since $a^2 + 3b^2 = 2$ has no integer solution. So all three are irreducible. The units are $\pm 1$, so $2$ is not an associate of $1 \pm \sqrt{-3}$. Then $2$ divides $(1 + \sqrt{-3})(1 - \sqrt{-3})$ but neither factor, since $(1 \pm \sqrt{-3})/2 \notin R$. So $2$ is irreducible and not prime, and by the first lemma $R$ is not a PID.

### The library around it

The file `Mathlib.NumberTheory.Zsqrtd.GaussianInt` defines `ℤ[i]` and proves that it is Euclidean. The file `Mathlib.NumberTheory.Zsqrtd.QuadraticReciprocity` classifies the rational primes that stay prime, and `Mathlib.NumberTheory.SumTwoSquares` proves Fermat's theorem and the full theorem of the two squares: a natural number is a sum of two squares if and only if each prime $q \equiv 3 \pmod 4$ divides it to an even power. Volume 12 covers these results and the rings of integers of quadratic fields in general.

Common errors of a learner:

- `Zsqrtd.norm` has values in `ℤ`. An inequality of norms in `ℕ` needs `natAbs` or `Int.toNat`, or a cast.
- The rounding `round` in `GaussianInt.div_def` rounds a half up, so $\tfrac52$ becomes $3$. A hand computation that rounds $\tfrac52$ to $2$ is also a valid division, but its quotient is not the value of `x / y`.
- `ℤ[i]` is not a subtype of `ℂ`. A statement about complex numbers needs the coercion `GaussianInt.toComplex`.
- `Prime (p : ℤ[i])` and `Nat.Prime p` are different statements. The first fails for $p = 5$.

### Exercises

1. (A) Divide $11 + 7i$ by $3 - i$ in $\mathbb{Z}[i]$ with a remainder of norm at most $5$.
2. (A) Factor $10$, $17$ and $65$ into Gaussian primes.
3. (A) Show that $1 + i$ divides $a + bi$ if and only if $a \equiv b \pmod 2$.
4. (B) Compute $\gcd(29, 12 + i)$ in $\mathbb{Z}[i]$ with the Euclidean algorithm and write $29$ as a sum of two squares. Hint: $12^2 + 1 = 145 = 5 \cdot 29$.
5. (B) Show that $\mathbb{Z}[i]/(1 + i) \cong \mathbb{F}_2$ and $\mathbb{Z}[i]/(3)$ is a field with $9$ elements.
6. (B) Show that $\mathbb{Z}[\sqrt{-2}]$ is a Euclidean domain with the norm $a^2 + 2b^2$, and deduce that a prime $p \equiv 1, 3 \pmod 8$ is of the form $a^2 + 2b^2$. You may use that $-2$ is a square modulo such $p$.
7. (B) Use the identity of Diophantus to write $65 = 5 \cdot 13$ as a sum of two squares in two different ways.
8. (C) Show that the number of ways to write $n$ as $a^2 + b^2$ with $(a, b) \in \mathbb{Z}^2$ is $4$ times the number of ideals of $\mathbb{Z}[i]$ of norm $n$, where the norm of $(\alpha)$ is $N(\alpha)$. Check it for $n = 25$.
9. (C) Show that the representation $p = a^2 + b^2$ of a prime $p \equiv 1 \pmod 4$ is unique up to order and signs. Hint: a second one gives a second factorization of $p$ in $\mathbb{Z}[i]$.

### Notes and history

Fermat stated the theorem on sums of two squares in a letter to Mersenne in 1640, without proof. Euler found the first proof, in letters to Goldbach of 1749, by a descent argument. The identity of Diophantus is in the *Arithmetica* of Diophantus, and in Brahmagupta in a more general form. Gauss introduced the Gaussian integers in his second memoir on biquadratic residues (1832), proved unique factorization in them with the Euclidean algorithm, and listed the Gaussian primes. The short proof through the square root of $-1$ and the PID property is the standard modern one, as in Ireland and Rosen, *A Classical Introduction to Modern Number Theory*, Chapter 1. The proof by Zagier (1990) in one sentence uses an involution on a finite set instead.

In Mathlib, the Gaussian integers and Fermat's theorem are due to Chris Hughes, and the general theorem of the two squares to Chris Hughes and Michael Stoll. The type `Zsqrtd` is due to Mario Carneiro.

### Reference

<?reference?>
