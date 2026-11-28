---
title: Pythagorean triples and Fermat's last theorem for the exponent four
kind: theory
modules:
  - Mathlib.NumberTheory.PythagoreanTriples
  - Mathlib.NumberTheory.FLT.Basic
  - Mathlib.NumberTheory.FLT.Four
  - Mathlib.NumberTheory.FLT.Three
  - Mathlib.NumberTheory.FLT.MasonStothers
  - Mathlib.NumberTheory.FLT.Polynomial
explains:
  E3: [PythagoreanTriple, PythagoreanTriple.coprime_classification', not_fermat_42, fermatLastTheoremFour]
  E2: [PythagoreanTriple.classification, PythagoreanTriple.coprime_classification, PythagoreanTriple.even_odd_of_coprime, Int.sq_ne_two_mod_four, circleEquivGen, FermatLastTheoremWith, FermatLastTheoremFor, FermatLastTheorem, FermatLastTheoremFor.mono, not_fermatLastTheoremFor_two, Fermat42, Fermat42.Minimal, Fermat42.exists_minimal, Fermat42.not_minimal, FermatLastTheorem.of_odd_primes, fermatLastTheoremThree]
  E1: auto
families: [PythagoreanTriple.*, Fermat42.*, fermatLastTheoremFor_iff_*]
requires: [V02.C02, V06.C06]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Pythagorean triples and Fermat's last theorem for the exponent four

### Overview

A right triangle with integer sides gives three integers with $x^2 + y^2 = z^2$, for example $3^2 + 4^2 = 5^2$. This section finds all such triples. The answer is a formula with two parameters: up to a common factor and the order of $x$ and $y$, every solution is $(m^2 - n^2, 2mn, m^2 + n^2)$. The proof uses only parity and the fact that two coprime numbers whose product is a square are squares up to sign.

Fermat proved with the classification that $x^4 + y^4 = z^2$ has no solution in nonzero integers, by infinite descent. So Fermat's last theorem holds for each multiple of $4$. The section ends with the form of Fermat's last theorem in Mathlib and the reduction to odd prime exponents.

### Definitions

**Definition (Pythagorean triple).** A Pythagorean triple is a triple $(x, y, z)$ of integers with $x^2 + y^2 = z^2$. It is primitive if $\gcd(x, y) = 1$.

Remarks. Zero and negative entries are allowed: $(1, 0, -1)$ is a primitive triple. The condition $\gcd(x, y) = 1$ implies $\gcd(x, z) = \gcd(y, z) = 1$: a prime that divides $x$ and $z$ divides $z^2 - x^2 = y^2$, so it divides $y$. Each nonzero triple is $k = \gcd(x, y)$ times a primitive one, since $k^2 \mid z^2$ gives $k \mid z$.

::: mathlib
`PythagoreanTriple` · `Mathlib.NumberTheory.PythagoreanTriples`

The definition is `x * x + y * y = z * z` for `x y z : ℤ`. Primitivity is not a separate definition: the theorems take the hypothesis `Int.gcd x y = 1`.

<?decl PythagoreanTriple?>
:::

**Definition (Fermat's equation).** Let $R$ be a semiring and $n \in \mathbb{N}$. Fermat's last theorem holds in $R$ for the exponent $n$ if $a^n + b^n \ne c^n$ for all nonzero $a, b, c \in R$. Fermat's last theorem is the statement that it holds in $\mathbb{N}$ for every $n \ge 3$.

Remarks. The statement is false for $n = 1$ and $n = 2$. For a given $n$ the statements in $\mathbb{N}$, $\mathbb{Z}$ and $\mathbb{Q}$ are equivalent.

::: mathlib
`FermatLastTheoremWith` · `Mathlib.NumberTheory.FLT.Basic`

`FermatLastTheoremWith R n` says `∀ a b c : R, a ≠ 0 → b ≠ 0 → c ≠ 0 → a ^ n + b ^ n ≠ c ^ n`. Then `FermatLastTheoremFor n` is the case `R = ℕ`, and `FermatLastTheorem` is `∀ n ≥ 3, FermatLastTheoremFor n`. The lemma `not_fermatLastTheoremFor_two` records $3^2 + 4^2 = 5^2$. `FermatLastTheorem` is a statement in Mathlib, not a theorem: the index of this edition has no proof of it.

<?decl FermatLastTheoremWith?>
:::

::: mathlib
`FermatLastTheorem` · `Mathlib.NumberTheory.FLT.Basic`

<?decl FermatLastTheorem?>
:::

### Theorems and proofs

**Lemma (Squares modulo 4).** For each integer $z$, $z^2 \equiv 0$ or $1 \pmod 4$. In particular $z^2 \not\equiv 2 \pmod 4$.

*Proof.* If $z = 2k$, then $z^2 = 4k^2$. If $z = 2k + 1$, then $z^2 = 4(k^2 + k) + 1$. $\square$

**Lemma (Parity in a primitive triple).** If $(x, y, z)$ is a primitive Pythagorean triple, then one of $x, y$ is even and the other is odd. Then $z$ is odd.

*Proof.* Both even is impossible, since $2$ would divide $\gcd(x, y) = 1$. If both are odd, then $x^2 + y^2 \equiv 1 + 1 = 2 \pmod 4$ by the first lemma, but $z^2 \not\equiv 2 \pmod 4$. So exactly one of them is odd, $x^2 + y^2$ is odd, and $z$ is odd. $\square$

**Lemma (Coprime factors of a square).** Let $u, v \ge 0$ be integers with $\gcd(u, v) = 1$ and $uv = w^2$ for an integer $w$. Then $u$ and $v$ are squares.

*Proof.* If $u = 0$, then $\gcd(0, v) = v = 1$, and both are squares. In the same way for $v = 0$. Let $u, v \ge 1$. By the fundamental theorem of arithmetic (Volume 2, Chapter 2), each prime $p$ occurs in $w^2$ with an even exponent $2e$. Since $\gcd(u, v) = 1$, the prime $p$ does not divide both $u$ and $v$. So its exponent in $u$ is $0$ or $2e$, an even number. All exponents of $u$ are even, so $u$ is a square, and in the same way $v$ is a square. $\square$

**Theorem (Classification of primitive triples).** Let $(x, y, z)$ be a primitive Pythagorean triple with $x$ odd and $z > 0$. Then there are integers $m, n$ with $\gcd(m, n) = 1$, one of them even and one odd, such that
$$x = m^2 - n^2, \qquad y = 2mn, \qquad z = m^2 + n^2.$$
Conversely, for all such $m, n$ these formulas give a primitive Pythagorean triple with $x$ odd.

*Proof.* By the parity lemma $y$ is even and $z$ is odd. So $z + x$ and $z - x$ are even. Put
$$u = \frac{z + x}{2}, \qquad v = \frac{z - x}{2}, \qquad w = \frac{y}{2}.$$
These are integers, and $uv = (z^2 - x^2)/4 = y^2/4 = w^2$. A common divisor of $u$ and $v$ divides $u + v = z$ and $u - v = x$, and $\gcd(x, z) = 1$ by the remark after the definition. So $\gcd(u, v) = 1$. Next, $u + v = z > 0$ and $uv = w^2 \ge 0$, so $u$ and $v$ have the same sign or one is zero, and their sum is positive: $u, v \ge 0$. By the last lemma, $u = m^2$ and $v = n^2$ for integers $m, n \ge 0$. Then
$$x = u - v = m^2 - n^2, \qquad z = u + v = m^2 + n^2, \qquad y^2 = 4uv = (2mn)^2.$$
So $y = 2mn$ or $y = -2mn$. In the second case replace $n$ by $-n$, which does not change $x$ and $z$. A common prime divisor of $m$ and $n$ divides $u$ and $v$, so $\gcd(m, n) = 1$. Since $x = m^2 - n^2$ is odd, $m$ and $n$ have different parities.

For the converse, expand:
$$(m^2 - n^2)^2 + (2mn)^2 = m^4 - 2m^2n^2 + n^4 + 4m^2n^2 = (m^2 + n^2)^2.$$
The number $x = m^2 - n^2$ is odd, since $m$ and $n$ have different parities. Let $p$ be a prime with $p \mid x$ and $p \mid y = 2mn$. Then $p \ne 2$, so $p \mid m$ or $p \mid n$. If $p \mid m$, then $p \mid m^2 - x = n^2$ and $p \mid n$, against $\gcd(m, n) = 1$. The case $p \mid n$ is the same. So $\gcd(x, y) = 1$. $\square$

Since each triple is $k$ times a primitive one, every Pythagorean triple has the form
$$(x, y, z) = \big(k(m^2 - n^2), \ 2kmn, \ \pm k(m^2 + n^2)\big)$$
or the same with $x$ and $y$ exchanged. Mathlib states both forms.

::: mathlib
`PythagoreanTriple.coprime_classification'` · `Mathlib.NumberTheory.PythagoreanTriples`

The theorem in the form above, with the parities written with `% 2`. Mathlib does not factor $y^2$. It parametrizes the rational points of the unit circle by lines through $(0, -1)$, `circleEquivGen`, and clears the denominators. The parity lemma is `PythagoreanTriple.even_odd_of_coprime`, and the lemma on squares modulo 4 is `Int.sq_ne_two_mod_four`.

<?decl PythagoreanTriple.coprime_classification'?>
:::

::: mathlib
`PythagoreanTriple.classification` · `Mathlib.NumberTheory.PythagoreanTriples`

The classification of all triples as an equivalence, with the factor `k`, the two orders of `x` and `y`, and the two signs of `z`. The primitive form as an equivalence is `PythagoreanTriple.coprime_classification`.

<?decl PythagoreanTriple.classification?>
:::

**Theorem (Fermat).** There are no integers $x, y, z$ with $x \ne 0$, $y \ne 0$ and $x^4 + y^4 = z^2$.

*Proof.* Suppose a solution exists. Then $z^2 = x^4 + y^4 > 0$, so $z \ne 0$. Choose a solution with $|z|$ least among all solutions. Change the sign of $z$ if necessary, so that $z > 0$.

Step 1: $\gcd(x, y) = 1$. Let $p$ be a prime with $p \mid x$ and $p \mid y$. Then $p^4 \mid z^2$, so $p^2 \mid z$, and $(x/p, y/p, z/p^2)$ is a solution with a smaller $|z|$. This contradicts the choice.

Step 2: the first triple. The triple $(x^2, y^2, z)$ is a Pythagorean triple, and it is primitive by step 1. By the parity lemma one of $x^2, y^2$ is odd. Exchange $x$ and $y$ if necessary, so that $x$ is odd. The classification gives coprime $m, n$ of different parities with
$$x^2 = m^2 - n^2, \qquad y^2 = 2mn, \qquad z = m^2 + n^2.$$

Step 3: the parities of $m$ and $n$. The equation $x^2 + n^2 = m^2$ holds. If $m$ were even and $n$ odd, then $x^2 + n^2 \equiv 2 \pmod 4$ and $m^2 \equiv 0 \pmod 4$, a contradiction. So $m$ is odd and $n$ is even.

Step 4: the second triple. The triple $(x, n, m)$ is a Pythagorean triple. It is primitive: a prime dividing $x$ and $n$ divides $m^2$ and so $m$, against $\gcd(m, n) = 1$. Here $x$ is odd. Since $y \ne 0$, the product $2mn = y^2$ is positive, so $m$ and $n$ are nonzero and have the same sign. Replace $(m, n)$ by $(-m, -n)$ if necessary, which changes none of the three formulas, so that $m > 0$ and $n > 0$. The classification gives coprime $r, s$ of different parities with
$$x = r^2 - s^2, \qquad n = 2rs, \qquad m = r^2 + s^2.$$

Step 5: three squares. Now $y^2 = 2mn = 4rs(r^2 + s^2)$, so $(y/2)^2 = rs(r^2 + s^2)$, with $y$ even since $y^2$ is even. The product $rs = n/2$ is positive, so $r$ and $s$ are nonzero with the same sign. Replace $(r, s)$ by $(-r, -s)$ if necessary, so that $r, s > 0$. The three numbers $r$, $s$ and $r^2 + s^2$ are pairwise coprime: $\gcd(r, s) = 1$, and a prime dividing $r$ and $r^2 + s^2$ divides $s^2$. Their product is a square. The lemma on coprime factors, applied twice, shows that each of them is a square:
$$r = a^2, \qquad s = b^2, \qquad r^2 + s^2 = c^2,$$
with $a, b \ne 0$ and $c > 0$. Then $a^4 + b^4 = c^2$, a new solution.

Step 6: descent. Now $c \le c^2 = r^2 + s^2 = m$, and $m < m^2 + n^2 = z$ because $n \ne 0$. So $0 < c < z$, against the choice of the solution with $|z|$ least. So no solution exists. $\square$

**Corollary (Fermat's last theorem for $n = 4$).** There are no nonzero integers $a, b, c$ with $a^4 + b^4 = c^4$. More generally, if $4 \mid n$, there are no nonzero integers with $a^n + b^n = c^n$.

*Proof.* A solution of $a^4 + b^4 = c^4$ gives the solution $(a, b, c^2)$ of the theorem. If $n = 4k$, a solution of $a^n + b^n = c^n$ gives the solution $(a^k, b^k, c^k)$ of the exponent $4$. $\square$

::: mathlib
`not_fermat_42` · `Mathlib.NumberTheory.FLT.Four`

The theorem for integers, proved by the descent above. `Fermat42 a b c` is `a ≠ 0 ∧ b ≠ 0 ∧ a ^ 4 + b ^ 4 = c ^ 2`, `Fermat42.Minimal` adds that `c.natAbs` is least, `Fermat42.exists_minimal` gives a least solution, and `Fermat42.not_minimal` is step 6.

<?decl not_fermat_42?>
:::

::: mathlib
`fermatLastTheoremFour` · `Mathlib.NumberTheory.FLT.Four`

The corollary. With `FermatLastTheoremFor.mono` it gives every multiple of $4$.

<?decl fermatLastTheoremFour?>
:::

**Theorem (Reduction to odd primes).** If Fermat's last theorem holds for every odd prime exponent, then it holds for every exponent $n \ge 3$.

*Proof.* Let $n \ge 3$. If $n$ has an odd prime factor $p$, the statement for $p$ gives it for $n$, as in the corollary. Otherwise $n$ is a power of $2$, and $n \ge 3$ gives $4 \mid n$. The corollary covers this case. $\square$

::: mathlib
`FermatLastTheorem.of_odd_primes` · `Mathlib.NumberTheory.FLT.Four`

The reduction. The exponent $3$ is also in Mathlib as `fermatLastTheoremThree`, with a descent in $\mathbb{Z}[\zeta_3]$ that is too long for this section.

<?decl FermatLastTheorem.of_odd_primes?>
:::

::: mathlib
`fermatLastTheoremThree` · `Mathlib.NumberTheory.FLT.Three`

<?decl fermatLastTheoremThree?>
:::

### Examples

**Example (A table of primitive triples).** The pairs $m > n > 0$ with $\gcd(m, n) = 1$ and $m \not\equiv n \pmod 2$ give:

| $m$ | $n$ | $m^2 - n^2$ | $2mn$ | $m^2 + n^2$ |
|---|---|---|---|---|
| 2 | 1 | 3 | 4 | 5 |
| 3 | 2 | 5 | 12 | 13 |
| 4 | 1 | 15 | 8 | 17 |
| 4 | 3 | 7 | 24 | 25 |
| 5 | 2 | 21 | 20 | 29 |
| 5 | 4 | 9 | 40 | 41 |

For $(21, 20, 29)$ the proof gives $u = 25$, $v = 4$, so $m = 5$, $n = 2$.

**Example (Rational points on the circle).** The map $t \mapsto \left(\frac{2t}{1 + t^2}, \frac{1 - t^2}{1 + t^2}\right)$ sends $\mathbb{Q}$ onto the rational points of the circle $X^2 + Y^2 = 1$ other than $(0, -1)$. For $t = n/m$ it gives $\left(\frac{2mn}{m^2 + n^2}, \frac{m^2 - n^2}{m^2 + n^2}\right)$, the triple of the theorem divided by $z$. For $t = 2/5$ the point is $(20/29, 21/29)$. This is `circleEquivGen`.

**Counterexample (The parity condition is needed).** Take $m = 3$ and $n = 1$, both odd. The formulas give $(8, 6, 10)$, a Pythagorean triple that is not primitive. So the converse half of the theorem fails without the parity condition.

### The library around it

The file `Mathlib.NumberTheory.FLT.Basic` gives the translations `fermatLastTheoremFor_iff_int` and `fermatLastTheoremFor_iff_rat` between `ℕ`, `ℤ` and `ℚ`.

For polynomials, Fermat's equation has an elementary proof. The module `Mathlib.NumberTheory.FLT.MasonStothers` proves the Mason and Stothers theorem `Polynomial.abc`: if $a, b, c$ are nonzero polynomials over a field, $a$ and $b$ are coprime and $a + b + c = 0$, then each of $\deg a$, $\deg b$, $\deg c$ is less than the degree of the radical $\operatorname{rad}(abc)$, the product of the distinct irreducible factors, or else the three derivatives vanish. The second case is needed in characteristic $p$, where $a = X^p$ has derivative $0$. The proof bounds the degree of the Wronskian $ab' - a'b$, which $abc/\operatorname{rad}(abc)$ divides. The module `Mathlib.NumberTheory.FLT.Polynomial` deduces `Polynomial.flt`: for $n \geq 3$ with $n \neq 0$ in the field, coprime nonzero polynomials with $a^n + b^n = c^n$ are constant. In outline, $\operatorname{rad}(a^n b^n c^n)$ has degree at most $\deg a + \deg b + \deg c$, and the theorem gives $n \deg a < \deg a + \deg b + \deg c$ and the same for $b$ and $c$; the sum of the three inequalities fails for $n \geq 3$. The general form `Polynomial.flt_catalan` treats $ua^p + vb^q + wc^r = 0$ with $\frac1p + \frac1q + \frac1r \leq 1$, and `fermatLastTheoremWith'_polynomial` states the result as `FermatLastTheoremWith' k[X] n`, without the coprimality hypothesis: each solution is a common factor times units.

Common errors of a learner:

- `PythagoreanTriple x y z` allows `z < 0` and zero entries. A statement about the triangle needs `0 < x`, `0 < y` or `0 < z` as extra hypotheses.
- The classification needs `x % 2 = 1`, not `y % 2 = 1`. For a triple with `y` odd, apply `PythagoreanTriple.symm` first.

### Exercises

1. (A) Find all primitive Pythagorean triples with $z = 65$ and $x, y > 0$. Hint: $65 = 8^2 + 1^2 = 7^2 + 4^2$.
2. (A) Show that in each Pythagorean triple one of $x, y$ is divisible by $3$ and one of $x, y, z$ is divisible by $5$.
3. (A) Show that the area $xy/2$ of a right triangle with integer sides is an integer divisible by $6$.
4. (B) Show that each integer $k \ge 3$ is a leg of some Pythagorean triple with positive entries. Hint: treat $k$ odd and $k$ divisible by $4$ separately, and for $k \equiv 2 \pmod 4$ use $k/2$.
5. (B) Find all solutions of $x^2 + 2y^2 = z^2$ in positive coprime integers. Hint: imitate the proof with $2y^2 = (z - x)(z + x)$.
6. (B) Prove that there is no right triangle with integer sides whose area is a square. Hint: if $x^2 + y^2 = z^2$ and $xy/2 = w^2$, then $z^4 - (2xy)^2 = (x^2 - y^2)^2$; deduce a solution of $X^4 - Y^4 = Z^2$ and show by a descent like the one of the theorem that this equation has no solution with $XYZ \ne 0$.
7. (B) Show that Fermat's last theorem for the exponent $3$ gives it for the exponents $6$, $9$ and $12$, and that the theorem of this section gives it for $8$ and $12$. Which exponents below $20$ are covered by the cases $3$ and $4$ together?
8. (C) Show that $x^4 + y^4 = 2z^2$ has only the solutions with $x^2 = y^2 = |z|$. Hint: $\left(\frac{x^4 - y^4}{2}\right)^2 = z^4 - (xy)^4$, and exercise 6 shows that $X^4 - Y^4 = Z^2$ forces $Z = 0$ when $XY \ne 0$.

### Notes and history

The formula for the triples is in Euclid's *Elements*, Book X, as a lemma before Proposition 29. The descent proof that $x^4 + y^4 = z^2$ has no solution is due to Fermat, who wrote it in a margin of his copy of Diophantus in the form of exercise 6: the area of a right triangle with integer sides is not a square. In the same copy Fermat claimed that $a^n + b^n = c^n$ has no positive solution for $n \ge 3$. Andrew Wiles, with a step completed jointly with Richard Taylor, proved the full theorem in 1995. A standard reference for the material of this section is Ireland and Rosen, *A Classical Introduction to Modern Number Theory*, Chapter 17.

### Reference

<?reference?>
