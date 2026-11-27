---
title: Quadratic residues and the Legendre symbol
kind: theory
modules:
  - Mathlib.NumberTheory.LegendreSymbol.Basic
  - Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
  - Mathlib.NumberTheory.LegendreSymbol.ZModChar
explains:
  E3: [legendreSym, quadraticChar, ZMod.euler_criterion, ZMod.χ₄]
  E2: [legendreSym.mul, legendreSym.mod, legendreSym.sq_one, legendreSym.card_sqrts, legendreSym.at_neg_one, legendreSym.at_neg, legendreSym.prime_dvd_of_eq_neg_one, ZMod.euler_criterion_units, ZMod.pow_div_two_eq_neg_one_or_one, quadraticChar_one_iff_isSquare, quadraticChar_neg_one_iff_not_isSquare, quadraticChar_eq_pow_of_char_ne_two, quadraticChar_sum_zero, quadraticChar_card_sqrts, quadraticChar_dichotomy, quadraticChar_neg_one, FiniteField.isSquare_neg_one_iff, ZMod.χ₄_nat_eq_if_mod_four]
  E1: auto
families: []
requires: [V02.C06, V05.C03, V06.C04, V06.C05]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Quadratic residues and the Legendre symbol

### Overview

The equation $x^2 \equiv a \pmod p$ has a solution for some $a$ and not for others. Modulo $7$, the squares of $1, \dots, 6$ are $1, 4, 2, 2, 4, 1$, so $1, 2, 4$ are squares and $3, 5, 6$ are not. This section studies the set of squares modulo an odd prime $p$. It has exactly $(p-1)/2$ nonzero elements, it is a subgroup of index $2$ in $(\mathbb{Z}/p)^\times$, and Euler's criterion decides membership by one power: $a$ is a square if and only if $a^{(p-1)/2} \equiv 1$. The Legendre symbol $(a/p)$ records the answer as $1$, $-1$ or $0$, and it is a multiplicative function of $a$. Section 2 proves the law of quadratic reciprocity, which computes $(a/p)$ without any power. In Mathlib the symbol is a special case of the quadratic character of a finite field.

### Definitions

**Definition (Quadratic residue).** Let $p$ be an odd prime and $a$ an integer with $p \nmid a$. Then $a$ is a quadratic residue modulo $p$ if $x^2 \equiv a \pmod p$ has a solution, and a quadratic nonresidue otherwise.

**Definition (Legendre symbol).** For an odd prime $p$ and $a \in \mathbb{Z}$,
$$\left(\frac{a}{p}\right) = \begin{cases} 0 & \text{if } p \mid a, \\ 1 & \text{if } a \text{ is a quadratic residue modulo } p, \\ -1 & \text{if } a \text{ is a quadratic nonresidue modulo } p. \end{cases}$$

The symbol depends only on $a \bmod p$. The same definition makes sense in any finite field $F$: the quadratic character $\chi_F(a)$ is $0$ for $a = 0$, $1$ for a nonzero square and $-1$ otherwise.

::: mathlib
`quadraticChar` · `Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic`

`quadraticChar F : MulChar F ℤ` for a finite field `F` with decidable equality. Its underlying function is `quadraticCharFun F a = if a = 0 then 0 else if IsSquare a then 1 else -1`. The type `MulChar F ℤ` of multiplicative characters is the subject of Chapter 6; here it means a map $\chi$ with $\chi(1) = 1$, $\chi(ab) = \chi(a)\chi(b)$ and $\chi(a) = 0$ for nonunits. The characterizations are `quadraticChar_one_iff_isSquare` (for `a ≠ 0`) and `quadraticChar_neg_one_iff_not_isSquare`, and `quadraticChar_dichotomy` says that the value at `a ≠ 0` is $\pm 1$.

<?decl quadraticChar?>
:::

::: mathlib
`legendreSym` · `Mathlib.NumberTheory.LegendreSymbol.Basic`

`legendreSym p a : ℤ` for `p : ℕ` with `[Fact p.Prime]` and `a : ℤ`, defined as `quadraticChar (ZMod p) a`. The prime comes first, so `legendreSym p a` is $(a/p)$; the reversed order on paper is a frequent source of errors. The definition allows $p = 2$, where $(a/2) = a \bmod 2$, since every element of $\mathbb{Z}/2$ is a square. Most theorems ask `p ≠ 2`. The value depends only on `a % p`, by `legendreSym.mod`.

<?decl legendreSym?>
:::

### Theorems and proofs

Throughout, $p$ is an odd prime and $\mathbb{F}_p = \mathbb{Z}/p$, a field by Volume 2, Chapter 6.

**Theorem (The number of squares).** Exactly $(p-1)/2$ elements of $\mathbb{F}_p^\times$ are squares. They form a subgroup $Q$ of index $2$. For $a \in \mathbb{F}_p$, the number of $x \in \mathbb{F}_p$ with $x^2 = a$ is $1 + (a/p)$.

*Proof.* The map $s : \mathbb{F}_p^\times \to \mathbb{F}_p^\times$, $x \mapsto x^2$, is a group homomorphism with image $Q$, so $Q$ is a subgroup (Volume 5, Chapter 3). Its kernel is the set of roots of $x^2 - 1 = (x - 1)(x + 1)$, and in a field this is $\{1, -1\}$. Since $p$ is odd, $1 \neq -1$, so the kernel has $2$ elements, and $|Q| = (p - 1)/2$ by the first isomorphism theorem. For $a = 0$ the only root is $x = 0$. For a nonzero square $a = b^2$, the roots are $x$ with $s(x) = s(b)$, that is $x = \pm b$: two roots. For a nonsquare, there are none. In each case the number is $1 + (a/p)$. $\square$

::: mathlib
`legendreSym.card_sqrts` · `Mathlib.NumberTheory.LegendreSymbol.Basic`

For `p ≠ 2` and `a : ℤ`, the cardinality of `{x : ZMod p | x ^ 2 = a}` is `legendreSym p a + 1`, as an equation in `ℤ`. The version for any finite field of odd characteristic is `quadraticChar_card_sqrts`.

<?decl legendreSym.card_sqrts?>
:::

**Theorem (Euler's criterion).** For every integer $a$,
$$\left(\frac{a}{p}\right) \equiv a^{(p-1)/2} \pmod p.$$

*Proof.* If $p \mid a$, both sides are $0$ modulo $p$. Let $p \nmid a$ and $h = (p-1)/2$. By Fermat, $(a^h)^2 = a^{p-1} = 1$ in $\mathbb{F}_p$, so $a^h = \pm 1$. If $a = b^2$ is a square, then $a^h = b^{p-1} = 1$. So the $h$ elements of $Q$ are roots of the polynomial $X^h - 1$. A nonzero polynomial of degree $h$ over a field has at most $h$ roots (Volume 6, Chapter 5). So the roots of $X^h - 1$ are exactly the elements of $Q$, and for a nonsquare $a$, $a^h \neq 1$, so $a^h = -1$. $\square$

The proof does not need a primitive root. The congruence holds in $\mathbb{Z}$ modulo $p$, and since $p > 2$ the values $1$, $-1$ and $0$ stay distinct modulo $p$, so $a^{(p-1)/2} \bmod p$ determines the symbol.

::: mathlib
`ZMod.euler_criterion` · `Mathlib.NumberTheory.LegendreSymbol.Basic`

For `a : ZMod p` with `a ≠ 0`: `IsSquare a ↔ a ^ (p / 2) = 1`. The exponent is `p / 2`, division in `ℕ`, which is $(p-1)/2$ for odd $p$. The version for units is `ZMod.euler_criterion_units`, and `ZMod.pow_div_two_eq_neg_one_or_one` gives the dichotomy $a^{p/2} = \pm 1$. For the symbol itself, `quadraticChar_eq_pow_of_char_ne_two` states $\chi_F(a) = 1$ if $a^{|F|/2} = 1$ and $-1$ otherwise, for any finite field $F$ of odd characteristic.

<?decl ZMod.euler_criterion?>
:::

**Theorem (Multiplicativity).** $(ab/p) = (a/p)(b/p)$ for all integers $a, b$. In particular, the product of two nonresidues is a residue.

*Proof.* If $p$ divides $a$ or $b$, both sides are $0$. Otherwise Euler's criterion gives $(ab/p) \equiv (ab)^h = a^h b^h \equiv (a/p)(b/p) \pmod p$. Both sides are $\pm 1$, and $1 \not\equiv -1 \pmod p$, so they are equal. $\square$

So $a \mapsto (a/p)$ is a group homomorphism $\mathbb{F}_p^\times \to \{\pm 1\}$ with kernel $Q$. Since $Q$ has index $2$, the sum of the symbol over $\mathbb{F}_p$ is $0$: there are as many residues as nonresidues.

::: mathlib
`legendreSym.mul` · `Mathlib.NumberTheory.LegendreSymbol.Basic`

`legendreSym p (a * b) = legendreSym p a * legendreSym p b`, with no hypothesis, since `quadraticChar` is a `MulChar`. The bundled form is `legendreSym.hom : ℤ →*₀ ℤ`. The sum is `quadraticChar_sum_zero`, and `legendreSym.sq_one` says $(a/p)^2 = 1$ for $p \nmid a$.

<?decl legendreSym.mul?>
:::

**Theorem (The first supplement).** $(-1/p) = (-1)^{(p-1)/2}$. So $-1$ is a square modulo $p$ if and only if $p \equiv 1 \pmod 4$.

*Proof.* By Euler's criterion, $(-1/p) \equiv (-1)^{(p-1)/2} \pmod p$, and both sides are $\pm 1$. The exponent $(p-1)/2$ is even exactly when $p \equiv 1 \pmod 4$. $\square$

Volume 6, Chapter 6 proves the second statement with Wilson's theorem and uses it for the sums of two squares. The function $n \mapsto (-1)^{(n-1)/2}$ on odd $n$, and $0$ on even $n$, depends only on $n \bmod 4$; it is the character $\chi_4$.

::: mathlib
`legendreSym.at_neg_one` · `Mathlib.NumberTheory.LegendreSymbol.Basic`

For `p ≠ 2`, `legendreSym p (-1) = χ₄ p`. With `legendreSym.at_neg` this gives $(-a/p) = \chi_4(p)(a/p)$. For a general finite field, `quadraticChar_neg_one` gives `χ₄ (Fintype.card F)`, and `FiniteField.isSquare_neg_one_iff` says `IsSquare (-1) ↔ Fintype.card F % 4 ≠ 3`.

<?decl legendreSym.at_neg_one?>
:::

::: mathlib
`ZMod.χ₄` · `Mathlib.NumberTheory.LegendreSymbol.ZModChar`

`χ₄ : MulChar (ZMod 4) ℤ` with values $0, 1, 0, -1$ at $0, 1, 2, 3$. A natural number is cast to `ZMod 4` before evaluation; the formula on `ℕ` is `ZMod.χ₄_nat_eq_if_mod_four : χ₄ n = if n % 2 = 0 then 0 else if n % 4 = 1 then 1 else -1`. The same file has `χ₈` and `χ₈'` for Section 2.

<?decl ZMod.χ₄?>
:::

**Theorem (A nonresidue forces divisibility).** If $(a/p) = -1$ and $p \mid x^2 - a y^2$, then $p \mid x$ and $p \mid y$.

*Proof.* If $p \nmid y$, let $y'$ be an inverse of $y$ modulo $p$. Then $(x y')^2 \equiv a \pmod p$, so $a$ is a residue, which is false. So $p \mid y$, and then $p \mid x^2$, so $p \mid x$. $\square$

::: mathlib
`legendreSym.prime_dvd_of_eq_neg_one` · `Mathlib.NumberTheory.LegendreSymbol.Basic`

The theorem, with `x y : ℤ` and the conclusion `↑p ∣ x ∧ ↑p ∣ y`. Chapter 4 uses this kind of statement for Diophantine equations $x^2 - a y^2 = n$.

<?decl legendreSym.prime_dvd_of_eq_neg_one?>
:::

### Examples

**Example (The residues modulo $11$).** The squares of $1, \dots, 5$ modulo $11$ are $1, 4, 9, 5, 3$, and those of $6, \dots, 10$ repeat them. So the residues are $1, 3, 4, 5, 9$, five of them, as the theorem says. Euler's criterion checks two values: $2^5 = 32 \equiv -1$, so $(2/11) = -1$; and $3^5 = 243 = 22 \cdot 11 + 1$, so $(3/11) = 1$, in accordance with $3 \equiv 5^2$. Multiplicativity gives $(6/11) = -1$ and $(8/11) = (2/11)^3 = -1$, which agrees with the list.

**Example (Infinitely many primes $p \equiv 1 \pmod 4$).** Let $N \geq 1$ and let $p$ be a prime factor of $m = (2 \cdot N!)^2 + 1$. Then $p$ is odd, $p > N$ because $p \nmid N!$, and $(2 \cdot N!)^2 \equiv -1 \pmod p$. So $(-1/p) = 1$ and $p \equiv 1 \pmod 4$. Since $N$ is arbitrary, there are infinitely many such primes.

**Counterexample (A composite modulus).** Modulo $8$, the squares of the units $1, 3, 5, 7$ are all $1$. So $3$ and $5$ are not squares, and their product $15 \equiv 7$ is not a square either. The rule "nonresidue times nonresidue is a residue" fails, because $(\mathbb{Z}/8)^\times$ has the subgroup of squares $\{1\}$ of index $4$, not $2$. The Jacobi symbol of Section 3 is multiplicative, but for this reason it does not detect squares modulo a composite number.

**Counterexample (The prime $2$).** Modulo $2$ every element is a square, and $(p-1)/2$ is not an integer. Euler's criterion and the count $(p-1)/2$ need $p$ odd, which is why most theorems of the library have `p ≠ 2`.

### The library around it

`Mathlib.NumberTheory.LegendreSymbol.Basic` has `legendreSym` and its rules, the criteria of Euler, and the facts on $-1$ such as `ZMod.exists_sq_eq_neg_one_iff` (Volume 6, Chapter 6). `QuadraticChar.Basic` has the same theory for any finite field, with `quadraticChar_exists_neg_one` (a nonsquare exists in odd characteristic) and `quadraticChar_isQuadratic` (the values are $0$ and $\pm1$). The proofs in Mathlib go through the finite field, and the theorems on `legendreSym` are corollaries.

Common errors of a learner:

- `legendreSym p a` is $(a/p)$: the prime is the first argument.
- `legendreSym p a` takes `a : ℤ`, and `quadraticChar (ZMod p)` takes `a : ZMod p`. The cast `((a : ℤ) : ZMod p)` connects them.
- $(a/p) = 1$ needs $p \nmid a$: for $a = 0$ the equation $x^2 = 0$ has a solution, but $(0/p) = 0$.

### Exercises

1. (A) List the quadratic residues modulo $13$ and modulo $17$.
2. (A) Use Euler's criterion to compute $(5/13)$ and $(7/17)$.
3. (A) Show that the product of all quadratic residues modulo $p$ in $\{1, \dots, p-1\}$ is $\equiv (-1)^{(p+1)/2} \pmod p$. Hint: pair $x$ with $-x$ among the square roots.
4. (B) Show that $\sum_{x=0}^{p-1} \left(\frac{x^2 + 1}{p}\right) = -1$. Hint: count the solutions of $y^2 - x^2 = 1$ with the factorization $(y - x)(y + x) = 1$.
5. (B) Show that there are infinitely many primes $p \equiv 1 \pmod 3$. Hint: a prime factor $p > 3$ of $x^2 + x + 1$ has $(-3/p) = 1$; use $4(x^2 + x + 1) = (2x + 1)^2 + 3$ and the fact, proved in Section 2, that $(-3/p) = 1$ if and only if $p \equiv 1 \pmod 3$.
6. (B) Let $p \equiv 3 \pmod 4$ and let $a$ be a residue. Show that $x = a^{(p+1)/4}$ is a square root of $a$ modulo $p$, and compute a square root of $5$ modulo $11$.
7. (C) Let $F$ be a finite field of odd characteristic. Show that every element of $F$ is a sum of two squares. Hint: the sets $\{x^2\}$ and $\{a - y^2\}$ have $(|F|+1)/2$ elements each.

### Notes and history

Euler stated the criterion that carries his name, and Legendre introduced the symbol $(a/p)$ in 1798 in his *Essai sur la théorie des nombres*. Gauss treated quadratic residues in the *Disquisitiones Arithmeticae* of 1801. A standard reference is Ireland and Rosen, *A Classical Introduction to Modern Number Theory*, Chapter 5.

### Reference

<?reference?>
