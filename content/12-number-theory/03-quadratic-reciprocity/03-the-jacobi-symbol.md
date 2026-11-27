---
title: The Jacobi symbol
kind: theory
modules:
  - Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
  - Mathlib.NumberTheory.Zsqrtd.QuadraticReciprocity
explains:
  E3: [jacobiSym, jacobiSym.quadratic_reciprocity, ZMod.nonsquare_of_jacobiSym_eq_neg_one, jacobiSym.mod_left]
  E2: [jacobiSym.legendreSym.to_jacobiSym, jacobiSym.mul_left, jacobiSym.mul_right, jacobiSym.trichotomy, jacobiSym.zero_right, jacobiSym.one_right, jacobiSym.sq_one, jacobiSym.ne_zero, jacobiSym.at_neg_one, jacobiSym.at_two, jacobiSym.at_neg_two, jacobiSym.neg, jacobiSym.even_odd, jacobiSym.quadratic_reciprocity_one_mod_four, jacobiSym.quadratic_reciprocity_three_mod_four, "jacobiSym.quadratic_reciprocity'", qrSign, qrSign.neg_one_pow, jacobiSym.mod_right, jacobiSym.value_at, ZMod.nonsquare_iff_jacobiSym_eq_neg_one, ZMod.isSquare_of_jacobiSym_eq_one, GaussianInt.prime_of_nat_prime_of_mod_four_eq_three, GaussianInt.mod_four_eq_three_of_nat_prime_of_prime]
  E1: auto
families: []
requires: [V02.C06, V06.C06]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The Jacobi symbol

### Overview

Quadratic reciprocity of Section 2 computes $(a/p)$, but each step needs the prime factors of the numerator. Factoring is slow for large numbers. The Jacobi symbol extends $(a/p)$ to any odd denominator $n$ by multiplicativity. It obeys the same reciprocity law and the same supplements, so the computation becomes a Euclidean algorithm that never factors: reduce the numerator modulo the denominator, remove the factors $2$, and swap. When the denominator is prime, the result is the Legendre symbol.

The price is a weaker meaning. The value $-1$ still proves that $a$ is not a square modulo $n$, but the value $1$ proves nothing when $n$ is composite.

### Definitions

**Definition (Jacobi symbol).** Let $a \in \mathbb{Z}$ and let $n$ be an odd positive integer, $n = p_1 p_2 \cdots p_k$ with primes $p_i$, not necessarily distinct. The Jacobi symbol is
$$\left(\frac{a}{n}\right) = \prod_{i=1}^{k} \left(\frac{a}{p_i}\right),$$
with the empty product $(a/1) = 1$.

Each factor is $0$, $1$ or $-1$, so $(a/n) \in \{0, 1, -1\}$, and $(a/n) = 0$ exactly when $\gcd(a, n) > 1$.

::: mathlib
`jacobiSym` · `Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol`

`jacobiSym (a : ℤ) (b : ℕ) : ℤ` is the product of `legendreSym p a` over `b.primeFactorsList`, the prime factors with multiplicity. It is defined for every `b`, but it has the intended meaning only for odd `b`: `jacobiSym.zero_right` gives `jacobiSym a 0 = 1`, and a factor $2$ of `b` contributes `legendreSym 2 a`. The notation `J(a | b)` is open after `open NumberTheorySymbols`. The link to Section 1 is `jacobiSym.legendreSym.to_jacobiSym : legendreSym p a = jacobiSym a p`.

<?decl jacobiSym?>
:::

### Theorems and proofs

**Proposition (Basic properties).** Let $m$ and $n$ be odd and positive, and $a, b \in \mathbb{Z}$.

1. $(ab/n) = (a/n)(b/n)$ and $(a/mn) = (a/m)(a/n)$.
2. If $a \equiv b \pmod n$, then $(a/n) = (b/n)$.
3. If $\gcd(a, n) = 1$, then $(a^2/n) = 1$ and $(a/n^2) = 1$.

*Proof.* (1) The first identity holds for each factor $(\cdot/p_i)$ by the multiplicativity of the Legendre symbol, so it holds for the product. The second holds because the prime factors of $mn$ with multiplicity are those of $m$ followed by those of $n$. (2) If $a \equiv b \pmod n$, then $a \equiv b \pmod{p_i}$ for each $i$, and each factor is the same. (3) By (1), $(a^2/n) = (a/n)^2$ and $(a/n^2) = (a/n)^2$. Since $\gcd(a, n) = 1$, $(a/n) = \pm 1$. $\square$

::: mathlib
`jacobiSym.mod_left` · `Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol`

`jacobiSym a b = jacobiSym (a % b) b`, the reduction of the numerator. The multiplicative laws are `jacobiSym.mul_left` and `jacobiSym.mul_right`; the second needs `[NeZero b₁] [NeZero b₂]`. The value set is `jacobiSym.trichotomy`, and for coprime arguments `jacobiSym.sq_one` and `jacobiSym.ne_zero` hold. Also `jacobiSym.one_right` gives `jacobiSym a 1 = 1`.

<?decl jacobiSym.mod_left?>
:::

For odd $n$, put $\varepsilon(n) = (n - 1)/2$.

**Lemma.** For odd $m$ and $n$, $\varepsilon(mn) \equiv \varepsilon(m) + \varepsilon(n) \pmod 2$ and $(m^2n^2 - 1)/8 \equiv (m^2 - 1)/8 + (n^2 - 1)/8 \pmod 2$.

*Proof.* $(mn - 1) - (m - 1) - (n - 1) = (m - 1)(n - 1)$, and $4 \mid (m-1)(n-1)$, so the halves differ by an even number. In the same way $(m^2 n^2 - 1) - (m^2 - 1) - (n^2 - 1) = (m^2 - 1)(n^2 - 1)$, and $64 \mid (m^2-1)(n^2-1)$ because $8 \mid m^2 - 1$ for odd $m$. $\square$

So $n \mapsto (-1)^{\varepsilon(n)} = \chi_4(n)$ and $n \mapsto (-1)^{(n^2-1)/8} = \chi_8(n)$ are multiplicative on odd $n$, and so is $n \mapsto (-1)^{\varepsilon(m)\varepsilon(n)}$ for a fixed odd $m$.

**Theorem (Supplements).** For odd positive $n$, $(-1/n) = \chi_4(n)$, $(2/n) = \chi_8(n)$ and $(-2/n) = \chi_8'(n)$.

*Proof.* Both sides are multiplicative in $n$: the left side by property (1), the right side by the lemma. For a prime $n = p$, the identities are Euler's criterion for $-1$ in Section 1 and the second supplement in Section 2. $\square$

::: mathlib
`jacobiSym.at_two` · `Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol`

`Odd b → jacobiSym 2 b = χ₈ b`, with `jacobiSym.at_neg_one` and `jacobiSym.at_neg_two` for $-1$ and $-2$, and `jacobiSym.neg` for `jacobiSym (-a) b = χ₄ b * jacobiSym a b`. Mathlib proves the three with `jacobiSym.value_at`: a multiplicative function that agrees with $(a/p)$ at every odd prime $p$ agrees with $(a/n)$ at every odd $n$. This is the argument above in one lemma. The step that removes one factor $2$ from the numerator is `jacobiSym.even_odd`.

<?decl jacobiSym.at_two?>
:::

**Theorem (Reciprocity for the Jacobi symbol).** For odd positive $m$ and $n$,
$$\left(\frac{m}{n}\right) = (-1)^{\varepsilon(m)\varepsilon(n)} \left(\frac{n}{m}\right).$$

*Proof.* If $\gcd(m, n) > 1$, both sides are $0$. Otherwise write $m = \prod_i p_i$ and $n = \prod_j q_j$; all $p_i \neq q_j$ and all are odd. By property (1),
$$\left(\frac{m}{n}\right) = \prod_{i, j} \left(\frac{p_i}{q_j}\right) = \prod_{i, j} (-1)^{\varepsilon(p_i)\varepsilon(q_j)} \left(\frac{q_j}{p_i}\right),$$
by quadratic reciprocity for each pair. The product of the $(q_j/p_i)$ is $(n/m)$. The product of the signs is $(-1)^{\sum_i \varepsilon(p_i) \cdot \sum_j \varepsilon(q_j)}$, and by the lemma $\sum_i \varepsilon(p_i) \equiv \varepsilon(m)$ and $\sum_j \varepsilon(q_j) \equiv \varepsilon(n) \pmod 2$. $\square$

::: mathlib
`jacobiSym.quadratic_reciprocity` · `Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol`

For `a b : ℕ` with `Odd a` and `Odd b`, `jacobiSym a b = (-1) ^ (a / 2 * (b / 2)) * jacobiSym b a`. No coprimality is needed. The sign is also `qrSign b a`, and `qrSign.neg_one_pow` gives the power; `quadratic_reciprocity'` is the form with `qrSign`. The special forms are `quadratic_reciprocity_one_mod_four` and `quadratic_reciprocity_three_mod_four`.

<?decl jacobiSym.quadratic_reciprocity?>
:::

**Proposition (What the value tells).** If $(a/n) = -1$, then $a$ is not a square modulo $n$. If $n$ is prime, $(a/n) = 1$ implies that $a$ is a square modulo $n$.

*Proof.* If $a \equiv x^2 \pmod n$ with $\gcd(a, n) = 1$, then $a \equiv x^2 \pmod{p_i}$ for each $i$, so each factor is $1$ and $(a/n) = 1$. If $\gcd(a, n) > 1$, then $(a/n) = 0$. In both cases $(a/n) \neq -1$. The second claim is the meaning of the Legendre symbol. $\square$

::: mathlib
`ZMod.nonsquare_of_jacobiSym_eq_neg_one` · `Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol`

`jacobiSym a b = -1 → ¬IsSquare (a : ZMod b)`. For a prime `p`, `ZMod.nonsquare_iff_jacobiSym_eq_neg_one` is the equivalence and `ZMod.isSquare_of_jacobiSym_eq_one` the converse direction. The index of this edition has no declaration that turns `jacobiSym a b = 1` into a square for composite `b`, and the counterexample below shows why.

<?decl ZMod.nonsquare_of_jacobiSym_eq_neg_one?>
:::

**The algorithm.** To compute $(a/n)$ for odd $n > 0$:

1. Replace $a$ by $a \bmod n$. If $a = 0$, the result is $1$ if $n = 1$ and $0$ otherwise.
2. While $a$ is even, replace $a$ by $a/2$ and multiply the sign by $\chi_8(n)$.
3. Now $a$ is odd. Swap: $(a/n) = (-1)^{\varepsilon(a)\varepsilon(n)} (n/a)$, and go to step 1 with $(n, a)$ in place of $(a, n)$.

Each swap is a step of the Euclidean algorithm on $(n, a)$, so the number of steps is $O(\log n)$ and no factoring occurs. The method also decides whether $\gcd(a, n) = 1$: a result $0$ means $\gcd(a, n) > 1$.

### Examples

**Example (The symbol $(1001/9907)$).** The number $9907$ is prime: it has no prime factor up to $\sqrt{9907} < 100$. Without factoring $1001$:

- $1001 \equiv 1 \pmod 4$, so $(1001/9907) = (9907/1001) = (898/1001)$, since $9907 = 9 \cdot 1001 + 898$.
- $898 = 2 \cdot 449$ and $1001 \equiv 1 \pmod 8$, so $(898/1001) = (449/1001)$.
- $449 \equiv 1 \pmod 4$: $(449/1001) = (1001/449) = (103/449)$.
- $449 \equiv 1 \pmod 4$: $(103/449) = (449/103) = (37/103)$.
- $37 \equiv 1 \pmod 4$: $(37/103) = (103/37) = (29/37) = (37/29) = (8/29)$.
- $(8/29) = (2/29)^3 = (2/29) = -1$, since $29 \equiv 5 \pmod 8$.

So $(1001/9907) = -1$ and $x^2 \equiv 1001 \pmod{9907}$ has no solution. The intermediate symbols $(449/1001)$ and $(1001/449)$ have composite denominators, so they are Jacobi symbols and not Legendre symbols. A check by factoring: $1001 = 7 \cdot 11 \cdot 13$, and the product $(7/9907)(11/9907)(13/9907)$ gives the same value.

**Counterexample (The value $1$ does not give a square).** $(2/15) = (2/3)(2/5) = (-1)(-1) = 1$. But the squares modulo $15$ are $0, 1, 4, 6, 9, 10$, and $2$ is not among them. Indeed $2$ is not a square modulo $3$, so it is not a square modulo $15$. The symbol $1$ hides two factors $-1$.

**Example (A Gaussian prime).** The prime $7$ satisfies $7 \equiv 3 \pmod 4$, so $7$ stays prime in $\mathbb{Z}[i]$. The prime $13 \equiv 1 \pmod 4$ splits: $13 = (3 + 2i)(3 - 2i)$.

### The library around it

The file `Zsqrtd/QuadraticReciprocity.lean` applies the results of this chapter to the Gaussian integers of Volume 6, Chapter 6. A prime $p \equiv 3 \pmod 4$ stays prime in $\mathbb{Z}[i]$: a factor $\alpha$ would have $N(\alpha) = p$, a sum of two squares, which is impossible modulo $4$.

::: mathlib
`GaussianInt.prime_of_nat_prime_of_mod_four_eq_three` · `Mathlib.NumberTheory.Zsqrtd.QuadraticReciprocity`

`p % 4 = 3 → Prime (p : ℤ[i])`, for `[Fact p.Prime]`. The converse is `GaussianInt.mod_four_eq_three_of_nat_prime_of_prime`, and Volume 6, Chapter 6 gives the equivalence of the two.

<?decl GaussianInt.prime_of_nat_prime_of_mod_four_eq_three?>
:::

The reduction of the denominator modulo $4|a|$ is `jacobiSym.mod_right`.

Common errors of a learner:

- `jacobiSym a b` takes `a : ℤ` and `b : ℕ`. Reciprocity takes `a b : ℕ`, cast to `ℤ` in the numerator.
- For even `b` the value of `jacobiSym` has no meaning as a symbol; the theorems carry `Odd b`.
- `jacobiSym a b = 1` does not give `IsSquare (a : ZMod b)`.

### Exercises

1. (A) Compute $(1001/9907)$ again by factoring $1001$ and applying quadratic reciprocity to each prime factor.
2. (A) Compute $(2/21)$, $(5/21)$ and $(-1/21)$, and list the squares modulo $21$. Hint: $21 = 3 \cdot 7$.
3. (A) Compute $(3083/3911)$ with the algorithm. Hint: the first step is a swap with $3911 \equiv 3$ and $3083 \equiv 3 \pmod 4$.
4. (B) Show that for odd positive $n$, $(a/n) = (a/m)$ when $n \equiv m \pmod{4a}$ and $a > 0$. Hint: apply reciprocity twice, after removing the factors $2$ of $a$.
5. (B) Show that if $(a/n) = -1$ for odd $n$, then some prime $p \mid n$ has $(a/p) = -1$, and that $x^2 - a y^2 \equiv 0 \pmod p$ forces $p \mid x$ and $p \mid y$.
6. (B) For odd composite $n$, show that exactly half of the units modulo $n$ have $(a/n) = 1$ if $n$ is not a square. Hint: for a prime $p \mid n$ with odd exponent, use the Chinese remainder theorem to find a unit $b$ with $(b/n) = -1$.
7. (C) The Solovay-Strassen test calls an odd composite $n$ an Euler pseudoprime to the base $a$ if $a^{(n-1)/2} \equiv (a/n) \not\equiv 0 \pmod n$. Show that $561$ is a Carmichael number (Chapter 1, Section 2) and an Euler pseudoprime to the base $2$, but not to the base $5$. Hint: $(5/561) = 1$ and $5^{280} \equiv 67 \pmod{561}$.
8. (C) Let $k \geq 2$ and $F_k = 2^{2^k} + 1$. Show that $(5/F_k) = -1$, and deduce that $5$ can replace $3$ in Pepin's test: $F_k$ is prime if and only if $5^{(F_k - 1)/2} \equiv -1 \pmod{F_k}$. Hint: $F_k \equiv 2 \pmod 5$.

### Notes and history

Jacobi introduced the symbol in 1837. Its use as an algorithm without factoring belongs to the modern theory of computation, and it is the basis of the Solovay-Strassen primality test of 1977. A standard reference is Ireland and Rosen, *A Classical Introduction to Modern Number Theory*, Chapter 5, and Cohen, *A Course in Computational Algebraic Number Theory*, Section 1.4, for the algorithm.

### Reference

<?reference?>
