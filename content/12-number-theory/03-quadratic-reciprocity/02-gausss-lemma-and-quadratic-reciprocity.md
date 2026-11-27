---
title: Gauss's lemma and quadratic reciprocity
kind: theory
modules:
  - Mathlib.NumberTheory.LegendreSymbol.GaussEisensteinLemmas
  - Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
  - Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.GaussSum
explains:
  E3: [ZMod.gauss_lemma, ZMod.eisenstein_lemma, legendreSym.quadratic_reciprocity, legendreSym.at_two]
  E2: [ZMod.sum_mul_div_add_sum_mul_div_eq_mul, "legendreSym.quadratic_reciprocity'", legendreSym.quadratic_reciprocity_one_mod_four, legendreSym.quadratic_reciprocity_three_mod_four, legendreSym.at_neg_two, ZMod.exists_sq_eq_two_iff, ZMod.exists_sq_eq_neg_two_iff, ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one, ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_three, quadraticChar_two, quadraticChar_neg_two, quadraticChar_odd_prime, FiniteField.isSquare_two_iff, ZMod.χ₈_nat_eq_if_mod_eight]
  E1: auto
families: []
requires: [V02.C06, V05.C03, V06.C04]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Gauss's lemma and quadratic reciprocity

### Overview

Euler's criterion of Section 1 decides whether $a$ is a square modulo $p$, but it needs the power $a^{(p-1)/2}$. The law of quadratic reciprocity relates the two questions "is $q$ a square modulo $p$" and "is $p$ a square modulo $q$" for distinct odd primes $p$ and $q$: the answers are the same unless $p \equiv q \equiv 3 \pmod 4$, and then they are opposite. Together with the values $(-1/p)$ and $(2/p)$, this computes any Legendre symbol by repeated reduction, as a Euclidean algorithm.

This section proves the law by the route of Gauss and Eisenstein. Gauss's lemma expresses $(a/p)$ as a sign that counts residues in the upper half of $\{1, \dots, p - 1\}$. Eisenstein's lemma turns the count into a sum of integer parts, and a count of lattice points in a rectangle proves the law. Mathlib proves the law with Gauss sums instead; the last box describes that route. Throughout, $p$ and $q$ are odd primes and $h_p = (p-1)/2$.

### Definitions

**Definition (Half system and the Gauss count).** Let $p \nmid a$. For $1 \leq x \leq h_p$, let $r(ax)$ be the remainder of $ax$ modulo $p$, in $\{1, \dots, p - 1\}$. The Gauss count of $a$ is
$$\mu_p(a) = \#\{ x : 1 \leq x \leq h_p,\ r(ax) > h_p \}.$$

**Definition (The characters $\chi_8$ and $\chi_8'$).** For odd $n$, $\chi_8(n) = 1$ if $n \equiv \pm 1 \pmod 8$ and $-1$ if $n \equiv \pm 3 \pmod 8$; $\chi_8'(n) = 1$ if $n \equiv 1, 3 \pmod 8$ and $-1$ if $n \equiv 5, 7 \pmod 8$. Both are $0$ on even $n$, and $\chi_8' = \chi_4 \chi_8$.

::: mathlib
`ZMod.χ₈_nat_eq_if_mod_eight` · `Mathlib.NumberTheory.LegendreSymbol.ZModChar`

The value of `χ₈ : MulChar (ZMod 8) ℤ` on a natural number, as an `if` on `n % 8`. The companion for `χ₈'` is `ZMod.χ₈'_nat_eq_if_mod_eight`.

<?decl ZMod.χ₈_nat_eq_if_mod_eight?>
:::

### Theorems and proofs

**Theorem (Gauss's lemma).** If $p \nmid a$, then $(a/p) = (-1)^{\mu_p(a)}$.

*Proof.* For $1 \leq x \leq h_p$, put $\rho_x = r(ax)$ if $r(ax) \leq h_p$ and $\rho_x = p - r(ax)$ otherwise. Then $\rho_x \in \{1, \dots, h_p\}$ and $ax \equiv \pm \rho_x \pmod p$, with the sign $-$ exactly $\mu_p(a)$ times.

The $\rho_x$ are distinct. If $\rho_x = \rho_y$, then $ax \equiv \pm ay$, so $x \equiv \pm y \pmod p$ since $a$ is invertible. But $0 < x + y < p$ and $|x - y| < p$, so only $x = y$ is possible. So $\{\rho_1, \dots, \rho_{h_p}\} = \{1, \dots, h_p\}$. Multiply the congruences $ax \equiv \pm \rho_x$:
$$a^{h_p} \, h_p! \equiv (-1)^{\mu_p(a)} \, h_p! \pmod p.$$
Since $p \nmid h_p!$, $a^{h_p} \equiv (-1)^{\mu_p(a)}$, and Euler's criterion gives the claim. $\square$

::: mathlib
`ZMod.gauss_lemma` · `Mathlib.NumberTheory.LegendreSymbol.GaussEisensteinLemmas`

For `p ≠ 2` and `(a : ZMod p) ≠ 0`, `legendreSym p a = (-1) ^ #{x ∈ Finset.Ico 1 (p / 2).succ | p / 2 < (a * x).val}`. Here `(a * x).val` is the remainder in `ℕ`, and `Finset.Ico 1 (p / 2).succ` is $\{1, \dots, h_p\}$. The step $a^{h_p} = (-1)^{\mu}$ before Euler's criterion is `ZMod.gauss_lemma_aux`.

<?decl ZMod.gauss_lemma?>
:::

**Theorem (The second supplement).** $(2/p) = \chi_8(p) = (-1)^{(p^2 - 1)/8}$, and $(-2/p) = \chi_8'(p)$.

*Proof.* For $a = 2$ and $x \leq h_p$, $2x < p$, so $r(2x) = 2x$, and $\mu_p(2)$ is the number of $x \leq h_p$ with $2x > h_p$, that is $h_p - \lfloor h_p / 2 \rfloor$. Write $p = 8k + j$:

- $j = 1$: $h_p = 4k$, $\mu = 2k$, even.
- $j = 3$: $h_p = 4k + 1$, $\mu = 2k + 1$, odd.
- $j = 5$: $h_p = 4k + 2$, $\mu = 2k + 1$, odd.
- $j = 7$: $h_p = 4k + 3$, $\mu = 2k + 2$, even.

So $(2/p) = 1$ exactly for $p \equiv \pm 1 \pmod 8$. The exponent $(p^2 - 1)/8$ has the same parity in the four cases. Finally $(-2/p) = (-1/p)(2/p) = \chi_4(p)\chi_8(p) = \chi_8'(p)$. $\square$

::: mathlib
`legendreSym.at_two` · `Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity`

For `p ≠ 2`, `legendreSym p 2 = χ₈ p`. The forms with squares are `ZMod.exists_sq_eq_two_iff : IsSquare (2 : ZMod p) ↔ p % 8 = 1 ∨ p % 8 = 7` and, for $-2$, `legendreSym.at_neg_two` and `ZMod.exists_sq_eq_neg_two_iff`. In Mathlib they come from `quadraticChar_two` and `quadraticChar_neg_two`, valid in any finite field of odd characteristic, through `FiniteField.isSquare_two_iff`.

<?decl legendreSym.at_two?>
:::

**Theorem (Eisenstein's lemma).** If $a$ is odd and $p \nmid a$, then
$$\mu_p(a) \equiv \sum_{x=1}^{h_p} \left\lfloor \frac{ax}{p} \right\rfloor \pmod 2, \qquad \text{so} \qquad \left(\frac{a}{p}\right) = (-1)^{\sum_{x=1}^{h_p} \lfloor ax/p \rfloor}.$$

*Proof.* Write $ax = p \lfloor ax/p \rfloor + r(ax)$. Let $s_1, \dots, s_k$ be the remainders $\leq h_p$ and $u_1, \dots, u_\mu$ those $> h_p$, with $\mu = \mu_p(a)$. By the proof of Gauss's lemma, the numbers $s_i$ and $p - u_j$ are $1, \dots, h_p$ in some order. Put $S = \sum_x x$, $T = \sum_x \lfloor ax/p \rfloor$ and $U = \sum_j u_j$. Then
$$S = \sum_i s_i + \sum_j (p - u_j) = \sum_i s_i + \mu p - U, \qquad aS = pT + \sum_i s_i + U.$$
Subtract: $(a - 1) S = pT - \mu p + 2U$. Modulo $2$, the left side is $0$ because $a$ is odd, and $p \equiv 1$, so $0 \equiv T - \mu$. $\square$

::: mathlib
`ZMod.eisenstein_lemma` · `Mathlib.NumberTheory.LegendreSymbol.GaussEisensteinLemmas`

For `p ≠ 2`, odd `a : ℕ` and `(a : ZMod p) ≠ 0`, `legendreSym p a = (-1) ^ ∑ x ∈ Finset.Ico 1 (p / 2).succ, x * a / p`. The argument is a natural number, so a negative `a` needs `legendreSym.mod` first. The parity statement is `ZMod.eisenstein_lemma_aux`.

<?decl ZMod.eisenstein_lemma?>
:::

**Lemma (Lattice points).** For distinct odd primes $p$ and $q$,
$$\sum_{x=1}^{h_p} \left\lfloor \frac{qx}{p} \right\rfloor + \sum_{y=1}^{h_q} \left\lfloor \frac{py}{q} \right\rfloor = h_p h_q .$$

*Proof.* Count the $h_p h_q$ integer points $(x, y)$ with $1 \leq x \leq h_p$ and $1 \leq y \leq h_q$. None lies on the line $py = qx$: that would force $p \mid x$, but $0 < x < p$. For a fixed $x$, the points below the line have $1 \leq y < qx/p$, and there are $\lfloor qx/p \rfloor$ of them; all lie in the rectangle, because $qx/p \leq q h_p / p < q/2$ gives $\lfloor qx/p \rfloor \leq h_q$. So the points below the line number the first sum. In the same way, the points above the line number the second sum. $\square$

::: mathlib
`ZMod.sum_mul_div_add_sum_mul_div_eq_mul` · `Mathlib.NumberTheory.LegendreSymbol.GaussEisensteinLemmas`

The count, for `p` prime and `(q : ZMod p) ≠ 0`, with `p / 2 * (q / 2)` on the right. The proof in Mathlib splits the product of two `Finset.Ico` sets by the sign of $qx - py$, as above.

<?decl ZMod.sum_mul_div_add_sum_mul_div_eq_mul?>
:::

**Theorem (Quadratic reciprocity).** For distinct odd primes $p$ and $q$,
$$\left(\frac{p}{q}\right)\left(\frac{q}{p}\right) = (-1)^{\frac{p-1}{2}\cdot\frac{q-1}{2}}.$$
So $(p/q) = (q/p)$ if $p \equiv 1$ or $q \equiv 1 \pmod 4$, and $(p/q) = -(q/p)$ if $p \equiv q \equiv 3 \pmod 4$.

*Proof.* Since $q$ is odd and $p \nmid q$, Eisenstein's lemma gives $(q/p) = (-1)^{\sum_x \lfloor qx/p \rfloor}$, and in the same way $(p/q) = (-1)^{\sum_y \lfloor py/q \rfloor}$. Multiply and use the lemma on lattice points. The exponent $h_p h_q$ is odd exactly when both $h_p$ and $h_q$ are odd, that is $p \equiv q \equiv 3 \pmod 4$. $\square$

**Corollary.** $(-3/p) = 1$ if and only if $p \equiv 1 \pmod 3$, for a prime $p > 3$.

*Proof.* $(-3/p) = (-1/p)(3/p) = (-1)^{h_p} \cdot (-1)^{h_p}(p/3) = (p/3)$, and $(p/3) = 1$ exactly for $p \equiv 1 \pmod 3$. $\square$

::: mathlib
`legendreSym.quadratic_reciprocity` · `Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity`

`legendreSym q p * legendreSym p q = (-1) ^ (p / 2 * (q / 2))` for `p ≠ 2`, `q ≠ 2`, `p ≠ q`, with `p q : ℕ` cast to `ℤ`. The form `quadratic_reciprocity'` solves for `legendreSym q p` and drops `p ≠ q`; the two special forms are `quadratic_reciprocity_one_mod_four` and `quadratic_reciprocity_three_mod_four`. The statements with squares are `ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one` and `ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_three`.

<?decl legendreSym.quadratic_reciprocity?>
:::

::: mathlib
`quadraticChar_odd_prime` · `Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.GaussSum`

The route of Mathlib. For a finite field $F$ of odd characteristic $\neq p$, the quadratic character of $F$ at $p$ is the quadratic character of $\mathbb{Z}/p$ at $\chi_4(|F|)\,|F|$. The proof uses the quadratic Gauss sum $g = \sum_x \chi(x)\psi(x)$ with values in an extension field, the identity $g^2 = \chi(-1) p$, and the Frobenius map $g^{|F|} = \chi(|F|) g$. Quadratic reciprocity is the case $F = \mathbb{Z}/q$. Chapter 6 studies Gauss sums.

<?decl quadraticChar_odd_prime?>
:::

### Examples

**Example (The symbol $(2/7)$ by Gauss's lemma).** Here $h_7 = 3$ and $2 \cdot 1, 2 \cdot 2, 2 \cdot 3 = 2, 4, 6$. Two of them exceed $3$, so $(2/7) = (-1)^2 = 1$. Indeed $3^2 = 9 \equiv 2 \pmod 7$, and $7 \equiv -1 \pmod 8$.

**Example (The symbol $(3/101)$).** Since $101 \equiv 1 \pmod 4$, reciprocity gives $(3/101) = (101/3) = (2/3) = -1$, because $101 = 33 \cdot 3 + 2$ and $3 \equiv 3 \pmod 8$. So $x^2 \equiv 3 \pmod{101}$ has no solution.

**Example (A longer computation).** $219 = 3 \cdot 73$ and $383$ is prime with $383 \equiv 3 \pmod 4$. First $(3/383) = -(383/3) = -(2/3) = 1$. Next $73 \equiv 1 \pmod 4$, so $(73/383) = (383/73) = (18/73) = (2/73)(3/73)^2 = (2/73) = 1$, since $73 \equiv 1 \pmod 8$. So $(219/383) = 1$. The factorization of $219$ was needed at each step; the Jacobi symbol of Section 3 removes this need.

**Counterexample (The sign is needed).** For $p = 3$ and $q = 7$, both $\equiv 3 \pmod 4$: $(7/3) = (1/3) = 1$, but $(3/7) = -1$, since the squares modulo $7$ are $1, 2, 4$. So the rule $(p/q) = (q/p)$ fails without the sign. The rule needs both primes odd too: $(2/p)$ is not given by reciprocity but by the separate supplement.

### The library around it

`GaussEisensteinLemmas.lean` has the two lemmas and the lattice count, with the auxiliary bijection `ZMod.Ico_map_valMinAbs_natAbs_eq_Ico_map_id`, which is the step "the $\rho_x$ are $1, \dots, h_p$" of the proof. `QuadraticReciprocity.lean` has the law and the supplements for `legendreSym`. `QuadraticChar/GaussSum.lean` has the versions for any finite field: `quadraticChar_two`, `quadraticChar_neg_two`, `quadraticChar_odd_prime`, `FiniteField.isSquare_two_iff`, `FiniteField.isSquare_odd_prime_iff` and `quadraticChar_card_card`, the reciprocity between two finite fields.

Common errors of a learner:

- In `legendreSym.quadratic_reciprocity` the exponent is `p / 2 * (q / 2)`, with natural division, and the symbols are `legendreSym q p` and `legendreSym p q`, with `p` and `q` cast to `ℤ`.
- Reciprocity applies to a prime numerator. For $(219/383)$ the numerator must be factored first, or the Jacobi symbol used.

### Exercises

1. (A) Compute $(5/p)$ in terms of $p \bmod 5$, and list the primes $p < 100$ with $(5/p) = 1$.
2. (A) Compute $(3/p)$ in terms of $p \bmod 12$. Hint: the answer is $1$ for $p \equiv \pm 1 \pmod{12}$.
3. (A) Compute $(6/97)$, $(-5/41)$ and $(30/101)$.
4. (B) Find $\mu_{13}(5)$ directly and check Gauss's lemma against Euler's criterion.
5. (B) Show that a prime factor $p$ of $n^2 - 2$ with $n$ odd satisfies $p \equiv \pm 1 \pmod 8$, and deduce that there are infinitely many primes $p \equiv 7 \pmod 8$.
6. (B) Show that if $p \equiv 3 \pmod 4$ and $q = 2p + 1$ is prime, then $q \mid 2^p - 1$. Deduce that $23 \mid M_{11}$ and $47 \mid M_{23}$.
7. (C) Use reciprocity to prove the converse direction of Pepin's test of Chapter 1, Section 2: if $F_n$ is prime with $n \geq 1$, then $3^{(F_n - 1)/2} \equiv -1 \pmod{F_n}$.
8. (C) Prove the second supplement with Eisenstein's idea: show $\sum_{x=1}^{h_p} \lfloor 2x/p \rfloor = 0$ and adapt the proof of the lemma to $a = 2$ to get $\mu_p(2) \equiv (p^2 - 1)/8 \pmod 2$.

### Notes and history

Euler and Legendre stated the law of quadratic reciprocity, and Legendre gave an incomplete proof. Gauss gave the first complete proof in the *Disquisitiones Arithmeticae* (1801) and found several more later. Gauss's lemma is from his third proof. Eisenstein gave the proof with lattice points in 1844. A standard reference is Ireland and Rosen, *A Classical Introduction to Modern Number Theory*, Chapter 5, and Lemmermeyer, *Reciprocity Laws*, for the history of the many proofs.

### Reference

<?reference?>
