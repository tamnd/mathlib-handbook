---
title: Dirichlet's theorem on primes in progressions
kind: theory
modules:
  - Mathlib.NumberTheory.LSeries.PrimesInAP
  - Mathlib.Analysis.SumOverResidueClass
  - Mathlib.NumberTheory.LSeries.Dirichlet
  - Mathlib.NumberTheory.LSeries.WeakPNT
explains:
  E3: [ArithmeticFunction.vonMangoldt.residueClass, ArithmeticFunction.vonMangoldt.not_summable_residueClass_prime_div, Nat.infinite_setOfPred_prime_and_modEq, summable_indicator_mod_iff]
  E2: [ArithmeticFunction.vonMangoldt.residueClass_eq, ArithmeticFunction.vonMangoldt.residueClass_le, ArithmeticFunction.vonMangoldt.LSeries_residueClass_eq, ArithmeticFunction.vonMangoldt.LSeries_residueClass_lower_bound, ArithmeticFunction.vonMangoldt.LFunctionResidueClassAux, ArithmeticFunction.vonMangoldt.continuousOn_LFunctionResidueClassAux, ArithmeticFunction.vonMangoldt.summable_residueClass_non_primes_div, DirichletCharacter.LSeries_twist_vonMangoldt_eq, ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div, Nat.infinite_setOfPred_prime_and_eq_mod, Nat.forall_exists_prime_gt_and_modEq, Nat.frequently_atTop_prime_and_modEq, Nat.isEquivalent_card_prime_modEq, Chebyshev.tendsto_sum_log_prime_modEq_div_atTop, not_summable_of_antitone_of_neg, not_summable_indicator_mod_of_antitone_of_neg, summable_indicator_mod_iff_summable_indicator_mod, Finset.sum_indicator_mod]
  E1: auto
families: [ArithmeticFunction.vonMangoldt.residueClass_*]
requires: [V12.C02, V12.C06, V15.C01, V15.C05, V15.C07]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Dirichlet's theorem on primes in progressions

### Overview

Dirichlet's theorem says: if $q \ge 1$ and $\gcd(a, q) = 1$, there are infinitely many primes $p \equiv a \pmod q$. Section 1 proved the case $a = 1$ with cyclotomic polynomials. The general case needs the characters and L-series of Chapter 6. This section gives the proof as Mathlib has it. The orthogonality of characters isolates one residue class. The L-series of the isolated von Mangoldt function has a pole at $s = 1$, because $L(\chi, 1) \ne 0$ for $\chi \ne 1$. A pole forces the divergence of $\sum_{p \equiv a}\log p/p$, so the set of these primes is infinite.

A short independent topic comes first: for a decreasing function $f$, the sum of $f$ over one residue class converges if and only if the full sum converges.

### Definitions

**Definition (Residue class part of Λ).** For $q \ge 1$ and $a \in \mathbb{Z}/q$, let $\Lambda_a(n) = \Lambda(n)$ if $n \equiv a \pmod q$ and $\Lambda_a(n) = 0$ otherwise. So $\Lambda_a(n) = \log p$ when $n = p^k$ with $p^k \equiv a$, and $0$ for other $n$.

::: mathlib
`ArithmeticFunction.vonMangoldt.residueClass` · `Mathlib.NumberTheory.LSeries.PrimesInAP`

`residueClass a : ℕ → ℝ` is the indicator of `{n | (n : ZMod q) = a}` times `Λ`. It satisfies `0 ≤ residueClass a n` and `residueClass_le : residueClass a n ≤ Λ n`.

<?decl ArithmeticFunction.vonMangoldt.residueClass?>
:::

**Definition (Indicator of a residue class).** For $f : \mathbb{N} \to R$ and $k \in \mathbb{Z}/m$, the function $\mathbf{1}_k f$ is $f(n)$ when $n \equiv k \pmod m$ and $0$ otherwise. Then $f = \sum_{k \in \mathbb{Z}/m}\mathbf{1}_k f$.

::: mathlib
`Set.indicator` · `Mathlib.Algebra.Notation.Indicator`

The function `{n : ℕ | (n : ZMod m) = k}.indicator f`. The decomposition is `Finset.sum_indicator_mod`.

<?decl Set.indicator?>
:::

### Theorems and proofs

**Theorem (Sums over a residue class).** Let $m \ge 1$, $k \in \mathbb{Z}/m$, and $f : \mathbb{N} \to \mathbb{R}$ antitone. Then $\sum_n\mathbf{1}_k f(n)$ converges if and only if $\sum_n f(n)$ converges.

*Proof.* First, if $f(n_0) < 0$ for some $n_0$, then $f(n) \le f(n_0) < 0$ for all $n \ge n_0$, and in particular for the infinitely many $n \ge n_0$ in the class $k$. The terms do not tend to $0$, so neither sum converges. So suppose $f \ge 0$.

If $\sum f$ converges, then $\sum\mathbf{1}_k f$ converges, since $0 \le \mathbf{1}_k f \le f$.

Conversely, suppose $\sum\mathbf{1}_k f$ converges and let $l \in \mathbb{Z}/m$. Let $r \in \{0, \dots, m-1\}$ with $r \equiv l - k$. For $n \ge m$ with $n \equiv l$, the number $n - r$ is in the class $k$, and $f(n) \le f(n - r)$ since $f$ is antitone. The map $n \mapsto n - r$ is injective, so the tail $\sum_{n\ge m}\mathbf{1}_l f(n)$ is at most $\sum_n\mathbf{1}_k f(n)$. All terms are nonnegative, so $\sum\mathbf{1}_l f$ converges. Then $\sum f = \sum_{l}\sum\mathbf{1}_l f$ is a finite sum of convergent series. $\square$

::: mathlib
`summable_indicator_mod_iff` · `Mathlib.Analysis.SumOverResidueClass`

`Antitone f → ∀ k : ZMod m, Summable ({n | (n : ZMod m) = k}.indicator f) ↔ Summable f`. The negative case is `not_summable_of_antitone_of_neg` and `not_summable_indicator_mod_of_antitone_of_neg`. The comparison of two classes is `summable_indicator_mod_iff_summable_indicator_mod`.

<?decl summable_indicator_mod_iff?>
:::

**Lemma (Isolating a residue class).** Let $q \ge 1$ and $a \in (\mathbb{Z}/q)^\times$. Then for all $n$,
$$\Lambda_a(n) = \frac{1}{\varphi(q)}\sum_{\chi \bmod q}\overline{\chi(a)}\,\chi(n)\,\Lambda(n),$$
where the sum runs over the Dirichlet characters $\chi : \mathbb{Z}/q \to \mathbb{C}$.

*Proof.* By the orthogonality relation of Section 6.1, $\sum_\chi\chi(a)^{-1}\chi(n) = \varphi(q)$ if $n \equiv a$ and $0$ otherwise. This holds for $n$ prime to $q$, and also for $n$ not prime to $q$: then $\chi(n) = 0$ for all $\chi$, and $n \not\equiv a$ since $a$ is a unit. For $|z| = 1$, $z^{-1} = \bar z$. Multiply by $\Lambda(n)/\varphi(q)$. $\square$

::: mathlib
`ArithmeticFunction.vonMangoldt.residueClass_eq` · `Mathlib.NumberTheory.LSeries.PrimesInAP`

`IsUnit a → (fun n ↦ (residueClass a n : ℂ)) = (q.totient : ℂ)⁻¹ • ∑ χ, χ a⁻¹ • fun n ↦ χ n * Λ n`. Mathlib writes $\chi(a^{-1})$, which equals $\overline{\chi(a)}$.

<?decl ArithmeticFunction.vonMangoldt.residueClass_eq?>
:::

**Proposition (The L-series of Λ_a).** For $\operatorname{Re}s > 1$,
$$\sum_{n\ge1}\frac{\Lambda_a(n)}{n^s} = -\frac{1}{\varphi(q)}\sum_\chi\overline{\chi(a)}\,\frac{L'(\chi, s)}{L(\chi, s)}.$$

*Proof.* By the lemma, it is enough to show $\sum_n\chi(n)\Lambda(n)n^{-s} = -L'(\chi, s)/L(\chi, s)$. In Chapter 2, $\Lambda * 1 = \log$. Since $\chi$ is completely multiplicative, $\chi(d)\chi(n/d) = \chi(n)$, so $(\chi\Lambda) * \chi = \chi\log$. All three L-series converge absolutely for $\operatorname{Re}s > 1$, so by Section 6.2, $L(\chi\Lambda, s)L(\chi, s) = L(\chi\log, s)$. Termwise differentiation of $\sum\chi(n)n^{-s}$ gives $L(\chi\log, s) = -L'(\chi, s)$. Finally $L(\chi, s) \ne 0$ for $\operatorname{Re}s > 1$ (Section 6.2). $\square$

::: mathlib
`DirichletCharacter.LSeries_twist_vonMangoldt_eq` · `Mathlib.NumberTheory.LSeries.Dirichlet`

`1 < s.re → LSeries (χ · * Λ ·) s = -deriv (LSeries (χ ·)) s / LSeries (χ ·) s`. The case $\chi = 1$, $q = 1$ is `ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div`: $\sum\Lambda(n)n^{-s} = -\zeta'(s)/\zeta(s)$. The combination is `ArithmeticFunction.vonMangoldt.LSeries_residueClass_eq`.

<?decl DirichletCharacter.LSeries_twist_vonMangoldt_eq?>
:::

**Theorem (Pole at s = 1).** Let $a \in (\mathbb{Z}/q)^\times$. There is $C$ such that for real $x \in (1, 2]$,
$$\sum_{n\ge1}\frac{\Lambda_a(n)}{n^x} \ge \frac{1}{\varphi(q)(x - 1)} - C.$$

*Proof.* Split the sum of the proposition into the trivial character $\chi_0$ and the others.

For $\chi \ne \chi_0$, the function $L(\chi, s)$ extends to an entire function (Section 6.2, cited), and $L(\chi, 1) \ne 0$ (Section 6.2, cited). So $L'(\chi, s)/L(\chi, s)$ is continuous on a neighbourhood of $s = 1$, in particular bounded on $[1, 2]$.

For $\chi_0$, $L(\chi_0, s) = \zeta(s)\prod_{p \mid q}(1 - p^{-s})$ by the Euler products of Section 6.2. The finite product $P(s)$ is holomorphic and nonzero near $s = 1$, so $L'/L(\chi_0) = \zeta'/\zeta + P'/P$, with $P'/P$ bounded on $[1, 2]$. Since $\zeta(s) = \frac{1}{s-1} + h(s)$ with $h$ entire, $-\zeta'(s)/\zeta(s) = \frac{1}{s - 1} + g(s)$ with $g$ continuous on $[1, 2]$.

With $\overline{\chi_0(a)} = 1$, the sum is $\frac{1}{\varphi(q)(x - 1)}$ plus a function that is bounded on $(1, 2]$. $\square$

::: mathlib
`ArithmeticFunction.vonMangoldt.LSeries_residueClass_lower_bound` · `Mathlib.NumberTheory.LSeries.PrimesInAP`

`IsUnit a → ∃ C, ∀ {x : ℝ}, x ∈ Set.Ioc 1 2 → (q.totient : ℝ)⁻¹ / (x - 1) - C ≤ ∑' n, residueClass a n / n ^ x`. The proof uses the auxiliary function `LFunctionResidueClassAux a`, the L-series of $\Lambda_a$ minus $\varphi(q)^{-1}/(s - 1)$. Its continuity on $\operatorname{Re}s \ge 1$ is `continuousOn_LFunctionResidueClassAux`; it uses `DirichletCharacter.LFunction_ne_zero_of_one_le_re` of Section 6.2 on the whole line.

<?decl ArithmeticFunction.vonMangoldt.LSeries_residueClass_lower_bound?>
:::

**Theorem (Dirichlet).** Let $q \ge 1$ and $\gcd(a, q) = 1$. Then $\sum_{p \equiv a}\frac{\log p}{p}$ diverges, and there are infinitely many primes $p \equiv a \pmod q$.

*Proof.* The prime powers $p^k$ with $k \ge 2$ give a convergent part:
$$\sum_{p}\sum_{k\ge2}\frac{\log p}{p^k} = \sum_p\frac{\log p}{p(p - 1)} \le \sum_{n\ge2}\frac{\log n}{n(n-1)} < \infty.$$
Suppose that $\sum_{p\equiv a}\log p/p = S$ converges. Then $\sum_n\Lambda_a(n)/n \le S + S'$ with $S'$ the sum above, and for $x > 1$, $\sum_n\Lambda_a(n)/n^x \le \sum_n\Lambda_a(n)/n \le S + S'$. This contradicts the pole theorem as $x \to 1^+$. A finite set of primes gives a finite sum, so the set of primes $p \equiv a$ is infinite. $\square$

::: mathlib
`ArithmeticFunction.vonMangoldt.not_summable_residueClass_prime_div`, `Nat.infinite_setOfPred_prime_and_modEq` · `Mathlib.NumberTheory.LSeries.PrimesInAP`

`IsUnit a → ¬Summable fun n ↦ (if n.Prime then residueClass a n else 0) / n`, with the convergent part `summable_residueClass_non_primes_div`. The final forms are `Nat.infinite_setOfPred_prime_and_modEq : q ≠ 0 → a.Coprime q → {p | p.Prime ∧ p ≡ a [MOD q]}.Infinite`, its `ZMod` version `Nat.infinite_setOfPred_prime_and_eq_mod`, and `Nat.forall_exists_prime_gt_and_modEq : ∃ p > n, p.Prime ∧ p ≡ a [MOD q]`.

<?decl Nat.infinite_setOfPred_prime_and_modEq?>
:::

**Theorem (Prime number theorem in progressions, by citation).** For $\gcd(a, q) = 1$,
$$\#\{p \le x : p \equiv a \pmod q\} \sim \frac{1}{\varphi(q)}\,\frac{x}{\log x}.$$

The proof applies the theorem of Wiener and Ikehara of Section 2 to $f = \Lambda_a$ with $A = 1/\varphi(q)$: the function $G$ is `LFunctionResidueClassAux a`, continuous on $\operatorname{Re}s \ge 1$ because no $L(\chi, s)$ vanishes there. This gives $\sum_{n \le x}\Lambda_a(n) \sim x/\varphi(q)$. The passage to the count of primes is the argument of Section 2 for $\theta$ and $\pi$, restricted to one class.

::: mathlib
`Nat.isEquivalent_card_prime_modEq` · `Mathlib.NumberTheory.LSeries.WeakPNT`

`a.Coprime q → IsEquivalent atTop (fun x ↦ #{p ∈ Ioc 0 ⌊x⌋₊ | p.Prime ∧ p ≡ a [MOD q]}) (fun x ↦ x / (q.totient * log x))`. The form for $\sum\log p$ is `Chebyshev.tendsto_sum_log_prime_modEq_div_atTop`.

<?decl Nat.isEquivalent_card_prime_modEq?>
:::

### Examples

**Example (The modulus 4).** The characters mod $4$ are $\chi_0$ and $\chi_{-4}$, with $\chi_{-4}(n) = (-1)^{(n-1)/2}$ for odd $n$. The lemma gives
$$\Lambda_1 = \tfrac12(\chi_0 + \chi_{-4})\Lambda, \qquad \Lambda_3 = \tfrac12(\chi_0 - \chi_{-4})\Lambda.$$
For $n = 9$, $\Lambda(9) = \log 3$, $\chi_0(9) = \chi_{-4}(9) = 1$, so $\Lambda_1(9) = \log 3$ and $\Lambda_3(9) = 0$, as $9 \equiv 1 \pmod 4$. Here $L(\chi_{-4}, 1) = 1 - \frac13 + \frac15 - \cdots = \frac\pi4 \ne 0$, the series of Leibniz.

**Example (Counting by class).** Up to $1000$ there are $168$ primes. Without $2$ and $5$, the $166$ others split mod $10$ into $40$ primes $\equiv 1$, $42$ primes $\equiv 3$, $46$ primes $\equiv 7$ and $38$ primes $\equiv 9$, all near $166/4 = 41.5$, as the theorem in progressions predicts with $\varphi(10) = 4$.

**Counterexample (The unit hypothesis).** For $q = 4$ and $a = 2$, the only prime $p \equiv 2 \pmod 4$ is $2$. The lemma fails here: for $n = 2$ the right side is $0$, since $\chi(2) = 0$ for all $\chi$ mod $4$, but the left side $\Lambda_2(2) = \log 2$.

**Counterexample (Antitone is needed).** Let $f(n) = 1/n$ for odd $n$ and $f(n) = 0$ for even $n$. Then $\mathbf{1}_0 f = 0$ with $m = 2$ is summable, but $\sum f$ diverges. The function $f$ is not antitone.

### The library around it

`Mathlib.Analysis.SumOverResidueClass` also has `Nat.sumByResidueClasses`, which writes $\sum f$ as the sum over the classes. The file `Mathlib.NumberTheory.LSeries.PrimesInAP` builds on `Mathlib.NumberTheory.LSeries.Nonvanishing` for $L(\chi, s) \ne 0$ on $\operatorname{Re}s \ge 1$, and on `Mathlib.NumberTheory.LSeries.DirichletContinuation` for the continuation. The orthogonality is `DirichletCharacter.sum_char_inv_mul_char_eq` of Section 6.1.

Common errors of a learner:

- The residue `a` lives in `ZMod q` for `residueClass`, but in `ℕ` for `Nat.infinite_setOfPred_prime_and_modEq`. The hypotheses are `IsUnit a` and `a.Coprime q`, linked by `ZMod.isUnit_iff_coprime`.
- Dirichlet's theorem with `q = 0` is false in Mathlib's form, since `ZMod 0 = ℤ`. Each statement has `q ≠ 0` or `[NeZero q]`.

### Exercises

1. (A) Write $\Lambda_1$ and $\Lambda_2$ for $q = 3$ in terms of $\chi_0$ and the nontrivial character mod $3$, and check the formula at $n = 4$ and $n = 8$.
2. (A) Show that $\sum_{n \equiv 1 \bmod 4}1/n$ diverges, from the theorem on sums over a residue class.
3. (A) Show that there is a prime $p \equiv 7 \pmod{100}$ with $p > 10^6$, citing the Mathlib statement.
4. (B) Prove that $\sum_p\sum_{k \ge 2}\log p/p^k$ converges, and bound it by $\sum_{n\ge2}\log n/(n(n-1))$.
5. (B) Show that for each $q \ge 3$ and each $N$ there is a prime $p \equiv -1 \pmod q$ with $p > N$, and that for $q = 3, 4, 6$ this case has a proof in the style of Euclid.
6. (B) For $q = 8$, list the four characters and show that $L(\chi, 1) \ne 0$ for the character $\chi(n) = (-1)^{(n^2-1)/8}$ by grouping the terms of the series in blocks of $8$.
7. (C) Let $\ell$ be a prime. Show that there are infinitely many primes $p$ with $p \equiv 1 \pmod \ell$ and $p \not\equiv 1 \pmod{\ell^2}$, using Dirichlet's theorem with the modulus $\ell^2$.

### Notes and history

Dirichlet proved the theorem in 1837. He introduced the characters for this proof and showed $L(\chi, 1) \ne 0$; for real characters he used the class number formula. Section 1 gives the special case $a = 1$. The prime number theorem in progressions is due to de la Vallée Poussin, 1896. A reference is Apostol, *Introduction to Analytic Number Theory*, Chapter 7, and Serre, *A Course in Arithmetic*, Chapter VI.

### Reference

<?reference?>
