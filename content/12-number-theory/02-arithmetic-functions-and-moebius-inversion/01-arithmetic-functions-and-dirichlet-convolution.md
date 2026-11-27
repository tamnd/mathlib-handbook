---
title: Arithmetic functions and Dirichlet convolution
kind: theory
modules:
  - Mathlib.NumberTheory.ArithmeticFunction.Defs
  - Mathlib.NumberTheory.ArithmeticFunction.Zeta
  - Mathlib.NumberTheory.ArithmeticFunction.Misc
explains:
  E3: [ArithmeticFunction, ArithmeticFunction.IsMultiplicative, ArithmeticFunction.zeta, ArithmeticFunction.sigma, ArithmeticFunction.dirichletInverse]
  E2: [ArithmeticFunction.mul_apply, ArithmeticFunction.one_apply, ArithmeticFunction.IsMultiplicative.mul, ArithmeticFunction.IsMultiplicative.multiplicative_factorization, ArithmeticFunction.isUnit_iff_isUnit_apply_one, ArithmeticFunction.coe_zeta_mul_apply, ArithmeticFunction.isMultiplicative_sigma, ArithmeticFunction.zeta_mul_pow_eq_sigma, ArithmeticFunction.sigma_apply_prime_pow, ArithmeticFunction.sigma_zero_apply_prime_pow, Nat.card_divisors, ArithmeticFunction.cardFactors, ArithmeticFunction.cardDistinctFactors, ArithmeticFunction.self_mul_dirichletInverse]
  E1: auto
families: []
requires: [V12.C01, V02.C06, V03.C06]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Arithmetic functions and Dirichlet convolution

### Overview

The number of divisors $\tau(n)$, the sum of divisors $\sigma(n)$ and Euler's function $\varphi(n)$ are functions on the positive integers. Their values jump without order, but they have a common structure: each is a sum over the divisors of $n$, and each is determined by its values on prime powers. This section makes the structure precise. It defines the Dirichlet convolution $(f * g)(n) = \sum_{ab = n} f(a) g(b)$, proves that the arithmetic functions form a commutative ring under it, finds its units, and proves that the convolution of two multiplicative functions is multiplicative. The formulas for $\tau(n)$ and $\sigma(n)$ follow in a few lines. Section 2 uses the ring to invert $\zeta$ and to prove the Möbius inversion formula.

### Definitions

**Definition (Arithmetic function).** An arithmetic function with values in a commutative ring $R$ is a function $f : \mathbb{N}_{\geq 1} \to R$.

**Definition (Dirichlet convolution).** For arithmetic functions $f$ and $g$,
$$(f * g)(n) = \sum_{d \mid n} f(d)\, g(n/d) = \sum_{ab = n} f(a)\, g(b),$$
where the second sum runs over the pairs $(a, b)$ of positive integers with $ab = n$.

**Definition (Basic functions).** The unit function is $\varepsilon(1) = 1$ and $\varepsilon(n) = 0$ for $n > 1$. The constant function is $\zeta(n) = 1$. For $k \geq 0$, put $\mathrm{pow}_k(n) = n^k$, with $\mathrm{id} = \mathrm{pow}_1$, and $\sigma_k(n) = \sum_{d \mid n} d^k$. So $\tau = \sigma_0$ counts the divisors and $\sigma = \sigma_1$ adds them. Finally $\omega(n)$ is the number of distinct prime factors of $n$, and $\Omega(n)$ is the number of prime factors counted with multiplicity.

::: mathlib
`ArithmeticFunction` · `Mathlib.NumberTheory.ArithmeticFunction.Defs`

`ArithmeticFunction R` is the type of functions `ℕ → R` with `f 0 = 0`, for any `R` with a zero. So the domain is all of `ℕ`, and the value at `0` is fixed. This form lets the convolution use `Nat.divisorsAntidiagonal n`, which is empty for `n = 0`. Two functions are equal when they agree on every `n` (`ArithmeticFunction.ext`). The notation `ζ` needs `open scoped ArithmeticFunction.zeta`, and `σ`, `ω`, `Ω` need similar scoped openings.

<?decl ArithmeticFunction?>
:::

::: mathlib
`ArithmeticFunction.mul_apply` · `Mathlib.NumberTheory.ArithmeticFunction.Defs`

The convolution is the multiplication `f * g` of the type: `(f * g) n = ∑ x ∈ n.divisorsAntidiagonal, f x.1 * g x.2`. The unit is `1`, with `ArithmeticFunction.one_apply : 1 x = if x = 1 then 1 else 0`. The pointwise product is another operation, `ArithmeticFunction.pmul`.

<?decl ArithmeticFunction.mul_apply?>
:::

::: mathlib
`ArithmeticFunction.zeta` · `Mathlib.NumberTheory.ArithmeticFunction.Zeta`

`ζ : ArithmeticFunction ℕ` with `ζ x = if x = 0 then 0 else 1`. To use it in another ring, Mathlib casts it: `(ζ : ArithmeticFunction R)`. With the cast, `ArithmeticFunction.coe_zeta_mul_apply` gives `(↑ζ * f) x = ∑ i ∈ x.divisors, f i`.

<?decl ArithmeticFunction.zeta?>
:::

::: mathlib
`ArithmeticFunction.sigma` · `Mathlib.NumberTheory.ArithmeticFunction.Misc`

`σ k : ArithmeticFunction ℕ` with `σ k n = ∑ d ∈ n.divisors, d ^ k`. The number of divisors is `σ 0`, by `sigma_zero_apply`. The functions $\omega$ and $\Omega$ are `ArithmeticFunction.cardDistinctFactors` and `ArithmeticFunction.cardFactors`.

<?decl ArithmeticFunction.sigma?>
:::

**Definition (Multiplicative function).** An arithmetic function $f$ is multiplicative if $f(1) = 1$ and $f(mn) = f(m) f(n)$ for all coprime $m$ and $n$. It is completely multiplicative if $f(1) = 1$ and $f(mn) = f(m) f(n)$ for all $m$ and $n$.

::: mathlib
`ArithmeticFunction.IsMultiplicative` · `Mathlib.NumberTheory.ArithmeticFunction.Defs`

The predicate `f 1 = 1 ∧ ∀ {m n}, m.Coprime n → f (m * n) = f m * f n`, for `R` a monoid with zero. Use it with `IsMultiplicative.map_mul_of_coprime`. Mathlib has no separate predicate for complete multiplicativity on this type.

<?decl ArithmeticFunction.IsMultiplicative?>
:::

### Theorems and proofs

**Theorem (The ring of arithmetic functions).** Under pointwise addition and Dirichlet convolution, the arithmetic functions with values in $R$ form a commutative ring with unit $\varepsilon$.

*Proof.* Pointwise addition makes an abelian group. The convolution is commutative, because the map $(a, b) \mapsto (b, a)$ is a bijection of the pairs with $ab = n$. It is distributive over addition, because each term is linear in $f$ and in $g$. For associativity, expand both sides:
$$((f * g) * h)(n) = \sum_{cd = n} \Big( \sum_{ab = c} f(a) g(b) \Big) h(d) = \sum_{abd = n} f(a)\, g(b)\, h(d),$$
and in the same way $(f * (g * h))(n)$ is the sum of $f(a) g(b) h(d)$ over the triples with $abd = n$. Finally $(f * \varepsilon)(n) = \sum_{ab = n} f(a)\varepsilon(b) = f(n)$, since only $b = 1$ contributes. $\square$

**Theorem (Units).** An arithmetic function $f$ has an inverse for $*$ if and only if $f(1)$ is a unit of $R$.

*Proof.* If $f * g = \varepsilon$, then $f(1) g(1) = (f * g)(1) = 1$. Conversely, let $f(1)$ be a unit. Define $g$ by recursion on $n$: $g(1) = f(1)^{-1}$, and for $n > 1$
$$g(n) = -f(1)^{-1} \sum_{d \mid n,\ d < n} f(n/d)\, g(d).$$
The right side uses only $g(d)$ with $d < n$. Then $(f * g)(1) = 1$, and for $n > 1$
$$(f * g)(n) = f(1) g(n) + \sum_{d \mid n,\ d < n} f(n/d) g(d) = 0.$$
So $f * g = \varepsilon$, and by commutativity $g * f = \varepsilon$. $\square$

For example $\zeta(1) = 1$, so $\zeta$ has an inverse in the ring of integer valued functions. Section 2 shows that it is the Möbius function.

::: mathlib
`ArithmeticFunction.dirichletInverse` · `Mathlib.NumberTheory.ArithmeticFunction.Defs`

The recursion of the proof, with an argument `Invertible (f 1)`, so the definition is computable when `f` is. The equation $f * g = \varepsilon$ is `ArithmeticFunction.self_mul_dirichletInverse`. The criterion for a unit is `ArithmeticFunction.isUnit_iff_isUnit_apply_one`, in the commutative ring `ArithmeticFunction R`.

<?decl ArithmeticFunction.dirichletInverse?>
:::

**Lemma (Divisors of a product).** Let $m$ and $n$ be coprime. The map $(d_1, d_2) \mapsto d_1 d_2$ is a bijection from the pairs with $d_1 \mid m$, $d_2 \mid n$ to the divisors of $mn$.

*Proof.* The product $d_1 d_2$ divides $mn$. For a divisor $d$ of $mn$, put $d_1 = \gcd(d, m)$ and $d_2 = \gcd(d, n)$. Since $\gcd(m, n) = 1$, $d_1$ and $d_2$ are coprime, so $d_1 d_2 \mid d$. For a prime power $p^e \parallel d$, the prime $p$ divides at most one of $m$ and $n$, say $m$. Then $p^e \mid mn$ gives $p^e \mid m$ by Euclid's lemma, so $p^e \mid d_1$. So $d \mid d_1 d_2$, and $d = d_1 d_2$. If $d = d_1 d_2$ with $d_1 \mid m$, $d_2 \mid n$, then $\gcd(d, m) = \gcd(d_1, m) = d_1$ because $d_2$ is prime to $m$, so the pair is unique. $\square$

**Theorem (Convolution keeps multiplicativity).** If $f$ and $g$ are multiplicative, then $f * g$ is multiplicative.

*Proof.* First $(f * g)(1) = f(1) g(1) = 1$. Let $m$ and $n$ be coprime. By the lemma, the pairs $(a, b)$ with $ab = mn$ correspond to the quadruples $(a_1, b_1, a_2, b_2)$ with $a_1 b_1 = m$, $a_2 b_2 = n$, through $a = a_1 a_2$ and $b = b_1 b_2$. The factors $a_1$ and $a_2$ are coprime, as divisors of $m$ and $n$, and so are $b_1$ and $b_2$. So
$$(f * g)(mn) = \sum_{\substack{a_1 b_1 = m \\ a_2 b_2 = n}} f(a_1) f(a_2)\, g(b_1) g(b_2) = (f * g)(m)\,(f * g)(n). \qquad \square$$

::: mathlib
`ArithmeticFunction.IsMultiplicative.mul` · `Mathlib.NumberTheory.ArithmeticFunction.Defs`

The theorem, in a commutative semiring. The pointwise product keeps multiplicativity too, by `IsMultiplicative.pmul`.

<?decl ArithmeticFunction.IsMultiplicative.mul?>
:::

**Theorem (Values from prime powers).** If $f$ is multiplicative and $n = p_1^{e_1} \cdots p_r^{e_r}$ with distinct primes, then $f(n) = f(p_1^{e_1}) \cdots f(p_r^{e_r})$. Two multiplicative functions that agree on all prime powers are equal.

*Proof.* By induction on $r$: the factor $p_r^{e_r}$ is coprime to the product of the others. $\square$

::: mathlib
`ArithmeticFunction.IsMultiplicative.multiplicative_factorization` · `Mathlib.NumberTheory.ArithmeticFunction.Defs`

For `n ≠ 0`, `f n = n.factorization.prod fun p k ↦ f (p ^ k)`. Here `n.factorization` is the finitely supported function $p \mapsto v_p(n)$ of Chapter 1.

<?decl ArithmeticFunction.IsMultiplicative.multiplicative_factorization?>
:::

**Theorem (Divisor functions).** $\sigma_k = \zeta * \mathrm{pow}_k$, and $\sigma_k$ is multiplicative. For a prime $p$,
$$\sigma_k(p^e) = 1 + p^k + p^{2k} + \dots + p^{ek}, \qquad \tau(p^e) = e + 1, \qquad \sigma(p^e) = \frac{p^{e+1} - 1}{p - 1}.$$
So for $n = \prod p_i^{e_i}$, $\tau(n) = \prod (e_i + 1)$ and $\sigma(n) = \prod (p_i^{e_i + 1} - 1)/(p_i - 1)$.

*Proof.* By definition, $(\zeta * \mathrm{pow}_k)(n) = \sum_{ab = n} b^k = \sigma_k(n)$. The functions $\zeta$ and $\mathrm{pow}_k$ are completely multiplicative, so $\sigma_k$ is multiplicative by the previous theorem. The divisors of $p^e$ are $p^0, \dots, p^e$ (Chapter 1, Section 2), which gives the values on prime powers. $\square$

::: mathlib
`ArithmeticFunction.zeta_mul_pow_eq_sigma` · `Mathlib.NumberTheory.ArithmeticFunction.Misc`

`ζ * pow k = σ k` in `ArithmeticFunction ℕ`. Multiplicativity is `ArithmeticFunction.isMultiplicative_sigma`, and the values on prime powers are `sigma_apply_prime_pow` and `sigma_zero_apply_prime_pow`. The product formula for $\tau$ is `Nat.card_divisors`.

<?decl ArithmeticFunction.zeta_mul_pow_eq_sigma?>
:::

### Examples

**Example (The sum of the divisors of $12$).** The divisors of $12$ are $1, 2, 3, 4, 6, 12$, with sum $28$. Multiplicativity gives the same value: $\sigma(12) = \sigma(4)\sigma(3) = (1 + 2 + 4)(1 + 3) = 7 \cdot 4 = 28$. And $\tau(12) = (2 + 1)(1 + 1) = 6$.

**Example (A number with many divisors).** For $720 = 2^4 \cdot 3^2 \cdot 5$, $\tau(720) = 5 \cdot 3 \cdot 2 = 30$ and $\sigma(720) = 31 \cdot 13 \cdot 6 = 2418$.

**Example (A convolution by hand).** $(\mathrm{id} * \mathrm{id})(n) = \sum_{ab = n} ab = n\,\tau(n)$. For $n = 6$: $1 \cdot 6 + 2 \cdot 3 + 3 \cdot 2 + 6 \cdot 1 = 24 = 6 \cdot 4$.

**Counterexample (Coprimality is needed).** $\sigma(4) = 7$, but $\sigma(2)^2 = 9$. So $\sigma$ is multiplicative but not completely multiplicative. In the same way $\tau(4) = 3 \neq 4 = \tau(2)^2$. The function $\Omega$ is not multiplicative at all, since $\Omega(1) = 0 \neq 1$; it is additive: $\Omega(mn) = \Omega(m) + \Omega(n)$ for all $m, n \geq 1$, while $\omega(mn) = \omega(m) + \omega(n)$ needs coprime $m$ and $n$.

### The library around it

`Mathlib.NumberTheory.ArithmeticFunction.Defs` defines the type, the ring structure and `IsMultiplicative`. `Zeta.lean` has `ζ` and the pointwise operations `pmul` and `ppow`. `Misc.lean` has `σ`, `pow`, `id`, `ω`, `Ω`, and identities such as `ArithmeticFunction.cardFactors_mul` (additivity of $\Omega$) and `ArithmeticFunction.sum_Ioc_sigma0_eq_sum_div`, the identity $\sum_{n \leq N} \tau(n) = \sum_{n \leq N} \lfloor N/n \rfloor$.

Common errors of a learner:

- `f * g` is the Dirichlet convolution, not the pointwise product. The pointwise product is `f.pmul g`.
- `ζ` has values in `ℕ`. In a statement over `ℤ`, write `(ζ : ArithmeticFunction ℤ)`; the cast is a ring map, and `push_cast` moves it.
- `f 0 = 0` for every arithmetic function, so `σ k 0 = 0` and `ζ 0 = 0`. A formula like $\zeta(n) = 1$ needs `n ≠ 0`.
- `IsMultiplicative` needs `f 1 = 1`. The zero function satisfies $f(mn) = f(m) f(n)$ but is not multiplicative.

### Exercises

1. (A) Compute $\tau(n)$ and $\sigma(n)$ for $n = 60$, $360$ and $1001$.
2. (A) Show that $\tau(n)$ is odd if and only if $n$ is a square. Hint: $e + 1$ is odd if and only if $e$ is even.
3. (A) Show that $\prod_{d \mid n} d = n^{\tau(n)/2}$. Hint: pair $d$ with $n/d$.
4. (B) Show that $\zeta * \zeta = \tau$ and $\zeta * \tau = \sum_{d \mid n} \tau(d)$, and compute this last sum on $p^e$.
5. (B) Show that $f \mapsto f(1)$ is a ring map from the arithmetic functions to $R$, and that the inverse of a multiplicative function is multiplicative. Hint: define $h$ multiplicative with $h(p^e) = f^{-1}(p^e)$, then show $f * h = \varepsilon$ on prime powers.
6. (B) Let $f$ be completely multiplicative. Show that $f^{-1}(n) = \mu(n) f(n)$, where $\mu(p) = -1$, $\mu(p^e) = 0$ for $e \geq 2$, and $\mu$ is multiplicative.
7. (C) Show that $\sum_{n \leq N} \tau(n) = \sum_{d \leq N} \lfloor N/d \rfloor$, and deduce $\sum_{n \leq N} \tau(n) = N \log N + O(N)$. Hint: count the pairs $(d, m)$ with $dm \leq N$.

### Notes and history

Dirichlet studied the average order of $\tau(n)$ in 1849. The name Dirichlet convolution comes from the Dirichlet series $\sum f(n) n^{-s}$, whose product is the series of $f * g$. Chapter 7 uses this connection. A standard reference for this section is Apostol, *Introduction to Analytic Number Theory*, Chapter 2.

### Reference

<?reference?>
