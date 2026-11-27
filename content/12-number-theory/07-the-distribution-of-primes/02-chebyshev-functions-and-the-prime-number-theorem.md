---
title: Chebyshev functions and the prime number theorem
kind: theory
modules:
  - Mathlib.NumberTheory.PrimeCounting
  - Mathlib.NumberTheory.Chebyshev
  - Mathlib.NumberTheory.LSeries.WienerIkehara
  - Mathlib.NumberTheory.LSeries.WeakPNT
explains:
  E3: [Nat.primeCounting, Chebyshev.theta, Chebyshev.psi, Nat.isEquivalent_primeCounting]
  E2: [Nat.primeCounting', Nat.primesLE, Nat.tendsto_primeCounting, Nat.lcmUpto, Nat.factorization_lcmUpto, Chebyshev.psi_eq_log_lcmUpto, Chebyshev.theta_eq_log_primorial, Chebyshev.choose_dvd_lcmUpto, Chebyshev.two_pow_le_mul_lcmUpto, Chebyshev.theta_le_log4_mul_x, Chebyshev.psi_ge, Chebyshev.theta_le_psi, Chebyshev.psi_sub_theta_le, Chebyshev.psi_le_primeCounting_mul_log, Chebyshev.pi_ge, Chebyshev.pi_ge_of_four_le, Chebyshev.pi_le_log4_mul_div, Chebyshev.isLittleO_primeCounting_mul_log_sub_theta, Chebyshev.theta_eq_primeCounting_mul_log_sub_integral, WienerIkehara.tendsto_sum_div, Chebyshev.isEquivalent_psi_id, Chebyshev.isEquivalent_theta_id, Nat.eventually_exists_prime_mem_Ioc, Nat.isEquivalent_nth_prime_succ]
  E1: auto
families: [Chebyshev.*, Nat.primesLE_*]
requires: [V12.C01, V12.C02, V12.C06, V15.C05, V15.C07]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Chebyshev functions and the prime number theorem

### Overview

The prime counting function $\pi(x)$ is the number of primes $p \le x$. The prime number theorem says that $\pi(x) \sim x/\log x$. Mathlib proves it. This section gives the elementary part of the theory completely: the functions $\theta$ and $\psi$ of Chebyshev, their link to the least common multiple of $1, \dots, n$, the Chebyshev bounds $c_1 x \le \psi(x) \le c_2 x$, and the equivalence of the three forms $\pi(x) \sim x/\log x$, $\theta(x) \sim x$ and $\psi(x) \sim x$. The analytic step, a Tauberian theorem of Wiener and Ikehara, is stated and used without proof.

The von Mangoldt function $\Lambda$ of Chapter 2 is the link between the two parts: $\psi$ is the summatory function of $\Lambda$, and $\sum\Lambda(n)n^{-s} = -\zeta'(s)/\zeta(s)$.

### Definitions

**Definition (Prime counting).** For $n \in \mathbb{N}$, $\pi(n)$ is the number of primes $p \le n$, and $\pi'(n)$ is the number of primes $p < n$. For real $x$, the formulas of Mathlib use $\pi(\lfloor x\rfloor)$.

::: mathlib
`Nat.primeCounting` · `Mathlib.NumberTheory.PrimeCounting`

`Nat.primeCounting n` is the card of `Nat.primesLE n`, the finite set of primes `p ≤ n`, with the notation `π n` under `open Nat`. `Nat.primeCounting' n`, notation `π' n`, counts the primes `p < n`. `Nat.tendsto_primeCounting` says that `π n → ∞`, a form of Euclid's theorem.

<?decl Nat.primeCounting?>
:::

**Definition (Chebyshev functions).** For real $x$,
$$\theta(x) = \sum_{p \le x}\log p, \qquad \psi(x) = \sum_{n \le x}\Lambda(n) = \sum_{p^k \le x,\ k \ge 1}\log p.$$
So $\theta(x) = \log(\lfloor x\rfloor\#)$ is the logarithm of the primorial of Section 1, and $\psi$ counts each prime power $p^k \le x$ with the weight $\log p$.

::: mathlib
`Chebyshev.theta`, `Chebyshev.psi` · `Mathlib.NumberTheory.Chebyshev`

`Chebyshev.theta x = ∑ p ∈ Finset.Ioc 0 ⌊x⌋₊ with p.Prime, Real.log p` and `Chebyshev.psi x = ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, Λ n`, both functions `ℝ → ℝ`, with the notations `θ` and `ψ` in the scope `Chebyshev`. `Chebyshev.theta_eq_log_primorial` gives `θ x = log (primorial ⌊x⌋₊)`.

<?decl Chebyshev.theta?>
<?decl Chebyshev.psi?>
:::

**Definition (Least common multiple up to $n$).** $L(n) = \operatorname{lcm}(1, 2, \dots, n)$, with $L(0) = 1$.

::: mathlib
`Nat.lcmUpto` · `Mathlib.NumberTheory.Chebyshev`

`Nat.lcmUpto n` is the lcm of `Finset.Icc 1 n`. `Nat.factorization_lcmUpto` says that its exponent at a prime `p` is `Nat.log p n`, the largest `k` with `p ^ k ≤ n`.

<?decl Nat.lcmUpto?>
:::

### Theorems and proofs

**Proposition (ψ and the lcm).** For $n \in \mathbb{N}$, $\psi(n) = \log L(n)$.

*Proof.* For a prime $p$, $v_p(L(n)) = \max_{m \le n}v_p(m)$, the largest $k$ with $p^k \le n$, since $p^k$ itself is one of the $m$. So $\log L(n) = \sum_{p \le n}k_p\log p$ with $k_p = \lfloor\log_p n\rfloor$. In $\psi(n)$, the prime $p$ contributes $\log p$ once for each of $p, p^2, \dots, p^{k_p}$, so also $k_p\log p$. $\square$

**Theorem (Chebyshev bounds).** For real $x \ge 0$ and $n \in \mathbb{N}$,

1. $\theta(x) \le x\log 4$;
2. $\psi(n) \ge n\log 2 - \log(n + 1)$;
3. $0 \le \psi(x) - \theta(x) \le \sqrt{x}\,\log x$ for $x \ge 1$.

*Proof.* (1) By Section 1, $\lfloor x\rfloor\# \le 4^{\lfloor x\rfloor} \le 4^x$; take logarithms.

(2) First, $\binom nk \mid L(n)$ for each $k \le n$. By Legendre's formula of Chapter 1, $v_p\binom nk = \sum_{j \ge 1}\left(\lfloor n/p^j\rfloor - \lfloor k/p^j\rfloor - \lfloor (n - k)/p^j\rfloor\right)$. Each term is $0$ or $1$, and it is $0$ when $p^j > n$. So $v_p\binom nk \le \lfloor\log_p n\rfloor = v_p(L(n))$. Then
$$2^n = \sum_{k=0}^n\binom nk \le (n + 1)L(n),$$
and the proposition gives $n\log 2 \le \log(n + 1) + \psi(n)$.

(3) The difference $\psi(x) - \theta(x)$ is the sum of $\log p$ over the prime powers $p^k \le x$ with $k \ge 2$. Such a $p$ satisfies $p \le \sqrt x$, and for a fixed $p$ there are at most $\log x/\log p$ values of $k$. So the sum is at most $\sum_{p \le \sqrt x}\log x \le \sqrt x\log x$. $\square$

::: mathlib
`Chebyshev.theta_le_log4_mul_x`, `Chebyshev.psi_ge`, `Chebyshev.psi_sub_theta_le` · `Mathlib.NumberTheory.Chebyshev`

The three bounds are `theta_le_log4_mul_x : 0 ≤ x → θ x ≤ log 4 * x`, `psi_ge : n * log 2 - log (n + 1) ≤ ψ n` and `psi_sub_theta_le : 1 ≤ x → ψ x - θ x ≤ 2 * √x * log x`, with the weaker constant $2$. The divisibility step is `Chebyshev.choose_dvd_lcmUpto` and the sum step is `Chebyshev.two_pow_le_mul_lcmUpto : 2 ^ n ≤ (n + 1) * n.lcmUpto`. The order of the two functions is `Chebyshev.theta_le_psi`.

<?decl Chebyshev.theta_le_log4_mul_x?>
<?decl Chebyshev.psi_ge?>
:::

**Corollary (Chebyshev bounds for π).** For $n \ge 2$ and real $x > 1$,
$$\frac{n\log 2 - \log(n + 1)}{\log n} \le \pi(n), \qquad \pi(x) \le \frac{x\log 4}{\log\sqrt x} + \sqrt x.$$

*Proof.* Each prime power $p^k \le n$ contributes $\log p$ to $\psi(n)$, and the number of such $k$ for a fixed $p$ is at most $\log n/\log p$. So $\psi(n) \le \pi(n)\log n$, and (2) gives $\pi(n)\log n \ge n\log 2 - \log(n + 1)$. For the upper bound, the primes $p \le \sqrt x$ are at most $\sqrt x$ in number, and each prime $p \in (\sqrt x, x]$ has $\log p > \log\sqrt x$, so their number is at most $\theta(x)/\log\sqrt x \le x\log 4/\log\sqrt x$ by (1). $\square$

::: mathlib
`Chebyshev.pi_ge_of_four_le`, `Chebyshev.pi_le_log4_mul_div` · `Mathlib.NumberTheory.Chebyshev`

The weaker bound above is `Chebyshev.pi_ge`. Mathlib also has the sharper `pi_ge_of_four_le : 4 ≤ n → n * log 2 / log n ≤ π n`, and `pi_le_log4_mul_div : 1 < x → π ⌊x⌋₊ ≤ log 4 * x / log √x + √x`. The step $\psi(n) \le \pi(n)\log n$ is `Chebyshev.psi_le_primeCounting_mul_log`.

<?decl Chebyshev.pi_ge_of_four_le?>
:::

**Theorem (Equivalent forms).** The following are equivalent as $x \to \infty$:
$$\text{(a)}\ \pi(x) \sim \frac{x}{\log x}, \qquad \text{(b)}\ \theta(x) \sim x, \qquad \text{(c)}\ \psi(x) \sim x.$$

*Proof.* (b) and (c) are equivalent since $|\psi(x) - \theta(x)| \le \sqrt x\log x = o(x)$.

For (a) and (b), it is enough to show $\pi(x)\log x - \theta(x) = o(x)$. First $\theta(x) \le \pi(x)\log x$, since each of the $\pi(x)$ terms $\log p$ is at most $\log x$. For the other side, fix $0 < \varepsilon < 1$. The primes $p \in (x^{1-\varepsilon}, x]$ have $\log p > (1 - \varepsilon)\log x$, and there are at least $\pi(x) - x^{1-\varepsilon}$ of them. So
$$\theta(x) \ge (1 - \varepsilon)\log x\,\left(\pi(x) - x^{1-\varepsilon}\right),$$
and
$$0 \le \pi(x)\log x - \theta(x) \le \varepsilon\,\pi(x)\log x + x^{1-\varepsilon}\log x.$$
By the corollary, $\pi(x)\log x \le 2x\log 4 + \sqrt x\log x \le 4x$ for large $x$, and $x^{1-\varepsilon}\log x = o(x)$. So $\limsup_x\left(\pi(x)\log x - \theta(x)\right)/x \le 4\varepsilon$ for each $\varepsilon$, and the limit is $0$. $\square$

::: mathlib
`Chebyshev.isLittleO_primeCounting_mul_log_sub_theta` · `Mathlib.NumberTheory.Chebyshev`

`(fun x ↦ π ⌊x⌋₊ * log x - θ x) =o[atTop] id`. Mathlib also has the exact formulas of partial summation, `Chebyshev.theta_eq_primeCounting_mul_log_sub_integral`:
$$\theta(x) = \pi(x)\log x - \int_2^x\frac{\pi(t)}{t}\,dt \qquad (x \ge 2),$$
and its inverse `Chebyshev.primeCounting_eq_theta_div_log_add_integral`.

<?decl Chebyshev.isLittleO_primeCounting_mul_log_sub_theta?>
:::

**Theorem (Wiener and Ikehara, cited).** Let $f : \mathbb{N} \to \mathbb{R}_{\ge0}$ with $\sum_{n < N}f(n) \le CN$ for all $N$. Suppose that there are $A \in \mathbb{R}$ and a function $G$, continuous on $\{\operatorname{Re}s \ge 1\}$, with $G(s) = \sum_n f(n)n^{-s} - A/(s - 1)$ for $\operatorname{Re}s > 1$. Then $\frac1x\sum_{n \le x}f(n) \to A$.

The proof uses Fourier analysis and is not given here.

::: mathlib
`WienerIkehara.tendsto_sum_div` · `Mathlib.NumberTheory.LSeries.WienerIkehara`

The statement above, with the hypothesis `∀ n, ∑ i ∈ range n, f i ≤ C * n`, `ContinuousOn G {s | 1 ≤ s.re}`, `Set.EqOn G (fun s ↦ LSeries (fun n ↦ f n) s - A / (s - 1)) {s | 1 < s.re}` and `0 ≤ f`. The conclusion is `Tendsto (fun x ↦ (∑ n ∈ Icc 0 ⌊x⌋₊, f n) / x) atTop (𝓝 A)`.

<?decl WienerIkehara.tendsto_sum_div?>
:::

**Theorem (Prime number theorem).** $\psi(x) \sim x$, $\theta(x) \sim x$ and $\pi(x) \sim x/\log x$.

*Proof.* Apply the theorem of Wiener and Ikehara to $f = \Lambda$ with $A = 1$. The bound $\sum_{n<N}\Lambda(n) = \psi(N - 1) \le CN$ follows from (1) and (3). For $\operatorname{Re}s > 1$, the L-series of $\Lambda$ is $-\zeta'(s)/\zeta(s)$ (Chapter 2 and Section 6.2). The function $\zeta(s) - 1/(s - 1)$ extends to an entire function, and $\zeta(s) \ne 0$ on $\operatorname{Re}s \ge 1$ by Section 6.2. So $-\zeta'/\zeta$ has a simple pole with residue $1$ at $s = 1$ and no other pole on $\operatorname{Re}s \ge 1$, and $G(s) = -\zeta'(s)/\zeta(s) - 1/(s - 1)$ is continuous on $\operatorname{Re}s \ge 1$. This gives $\psi(x)/x \to 1$, and the theorem on equivalent forms gives the other two. $\square$

The proof is complete relative to the theorem of Wiener and Ikehara and the analytic continuation of $\zeta$, which this handbook cites.

::: mathlib
`Nat.isEquivalent_primeCounting` · `Mathlib.NumberTheory.LSeries.WeakPNT`

`IsEquivalent atTop (fun x ↦ (π ⌊x⌋₊ : ℝ)) (fun x ↦ x / log x)`. The same file proves the version for primes in a residue class (Section 3). The forms for $\psi$ and $\theta$ are `Chebyshev.isEquivalent_psi_id` and `Chebyshev.isEquivalent_theta_id`. The name "weak" refers to the absence of an error term: the index of this edition has no declaration for the prime number theorem with the error term $O(x e^{-c\sqrt{\log x}})$ of de la Vallée Poussin.

<?decl Nat.isEquivalent_primeCounting?>
:::

**Corollary.** For each $\varepsilon > 0$ and all large $x$ there is a prime in $(x, (1 + \varepsilon)x]$. If $p_n$ is the $n$-th prime, $p_{n+1}/p_n \to 1$.

*Proof.* $\theta((1 + \varepsilon)x) - \theta(x) = (1 + \varepsilon)x - x + o(x) = \varepsilon x + o(x)$, which is positive for large $x$. A positive difference of $\theta$ needs a prime in the interval. For the second claim, apply the first with $x = p_n$: for large $n$, $p_{n+1} \le (1 + \varepsilon)p_n$. $\square$

::: mathlib
`Nat.eventually_exists_prime_mem_Ioc` · `Mathlib.NumberTheory.LSeries.WeakPNT`

`0 < ε → ∀ᶠ x in atTop, ∃ p, p.Prime ∧ (p : ℝ) ∈ Set.Ioc x ((1 + ε) * x)`, and `Nat.isEquivalent_nth_prime_succ` for $p_{n+1} \sim p_n$.

<?decl Nat.eventually_exists_prime_mem_Ioc?>
:::

### Examples

**Example (Values at $x = 100$).** There are $25$ primes up to $100$. So $\pi(100) = 25$, while $100/\log 100 = 21.7$. The value $\theta(100) = \log(100\#) = 83.7$, and $\psi(100) = \log L(100) = 94.0$. The difference $\psi - \theta = 10.3$ comes from the prime powers $4, 8, 16, 32, 64, 9, 27, 81, 25, 49$, and it is below the bound $\sqrt{100}\log 100 = 46.1$.

**Example (Lower bound by binomial coefficients).** For $n = 10$, $2^{10} = 1024 \le 11 \cdot L(10) = 11 \cdot 2520 = 27720$. Each $\binom{10}{k}$ divides $2520 = 2^3 \cdot 3^2 \cdot 5 \cdot 7$; for example $\binom{10}{5} = 252 = 2^2 \cdot 3^2 \cdot 7$.

**Example (Slow convergence).** At $x = 10^6$, $\pi(x) = 78498$ and $x/\log x = 72382$, a ratio of $1.084$. The ratio tends to $1$ slowly, with an error of order $1/\log x$. The logarithmic integral $\operatorname{li}(x) = \int_2^x dt/\log t$ is a much better approximation, about $78627$ at $10^6$. The index of this edition has no declaration for $\operatorname{li}$ or for the equivalence $\pi(x) \sim \operatorname{li}(x)$ under that name.

**Counterexample (Bounds without asymptotics).** The Chebyshev bounds give $\log 2 \le \liminf\psi(x)/x$ and $\limsup\theta(x)/x \le \log 4$. Elementary methods of this type alone do not show that the limit exists: the function $f(x) = x(1 + 0.2\sin\log\log x)$ satisfies the same bounds and has no asymptotic $f(x) \sim cx$.

### The library around it

`Mathlib.NumberTheory.PrimeCounting` also has the bound `Nat.primeCounting_add_le`, which counts the primes in an interval by the residues coprime to $a$. `Mathlib.NumberTheory.Chebyshev` has the decomposition $\psi(x) = \sum_{k\ge1}\theta(x^{1/k})$ as `Chebyshev.psi_eq_sum_theta`, and asymptotic forms such as `Chebyshev.isLittleO_psi_sub_theta_id`. 

Common errors of a learner:

- `π n` counts the primes `≤ n`, and `π' n` the primes `< n`. So `π 7 = 4` and `π' 7 = 3`.
- `Chebyshev.theta` and `Chebyshev.psi` take real arguments. On natural numbers, use the lemmas with a cast, such as `Chebyshev.psi_eq_log_lcmUpto (n : ℕ) : ψ n = log (n.lcmUpto)`.
- `IsEquivalent atTop u v` means `u - v =o[atTop] v`, not a limit of `u / v`. The two agree when `v` is eventually nonzero; use `Asymptotics.isEquivalent_iff_tendsto_one`.

### Exercises

1. (A) Compute $\theta(30)$, $\psi(30)$ and $L(30)$, and check $\psi(30) = \log L(30)$.
2. (A) Evaluate the lower bound of the corollary at $n = 100$ and $n = 1000$, and compare it with $\pi(100) = 25$ and $\pi(1000) = 168$.
3. (A) Show that $\pi(x) = o(x)$ using only the upper Chebyshev bound.
4. (B) Show that $\psi(x) = \sum_{k \ge 1}\theta(x^{1/k})$, where the sum is finite.
5. (B) Prove the formula $\theta(x) = \pi(x)\log x - \int_2^x\pi(t)/t\,dt$ for $x \ge 2$, by writing $\log p = \log x - \int_p^x dt/t$.
6. (B) Deduce from the prime number theorem that $p_n \sim n\log n$.
7. (C) Show that the prime number theorem implies Bertrand's postulate for all large $n$, and explain why it does not give the full statement of Section 1 without more work.

### Notes and history

Gauss and Legendre conjectured the prime number theorem near 1800 from tables. Chebyshev proved bounds of the type of this section around 1850, and showed that if $\pi(x)\log x/x$ has a limit, the limit is $1$. Riemann linked the distribution of primes to the zeros of $\zeta$ in 1859. Hadamard and de la Vallée Poussin proved the theorem independently in 1896. Wiener and Ikehara found the Tauberian theorem around 1931. Selberg and Erdős gave elementary proofs in 1949. A reference is Apostol, *Introduction to Analytic Number Theory*, Chapters 4 and 13.

### Reference

<?reference?>
