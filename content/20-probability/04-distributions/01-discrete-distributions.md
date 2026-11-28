---
title: Discrete distributions
kind: theory
modules:
  - Mathlib.Probability.ProbabilityMassFunction.Basic
  - Mathlib.Probability.ProbabilityMassFunction.Constructions
  - Mathlib.Probability.ProbabilityMassFunction.Monad
  - Mathlib.Probability.ProbabilityMassFunction.Integrals
  - Mathlib.Probability.ProbabilityMassFunction.Binomial
  - Mathlib.Probability.Distributions.Bernoulli
  - Mathlib.Probability.Distributions.TwoValued
  - Mathlib.Probability.Distributions.Binomial
  - Mathlib.Probability.Distributions.Geometric
  - Mathlib.Probability.Distributions.Poisson.Basic
  - Mathlib.Probability.Distributions.Poisson.PoissonLimitThm
  - Mathlib.Probability.Distributions.SetBernoulli
  - Mathlib.Probability.Combinatorics.BinomialRandomGraph.Defs
explains:
  E3: [PMF, PMF.toMeasure, ProbabilityTheory.bernoulliMeasure, ProbabilityTheory.binomial, ProbabilityTheory.geometricMeasure, ProbabilityTheory.poissonMeasure, ProbabilityTheory.tendsto_choose_mul_pow_of_tendsto_mul_atTop]
  E2: [PMF.tsum_coe, PMF.toMeasure_apply, PMF.support, PMF.pure, PMF.bind, PMF.map, PMF.ofFinset, PMF.ofFintype, PMF.integral_eq_tsum, ProbabilityTheory.binomial_singleton, ProbabilityTheory.binomial_one_eq_bernoulliMeasure, ProbabilityTheory.integral_binomial, ProbabilityTheory.geometricMeasure_singleton, ProbabilityTheory.poissonMeasure_singleton, ProbabilityTheory.poissonMeasure_conv_poissonMeasure, ProbabilityTheory.IndepFun.hasLaw_add_poissonMeasure, ProbabilityTheory.hasLaw_indicator_one_bernoulliMeasure, ProbabilityTheory.variance_of_ae_eq_zero_or_one]
  E1: auto
families: []
requires: [V03, V13, V15, V20.C01, V20.C02, V20.C03]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Discrete distributions

### Overview

A law on a countable set is given by the probabilities of its points. This section describes that description, the probability mass function, and the four discrete laws that appear everywhere: the Bernoulli law of one trial, the binomial law of the number of successes in $n$ trials, the geometric law of the waiting time for a first success, and the Poisson law of rare events. It proves the Poisson limit theorem, which explains why the Poisson law describes rare events, and the stability of the Poisson laws under independent sums.

Mathlib has two descriptions of a discrete law. The type `PMF α` describes it by its mass function and has the structure of a monad, which suits the description of random algorithms. The named laws `binomial`, `geometricMeasure` and `poissonMeasure` are measures on `ℕ`, which suits the rest of the measure theoretic library.

### Definitions

**Definition (Probability mass function).** Let $S$ be a countable set. A *probability mass function* on $S$ is a function $f : S \to [0, 1]$ with $\sum_{s \in S} f(s) = 1$. It defines the probability measure $\mu_f(A) = \sum_{s \in A} f(s)$ on all subsets of $S$, and each probability measure on $S$ has this form, with $f(s) = \mu(\{s\})$. A random variable $X$ is *discrete* if it takes values in a countable set; its mass function is $s \mapsto P(X = s)$.

::: mathlib
`PMF` · `Mathlib.Probability.ProbabilityMassFunction.Basic`

`PMF α` is the subtype of the functions `f : α → ℝ≥0∞` with `HasSum f 1`, on any type `α`, countable or not. `PMF.tsum_coe` gives `∑' a, p a = 1`, and `PMF.support p` is the set of the points of positive mass, which is countable. The constructors are in `Mathlib.Probability.ProbabilityMassFunction.Constructions`: `PMF.ofFinset`, `PMF.ofFintype` and the image `PMF.map`. The mass functions `PMF.bernoulli` and `PMF.binomial` of the same file are deprecated in this edition, in favour of the measures `bernoulliMeasure` and `binomial` below. The monad structure is in `Mathlib.Probability.ProbabilityMassFunction.Monad`: `PMF.pure a` is the point mass at `a`, and `PMF.bind p f` draws `a` from `p` and then a value from `f a`.

<?decl PMF?>
:::

::: mathlib
`PMF.toMeasure` · `Mathlib.Probability.ProbabilityMassFunction.Basic`

`p.toMeasure` is the measure `s ↦ ∑' x, s.indicator p x` on a measurable space `α`, by `PMF.toMeasure_apply`. It is a probability measure, and for measurable singletons the map `toMeasure` is injective. `PMF.integral_eq_tsum` computes integrals against it as sums.

<?decl PMF.toMeasure?>
:::

**Definition (The four discrete laws).** Let $p \in [0, 1]$, $n \in \mathbb{N}$ and $\lambda \ge 0$.

1. The *Bernoulli law* with parameter $p$ on two points $x, y$ gives mass $p$ to $x$ and $1 - p$ to $y$. Usually $x = 1$ and $y = 0$.
2. The *binomial law* $\operatorname{Bin}(n, p)$ on $\{0, \ldots, n\}$ gives mass $\binom{n}{k} p^k (1 - p)^{n - k}$ to $k$.
3. The *geometric law* with parameter $p > 0$ on $\mathbb{N}$ gives mass $(1 - p)^k p$ to $k$. It is the law of the number of failures before the first success in independent trials with success probability $p$.
4. The *Poisson law* $\operatorname{Po}(\lambda)$ on $\mathbb{N}$ gives mass $e^{-\lambda} \lambda^k / k!$ to $k$.

Each is a probability measure: the binomial theorem gives $\sum_k \binom{n}{k} p^k (1-p)^{n-k} = (p + 1 - p)^n = 1$, the geometric series gives $\sum_k (1-p)^k p = 1$, and the exponential series gives $\sum_k \lambda^k/k! = e^\lambda$.

::: mathlib
`ProbabilityTheory.bernoulliMeasure` · `Mathlib.Probability.Distributions.Bernoulli`

`bernoulliMeasure x y p` for `p : unitInterval` is `p • dirac x + (1 - p) • dirac y`, with the notation `Ber(x, y, p)`. The indicator of an event of probability `p` has this law: `hasLaw_indicator_one_bernoulliMeasure`. The file `Mathlib.Probability.Distributions.TwoValued` computes the mean and the variance of a variable with values in $\{0, 1\}$: `variance_of_ae_eq_zero_or_one` gives $P(X = 1)P(X = 0)$.

<?decl ProbabilityTheory.bernoulliMeasure?>
:::

::: mathlib
`ProbabilityTheory.binomial` · `Mathlib.Probability.Distributions.Binomial`

`binomial n p : Measure ℕ` for `p : unitInterval`, with the notation `Bin(n, p)`. `binomial_singleton` gives the mass of `{k}`, `binomial_one_eq_bernoulliMeasure` the case `n = 1`, and `integral_binomial` the integral as a finite sum. The older `PMF.binomial` in `Mathlib.Probability.ProbabilityMassFunction.Binomial`, a mass function on `Fin (n + 1)`, is deprecated and points to `binomial`.

<?decl ProbabilityTheory.binomial?>
:::

::: mathlib
`ProbabilityTheory.geometricMeasure` · `Mathlib.Probability.Distributions.Geometric`

`geometricMeasure p : Measure ℕ`, with `geometricMeasure_singleton : p ≠ 0 → geometricMeasure p {n} = ofReal ((1 - p) ^ n * p)`. So the law counts the failures before the first success and starts at `0`.

<?decl ProbabilityTheory.geometricMeasure?>
:::

::: mathlib
`ProbabilityTheory.poissonMeasure` · `Mathlib.Probability.Distributions.Poisson.Basic`

`poissonMeasure r : Measure ℕ` for `r : ℝ≥0`, with the notation `Po(r)`, and `poissonMeasure_singleton r n : poissonMeasure r {n} = ofReal (exp (-r) * r ^ n / n !)`. The characteristic function is `charFun_map_cast_poissonMeasure`.

<?decl ProbabilityTheory.poissonMeasure?>
:::

### Theorems and proofs

**Theorem (Means and variances).**

| law | mean | variance |
|---|---|---|
| Bernoulli $p$ on $\{1, 0\}$ | $p$ | $p(1-p)$ |
| $\operatorname{Bin}(n, p)$ | $np$ | $np(1-p)$ |
| geometric $p$ | $(1-p)/p$ | $(1-p)/p^2$ |
| $\operatorname{Po}(\lambda)$ | $\lambda$ | $\lambda$ |

*Proof.* The Bernoulli and binomial rows are the examples of Chapter 3, Section 2. For the geometric law, the generating function is $E[s^N] = \sum_k (1-p)^k p s^k = p/(1 - (1-p)s)$ for $|s| < 1/(1-p)$. Its derivatives at $s = 1$ are $E[N] = (1-p)/p$ and $E[N(N-1)] = 2(1-p)^2/p^2$, so $\operatorname{Var}(N) = 2(1-p)^2/p^2 + (1-p)/p - (1-p)^2/p^2 = (1-p)/p^2$. For the Poisson law, $E[N(N-1)\cdots(N - r + 1)] = \sum_{k \ge r} e^{-\lambda}\lambda^k/(k - r)! = \lambda^r$; take $r = 1$ and $r = 2$. $\square$

**Theorem (Sums of independent Poisson variables).** If $X$ and $Y$ are independent with laws $\operatorname{Po}(\lambda)$ and $\operatorname{Po}(\mu)$, then $X + Y$ has the law $\operatorname{Po}(\lambda + \mu)$.

*Proof.* By the convolution formula of Chapter 2,
$$P(X + Y = n) = \sum_{k=0}^n e^{-\lambda}\frac{\lambda^k}{k!} e^{-\mu}\frac{\mu^{n-k}}{(n-k)!} = \frac{e^{-(\lambda + \mu)}}{n!}\sum_{k=0}^n \binom{n}{k}\lambda^k \mu^{n-k} = e^{-(\lambda+\mu)}\frac{(\lambda + \mu)^n}{n!}. \quad \square$$

::: mathlib
`ProbabilityTheory.poissonMeasure_conv_poissonMeasure` · `Mathlib.Probability.Distributions.Poisson.Basic`

`(poissonMeasure r₁).conv (poissonMeasure r₂) = poissonMeasure (r₁ + r₂)`. The form with random variables is `IndepFun.hasLaw_add_poissonMeasure`: from `IndepFun X Y P`, `HasLaw X (poissonMeasure r₁) P` and `HasLaw Y (poissonMeasure r₂) P` it gives `HasLaw (X + Y) (poissonMeasure (r₁ + r₂)) P`.

<?decl ProbabilityTheory.poissonMeasure_conv_poissonMeasure?>
:::

**Theorem (Poisson limit theorem).** Let $p_n \in [0, 1]$ with $n p_n \to \lambda$. Then for each $k \in \mathbb{N}$,
$$\binom{n}{k} p_n^k (1 - p_n)^{n - k} \longrightarrow e^{-\lambda}\frac{\lambda^k}{k!}.$$

*Proof.* Write $\binom{n}{k} p_n^k = \frac{n(n-1)\cdots(n-k+1)}{n^k} \cdot \frac{(np_n)^k}{k!}$. The first factor tends to $1$ and the second to $\lambda^k/k!$. Next, $p_n \to 0$, so $(1 - p_n)^{-k} \to 1$. Last, $\log (1 - p_n)^n = n \log(1 - p_n) = -np_n(1 + O(p_n)) \to -\lambda$, so $(1 - p_n)^n \to e^{-\lambda}$. $\square$

The theorem says that the number of successes in many trials, each with a small probability, is approximately Poisson. Section 2 of Chapter 5 states the corresponding convergence in law.

::: mathlib
`ProbabilityTheory.tendsto_choose_mul_pow_of_tendsto_mul_atTop` · `Mathlib.Probability.Distributions.Poisson.PoissonLimitThm`

For `p : ℕ → ℝ` with `Tendsto (fun n ↦ n * p n) atTop (𝓝 r)`: `Tendsto (fun n ↦ n.choose k * p n ^ k * (1 - p n) ^ (n - k)) atTop (𝓝 (exp (-r) * r ^ k / k !))`. The steps of the proof are `tendsto_zero_of_tendsto_mul_atTop` ($p_n \to 0$) and `tendsto_choose_mul_pow_atTop` (the first two factors).

<?decl ProbabilityTheory.tendsto_choose_mul_pow_of_tendsto_mul_atTop?>
:::

**Theorem (The geometric law has no memory).** If $N$ is geometric, $P(N \ge m + k \mid N \ge m) = P(N \ge k)$ for all $m, k \in \mathbb{N}$.

*Proof.* $P(N \ge j) = \sum_{i \ge j}(1-p)^i p = (1-p)^j$. So the ratio is $(1-p)^{m+k}/(1-p)^m = (1-p)^k$. $\square$

### Examples

**Example (Misprints).** A book of $500$ pages has $300$ misprints, each on a page chosen uniformly and independently. The number of misprints on page $1$ is $\operatorname{Bin}(300, 1/500)$, with $np = 0.6$. The Poisson approximation gives $P(\text{no misprint}) \approx e^{-0.6} \approx 0.549$; the exact value is $(499/500)^{300} \approx 0.548$. The probability of at least two misprints is about $1 - e^{-0.6}(1 + 0.6) \approx 0.122$.

**Example (A random algorithm as a PMF).** The monad structure of `PMF` describes a two stage experiment: toss a fair coin; on heads, roll a die, on tails, roll two dice and add. In Lean this is `PMF.bind coin (fun b ↦ if b then die else twoDice)`, with `coin := PMF.ofFintype (fun _ : Bool ↦ 1/2) h` and the two other mass functions built in the same way. The law of total probability of Chapter 1 is the formula `(p.bind f) b = ∑' a, p a * f a b`. Here $P(6) = \frac12 \cdot \frac16 + \frac12 \cdot \frac{5}{36} = \frac{11}{72}$.

**Counterexample (Sums of geometric variables are not geometric).** Let $N_1, N_2$ be independent and geometric with $p = 1/2$. Then $P(N_1 + N_2 = 0) = 1/4$ and $P(N_1 + N_2 = 1) = 2 \cdot \frac12 \cdot \frac14 = 1/4$. A geometric law with $P(0) = q$ has $P(1) = q(1-q)$, which for $q = 1/4$ is $3/16 \neq 1/4$. The sum has the negative binomial law $P(N_1 + N_2 = k) = (k+1)2^{-k-2}$.

### The library around it

`PMF` is the older of the two descriptions. Its files have the monad laws (`PMF.pure_bind`, `PMF.bind_pure`). In this edition Mathlib moves the named laws from `PMF` to measures: the uniform mass functions on finite sets and the Bernoulli and binomial mass functions are deprecated, and their replacements are `Measure.uniformOfFinset`, `bernoulliMeasure` and `binomial`. The named laws on `ℕ` are newer and have a uniform API: the mass of a singleton (`_singleton`, `_real_singleton`), the integral as a sum (`integral_binomial`, `integral_geometricMeasure`, `integral_poissonMeasure`), the integrability (`integrable_poissonMeasure_iff`) and the image in a semiring by `Nat.cast` (`map_cast_binomial_eq_sum_dirac`).

The module `Mathlib.Probability.Distributions.SetBernoulli` defines `ProbabilityTheory.setBernoulli` $u$ $p$, with the notation `setBer(u, p)`. It is a measure on the subsets of a type $\iota$: each element of $u$ is in the random set with probability $p$, independently, and no element outside $u$ is in it. It is the image of an infinite product of Bernoulli laws, and `ProbabilityTheory.setBernoulli_apply` computes it in this form. The random set is a subset of $u$ almost surely, by `ProbabilityTheory.setBernoulli_ae_subset`. When $u$ is finite and $s \subseteq u$, `ProbabilityTheory.setBernoulli_singleton` gives the mass $p^{|s|} (1 - p)^{|u \setminus s|}$, and `ProbabilityTheory.map_ncard_setBernoulli_apply` describes the law of the number of elements, which is binomial. The predicate `ProbabilityTheory.IsSetBernoulli` says that a random set has this law. The parameter $p$ is in the unit interval `unitInterval`, so a computation often needs a cast to $[0, \infty]$.

The module `Mathlib.Probability.Combinatorics.BinomialRandomGraph.Defs` uses it to define the binomial random graph `SimpleGraph.binomialRandom` $V$ $p$, with the notation `G(V, p)`. It is a measure on the simple graphs on $V$ in which each possible edge is present with probability $p$, independently. The theorem `SimpleGraph.binomialRandom_eq_map` writes it as the image of the set Bernoulli measure on the nondiagonal pairs under the map from edge sets to graphs, and `SimpleGraph.binomialRandom_apply` computes it with the product of Bernoulli laws.

Common errors of a learner:

- The parameter of `binomial`, `bernoulliMeasure` and `geometricMeasure` is `p : unitInterval`, a subtype of `ℝ`; the parameter of `poissonMeasure` is `r : ℝ≥0`.
- `binomial n p` is a measure on `ℕ`, not on `Fin (n + 1)`. A real variable with this law is stated as `HasLaw X ((binomial n p).map Nat.cast) P`.
- Some books define the geometric law on $\{1, 2, \ldots\}$ as the index of the first success. Mathlib counts failures, from $0$.

### Exercises

1. (A) Compute $P(X \ge 2)$ for $X \sim \operatorname{Po}(1)$.
2. (A) Show that the mode of $\operatorname{Bin}(n, p)$, the most likely value, is $\lfloor (n+1)p \rfloor$ when $(n+1)p$ is not an integer.
3. (A) Let $X \sim \operatorname{Bin}(n, p)$ and $Y \sim \operatorname{Bin}(m, p)$ be independent. Show that $X + Y \sim \operatorname{Bin}(n + m, p)$.
4. (B) Let $N \sim \operatorname{Po}(\lambda)$, and given $N = n$, let $X$ be binomial with parameters $n$ and $p$. Show that $X \sim \operatorname{Po}(\lambda p)$ and that $X$ and $N - X$ are independent.
5. (B) Show that a law on $\mathbb{N}$ with $P(N \ge m + k \mid N \ge m) = P(N \ge k)$ for all $m, k$ and $P(N = 0) \in (0, 1)$ is geometric.
6. (B) Write the experiment "toss a fair coin until two heads in a row appear, and return the number of tosses" with `PMF.bind`, and compute the mean number of tosses.
7. (C) Let $X$ be the number of fixed points of a uniform random permutation of $\{1, \ldots, n\}$. Use inclusion and exclusion to show $P(X = k) \to e^{-1}/k!$.

### Notes and history

Jakob Bernoulli studied repeated trials in *Ars Conjectandi*, published in 1713 after his death. Poisson derived his law as a limit of the binomial law in his book of 1837 on the probability of judgements. Bortkiewicz applied it in 1898 to the number of Prussian soldiers killed by kicks of horses, the classical data set for the law of rare events.

### Reference

<?reference?>
