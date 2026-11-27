---
title: Random variables and their laws
kind: theory
modules:
  - Mathlib.Probability.HasLaw
  - Mathlib.Probability.HasLawExists
  - Mathlib.Probability.IdentDistrib
  - Mathlib.Probability.CDF
explains:
  E3: [ProbabilityTheory.HasLaw, ProbabilityTheory.IdentDistrib, ProbabilityTheory.cdf, MeasureTheory.Measure.cdf_eq_iff]
  E2: [ProbabilityTheory.HasLaw.comp, ProbabilityTheory.HasLaw.measure_eq, ProbabilityTheory.HasLaw.integral_comp, ProbabilityTheory.hasLaw_map, ProbabilityTheory.HasLaw.identDistrib, ProbabilityTheory.IdentDistrib.comp, ProbabilityTheory.IdentDistrib.integral_eq, ProbabilityTheory.IdentDistrib.measure_mem_eq, ProbabilityTheory.monotone_cdf, ProbabilityTheory.tendsto_cdf_atTop, ProbabilityTheory.tendsto_cdf_atBot, ProbabilityTheory.cdf_eq_real, ProbabilityTheory.measure_cdf, MeasureTheory.Measure.exists_hasLaw, ProbabilityTheory.exists_iid]
  E1: auto
families: []
requires: [V03, V13, V15]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Random variables and their laws

### Overview

A random variable is a quantity that depends on the outcome of the experiment: the sum of two dice, the time of the first success, the position of a particle. Formally it is a measurable map $X : \Omega \to E$. The probability space $\Omega$ is usually not interesting in itself. What matters is the *law* of $X$, the measure on $E$ that says how likely each set of values is. Two variables on different spaces can have the same law, and then each statement that depends only on the law holds for both.

This section defines random variables and laws, proves the transfer formula that computes a probability or an expectation through the law, and studies the distribution function of a real variable. The main theorem says that the distribution function determines the law. The section ends with the existence of a random variable with a given law.

### Definitions

**Definition (Random variable).** Let $(\Omega, \mathcal{F}, P)$ be a probability space and $(E, \mathcal{E})$ a measurable space. A *random variable* with values in $E$ is a measurable map $X : \Omega \to E$, that is, $X^{-1}(B) \in \mathcal{F}$ for each $B \in \mathcal{E}$. A *real random variable* is the case $E = \mathbb{R}$ with the Borel σ-algebra.

The event $X^{-1}(B)$ is written $\{X \in B\}$. Measurability is exactly what makes $P(X \in B)$ defined. For a real variable it is enough that $\{X \le t\} \in \mathcal{F}$ for each $t$, because the half-lines $(-\infty, t]$ generate the Borel σ-algebra (Volume 18).

**Definition (Law).** The *law* (or *distribution*) of $X$ is the image measure
$$P_X(B) = P(X \in B) = P\big(X^{-1}(B)\big) \qquad (B \in \mathcal{E}).$$
It is a probability measure on $E$. The variable $X$ *has law* $\mu$ if $P_X = \mu$, written $X \sim \mu$. Two variables $X$ on $(\Omega, P)$ and $Y$ on $(\Omega', P')$ are *identically distributed* if $P_X = P'_Y$.

The measure $P_X$ is countably additive because preimages commute with unions and keep disjointness. Its total mass is $P(X^{-1}(E)) = P(\Omega) = 1$.

::: mathlib
`ProbabilityTheory.HasLaw` · `Mathlib.Probability.HasLaw`

`HasLaw X μ P` is a structure with two fields: `aemeasurable : AEMeasurable X P` and `map_eq : P.map X = μ`. The measure `P` is an `autoParam` that defaults to `volume`, so `HasLaw X μ` reads "X has law μ" in a text with one fixed space. The law itself is `Measure.map X P`, the image measure of Volume 18. Mathlib asks only for almost everywhere measurability, because a variable that is changed on a null set should keep its law. The lemma `hasLaw_map` says that every a.e. measurable `X` has the law `P.map X`.

<?decl ProbabilityTheory.HasLaw?>
:::

::: mathlib
`ProbabilityTheory.IdentDistrib` · `Mathlib.Probability.IdentDistrib`

`IdentDistrib f g μ ν` says that `f` on `(α, μ)` and `g` on `(β, ν)` are a.e. measurable and that `μ.map f = ν.map g`. The two spaces may differ. The measures default to `volume`. The file proves that the relation passes to `f ∘ φ` and `g ∘ φ` for a measurable `φ` (`IdentDistrib.comp`), and that each quantity that depends only on the law agrees: `measure_mem_eq`, `integral_eq`, `variance_eq`, `memLp_iff`. `HasLaw.identDistrib` turns two variables with the same law into an `IdentDistrib`.

<?decl ProbabilityTheory.IdentDistrib?>
:::

**Definition (Distribution function).** Let $X$ be a real random variable. Its *distribution function* is $F_X(t) = P(X \le t)$ for $t \in \mathbb{R}$. For a probability measure $\mu$ on $\mathbb{R}$, $F_\mu(t) = \mu((-\infty, t])$, so $F_X = F_{P_X}$.

::: mathlib
`ProbabilityTheory.cdf` · `Mathlib.Probability.CDF`

`cdf μ` is a `StieltjesFunction`: a monotone, right continuous function `ℝ → ℝ`, bundled with these two proofs. It is defined for every measure `μ` on `ℝ` through the conditional distribution function of Chapter 8, and it equals `t ↦ μ.real (Iic t)` when `μ` is a probability measure (`cdf_eq_real`). For a measure that is not a probability measure the value is a junk value. The distribution function of a variable `X` is `cdf (P.map X)`.

<?decl ProbabilityTheory.cdf?>
:::

### Theorems and proofs

**Theorem (Transfer formula).** Let $X : \Omega \to E$ be a random variable with law $\mu$.

1. For each measurable $g : E \to F$, the variable $g(X)$ has law $\mu \circ g^{-1}$, the image of $\mu$ under $g$.
2. For each measurable $g : E \to [0, \infty]$, $\int_\Omega g(X)\, dP = \int_E g\, d\mu$. The same holds for $g : E \to \mathbb{R}$ when either side is integrable.

*Proof.* 1. For a measurable $C \subseteq F$, $P(g(X) \in C) = P(X \in g^{-1}(C)) = \mu(g^{-1}(C))$.

2. Let $g = \mathbf{1}_B$ for a measurable $B$. Then $\int \mathbf{1}_B(X)\, dP = P(X \in B) = \mu(B) = \int \mathbf{1}_B\, d\mu$. Both sides are linear in $g$, so the formula holds for nonnegative simple functions. A measurable $g \ge 0$ is the increasing limit of simple functions $g_n \ge 0$. Then $g_n(X)$ increases to $g(X)$, and the monotone convergence theorem on both sides gives the formula for $g$. For a real $g$, apply the formula to $g^+$ and $g^-$: the integrability conditions agree because they are the finiteness of $\int |g|\, d\mu = \int |g(X)|\, dP$. $\square$

::: mathlib
`ProbabilityTheory.HasLaw.integral_comp` · `Mathlib.Probability.HasLaw`

From `HasLaw X μ P` and an a.e. strongly measurable `f` with respect to `μ`, it gives `P[f ∘ X] = μ[f]`, that is, `∫ ω, f (X ω) ∂P = ∫ x, f x ∂μ`. It is a corollary of `MeasureTheory.integral_map` of Volume 18. The forms `HasLaw.lintegral_comp` and `HasLaw.measure_eq` give the nonnegative integral and the probability of an event `{ω | p (X ω)}`. Part 1 is `HasLaw.comp`.

<?decl ProbabilityTheory.HasLaw.integral_comp?>
:::

**Theorem (Properties of the distribution function).** Let $\mu$ be a probability measure on $\mathbb{R}$ and $F = F_\mu$.

1. $F$ is nondecreasing.
2. $F$ is right continuous.
3. $F(t) \to 0$ as $t \to -\infty$ and $F(t) \to 1$ as $t \to +\infty$.
4. $F$ has a left limit $F(t^-) = \mu((-\infty, t))$ at each $t$, and $\mu(\{t\}) = F(t) - F(t^-)$.

*Proof.* 1. If $s \le t$, then $(-\infty, s] \subseteq (-\infty, t]$.

2. Let $t_n \downarrow t$. The sets $(-\infty, t_n]$ decrease to $(-\infty, t]$, and they have finite measure, so continuity from above of a measure gives $F(t_n) \to F(t)$. Since $F$ is monotone, convergence along one decreasing sequence gives the right limit.

3. As $t_n \downarrow -\infty$, the sets $(-\infty, t_n]$ decrease to $\emptyset$, so $F(t_n) \to 0$. As $t_n \uparrow +\infty$ they increase to $\mathbb{R}$, and continuity from below gives $F(t_n) \to \mu(\mathbb{R}) = 1$.

4. Let $t_n \uparrow t$ with $t_n < t$. The sets $(-\infty, t_n]$ increase to $(-\infty, t)$. Then $\mu(\{t\}) = \mu((-\infty, t]) - \mu((-\infty, t))$. $\square$

**Theorem (The distribution function determines the law).** If $\mu$ and $\nu$ are probability measures on $\mathbb{R}$ with $F_\mu = F_\nu$, then $\mu = \nu$. Conversely, each function $F$ with the properties 1 to 3 is $F_\mu$ for exactly one probability measure $\mu$.

*Proof.* The half-lines $(-\infty, t]$ form a π-system: the intersection of two of them is a third. They generate the Borel σ-algebra. Two finite measures with the same total mass that agree on a generating π-system are equal, by the π-λ theorem of Volume 18. Here $\mu(\mathbb{R}) = \nu(\mathbb{R}) = 1$, so $\mu = \nu$.

For the converse, a nondecreasing right continuous $F$ defines the Lebesgue-Stieltjes measure $\mu_F$ with $\mu_F((a, b]) = F(b) - F(a)$; Volume 18 builds it with Carathéodory's theorem. Then $\mu_F((-\infty, t]) = \lim_{a \to -\infty} (F(t) - F(a)) = F(t)$ and $\mu_F(\mathbb{R}) = 1$ by property 3. Uniqueness is the first part. $\square$

::: mathlib
`MeasureTheory.Measure.cdf_eq_iff` · `Mathlib.Probability.CDF`

`cdf μ = cdf ν ↔ μ = ν` for probability measures on `ℝ`. Mathlib proves it from `measure_cdf`, which says `(cdf μ).measure = μ`: the Stieltjes measure of the distribution function is the measure itself. The converse part of the theorem is `cdf_measure_stieltjesFunction`: for a Stieltjes function `f` with limits `0` at `atBot` and `1` at `atTop`, `cdf f.measure = f`. The properties 1 and 3 are `monotone_cdf`, `tendsto_cdf_atBot` and `tendsto_cdf_atTop`; right continuity is part of the structure `StieltjesFunction`.

<?decl MeasureTheory.Measure.cdf_eq_iff?>
:::

**Theorem (Existence of a variable with a given law).** For each probability measure $\mu$ on a measurable space $E$, there is a probability space and a random variable on it with law $\mu$.

*Proof.* Take $\Omega = E$, $P = \mu$ and $X = \mathrm{id}$. Then $P(X \in B) = \mu(B)$. $\square$

The proof is trivial, and it shows why the space $\Omega$ is often left implicit. The real problem is to build several variables with given laws and a given joint behaviour, for example an infinite sequence of independent variables. Chapter 2 solves it with the infinite product measure.

::: mathlib
`MeasureTheory.Measure.exists_hasLaw` · `Mathlib.Probability.HasLawExists`

The statement is an existential over a type `Ω`, a σ-algebra, a measure `P` and a map `X` with `Measurable X ∧ HasLaw X μ P`, with the proof above. The same file has `exists_iid`: for each index type `ι` and each probability measure `μ` there is a family `X : ι → Ω → 𝓧` of independent variables, each with law `μ`. Chapter 2 explains its proof.

<?decl MeasureTheory.Measure.exists_hasLaw?>
:::

### Examples

**Example (The sum of two dice).** On $\Omega = \{1, \ldots, 6\}^2$ with the uniform probability, let $X(\omega_1, \omega_2) = \omega_1 + \omega_2$. The law of $X$ is the measure on $\{2, \ldots, 12\}$ with
$$P(X = k) = \frac{6 - |k - 7|}{36}.$$
For $k \le 7$ the outcomes with sum $k$ are $(1, k-1), \ldots, (k-1, 1)$, which are $k - 1 = 6 - |k - 7|$ outcomes. For $k > 7$ the map $(a, b) \mapsto (7 - a, 7 - b)$ is a bijection from the sum $k$ to the sum $14 - k$, so $P(X = k) = P(X = 14 - k)$. The distribution function is a step function: $F_X(t) = 0$ for $t < 2$, $F_X(t) = 1/36$ for $2 \le t < 3$, $F_X(t) = 3/36$ for $3 \le t < 4$, and so on, with $F_X(7) = 21/36$ and $F_X(t) = 1$ for $t \ge 12$. Each jump $F_X(k) - F_X(k^-)$ is $P(X = k)$, as in part 4 of the theorem.

**Example (A uniform variable).** Let $\Omega = [0, 1]$ with the Lebesgue measure and $X(\omega) = \omega$. Then $F_X(t) = 0$ for $t < 0$, $F_X(t) = t$ for $0 \le t \le 1$ and $F_X(t) = 1$ for $t > 1$. The variable $Y = -\log X$ (defined a.s.) has $P(Y \le t) = P(X \ge e^{-t}) = 1 - e^{-t}$ for $t \ge 0$. So $Y$ has the exponential law of Chapter 4. This is the method of *inversion*: if $F$ is continuous and strictly increasing, then $F^{-1}(X)$ has distribution function $F$.

**Counterexample (Equal laws, different variables).** On $[0, 1]$ with the Lebesgue measure, let $X(\omega) = \omega$ and $Y(\omega) = 1 - \omega$. Both have the uniform law on $[0, 1]$, so they are identically distributed. But $X \ne Y$ except at $\omega = 1/2$, and $X + Y = 1$ while $X + X = 2X$ is not constant. So the law of $X + Y$ is not determined by the laws of $X$ and $Y$. It depends on the joint law of the pair $(X, Y)$, and Chapter 2 shows that under independence the joint law is the product of the two laws.

### The library around it

The file `Mathlib.Probability.HasLaw` has the closure properties of `HasLaw`: `HasLaw.comp` for a measurable function of a variable, `HasLaw.fun_comp` for the composed form, `HasLaw.congr` for a.e. equal variables, and the lemmas `HasLaw.integrable_comp` and `HasLaw.memLp_comp` that move integrability between `Ω` and the space of values. The file `Mathlib.Probability.IdentDistrib` has the same family for `IdentDistrib`, together with arithmetic: `IdentDistrib.add_const`, `.neg`, `.norm`, `.sq` and `.pow`. Many theorems of the library, such as the strong law of Chapter 5, take the hypothesis `∀ i, IdentDistrib (X i) (X 0) μ μ` in this form.

Common errors of a learner:

- `HasLaw X μ` without a third argument means the law with respect to `volume`. In a file with an explicit measure `P`, write `HasLaw X μ P`.
- `Measure.map X P` is the junk value `0` when `X` is not a.e. measurable. A statement about the law needs the measurability of `X`, which `HasLaw` contains.
- `cdf μ t` is `μ.real (Iic t)`, with a closed half-line. The value `μ.real (Iio t)` is the left limit.

### Exercises

1. (A) Let $X$ be the larger of the two numbers shown by two dice. Compute $P(X = k)$ for $k = 1, \ldots, 6$. Hint: first compute $P(X \le k) = (k/6)^2$.
2. (A) Let $F$ be the distribution function of $X$. Express $P(a < X \le b)$, $P(X > a)$ and $P(X = a)$ with $F$.
3. (A) Show that if $X$ and $Y$ are identically distributed and $g$ is measurable, then $g(X)$ and $g(Y)$ are identically distributed.
4. (B) Show that a distribution function has at most countably many points of discontinuity. Hint: count the points with a jump larger than $1/n$.
5. (B) Let $F$ be a distribution function and define $G(u) = \inf\{t : F(t) \ge u\}$ for $u \in (0, 1)$. Show that $G(u) \le t$ if and only if $u \le F(t)$, and deduce that $G(U)$ has distribution function $F$ when $U$ is uniform on $(0, 1)$.
6. (B) Let $X$ be uniform on $[0, 1]$. Find the distribution function and the law of $X^2$.
7. (C) Show that the Cantor function $C$ on $[0, 1]$, extended by $0$ on the left and $1$ on the right, is a continuous distribution function, and that its measure gives mass $0$ to each point and mass $1$ to the Cantor set, which has Lebesgue measure $0$.

### Notes and history

The definition of a random variable as a measurable function and of its law as an image measure is part of Kolmogorov's axiomatics of 1933. The correspondence between distribution functions and measures on $\mathbb{R}$ is the theory of Lebesgue-Stieltjes integration, after Stieltjes (1894) and Lebesgue. In Mathlib the predicate `HasLaw` is recent, and many older files still state the hypothesis as `μ.map X = ν` with a separate measurability assumption.

### Reference

<?reference?>
