---
title: Conditional expectation and conditional variance
kind: theory
modules:
  - Mathlib.Probability.ConditionalExpectation
  - Mathlib.Probability.CondVar
explains:
  E3: [MeasureTheory.condExp_indep_eq, ProbabilityTheory.condExp_generateFrom_singleton, ProbabilityTheory.condVar, ProbabilityTheory.integral_condVar_add_variance_condExp]
  E2: [ProbabilityTheory.condExp_set_generateFrom_singleton, ProbabilityTheory.condVar_ae_eq_condExp_sq_sub_sq_condExp, ProbabilityTheory.condVar_ae_le_condExp_sq, ProbabilityTheory.condVar_bot, ProbabilityTheory.condVar_const, ProbabilityTheory.condVar_smul, ProbabilityTheory.condVar_of_not_integrable, ProbabilityTheory.setIntegral_condVar, ProbabilityTheory.integrable_condVar]
  E1: auto
families: []
requires: [V03, V13, V15, V20.C01, V20.C02, V20.C03, V20.C04, V20.C05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Conditional expectation and conditional variance

### Overview

The conditional expectation $E[X \mid \mathcal{G}]$ is the best prediction of $X$ from the information in a sub-$\sigma$-algebra $\mathcal{G}$. It is a random variable, and it is defined only up to a null set. Volume 18, Measure and integration, constructs it and proves its general properties: linearity, monotonicity, the tower property, the pull out property and the conditional forms of the convergence theorems. This section states the definition and these properties in the language of probability, and adds the results that Mathlib puts in its probability part: conditioning on an independent $\sigma$-algebra, conditioning on one event, and the conditional variance with the law of total variance.

### Definitions

**Definition (Conditional expectation).** Let $X$ be an integrable real variable on $(\Omega, \mathcal{F}, P)$ and let $\mathcal{G} \subseteq \mathcal{F}$ be a $\sigma$-algebra. A *conditional expectation* of $X$ given $\mathcal{G}$ is a $\mathcal{G}$-measurable integrable variable $Y$ with
$$E[Y \mathbf{1}_G] = E[X \mathbf{1}_G] \quad \text{for all } G \in \mathcal{G}.$$
It exists by the Radon-Nikodym theorem, applied to the measure $G \mapsto E[X\mathbf{1}_G]$ on $\mathcal{G}$, and it is unique up to a.s. equality. It is written $E[X \mid \mathcal{G}]$. For a variable $Z$, $E[X \mid Z] = E[X \mid \sigma(Z)]$, and by the Doob-Dynkin lemma $E[X \mid Z] = h(Z)$ for a measurable $h$. The *conditional probability* of an event $A$ is $P(A \mid \mathcal{G}) = E[\mathbf{1}_A \mid \mathcal{G}]$. If $X \in L^2$, then $E[X \mid \mathcal{G}]$ is the orthogonal projection of $X$ on the closed subspace $L^2(\mathcal{G})$.

::: mathlib
`MeasureTheory.condExp` · `Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic`

`condExp m μ f`, with the notation `μ[f | m]`, is a fixed function, chosen to be `m`-strongly measurable. It has the junk value `0` if `f` is not integrable, if `m` is not below the ambient σ-algebra, or if `μ.trim hm` is not σ-finite. The defining property is `setIntegral_condExp`, and `integral_condExp` is $E[E[X \mid \mathcal{G}]] = E[X]$. The tower property is `condExp_condExp_of_le`, and the pull out property is `condExp_mul_of_stronglyMeasurable_left`. These names are in the measure theory part of the library, which Volume 18 describes.

<?decl MeasureTheory.condExp?>
:::

**Definition (Conditional variance).** For $X \in L^2$, the *conditional variance* of $X$ given $\mathcal{G}$ is
$$\operatorname{Var}(X \mid \mathcal{G}) = E\big[(X - E[X \mid \mathcal{G}])^2 \,\big|\, \mathcal{G}\big].$$

::: mathlib
`ProbabilityTheory.condVar` · `Mathlib.Probability.CondVar`

`condVar m X μ` is `μ[(X - μ[X | m]) ^ 2 | m]`, with the notation `Var[X; μ | m]`. Like `condExp`, it is `0` when the square is not integrable (`condVar_of_not_integrable`), and it is always integrable (`integrable_condVar`). `condVar_const` and `condVar_smul` are the rules $\operatorname{Var}(c \mid \mathcal{G}) = 0$ and $\operatorname{Var}(cX \mid \mathcal{G}) = c^2 \operatorname{Var}(X \mid \mathcal{G})$. `setIntegral_condVar` is the defining property on the sets of `m`.

<?decl ProbabilityTheory.condVar?>
:::

### Theorems and proofs

The following properties hold a.s., for integrable $X, Y$ and $\sigma$-algebras $\mathcal{H} \subseteq \mathcal{G} \subseteq \mathcal{F}$. Volume 18 proves them.

1. Linearity, and monotonicity: $X \le Y$ implies $E[X \mid \mathcal{G}] \le E[Y \mid \mathcal{G}]$.
2. The tower property: $E[E[X \mid \mathcal{G}] \mid \mathcal{H}] = E[X \mid \mathcal{H}]$.
3. Pull out: if $Z$ is $\mathcal{G}$-measurable and $ZX$ is integrable, then $E[ZX \mid \mathcal{G}] = Z\,E[X \mid \mathcal{G}]$.
4. Jensen: for a convex $\varphi$ with $\varphi(X)$ integrable, $\varphi(E[X \mid \mathcal{G}]) \le E[\varphi(X) \mid \mathcal{G}]$. In particular $E[X \mid \mathcal{G}]$ is a contraction in each $L^p$.
5. Monotone and dominated convergence for conditional expectations.

**Theorem (Conditioning on an independent $\sigma$-algebra).** If $\sigma(X)$ and $\mathcal{G}$ are independent, then $E[X \mid \mathcal{G}] = E[X]$ a.s.

*Proof.* The constant $E[X]$ is $\mathcal{G}$-measurable. For $G \in \mathcal{G}$, the variables $X$ and $\mathbf{1}_G$ are independent, so $E[X \mathbf{1}_G] = E[X]P(G) = E[E[X]\mathbf{1}_G]$ by the product rule of Chapter 3. Uniqueness gives the result. $\square$

::: mathlib
`MeasureTheory.condExp_indep_eq` · `Mathlib.Probability.ConditionalExpectation`

For `m₁ ≤ m`, `m₂ ≤ m` with `SigmaFinite (μ.trim hle₂)`, an `m₁`-strongly measurable `f` and `Indep m₁ m₂ μ`, the conclusion is `μ[f | m₂] =ᵐ[μ] fun _ ↦ ∫ x, f x ∂μ`. The independence is between σ-algebras, as in Chapter 2: take `m₁ = MeasurableSpace.comap X _` for a variable `X`. The name is in the namespace `MeasureTheory`, but the file is in the probability part.

<?decl MeasureTheory.condExp_indep_eq?>
:::

**Theorem (Conditioning on one event).** Let $B$ be an event with $P(B) > 0$ and let $\mathcal{G} = \sigma(B) = \{\emptyset, B, B^c, \Omega\}$. Then $E[X \mid \mathcal{G}] = E[X \mid B]$ a.s. on $B$, where $E[X \mid B] = E[X \mathbf{1}_B]/P(B)$ is the expectation under the conditional measure $P(\cdot \mid B)$ of Chapter 1.

*Proof.* A $\mathcal{G}$-measurable function is constant on $B$ and on $B^c$. If its value on $B$ is $c$, the defining property for $G = B$ gives $cP(B) = E[X\mathbf{1}_B]$. $\square$

::: mathlib
`ProbabilityTheory.condExp_generateFrom_singleton` · `Mathlib.Probability.ConditionalExpectation`

For a measurable `s` and an integrable `f`, `μ[f | generateFrom {s}] =ᵐ[μ.restrict s] fun _ ↦ ∫ x, f x ∂μ[|s]`. The measure `μ[|s]` is `cond μ s` of Chapter 1. The form for an indicator is `condExp_set_generateFrom_singleton`, with the value `μ[|s].real t`.

<?decl ProbabilityTheory.condExp_generateFrom_singleton?>
:::

**Theorem (Law of total variance).** For $X \in L^2$,
$$\operatorname{Var}(X) = E[\operatorname{Var}(X \mid \mathcal{G})] + \operatorname{Var}(E[X \mid \mathcal{G}]).$$

*Proof.* Put $Y = E[X \mid \mathcal{G}]$. First, $\operatorname{Var}(X \mid \mathcal{G}) = E[X^2 \mid \mathcal{G}] - Y^2$: expand $(X - Y)^2$ and use the pull out property, $E[XY \mid \mathcal{G}] = Y^2$. Take expectations: $E[\operatorname{Var}(X \mid \mathcal{G})] = E[X^2] - E[Y^2]$. Also $\operatorname{Var}(Y) = E[Y^2] - E[Y]^2 = E[Y^2] - E[X]^2$ by the tower property. Add the two equations. $\square$

::: mathlib
`ProbabilityTheory.integral_condVar_add_variance_condExp` · `Mathlib.Probability.CondVar`

For `m ≤ m₀`, a probability measure and `MemLp X 2 μ`, `∫ ω, condVar m X μ ω ∂μ + variance μ[X | m] μ = variance X μ`. The first step of the proof is `condVar_ae_eq_condExp_sq_sub_sq_condExp`, and `condVar_ae_le_condExp_sq` is the bound $\operatorname{Var}(X \mid \mathcal{G}) \le E[X^2 \mid \mathcal{G}]$. For the trivial σ-algebra `⊥`, `condVar_bot` gives the constant `variance X μ`.

<?decl ProbabilityTheory.integral_condVar_add_variance_condExp?>
:::

### Examples

**Example (A random sum).** Let $N$ be a variable with values in $\mathbb{N}$ and let $X_1, X_2, \ldots$ be i.i.d. with mean $m$ and variance $\sigma^2$, independent of $N$. Put $S = X_1 + \cdots + X_N$. Given $\sigma(N)$, on the event $\{N = n\}$ the sum has the law of $X_1 + \cdots + X_n$. So $E[S \mid N] = Nm$ and $\operatorname{Var}(S \mid N) = N\sigma^2$. The tower property gives Wald's identity $E[S] = mE[N]$, and the law of total variance gives
$$\operatorname{Var}(S) = \sigma^2 E[N] + m^2 \operatorname{Var}(N).$$
For an insurer with $N \sim \operatorname{Poi}(\lambda)$ claims of mean $m$ and variance $\sigma^2$, $\operatorname{Var}(S) = \lambda(\sigma^2 + m^2) = \lambda E[X_1^2]$.

**Example (Gaussian regression).** Let $(X, Y)$ be jointly Gaussian with mean $0$, variances $1$ and covariance $r$. By Section 4.3, $Y - rX$ is independent of $X$, because the pair $(X, Y - rX)$ is jointly Gaussian with covariance $0$. So $E[Y \mid X] = rX + E[Y - rX \mid X] = rX$ by the theorem on independent $\sigma$-algebras, and $\operatorname{Var}(Y \mid X) = \operatorname{Var}(Y - rX) = 1 - r^2$, a constant. The law of total variance reads $1 = (1 - r^2) + r^2$.

**Counterexample (A version, not a function).** Let $\Omega = [0, 1]$ with the Lebesgue measure, let $\mathcal{G}$ be the $\sigma$-algebra of sets of measure $0$ or $1$, and let $X(\omega) = \omega$. Each $\mathcal{G}$-measurable function is a.s. constant, so $E[X \mid \mathcal{G}] = 1/2$ a.s. The function $Y$ with $Y(\omega) = 1/2$ for $\omega \ne 1/3$ and $Y(1/3) = 7$ is also $\mathcal{G}$-measurable and satisfies the definition. So the conditional expectation is an equivalence class, and the value of `μ[X | m]` at one point has no meaning. The theorems on `condExp` are stated with `=ᵐ[μ]` for this reason.

### The library around it

The construction of `condExp` and its general properties are in `Mathlib.MeasureTheory.Function.ConditionalExpectation`, which Volume 18 describes; the conditional Jensen inequality and the pull out lemmas are there too. `Mathlib.Probability.ConditionalExpectation` has the results that need independence and the conditional measure. `Mathlib.Probability.CondVar` defines the conditional variance. The conditional expectation as an integral against a kernel, `condExpKernel`, is in Section 2, and the conditional distribution `condDistrib` is in Chapter 8.

Common errors of a learner:

- `μ[f | m]` takes the σ-algebra first in the notation, and Lean needs `m ≤ mΩ` as a hypothesis for most lemmas. Without it, the value is `0`.
- Results about `condExp` hold a.e., with `=ᵐ[μ]`. A rewrite with `rw` needs an equality, so use `EventuallyEq.trans` and its relatives.
- `condExp_indep_eq` needs strong measurability of `f` for `m₁`, and not only for the ambient σ-algebra.

### Exercises

1. (A) Let $X$ and $Y$ be independent and integrable. Show that $E[X + Y \mid Y] = E[X] + Y$ a.s.
2. (A) Let $\Omega = \{1, \ldots, 6\}$ with the uniform measure, $X(\omega) = \omega$ and $\mathcal{G} = \sigma(\{2, 4, 6\})$. Compute $E[X \mid \mathcal{G}]$ and $\operatorname{Var}(X \mid \mathcal{G})$, and check the law of total variance.
3. (A) Show that if $X$ is $\mathcal{G}$-measurable and in $L^2$, then $\operatorname{Var}(X \mid \mathcal{G}) = 0$ a.s.
4. (B) Show that $E[(X - E[X \mid \mathcal{G}])^2] \le E[(X - Z)^2]$ for each $\mathcal{G}$-measurable $Z \in L^2$.
5. (B) Let $X_1, \ldots, X_n$ be i.i.d. and integrable, with sum $S_n$. Show that $E[X_1 \mid S_n] = S_n/n$ a.s.
6. (B) Let $N \sim \operatorname{Geo}(p)$ on $\{1, 2, \ldots\}$ and let the $X_k$ be i.i.d. $\operatorname{Exp}(r)$ and independent of $N$. Compute $E[S]$ and $\operatorname{Var}(S)$ for $S = X_1 + \cdots + X_N$, and identify the law of $S$.
7. (C) Show that the family $\{E[X \mid \mathcal{G}] : \mathcal{G} \subseteq \mathcal{F} \text{ a } \sigma\text{-algebra}\}$ is uniformly integrable for each integrable $X$.

### Notes and history

Kolmogorov defined the conditional expectation with respect to a $\sigma$-algebra in his *Grundbegriffe der Wahrscheinlichkeitsrechnung* of 1933, with the Radon-Nikodym theorem. Earlier work had defined conditional probabilities only for events of positive probability. Wald published his identity for random sums in 1944, in the context of sequential analysis.

### Reference

<?reference?>
