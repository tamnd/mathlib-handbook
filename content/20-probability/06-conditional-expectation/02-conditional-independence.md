---
title: Regular conditional probabilities and conditional independence
kind: theory
modules:
  - Mathlib.Probability.Kernel.Condexp
  - Mathlib.Probability.Independence.Conditional
explains:
  E3: [ProbabilityTheory.condExpKernel, ProbabilityTheory.condExp_ae_eq_integral_condExpKernel, ProbabilityTheory.CondIndep, ProbabilityTheory.CondIndepFun, ProbabilityTheory.condIndepFun_iff_condExp_inter_preimage_eq_mul]
  E2: [ProbabilityTheory.condExpKernel_ae_eq_condExp, ProbabilityTheory.compProd_trim_condExpKernel, ProbabilityTheory.condExpKernel_singleton_ae_eq_cond, ProbabilityTheory.instIsMarkovKernelCondExpKernel, ProbabilityTheory.CondIndepSet, ProbabilityTheory.condIndepSet_iff, ProbabilityTheory.condIndep_iff, ProbabilityTheory.iCondIndep, ProbabilityTheory.iCondIndepFun, ProbabilityTheory.CondIndepFun.comp, ProbabilityTheory.CondIndepFun.symm, ProbabilityTheory.condIndepFun_iff_map_prod_eq_prod_condDistrib_prod_condDistrib]
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

## Regular conditional probabilities and conditional independence

### Overview

For each event $A$, the conditional probability $P(A \mid \mathcal{G})$ is a random variable defined up to a null set. The null set depends on $A$, and there are uncountably many events, so the map $A \mapsto P(A \mid \mathcal{G})(\omega)$ need not be a measure for a fixed $\omega$. On a standard Borel space a good choice exists: a *regular conditional probability*, which is a Markov kernel from $(\Omega, \mathcal{G})$ to $(\Omega, \mathcal{F})$. This section states that result, shows that conditional expectations are integrals against this kernel, and uses it to define conditional independence. Mathlib defines conditional independence in exactly this way, as the independence of Chapter 2 with respect to a kernel.

### Definitions

**Definition (Regular conditional probability).** Let $\mathcal{G} \subseteq \mathcal{F}$. A *regular conditional probability* given $\mathcal{G}$ is a map $\kappa : \Omega \times \mathcal{F} \to [0, 1]$ such that

- for each $\omega$, $\kappa(\omega, \cdot)$ is a probability measure on $\mathcal{F}$;
- for each $A \in \mathcal{F}$, $\omega \mapsto \kappa(\omega, A)$ is $\mathcal{G}$-measurable and equal a.s. to $P(A \mid \mathcal{G})$.

The first two conditions say that $\kappa$ is a Markov kernel from $(\Omega, \mathcal{G})$ to $(\Omega, \mathcal{F})$, in the sense of Chapter 8.

::: mathlib
`ProbabilityTheory.condExpKernel` · `Mathlib.Probability.Kernel.Condexp`

`condExpKernel μ m : Kernel Ω Ω` is defined for a finite measure `μ` on a standard Borel space `Ω` and any σ-algebra `m`. It is a Markov kernel (`instIsMarkovKernelCondExpKernel`) from `Ω` with the σ-algebra `m` to `Ω` with `mΩ`. The construction works with `m ⊓ mΩ`, which is below `mΩ`, and then changes the σ-algebra of the source with `Kernel.comap`. `condExpKernel_ae_eq_condExp` is the second condition of the text: `(fun ω ↦ (condExpKernel μ m ω).real s) =ᵐ[μ] μ[s.indicator 1 | m]`. The kernel is built from the conditional distribution `condDistrib id id μ` of Chapter 8.

<?decl ProbabilityTheory.condExpKernel?>
:::

**Definition (Conditional independence).** Let $\mathcal{G} \subseteq \mathcal{F}$. Two $\sigma$-algebras $\mathcal{M}_1, \mathcal{M}_2 \subseteq \mathcal{F}$ are *conditionally independent given $\mathcal{G}$* if
$$P(A \cap B \mid \mathcal{G}) = P(A \mid \mathcal{G})\, P(B \mid \mathcal{G}) \quad \text{a.s., for all } A \in \mathcal{M}_1,\ B \in \mathcal{M}_2.$$
Two variables $X$ and $Y$ are conditionally independent given $\mathcal{G}$ if $\sigma(X)$ and $\sigma(Y)$ are. Events and families are treated in the same way as in Chapter 2.

::: mathlib
`ProbabilityTheory.CondIndep` · `Mathlib.Probability.Independence.Conditional`

`CondIndep m' m₁ m₂ hm' μ` is defined as `Kernel.Indep m₁ m₂ (condExpKernel μ m') (μ.trim hm')`: the independence with respect to a kernel of Chapter 2, for the kernel of regular conditional probabilities. It needs a standard Borel space and a finite measure. `condIndep_iff` gives the form of the text, with `μ[(t1 ∩ t2).indicator 1 | m'] =ᵐ[μ] μ[t1.indicator 1 | m'] * μ[t2.indicator 1 | m']`. The versions for events and for families are `CondIndepSet` with `condIndepSet_iff`, and `iCondIndep`.

<?decl ProbabilityTheory.CondIndep?>
:::

::: mathlib
`ProbabilityTheory.CondIndepFun` · `Mathlib.Probability.Independence.Conditional`

`CondIndepFun m' hm' f g μ` is the conditional independence of the σ-algebras `comap f` and `comap g`, again through `Kernel.IndepFun`. For families there is `iCondIndepFun`. The basic rules are `CondIndepFun.symm` and `CondIndepFun.comp`, as for `IndepFun`.

<?decl ProbabilityTheory.CondIndepFun?>
:::

### Theorems and proofs

**Theorem (Existence of regular conditional probabilities).** Let $(\Omega, \mathcal{F})$ be a standard Borel space, let $P$ be a finite measure and let $\mathcal{G} \subseteq \mathcal{F}$. Then a regular conditional probability given $\mathcal{G}$ exists, and it is unique up to a $P$-null set of $\omega$.

*Proof (sketch).* A standard Borel space is isomorphic to a Borel subset of $\mathbb{R}$, so it is sufficient to treat $\Omega \subseteq \mathbb{R}$. For each rational $q$, choose a version $F(\omega, q)$ of $P((-\infty, q] \mid \mathcal{G})$. Countably many conditions say that $q \mapsto F(\omega, q)$ is monotone with the limits $0$ and $1$ and is right continuous along the rationals. Each condition holds a.s., so they all hold outside one null set $N$. For $\omega \notin N$, $F(\omega, \cdot)$ extends to a distribution function, and it defines a probability measure $\kappa(\omega, \cdot)$ by the correspondence of Chapter 1. On $N$, take a fixed probability measure. A monotone class argument shows that $\kappa(\cdot, A)$ is a version of $P(A \mid \mathcal{G})$ for each Borel $A$. Uniqueness: two such kernels agree a.s. on the countable $\pi$-system of the intervals $(-\infty, q]$, so a.s. on all of $\mathcal{F}$. $\square$

The proof in Mathlib goes through the same steps, with the conditional distribution function `condCDF` of Chapter 8 and the disintegration of a measure on a product space.

**Theorem (Conditional expectation as an integral).** Under the hypotheses above, for an integrable $X$,
$$E[X \mid \mathcal{G}](\omega) = \int X(\omega')\, \kappa(\omega, d\omega') \quad \text{for a.e. } \omega.$$

*Proof.* For $X = \mathbf{1}_A$ this is the definition. Both sides are linear in $X$, so it holds for simple $X$. For $X \ge 0$, take simple $X_n \uparrow X$: the left side converges by conditional monotone convergence and the right side by monotone convergence for each $\omega$. The general case follows from $X = X^+ - X^-$. $\square$

::: mathlib
`ProbabilityTheory.condExp_ae_eq_integral_condExpKernel` · `Mathlib.Probability.Kernel.Condexp`

For `m ≤ mΩ` and an integrable `f` with values in a Banach space, `μ[f | m] =ᵐ[μ] fun ω ↦ ∫ y, f y ∂(condExpKernel μ m ω)`. The disintegration identity behind it is `compProd_trim_condExpKernel`: `(μ.trim hm) ⊗ₘ condExpKernel μ m` is the image of `μ` under the diagonal map $\omega \mapsto (\omega, \omega)$.

<?decl ProbabilityTheory.condExp_ae_eq_integral_condExpKernel?>
:::

**Theorem (Criterion for conditional independence of variables).** Let $X, Y$ be measurable. Then $X$ and $Y$ are conditionally independent given $\mathcal{G}$ if and only if, for all measurable $S, T$,
$$P(X \in S, Y \in T \mid \mathcal{G}) = P(X \in S \mid \mathcal{G})\, P(Y \in T \mid \mathcal{G}) \quad \text{a.s.}$$

*Proof.* The sets $\{X \in S\}$ are exactly the sets of $\sigma(X)$, so this is the definition for $\sigma(X)$ and $\sigma(Y)$. In the kernel form the step needs care: the kernel statement says that for a.e. $\omega$ the measure $\kappa(\omega, \cdot)$ makes $A$ and $B$ independent. The two forms agree because $\kappa(\cdot, A)$ is a version of $P(A \mid \mathcal{G})$ for each $A$, and because the null set may depend on $A$ and $B$ in both forms. $\square$

::: mathlib
`ProbabilityTheory.condIndepFun_iff_condExp_inter_preimage_eq_mul` · `Mathlib.Probability.Independence.Conditional`

For measurable `f` and `g`, `CondIndepFun m' hm' f g μ` is equivalent to `μ[(f ⁻¹' s ∩ g ⁻¹' t).indicator 1 | m'] =ᵐ[μ] μ[(f ⁻¹' s).indicator 1 | m'] * μ[(g ⁻¹' t).indicator 1 | m']` for all measurable `s`, `t`. When the conditioning is on a variable `k`, `condIndepFun_iff_map_prod_eq_prod_condDistrib_prod_condDistrib` gives a form with laws: the joint law of `(k, f, g)` is the law of `k` combined with the product of the conditional laws of `f` and `g` given `k`.

<?decl ProbabilityTheory.condIndepFun_iff_condExp_inter_preimage_eq_mul?>
:::

### Examples

**Example (Conditioning on an event).** Let $B$ be an event with $P(B) > 0$ and $\mathcal{G} = \sigma(B)$. Then $\kappa(\omega, \cdot) = P(\cdot \mid B)$ for a.e. $\omega \in B$: the regular conditional probability on $B$ is the conditional measure of Chapter 1. This is `condExpKernel_singleton_ae_eq_cond`. Two events $A_1, A_2$ are conditionally independent given $\sigma(B)$ when they are independent under $P(\cdot \mid B)$ and under $P(\cdot \mid B^c)$.

**Example (A common cause).** Choose a coin at random: a fair coin with probability $1/2$, and a coin with $P(\text{heads}) = 0.9$ with probability $1/2$. Let $C$ be the choice, and toss the chosen coin twice, with results $X_1$ and $X_2$. Given $C$, the tosses are independent, so $X_1$ and $X_2$ are conditionally independent given $\sigma(C)$. They are not independent: $P(X_1 = H) = (0.5 + 0.9)/2 = 0.7$, and $P(X_1 = X_2 = H) = (0.25 + 0.81)/2 = 0.53 \ne 0.49$. The first toss gives information about the coin, and so about the second toss.

**Counterexample (Independence does not give conditional independence).** Let $X_1, X_2$ be independent fair bits and let $Z = X_1 + X_2 \bmod 2$. Then $X_1$ and $X_2$ are independent, but given $\sigma(Z)$ they are not: on $\{Z = 0\}$, $X_2 = X_1$, so $P(X_1 = 1, X_2 = 1 \mid Z) = 1/2$ on this event, while $P(X_1 = 1 \mid Z)P(X_2 = 1 \mid Z) = 1/4$. Conditioning on a common effect creates a dependence.

### The library around it

`Mathlib.Probability.Kernel.Condexp` has the kernel `condExpKernel`, its measurability and integrability lemmas, and the identification with `condExp`. `Mathlib.Probability.Independence.Conditional` repeats the theory of Chapter 2 for conditional independence: π-systems (`CondIndepSets.condIndep`), unions of σ-algebras (`condIndep_iSup_of_disjoint`), finite families (`iCondIndepFun.condIndepFun_finset`) and the algebraic rules (`iCondIndepFun.indepFun_add_left`). The general theory of kernels, which this section uses, is in Chapter 8. The independence of Chapter 2 is the special case where the conditioning σ-algebra is trivial.

Common errors of a learner:

- `CondIndep` needs `[StandardBorelSpace Ω]` and a finite measure, because it is defined through `condExpKernel`. The unconditional `Indep` has no such hypothesis.
- The σ-algebra of the conditioning is an explicit argument, followed by the proof `hm' : m' ≤ mΩ`. For the conditioning on a variable `k`, use `MeasurableSpace.comap k inferInstance` and its proof `k_meas.comap_le`.
- `condExpKernel μ m` is defined for every σ-algebra `m`, also when `m` is not below `mΩ`. Then the lemmas give the conditional expectation for `m ⊓ mΩ`, as in `condExp_ae_eq_integral_condExpKernel'`.

### Exercises

1. (A) Show that if $X$ is $\mathcal{G}$-measurable, then $X$ and each $Y$ are conditionally independent given $\mathcal{G}$.
2. (A) In the example of the common cause, compute $P(X_2 = H \mid X_1 = H)$.
3. (A) Show that conditional independence given the trivial $\sigma$-algebra $\{\emptyset, \Omega\}$ is the same as independence.
4. (B) Let $X, Y, Z$ be variables with $X$ and $Y$ conditionally independent given $\sigma(Z)$. Show that $E[XY \mid Z] = E[X \mid Z]E[Y \mid Z]$ for bounded $X, Y$.
5. (B) Let $X$ and $Y$ be conditionally independent given $\mathcal{G}$, and let $\mathcal{G}$ and $\sigma(X)$ be independent. Show that $X$ and $\sigma(Y) \vee \mathcal{G}$ are independent.
6. (B) Let $(X, Y)$ have a density $f(x, y)$ on $\mathbb{R}^2$. Show that $\kappa(x, dy) = f(x, y)\,dy/\int f(x, y')\,dy'$ is a regular conditional law of $Y$ given $X = x$, where the denominator is positive.
7. (C) Let $X$ be a real variable on a standard Borel space. Show that a regular conditional probability given $\sigma(X)$ can be chosen in the form $\kappa(\omega, \cdot) = \nu(X(\omega), \cdot)$ for a Markov kernel $\nu$ from $\mathbb{R}$ to $\Omega$, and that $\nu$ is unique up to a null set for the law of $X$.

### Notes and history

Kolmogorov's definition of 1933 gives a conditional probability for each event separately. A choice that is a measure for each $\omega$ needs a hypothesis on the space, and standard Borel spaces are the usual setting for it. The notion of conditional independence is central in the theory of Markov chains, where the future and the past are conditionally independent given the present, and in graphical models in statistics.

### Reference

<?reference?>
