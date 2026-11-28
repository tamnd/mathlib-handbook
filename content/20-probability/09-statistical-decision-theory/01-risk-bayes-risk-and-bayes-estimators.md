---
title: Risk, Bayes risk and Bayes estimators
kind: api
modules:
  - Mathlib.Probability.Decision.Risk.Defs
  - Mathlib.Probability.Decision.Risk.Basic
  - Mathlib.Probability.Decision.Risk.Countable
  - Mathlib.Probability.Decision.Risk.RiskIncrease
  - Mathlib.Probability.Decision.BayesEstimator
explains:
  E2: [ProbabilityTheory.avgRisk, ProbabilityTheory.bayesRisk, ProbabilityTheory.minimaxRisk, ProbabilityTheory.bayesRisk_le_minimaxRisk, ProbabilityTheory.bayesRisk_le_bayesRisk_comp, ProbabilityTheory.bayesRisk_const, ProbabilityTheory.riskIncrease, ProbabilityTheory.riskIncrease_comp_le, ProbabilityTheory.IsBayesEstimator, ProbabilityTheory.IsArgminEstimator.isBayesEstimator]
  E1: auto
families: []
requires: [V18, V20.C01, V20.C08]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Risk, Bayes risk and Bayes estimators

### Overview

An estimation problem has four parts. The parameter space $\Theta$ contains the unknown parameter. The data generating kernel $P$ from $\Theta$ to the data space $\mathcal{X}$ gives the law $P(\theta)$ of the data for each parameter. The space $\mathcal{Y}$ contains the estimates, and it is often $\Theta$ itself. The loss $\ell : \Theta \to \mathcal{Y} \to [0, \infty]$ gives the cost $\ell(\theta, y)$ of the estimate $y$ when the parameter is $\theta$. Lower is better.

An estimator is a Markov kernel $\kappa$ from $\mathcal{X}$ to $\mathcal{Y}$. A deterministic estimator $x \mapsto f(x)$ is the Dirac kernel of $f$, but a kernel also allows randomized estimators. The data is drawn from $P(\theta)$ and the estimate from $\kappa(x)$, so the estimate has the law $(\kappa \circ P)(\theta)$. The risk of $\kappa$ at $\theta$ is the mean loss
$$R(\theta, \kappa) = \int \ell(\theta, y) \, d(\kappa \circ P)(\theta)(y).$$

A risk is a function of $\theta$, and two estimators are seldom ordered for all $\theta$ at once. The theory reduces the function to one number in two ways. The Bayesian way takes a prior measure $\pi$ on $\Theta$ and averages: the average risk is $\int R(\theta, \kappa) \, d\pi(\theta)$, and the Bayes risk is the infimum of the average risk over all estimators. The minimax way takes the worst case: the minimax risk is the infimum over estimators of $\sup_\theta R(\theta, \kappa)$. The Bayes risk for each prior is at most the minimax risk.

Two further results are in this section. The data processing inequality says that a further random transformation of the data cannot lower the Bayes risk. And a Bayes estimator can be found point by point: for each $x$, choose the estimate that minimizes the posterior mean loss.

### The library around it

#### The three risks

The module `Mathlib.Probability.Decision.Risk.Defs` defines the three risks, all with values in $[0, \infty]$. Mathlib gives no name to the risk $R(\theta, \kappa)$ itself. The lemma names call the integral $\int \ell(\theta, y) \, d(\kappa \circ P)(\theta)(y)$ the risk.

- `ProbabilityTheory.avgRisk` $\ell$ $P$ $\kappa$ $\pi$ is the average risk $\int R(\theta, \kappa) \, d\pi(\theta)$.
- `ProbabilityTheory.bayesRisk` $\ell$ $P$ $\pi$ is the infimum of the average risk over all Markov kernels $\kappa$.
- `ProbabilityTheory.minimaxRisk` $\ell$ $P$ is the infimum over all Markov kernels of $\sup_\theta R(\theta, \kappa)$.

The module also proves that the risks are $0$ when the loss, the kernel or the prior is $0$, and when one of the spaces is empty. Because the values are in $[0, \infty]$, no integrability hypothesis is needed, and the definitions apply to all losses.

#### Comparison and data processing

The module `Mathlib.Probability.Decision.Risk.Basic` proves the main inequalities. The theorem `ProbabilityTheory.bayesRisk_le_avgRisk` says that the Bayes risk is at most the average risk of each estimator, and `ProbabilityTheory.avgRisk_le_iSup_risk` says that for a probability prior the average risk is at most the worst risk. Together they give `ProbabilityTheory.bayesRisk_le_minimaxRisk`, and then `ProbabilityTheory.iSup_bayesRisk_le_minimaxRisk`: the supremum of the Bayes risks over all priors is at most the minimax risk. The equality is the minimax theorem, which needs more hypotheses and is not in this module.

The theorem `ProbabilityTheory.bayesRisk_le_bayesRisk_comp` is the data processing inequality. For a Markov kernel $\eta$ from $\mathcal{X}$ to $\mathcal{X}'$,
$$\mathrm{bayesRisk}(\ell, P, \pi) \le \mathrm{bayesRisk}(\ell, \eta \circ P, \pi).$$
The proof is short: each estimator $\kappa$ for the data $\eta \circ P$ gives the estimator $\kappa \circ \eta$ for the data $P$, with the same average risk. The theorem `ProbabilityTheory.bayesRisk_le_bayesRisk_map` is the case of a measurable map, and `ProbabilityTheory.minimaxRisk_le_minimaxRisk_comp` is the minimax version. The theorem `ProbabilityTheory.bayesRisk_compProd_le_bayesRisk` says that more data, in the form $P \otimes \eta$, can only lower the risk.

Data that does not depend on $\theta$ carries no information. The theorem `ProbabilityTheory.bayesRisk_const` says that for a constant kernel the Bayes risk is $\inf_y \int \ell(\theta, y) \, d\pi(\theta)$, the best risk of a constant estimate. The theorem `ProbabilityTheory.bayesRisk_discard` is the same statement for the kernel that discards the data. The theorem `ProbabilityTheory.bayesRisk_le_iInf` says that the Bayes risk is at most this value for each Markov kernel $P$, and `ProbabilityTheory.bayesRisk_lt_top` gives finiteness for a bounded loss.

#### Countable parameter spaces

The module `Mathlib.Probability.Decision.Risk.Countable` writes the integral over $\pi$ as a sum when $\Theta$ is countable. The theorem `ProbabilityTheory.avgRisk_countable` gives $\mathrm{avgRisk} = \sum_\theta R(\theta, \kappa) \, \pi(\{\theta\})$, and `ProbabilityTheory.avgRisk_fintype` is the version with a finite sum. The theorems `ProbabilityTheory.bayesRisk_countable` and `ProbabilityTheory.bayesRisk_fintype` give the same form for the Bayes risk. The primed variants write the integral over the estimates as a sum when $\mathcal{Y}$ is countable. Hypothesis testing, with two parameters and two estimates, is the main application.

#### The risk increase

The module `Mathlib.Probability.Decision.Risk.RiskIncrease` measures how much the data helps. The quantity `ProbabilityTheory.riskIncrease` $\ell$ $P$ $\pi$ is the Bayes risk without the data minus the Bayes risk with the data:
$$\mathrm{riskIncrease}(\ell, P, \pi) = \mathrm{bayesRisk}(\ell, \mathrm{discard} \circ P, \pi) - \mathrm{bayesRisk}(\ell, P, \pi).$$
The subtraction is truncated at $0$ in $[0, \infty]$. For a Markov kernel $P$, the theorem `ProbabilityTheory.riskIncrease_eq_iInf_sub` writes the first term as $\inf_y \int \ell(\theta, y) \, d\pi(\theta)$. The theorem `ProbabilityTheory.riskIncrease_comp_le` is the data processing inequality for this quantity: $\mathrm{riskIncrease}(\ell, \eta \circ P, \pi) \le \mathrm{riskIncrease}(\ell, P, \pi)$. With a suitable loss, the risk increase is a statistical divergence, and this inequality becomes the data processing inequality for the divergence.

#### Bayes estimators and the posterior

The module `Mathlib.Probability.Decision.BayesEstimator` uses the posterior kernel $P^\dagger_\pi$ of Section 2 of Chapter 8, `ProbabilityTheory.posterior`. The predicate `ProbabilityTheory.IsBayesEstimator` $\ell$ $P$ $\kappa$ $\pi$ says that $\kappa$ attains the Bayes risk. The theorem `ProbabilityTheory.avgRisk_eq_lintegral_posterior_prod` rewrites the average risk as an integral over the data: first draw $x$ from the marginal $P \circ \pi$, then draw $\theta$ from the posterior and $y$ from $\kappa(x)$. The consequence `ProbabilityTheory.lintegral_iInf_posterior_le_bayesRisk` is a lower bound:
$$\int \inf_y \int \ell(\theta, y) \, dP^\dagger_\pi(x)(\theta) \, d(P \circ \pi)(x) \le \mathrm{bayesRisk}(\ell, P, \pi).$$

A measurable $f : \mathcal{X} \to \mathcal{Y}$ is an argmin estimator, by the structure `ProbabilityTheory.IsArgminEstimator`, when $f(x)$ minimizes the posterior mean loss $y \mapsto \int \ell(\theta, y) \, dP^\dagger_\pi(x)(\theta)$ for almost every $x$. The theorem `ProbabilityTheory.IsArgminEstimator.isBayesEstimator` says that its Dirac kernel `ProbabilityTheory.IsArgminEstimator.kernel` is a Bayes estimator. The structure `ProbabilityTheory.HasArgminEstimator` says that such an $f$ exists, and then `ProbabilityTheory.HasArgminEstimator.bayesRisk_eq` gives equality in the lower bound. The existence of an argmin estimator needs a measurable selection theorem, so Mathlib takes it as a hypothesis. These results need $\Theta$ to be a nonempty standard Borel space, so that the posterior exists.

#### Common errors

1. The risks are in $[0, \infty]$ and the loss is a function into $[0, \infty]$. A real valued loss, such as a squared error written in $\mathbb{R}$, must be converted with `ENNReal.ofReal` before it can be used.
2. The Bayes risk is an infimum over Markov kernels, not over measurable functions. A proof that the Bayes risk is at most a value can use a deterministic estimator, but a proof that it is at least a value must treat all randomized estimators.
3. The quantity `ProbabilityTheory.riskIncrease` uses the truncated subtraction of $[0, \infty]$. When both Bayes risks are infinite the risk increase is $0$, and an identity that adds the two terms back needs the finiteness of the second term.

### Exercises

1. (A) Let $\Theta = \mathcal{Y} = \{0, 1\}$, let $\ell(\theta, y) = 1$ if $y \ne \theta$ and $0$ otherwise, and let $\pi$ give mass $1/2$ to each point. Compute the Bayes risk when the data is discarded.
2. (A) Show that the average risk of the Dirac kernel of $f$ is $\int \int \ell(\theta, f(x)) \, dP(\theta)(x) \, d\pi(\theta)$.
3. (B) Prove the data processing inequality for the Bayes risk: build from an estimator for $\eta \circ P$ an estimator for $P$ with the same average risk.
4. (B) In the setting of Exercise 1, let $P(0)$ and $P(1)$ be two probability measures with densities $p_0$ and $p_1$ with respect to a measure $\mu$. Show that the Bayes risk is $\frac{1}{2} \int \min(p_0, p_1) \, d\mu$ and that the test $f(x) = 1$ if $p_1(x) > p_0(x)$ is a Bayes estimator.
5. (B) Show that the minimax risk is at least the Bayes risk for each probability prior, and give an example on a finite space where some prior attains equality.
6. (C) Let $\mathcal{Y} = \mathbb{R}$ and $\ell(\theta, y) = (\theta - y)^2$ for a real parameter with finite second moment under the prior. Show that the posterior mean is an argmin estimator, and that the Bayes risk is the mean of the posterior variance.

### Reference

<?reference?>
