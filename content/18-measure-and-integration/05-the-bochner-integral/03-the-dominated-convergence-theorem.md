---
title: The dominated convergence theorem
kind: theory
modules:
  - Mathlib.MeasureTheory.Integral.DominatedConvergence
  - Mathlib.MeasureTheory.Function.Egorov
  - Mathlib.MeasureTheory.Function.ConvergenceInMeasure
  - Mathlib.MeasureTheory.Function.ConvergenceInDistribution
explains:
  E3: [MeasureTheory.tendsto_integral_of_dominated_convergence, MeasureTheory.integral_tsum, MeasureTheory.tendstoUniformlyOn_of_ae_tendsto, MeasureTheory.TendstoInMeasure]
  E2: [MeasureTheory.tendsto_integral_filter_of_dominated_convergence, MeasureTheory.hasSum_integral_of_dominated_convergence, MeasureTheory.integral_tsum_of_summable_integral_norm, intervalIntegral.continuous_of_dominated_interval, MeasureTheory.tendstoInMeasure_of_tendsto_ae, MeasureTheory.TendstoInMeasure.exists_seq_tendsto_ae]
  E1: auto
families: []
requires: [V13, V15, V18.C02, V18.C03, V18.C04]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The dominated convergence theorem

### Overview

The dominated convergence theorem is the main tool to exchange a limit and an integral. It says that $\int f_n \to \int f$ when $f_n \to f$ almost everywhere and one integrable function bounds every $\|f_n\|$. This section proves it for the Bochner integral of Section 2 of this chapter, from the theorem for $[0, \infty]$ in Chapter 4, Section 2. Its corollaries are the integral of a series and the continuity of an integral that depends on a parameter. The section ends with two other modes of convergence: almost uniform convergence, through the theorem of Egorov, and convergence in measure.

### Definitions

Throughout, $E$ is a Banach space and $(X, \mathcal{A}, \mu)$ a measure space.

**Definition (Convergence in measure).** Functions $f_n : X \to E$ *converge in measure* to $f$ if for every $\varepsilon > 0$,
$$\mu(\{x : \|f_n(x) - f(x)\| \ge \varepsilon\}) \to 0.$$

**Definition (Almost uniform convergence).** Functions $f_n$ converge to $f$ *almost uniformly* on $S$ if for every $\varepsilon > 0$ there is a measurable $T \subseteq S$ with $\mu(T) \le \varepsilon$ such that $f_n \to f$ uniformly on $S \setminus T$.

::: mathlib
`MeasureTheory.TendstoInMeasure` · `Mathlib.MeasureTheory.Function.ConvergenceInMeasure`

`TendstoInMeasure μ f l g` says that for every `ε > 0`, `μ {x | ε ≤ edist (f i x) (g x)}` tends to $0$ along the filter `l`. The target needs only an extended distance.

<?decl MeasureTheory.TendstoInMeasure?>
:::

### Theorems and proofs

**Lemma (Limits stay measurable).** If $f_n$ are almost everywhere strongly measurable and $f_n \to f$ almost everywhere, then $f$ is almost everywhere strongly measurable.

*Proof.* Change each $f_n$ on a null set so that it is strongly measurable. The countably many null sets and the set where $f_n \not\to f$ have a null union $N$. Outside $N$, $f$ is the pointwise limit of $f_n$. By the theorem of Section 1, each $f_n$ is measurable with separable range. The proof of that theorem shows that the limit $f \mathbf{1}_{X \setminus N}$ is measurable, and its range lies in the closure of the union of the ranges of the $f_n$ and of $\{0\}$, a separable set. So $f \mathbf{1}_{X \setminus N}$ is strongly measurable, and it equals $f$ almost everywhere. $\square$

**Theorem (Dominated convergence).** Let $f_n : X \to E$ be almost everywhere strongly measurable with $f_n \to f$ almost everywhere. Let $g : X \to \mathbb{R}$ be integrable with $\|f_n\| \le g$ almost everywhere for every $n$. Then $f$ is integrable and
$$\int f_n \, d\mu \to \int f \, d\mu.$$

*Proof.* Outside a null set, $\|f\| = \lim_n \|f_n\| \le g$. With the lemma, domination in Section 1 shows that $f$ is integrable. The functions $f_n$ are integrable for the same reason. Put $h_n = \|f_n - f\|$. Then $h_n \to 0$ and $h_n \le 2g$ almost everywhere, and $\int 2g \, d\mu < \infty$. The dominated convergence theorem of Chapter 4, Section 2, for the functions $h_n$ with values in $[0, \infty)$, with the theorem on real functions of Section 2, gives $\int h_n \, d\mu \to 0$. Linearity and the norm bound of Section 2 give
$$\Big\| \int f_n \, d\mu - \int f \, d\mu \Big\| = \Big\| \int (f_n - f) \, d\mu \Big\| \le \int h_n \, d\mu \to 0. \qquad \square$$

::: mathlib
`MeasureTheory.tendsto_integral_of_dominated_convergence` · `Mathlib.MeasureTheory.Integral.DominatedConvergence`

The arguments are `bound : α → ℝ`, `∀ n, AEStronglyMeasurable (F n) μ`, `Integrable bound μ`, `∀ n, ∀ᵐ a ∂μ, ‖F n a‖ ≤ bound a`, and `∀ᵐ a ∂μ, Tendsto (fun n ↦ F n a) atTop (𝓝 (f a))`. The conclusion is a `Tendsto` of the integrals. The form `tendsto_integral_filter_of_dominated_convergence` replaces `atTop` on ℕ by a countably generated filter, and its hypotheses need only hold eventually.

<?decl MeasureTheory.tendsto_integral_of_dominated_convergence?>
<?decl MeasureTheory.tendsto_integral_filter_of_dominated_convergence?>
:::

**Corollary (Series).** Let $f_k$ be integrable with $\sum_k \int \|f_k\| \, d\mu < \infty$. Then $\sum_k f_k(x)$ converges for almost every $x$, its sum is integrable, and
$$\int \sum_k f_k \, d\mu = \sum_k \int f_k \, d\mu.$$

*Proof.* Put $G = \sum_k \|f_k\|$, with values in $[0, \infty]$. The corollary on series of Chapter 4, Section 2 gives $\int G \, d\mu = \sum_k \int \|f_k\| \, d\mu < \infty$, so $G < \infty$ almost everywhere by the Markov inequality. At such a point the series $\sum_k f_k(x)$ converges absolutely, so it converges in the complete space $E$, as in Section 1. The partial sums $S_n = \sum_{k \le n} f_k$ satisfy $\|S_n\| \le G$. Dominated convergence with the bound $G$ gives $\int S_n \, d\mu \to \int \sum_k f_k \, d\mu$, and $\int S_n \, d\mu = \sum_{k \le n} \int f_k \, d\mu$ by linearity. $\square$

::: mathlib
`MeasureTheory.integral_tsum` · `Mathlib.MeasureTheory.Integral.DominatedConvergence`

`∫ a, ∑' i, f i a ∂μ = ∑' i, ∫ a, f i a ∂μ` for a countable index type, with `∀ i, AEStronglyMeasurable (f i) μ` and `∑' i, ∫⁻ a, ‖f i a‖ₑ ∂μ ≠ ⊤`. The form `integral_tsum_of_summable_integral_norm` takes integrable terms and a summable series of `∫ a, ‖F i a‖ ∂μ`. `hasSum_integral_of_dominated_convergence` allows a separate bound for each term.

<?decl MeasureTheory.integral_tsum?>
<?decl MeasureTheory.integral_tsum_of_summable_integral_norm?>
<?decl MeasureTheory.hasSum_integral_of_dominated_convergence?>
:::

**Corollary (Continuity of parameter integrals).** Let $Y$ be a metric space and $F : Y \times X \to E$ with each $F(y, \cdot)$ almost everywhere strongly measurable. Let $g$ be integrable with $\|F(y, x)\| \le g(x)$ for all $y$ and almost every $x$, and let $y \mapsto F(y, x)$ be continuous for almost every $x$. Then $y \mapsto \int F(y, x) \, d\mu(x)$ is continuous.

*Proof.* In a metric space, continuity at $y$ follows from sequential continuity. Let $y_n \to y$. For almost every $x$, $F(y_n, x) \to F(y, x)$. The bound $g$ does not depend on $n$, and the theorem gives $\int F(y_n, x) \, d\mu(x) \to \int F(y, x) \, d\mu(x)$. $\square$

::: mathlib
`intervalIntegral.continuous_of_dominated_interval` · `Mathlib.MeasureTheory.Integral.DominatedConvergence`

The corollary for an integral over an interval, which Chapter 8 defines. The general form `MeasureTheory.continuous_of_dominated` is in `Mathlib.MeasureTheory.Integral.Bochner.Basic` and needs only a first countable parameter space.

<?decl intervalIntegral.continuous_of_dominated_interval?>
<?decl MeasureTheory.continuous_of_dominated?>
:::

**Theorem (Egorov).** Let $S$ be measurable with $\mu(S) < \infty$, let $f_n, f : X \to E$ be strongly measurable, and let $f_n \to f$ almost everywhere on $S$. Then $f_n \to f$ almost uniformly on $S$.

*Proof.* For $k, n \ge 1$ put
$$B_{k,n} = \bigcup_{m \ge n} \{x \in S : \|f_m(x) - f(x)\| \ge 1/k\}.$$
These sets are measurable, since $x \mapsto \|f_m(x) - f(x)\|$ is measurable by Section 1. For fixed $k$ they decrease in $n$, and a point of $\bigcap_n B_{k,n}$ is a point of $S$ where $f_n(x) \not\to f(x)$. So $\mu(\bigcap_n B_{k,n}) = 0$. Since $\mu(S) < \infty$, continuity from above (Chapter 2) gives $\mu(B_{k,n}) \to 0$ as $n \to \infty$.

Let $\varepsilon > 0$. Choose $n_k$ with $\mu(B_{k, n_k}) \le \varepsilon 2^{-k}$, and put $T = \bigcup_k B_{k, n_k}$. Then $\mu(T) \le \varepsilon$. For $x \in S \setminus T$ and $m \ge n_k$, $x \notin B_{k, n_k}$ gives $\|f_m(x) - f(x)\| < 1/k$. This bound does not depend on $x$, so the convergence is uniform on $S \setminus T$. $\square$

::: mathlib
`MeasureTheory.tendstoUniformlyOn_of_ae_tendsto` · `Mathlib.MeasureTheory.Function.Egorov`

The hypotheses are `StronglyMeasurable` for each `f n` and for `g`, `MeasurableSet s`, `μ s ≠ ⊤`, `∀ᵐ x ∂μ, x ∈ s → Tendsto (fun n ↦ f n x) atTop (𝓝 (g x))` and `0 < ε`. The conclusion is `∃ t ⊆ s, MeasurableSet t ∧ μ t ≤ ε ∧ TendstoUniformlyOn f g atTop (s \ t)`. The index can be any countable directed type.

<?decl MeasureTheory.tendstoUniformlyOn_of_ae_tendsto?>
:::

**Proposition (Convergence in measure).** (a) If $\mu(X) < \infty$ and $f_n \to f$ almost everywhere, with all functions strongly measurable, then $f_n \to f$ in measure. (b) If $f_n \to f$ in measure, a subsequence converges to $f$ almost everywhere.

*Proof.* (a) Let $\varepsilon, \delta > 0$. Egorov with $S = X$ gives $T$ with $\mu(T) \le \delta$ and uniform convergence on $X \setminus T$. For large $n$, $\|f_n - f\| < \varepsilon$ on $X \setminus T$, so $\mu(\{\|f_n - f\| \ge \varepsilon\}) \le \delta$.

(b) Choose $n_1 < n_2 < \dots$ with $\mu(A_k) \le 2^{-k}$, where $A_k = \{\|f_{n_k} - f\| \ge 2^{-k}\}$. Then $\sum_k \mu(A_k) < \infty$. By Exercise 6 of Chapter 4, Section 2, almost every $x$ lies in only finitely many $A_k$. For such $x$, $\|f_{n_k}(x) - f(x)\| < 2^{-k}$ for all large $k$, so $f_{n_k}(x) \to f(x)$. $\square$

::: mathlib
`MeasureTheory.tendstoInMeasure_of_tendsto_ae` · `Mathlib.MeasureTheory.Function.ConvergenceInMeasure`

Part (a), with `[IsFiniteMeasure μ]` and `AEStronglyMeasurable` functions. Part (b) is `TendstoInMeasure.exists_seq_tendsto_ae`, which returns a `StrictMono` map `ns : ℕ → ℕ`.

<?decl MeasureTheory.tendstoInMeasure_of_tendsto_ae?>
<?decl MeasureTheory.TendstoInMeasure.exists_seq_tendsto_ae?>
:::

### Examples

**Example (Powers on the unit interval).** Let $f_n(x) = x^n$ on $[0, 1]$. Then $f_n \to 0$ at every $x < 1$, so almost everywhere, and $|f_n| \le 1$, which is integrable on $[0, 1]$. So $\int_{[0,1]} x^n \, d\lambda \to 0$, with no computation of the integrals. Egorov is visible here: the convergence is uniform on $[0, 1 - \delta]$, and not on $[0, 1)$.

**Example (A continuous parameter integral).** Let $\Phi(t) = \int_{\mathbb{R}} e^{-|x|} \cos(tx) \, d\lambda(x)$. The integrand is continuous in $t$, and $|e^{-|x|} \cos(tx)| \le e^{-|x|}$, which is integrable by Exercise 1 of Section 1. The corollary shows that $\Phi$ is continuous on $\mathbb{R}$.

**Counterexample (No integrable bound).** Let $f_n = n \mathbf{1}_{(0, 1/n)}$ on $[0, 1]$. Then $f_n \to 0$ at every point and $\int f_n \, d\lambda = 1$, so the conclusion fails. The smallest bound is $\sup_n f_n$, which is at least $\frac{1}{2x}$ on $(0, \frac12)$, and $1/x$ is not integrable by the example of Section 1.

**Counterexample (Convergence in measure without pointwise limit).** On $[0, 1]$, list the dyadic intervals $[j 2^{-k}, (j+1) 2^{-k}]$ in the order of $k$ and then $j$, and let $f_n$ be the indicator of the $n$-th one. Then $\lambda(\{f_n \ne 0\}) \to 0$, so $f_n \to 0$ in measure. But every $x$ lies in one interval of each level $k$, so $f_n(x) = 1$ for infinitely many $n$, and $f_n(x) \not\to 0$. The subsequence of the intervals $[0, 2^{-k}]$ converges to $0$ at every $x > 0$, as part (b) predicts.

### The library around it

The file `Mathlib.MeasureTheory.Integral.DominatedConvergence` holds the theorem, its forms for series and for interval integrals, and the continuity of parameter integrals over intervals. Differentiation under the integral sign is in `Mathlib.Analysis.Calculus.ParametricIntegral`. It rests on dominated convergence for the difference quotients.

Convergence in measure has a weaker relative for random variables. The predicate `MeasureTheory.TendstoInDistribution X l Z μ` says that the laws of the functions $X_n$ under the probability measures $\mu_n$ converge weakly to the law of $Z$: the integrals of every bounded continuous function converge. The functions may live on different spaces. Convergence in measure implies convergence in distribution, by `MeasureTheory.TendstoInMeasure.tendstoInDistribution`, and convergence almost everywhere does too, by `MeasureTheory.tendstoInDistribution_of_ae_tendsto`. The continuous mapping theorem is `MeasureTheory.TendstoInDistribution.continuous_comp`. The lemma `MeasureTheory.tendstoInDistribution_of_tendstoInMeasure_sub` says that if $X_n \to Z$ in distribution and $Y_n - X_n \to 0$ in measure, then $Y_n \to Z$ in distribution. The theorem of Slutsky, `MeasureTheory.TendstoInDistribution.prodMk_of_tendstoInMeasure_const`, follows: if $Y_n \to c$ in measure for a constant $c$, then $(X_n, Y_n) \to (Z, c)$ in distribution. The limit law is unique, by `MeasureTheory.tendstoInDistribution_unique`.

Common errors of a learner:

- Using a bound that depends on $n$. The bound $g$ must work for every $n$.
- Forgetting the measurability of each $f_n$. The limit needs none.
- Applying Egorov on a set of infinite measure: $\mathbf{1}_{[n, n+1]} \to 0$ on $\mathbb{R}$, but not uniformly outside any set of finite measure.
- Expecting convergence in measure to give convergence almost everywhere of the whole sequence.

### Exercises

1. (A) Compute $\lim_n \int_{[0, \infty)} e^{-nx} \, d\lambda(x)$. Hint: $e^{-nx} \le e^{-x}$ for $n \ge 1$.
2. (A) Show that $\int_{[0,1]} \frac{n x}{1 + n^2 x^2} \, d\lambda \to 0$. Hint: $2nx \le 1 + n^2 x^2$.
3. (A) Show that the sequence $\mathbf{1}_{[n, n+1]}$ on $\mathbb{R}$ does not converge in measure to $0$.
4. (B) Let $f$ be integrable on $\mathbb{R}$. Show that $t \mapsto \int f(x) e^{-itx} \, d\lambda(x)$ is continuous. Hint: the corollary on parameter integrals.
5. (B) Let $f$ be integrable. Show that $\int_{[-n, n]} f \, d\lambda \to \int f \, d\lambda$. Hint: $f_n = f \mathbf{1}_{[-n, n]}$.
6. (B) Show that $\sum_{k \ge 1} \int_{[0,1]} x^k (1 - x) \, d\lambda = \int_{[0,1]} x \, d\lambda$. Hint: the corollary on series of Chapter 4, Section 2.
7. (C) Let $\mu(X) < \infty$, $f_n \to f$ in measure, and $\|f_n\| \le g$ with $g$ integrable. Show that $\int f_n \, d\mu \to \int f \, d\mu$. Hint: if not, take a subsequence that stays away from $\int f$, and use part (b).

### Notes and history

The dominated convergence theorem carries the name of Lebesgue. In Mathlib, the file on dominated convergence has Zhouhang Zhou, Yury Kudryashov, Patrick Massot and Louis (Yiyang) Liu as authors, the file on the theorem of Egorov has Kexing Ying, and the file on convergence in measure has Rémy Degenne and Kexing Ying.

### Reference

<?reference?>
