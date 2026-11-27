---
title: Extreme values and uniform continuity
kind: theory
modules:
  - Mathlib.Analysis.Oscillation
explains:
  E3: [oscillation]
  E2: [oscillationWithin, ContinuousAt.oscillation_eq_zero, ContinuousWithinAt.oscillationWithin_eq_zero, oscillationWithin_univ_eq_oscillation, IsCompact.uniform_oscillation]
  E1: auto
families: []
requires: [V02, V13, V15.C01]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Extreme values and uniform continuity

### Overview

The last section used the completeness of $\mathbb{R}$ through the least upper bound. This section uses it through the Bolzano-Weierstrass theorem of Chapter 1: every bounded sequence of reals has a convergent subsequence. Two theorems follow, both on a closed bounded interval $[a, b]$. The extreme value theorem says that a continuous function on $[a, b]$ is bounded and attains its maximum and minimum. The Heine-Cantor theorem says that it is uniformly continuous.

Both theorems fail on open and on unbounded intervals. The section then treats Lipschitz functions and the oscillation of a function at a point, which measures how far the function is from continuity there.

### Definitions

**Definition (Bounded function).** A function $f : D \to \mathbb{R}$ is *bounded* if $|f(x)| \le C$ for some $C$ and all $x \in D$. It *attains its maximum* at $c \in D$ if $f(x) \le f(c)$ for all $x \in D$, and its minimum if $f(x) \ge f(c)$ for all $x \in D$.

**Definition (Uniform continuity).** A function $f : D \to \mathbb{R}$ is *uniformly continuous* on $D$ if for every $\varepsilon > 0$ there is $\delta > 0$ such that $|f(x) - f(y)| < \varepsilon$ for all $x, y \in D$ with $|x - y| < \delta$.

Remarks. In continuity, $\delta$ may depend on the point; here it depends on $\varepsilon$ only. The negation reads: there are $\varepsilon > 0$ and sequences $x_n, y_n \in D$ with $|x_n - y_n| \to 0$ and $|f(x_n) - f(y_n)| \ge \varepsilon$ for all $n$.

**Definition (Lipschitz function).** Let $K \ge 0$. A function $f$ is *Lipschitz with constant* $K$ on $D$ if $|f(x) - f(y)| \le K |x - y|$ for all $x, y \in D$.

**Definition (Oscillation).** Let $f : \mathbb{R} \to \mathbb{R}$, $a \in \mathbb{R}$, and for $\delta > 0$ let $\omega_f(a, \delta) = \sup \{ |f(x) - f(y)| : x, y \in (a - \delta, a + \delta) \}$, a value in $[0, \infty]$. The *oscillation* of $f$ at $a$ is $\omega_f(a) = \inf_{\delta > 0} \omega_f(a, \delta)$.

Remarks. The value $\omega_f(a, \delta)$ is the diameter of $f((a - \delta, a + \delta))$ and grows with $\delta$, so the infimum is the limit as $\delta \to 0^+$. The value $\infty$ is possible: $f(x) = 1/x$ with $f(0) = 0$ has $\omega_f(0) = \infty$.

::: mathlib
`oscillation` · `Mathlib.Analysis.Oscillation`

The definition is `oscillation f x = ⨅ S ∈ (𝓝 x).map f, Metric.ediam S`, a value in `ℝ≥0∞`. A set `S` is in `(𝓝 x).map f` when its preimage is a neighbourhood of `x`, so this is the infimum of the diameters of the images of the neighbourhoods of `x`: the number $\omega_f(a)$ above. The domain is any topological space and the target any extended metric space. The variant `oscillationWithin f D x` uses `𝓝[D] x`, and `oscillationWithin_univ_eq_oscillation` relates the two.

<?decl oscillation?>
:::

### Theorems and proofs

**Theorem (Extreme value theorem).** Let $a \le b$ and let $f$ be continuous on $[a, b]$. Then $f$ is bounded, and there are $c, d \in [a, b]$ with $f(d) \le f(x) \le f(c)$ for all $x \in [a, b]$.

*Proof.* Boundedness. Assume not. For each $n$ choose $x_n \in [a, b]$ with $|f(x_n)| > n$. By Bolzano-Weierstrass a subsequence $x_{n_k}$ converges to some $c$, and $a \le c \le b$ because $[a, b]$ is closed. By continuity $f(x_{n_k}) \to f(c)$, so the sequence $f(x_{n_k})$ is bounded. But $|f(x_{n_k})| > n_k \ge k$, a contradiction.

Maximum. The set $f([a, b])$ is bounded and not empty, so it has a supremum $M$. For each $n \ge 1$ choose $x_n \in [a, b]$ with $M - 1/n < f(x_n) \le M$. A subsequence $x_{n_k}$ converges to some $c \in [a, b]$. By continuity $f(x_{n_k}) \to f(c)$, and by the squeeze theorem $f(x_{n_k}) \to M$. So $f(c) = M \ge f(x)$ for all $x$. For the minimum apply this to $-f$. $\square$

The proof used three properties of $[a, b]$: bounded, for Bolzano-Weierstrass; closed, so that $c$ stays in it; not empty. These say that $[a, b]$ is a nonempty compact set.

::: mathlib
`IsCompact.exists_isMaxOn` · `Mathlib.Topology.Order.Compact`

The form `IsCompact s → s.Nonempty → ContinuousOn f s → ∃ x ∈ s, IsMaxOn f s x`, and `IsCompact.exists_isMinOn` for the minimum. Here `IsMaxOn f s x` means `∀ y ∈ s, f y ≤ f x`. For an interval the hypotheses come from `CompactIccSpace.isCompact_Icc` and `Set.nonempty_Icc`. Boundedness alone is `IsCompact.bddAbove_image`.

<?decl IsCompact.exists_isMaxOn?>
:::

::: mathlib
`tendsto_subseq_of_bounded` · `Mathlib.Topology.MetricSpace.Sequences`

The Bolzano-Weierstrass theorem in a proper metric space: for a bounded set `s` and a sequence `x` in `s`, there are `a ∈ closure s` and a strictly increasing `φ` with `Tendsto (x ∘ φ) atTop (𝓝 a)`. For `s = Set.Icc a b`, the closure is `s`.

<?decl tendsto_subseq_of_bounded?>
:::

**Theorem (Heine-Cantor).** Let $f$ be continuous on $[a, b]$. Then $f$ is uniformly continuous on $[a, b]$.

*Proof.* Assume not. Then there are $\varepsilon > 0$ and $x_n, y_n \in [a, b]$ with $|x_n - y_n| < 1/n$ and $|f(x_n) - f(y_n)| \ge \varepsilon$ for every $n \ge 1$. A subsequence $x_{n_k}$ converges to some $c \in [a, b]$. Since $|y_{n_k} - c| < 1/n_k + |x_{n_k} - c|$, also $y_{n_k} \to c$. By continuity at $c$, $f(x_{n_k}) - f(y_{n_k}) \to f(c) - f(c) = 0$, which contradicts $|f(x_{n_k}) - f(y_{n_k})| \ge \varepsilon$. $\square$

::: mathlib
`IsCompact.uniformContinuousOn_of_continuous` · `Mathlib.Topology.UniformSpace.HeineCantor`

The form `IsCompact s → ContinuousOn f s → UniformContinuousOn f s`. On a metric space, `Metric.uniformContinuousOn_iff` unfolds `UniformContinuousOn f s` into the $\varepsilon$-$\delta$ form. Mathlib defines uniform continuity with uniform structures, because the notion also makes sense without a metric.

<?decl IsCompact.uniformContinuousOn_of_continuous?>
:::

**Theorem (Lipschitz implies uniformly continuous).** If $f$ is Lipschitz with constant $K$ on $D$, then $f$ is uniformly continuous on $D$.

*Proof.* Let $\delta = \varepsilon / (K + 1)$. For $|x - y| < \delta$, $|f(x) - f(y)| \le K\delta < \varepsilon$. $\square$

::: mathlib
`LipschitzWith` · `Mathlib.Topology.EMetricSpace.Lipschitz`

`LipschitzWith K f` means `∀ x y, edist (f x) (f y) ≤ K * edist x y` with `K : ℝ≥0`. On a metric space `lipschitzWith_iff_dist_le_mul` converts it to `dist (f x) (f y) ≤ K * dist x y`. The theorem above is `LipschitzWith.uniformContinuous`, and `LipschitzOnWith.uniformContinuousOn` is the form on a set. Chapter 3 shows with the mean value theorem that $|f'| \le K$ gives the constant $K$.

<?decl LipschitzWith?>
:::

**Theorem (Oscillation and continuity).** The function $f$ is continuous at $a$ if and only if $\omega_f(a) = 0$.

*Proof.* Assume $f$ is continuous at $a$, and let $\varepsilon > 0$. Choose $\delta$ with $|f(x) - f(a)| < \varepsilon/2$ for $|x - a| < \delta$. For $x, y \in (a - \delta, a + \delta)$, $|f(x) - f(y)| < \varepsilon$. So $\omega_f(a) \le \omega_f(a, \delta) \le \varepsilon$ for every $\varepsilon$, and $\omega_f(a) = 0$. Conversely, if $\omega_f(a) = 0$ and $\varepsilon > 0$, there is $\delta$ with $\omega_f(a, \delta) < \varepsilon$. For $|x - a| < \delta$, both $x$ and $a$ lie in $(a - \delta, a + \delta)$, so $|f(x) - f(a)| < \varepsilon$. $\square$

::: mathlib
`ContinuousAt.oscillation_eq_zero` · `Mathlib.Analysis.Oscillation`

The first half of the theorem: `ContinuousAt f x → oscillation f x = 0`, and `ContinuousWithinAt.oscillationWithin_eq_zero` within a set. At the commit of this handbook the index has no lemma for the converse. The proof above is short.

<?decl ContinuousAt.oscillation_eq_zero?>
:::

::: mathlib
`IsCompact.uniform_oscillation` · `Mathlib.Analysis.Oscillation`

A uniform form on a compact set `K`: if `∀ x ∈ K, oscillation f x < ε`, then `∃ δ > 0, ∀ x ∈ K, Metric.ediam (f '' Metric.eball x (ENNReal.ofReal δ)) ≤ ε`. For a continuous `f` all oscillations are `0`, and the statement gives the Heine-Cantor theorem with `≤ ε`. The proof on paper is the proof of Heine-Cantor: a sequence of bad points has a convergent subsequence, and the limit point has small oscillation (Exercise 6).

<?decl IsCompact.uniform_oscillation?>
:::

### Examples

**Counterexample (Open and unbounded intervals).** Each hypothesis of the extreme value theorem is needed. On $(0, 1)$, $1/x$ is continuous and unbounded: the sequence $1/(n+1)$ has its limit $0$ outside the interval. On $(0, 1)$, $x$ is bounded with supremum $1$ and has no maximum. On $[0, \infty)$, $x$ is unbounded: $x_n = n$ has no convergent subsequence. On $[0, 1]$, $1/x$ with value $0$ at $0$ is unbounded, because it is not continuous at $0$.

**Example ($x^2$ is not uniformly continuous on $\mathbb{R}$).** Let $x_n = n$ and $y_n = n + 1/n$. Then $|x_n - y_n| = 1/n \to 0$, but $y_n^2 - x_n^2 = 2 + 1/n^2 \ge 2$. On $[0, 2]$, $|x^2 - y^2| = |x + y|\,|x - y| \le 4|x - y|$, so $x^2$ is Lipschitz with constant $4$ there, and $\delta = \varepsilon/4$ works.

**Example ($1/x$ on $(0, 1)$ and on $[r, \infty)$).** Let $x_n = 1/n$ and $y_n = 1/(n+1)$. Then $|x_n - y_n| = 1/(n(n+1)) \to 0$, and $|1/x_n - 1/y_n| = 1$. So $1/x$ is not uniformly continuous on $(0, 1)$. For $x, y \ge r > 0$,
$$\left| \frac{1}{x} - \frac{1}{y} \right| = \frac{|x - y|}{x y} \le \frac{|x - y|}{r^2},$$
so $1/x$ is Lipschitz with constant $1/r^2$ on $[r, \infty)$. Mathlib has the related `Real.uniformContinuous_inv`.

**Example (Oscillations).** For the sign function, every interval around $0$ has image $\{-1, 0, 1\}$, so $\omega(0) = 2$ and $\omega(a) = 0$ for $a \ne 0$. For $\mathbf{1}_{\mathbb{Q}}$, $\omega(a) = 1$ everywhere. For the Thomae function, $f(p/q) = 1/q$ in lowest terms and $f = 0$ on the irrationals, a bounded interval contains only finitely many rationals with denominator at most $q$. So around $a = p/q$ a small interval has values $1/q$, $0$ and numbers below $1/q$, and $\omega(p/q) = 1/q$. At irrational $a$ the same argument gives $\omega(a) < \varepsilon$ for every $\varepsilon$, so $\omega(a) = 0$. The Thomae function is continuous exactly at the irrationals.

### The library around it

The extreme value theorem has more forms in `Mathlib.Topology.Order.Compact`, for example `ContinuousOn.image_Icc`, which says that the image of `Set.Icc a b` is a closed interval. The Lipschitz API is in `Mathlib.Topology.EMetricSpace.Lipschitz` and `Mathlib.Topology.MetricSpace.Lipschitz`.

Common errors of a learner:

- Applying the extreme value theorem on an open interval or on `Set.Ici 0`. Mathlib asks for `IsCompact s`.
- Forgetting `s.Nonempty`. A function on the empty set has no maximum.
- Writing the Lipschitz constant as a real number. `LipschitzWith` takes `K : ℝ≥0`, so a real `c` needs `Real.toNNReal c`.
- Expecting `oscillation f x` to be real. It lies in `ℝ≥0∞` and can be `⊤`.

The reference table at the end of the section lists the declarations of this section.

### Exercises

1. (A) Find the maximum and minimum of $x^3 - 3x$ on $[-2, 3]$. Hint: $x^3 - 3x - 2 = (x + 1)^2(x - 2)$ and $x^3 - 3x + 2 = (x - 1)^2(x + 2)$.
2. (A) Prove that $3x + 7$ is uniformly continuous on $\mathbb{R}$, and give $\delta$ for $\varepsilon = 0.01$.
3. (A) Compute the oscillation of $\lfloor x \rfloor$ at every point.
4. (B) Let $f$ be continuous and positive on $[a, b]$. Prove that $f \ge m$ for some $m > 0$. Give a counterexample on $(0, 1)$.
5. (B) Prove that $\sqrt{x}$ is uniformly continuous on $[0, \infty)$ but not Lipschitz on $[0, 1]$. Hint: $|\sqrt{x} - \sqrt{y}| \le \sqrt{|x - y|}$.
6. (B) Prove the uniform oscillation statement on $[a, b]$: if $\omega_f(x) < \varepsilon$ for all $x \in [a, b]$, then there is $\delta > 0$ with $\omega_f(x, \delta) \le \varepsilon$ for all $x \in [a, b]$. Hint: follow the proof of Heine-Cantor.
7. (C) Prove that $\{x : \omega_f(x) \ge \varepsilon\}$ is closed, and deduce that the set of discontinuities of $f$ is a countable union of closed sets.

### Notes and history

Weierstrass proved the extreme value theorem in his Berlin lectures of the 1860s. Heine introduced uniform continuity in 1872 and proved the theorem on closed intervals. Lipschitz used his condition in 1864. Rudin, *Principles of Mathematical Analysis*, Chapter 4, states both theorems for compact metric spaces, as Mathlib does.

### Reference

<?reference?>
