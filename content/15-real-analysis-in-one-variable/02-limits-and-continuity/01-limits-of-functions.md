---
title: Limits of functions
kind: theory
modules: []
explains:
  E1: [Metric.tendsto_nhdsWithin_nhds, Metric.tendsto_nhds_nhds, nhdsWithin, nhdsLT_sup_nhdsGT, Filter.tendsto_sup, tendsto_nhds_iff_seq_tendsto, tendsto_nhds_unique, Filter.Tendsto.add, Filter.Tendsto.mul, Filter.Tendsto.div, tendsto_of_tendsto_of_tendsto_of_le_of_le', Filter.Tendsto.comp, tendsto_inv_atTop_zero, tendsto_nhdsWithin_congr]
families: []
requires: [V02, V13, V15.C01]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Limits of functions

### Overview

Chapter 1 studied the limit of a sequence. This section studies the limit of a function: the values $f(x)$ come close to $L$ when $x$ is close to a point $a$, or when $x$ is large. The definition uses $\varepsilon$ and $\delta$. The main theorems are the uniqueness of the limit, the sequential characterization, the algebra of limits, the squeeze theorem and the rule for compositions.

Mathlib states each rule once for all kinds, because a limit is the statement `Filter.Tendsto f l₁ l₂`, where the filter `l₁` says where $x$ goes and the filter `l₂` says where $f(x)$ goes.

### Definitions

In this section $D \subseteq \mathbb{R}$ and $f : D \to \mathbb{R}$. A point $a \in \mathbb{R}$ is an *accumulation point* of $D$ if every interval $(a - \delta, a + \delta)$ with $\delta > 0$ contains a point of $D$ other than $a$.

**Definition (Limit of a function at a point).** Let $a$ be an accumulation point of $D$ and $L \in \mathbb{R}$. Then $\lim_{x \to a} f(x) = L$ if for every $\varepsilon > 0$ there is $\delta > 0$ such that $|f(x) - L| < \varepsilon$ for all $x \in D$ with $0 < |x - a| < \delta$.

Remarks. The condition $0 < |x - a|$ removes the point $a$, so the value $f(a)$ plays no role.

**Definition (One-sided limits and limits at infinity).** The *right limit* $\lim_{x \to a^+} f(x) = L$ uses the points $x \in D$ with $a < x < a + \delta$ in place of $0 < |x - a| < \delta$, and the left limit uses $a - \delta < x < a$. For $D$ unbounded above, $\lim_{x \to +\infty} f(x) = L$ if for every $\varepsilon > 0$ there is $M$ with $|f(x) - L| < \varepsilon$ for all $x \in D$ with $x > M$.

A filter is the collection of all sets that contain a source set of one kind: punctured intervals, half intervals or rays.

**Definition (The filters of real analysis).** Let $a \in \mathbb{R}$ and $s \subseteq \mathbb{R}$.

1. The neighbourhood filter $\mathcal{N}(a)$ is the collection of sets that contain an interval $(a - \delta, a + \delta)$ with $\delta > 0$.
2. The filter $\mathcal{N}_s(a)$ is the collection of sets $V$ with $V \supseteq U \cap s$ for some $U \in \mathcal{N}(a)$.
3. The punctured filter is $\mathcal{N}_{\ne}(a) = \mathcal{N}_{\mathbb{R} \setminus \{a\}}(a)$, and the right filter is $\mathcal{N}_{>}(a) = \mathcal{N}_{(a, \infty)}(a)$.
4. The filter $\mathrm{atTop}$ is the collection of sets that contain a ray $(M, \infty)$.

For filters $F$ on the source and $G$ on the target, $f$ *tends to* $G$ along $F$ if $f^{-1}(V) \in F$ for every $V \in G$.

With these filters, $\lim_{x \to a} f(x) = L$ says that $f$ tends to $\mathcal{N}(L)$ along $\mathcal{N}_{\ne}(a)$. The right limit uses $\mathcal{N}_{>}(a)$, and the limit at $+\infty$ uses $\mathrm{atTop}$ on the source.

::: mathlib
`nhdsWithin` · `Mathlib.Topology.Defs.Filter`

The filter $\mathcal{N}_s(a)$ is `nhdsWithin a s`, with the notation `𝓝[s] a`. It is `𝓝 a ⊓ 𝓟 s`. The notations `𝓝[≠] a`, `𝓝[>] a` and `𝓝[<] a` abbreviate `𝓝[{a}ᶜ] a`, `𝓝[Set.Ioi a] a` and `𝓝[Set.Iio a] a`.

<?decl nhdsWithin?>
:::

::: mathlib
`Metric.tendsto_nhdsWithin_nhds` · `Mathlib.Topology.MetricSpace.Pseudo.Defs`

This lemma turns `Tendsto f (𝓝[s] a) (𝓝 b)` into the form: for every `ε > 0` there is `δ > 0` such that `x ∈ s` and `dist x a < δ` give `dist (f x) b < ε`. With `s = {a}ᶜ` this is the textbook definition, and on `ℝ` the distance is `|x - y|`. The unpunctured form `Metric.tendsto_nhds_nhds` allows $x = a$, so it forces $b = f(a)$: it is continuity, the subject of the next section.

<?decl Metric.tendsto_nhdsWithin_nhds?>
:::

### Theorems and proofs

**Theorem (Uniqueness of the limit).** Let $a$ be an accumulation point of $D$. If $\lim_{x \to a} f(x) = L$ and $\lim_{x \to a} f(x) = M$, then $L = M$.

*Proof.* Assume $L \ne M$ and put $\varepsilon = |L - M| / 2$. Take $\delta_1$ for $L$ and $\delta_2$ for $M$, and $\delta = \min(\delta_1, \delta_2)$. Since $a$ is an accumulation point, there is $x \in D$ with $0 < |x - a| < \delta$. Then $|L - M| \le |L - f(x)| + |f(x) - M| < 2\varepsilon = |L - M|$, a contradiction. $\square$

In Mathlib this is `tendsto_nhds_unique`, for a filter `l` with `[l.NeBot]`. Here `NeBot` is the accumulation condition.

**Theorem (Sequential characterization).** Let $a$ be an accumulation point of $D$. Then $\lim_{x \to a} f(x) = L$ if and only if $f(x_n) \to L$ for every sequence $(x_n)$ in $D \setminus \{a\}$ with $x_n \to a$.

*Proof.* Assume $\lim_{x \to a} f(x) = L$. Let $x_n \to a$ in $D \setminus \{a\}$, and let $\varepsilon > 0$. Choose $\delta$ for $\varepsilon$. There is $N$ with $|x_n - a| < \delta$ for $n \ge N$. Also $x_n \ne a$, so $0 < |x_n - a| < \delta$ and $|f(x_n) - L| < \varepsilon$ for $n \ge N$.

Conversely, assume that the limit is not $L$. Then there is $\varepsilon > 0$ such that for every $\delta > 0$ there is $x \in D$ with $0 < |x - a| < \delta$ and $|f(x) - L| \ge \varepsilon$. For each $n$ choose such a point $x_n$ for $\delta = 1/(n+1)$. Then $x_n \in D \setminus \{a\}$ and $x_n \to a$, but $|f(x_n) - L| \ge \varepsilon$ for all $n$, so $f(x_n) \not\to L$. $\square$

::: mathlib
`tendsto_nhds_iff_seq_tendsto` · `Mathlib.Topology.Sequences`

The sequential characterization for the filter `𝓝 a`, in any Fréchet-Urysohn space, for example any metric space: `Tendsto f (𝓝 a) (𝓝 b) ↔ ∀ u, Tendsto u atTop (𝓝 a) → Tendsto (f ∘ u) atTop (𝓝 b)`.

<?decl tendsto_nhds_iff_seq_tendsto?>
:::

**Theorem (Algebra of limits).** Let $\lim_{x \to a} f(x) = L$ and $\lim_{x \to a} g(x) = M$. Then $\lim (f + g) = L + M$ and $\lim f g = L M$. If $M \ne 0$, then $g(x) \ne 0$ for $x \ne a$ near $a$, and $\lim f/g = L/M$.

*Proof.* Let $\varepsilon > 0$. Each statement below is for $x \in D$ with $0 < |x - a| < \delta$, where $\delta$ is the minimum of the finitely many values that the proof takes.

Sum: take $|f(x) - L| < \varepsilon/2$ and $|g(x) - M| < \varepsilon/2$. The triangle inequality gives $|f(x) + g(x) - L - M| < \varepsilon$.

Product: $f(x) g(x) - L M = f(x)(g(x) - M) + M (f(x) - L)$. Take $|f(x) - L| < 1$, so $|f(x)| < |L| + 1$. Take also $|g(x) - M| < \varepsilon / (2(|L| + 1))$ and $|f(x) - L| < \varepsilon / (2(|M| + 1))$. Then $|f(x) g(x) - L M| < \varepsilon/2 + \varepsilon/2 = \varepsilon$.

Quotient: by the product rule it suffices to treat $1/g$. Take $|g(x) - M| < |M|/2$. Then $|g(x)| > |M|/2 > 0$. Take also $|g(x) - M| < \varepsilon M^2/2$. Then
$$\left| \frac{1}{g(x)} - \frac{1}{M} \right| = \frac{|M - g(x)|}{|g(x)|\,|M|} < \frac{\varepsilon M^2/2}{|M|^2/2} = \varepsilon. \qquad \square$$

::: mathlib
`Filter.Tendsto.add` · `Mathlib.Topology.Algebra.Monoid.Defs`

From `Tendsto f l (𝓝 a)` and `Tendsto g l (𝓝 b)` it gives `Tendsto (fun x ↦ f x + g x) l (𝓝 (a + b))`. The filter `l` is arbitrary, so one lemma covers $x \to a$, $x \to a^+$, $x \to +\infty$ and sequences. `Filter.Tendsto.mul` has the same form, and `Filter.Tendsto.div` needs `b ≠ 0`. Since `x / 0 = 0` in Mathlib, `f x / g x` is defined everywhere, and the quotient rule needs no statement about the zeros of `g`.

<?decl Filter.Tendsto.add?>
:::

**Theorem (Squeeze).** Let $g(x) \le f(x) \le h(x)$ for $x \in D \setminus \{a\}$ near $a$, and $\lim g = L = \lim h$ at $a$. Then $\lim_{x \to a} f(x) = L$.

*Proof.* For $\varepsilon > 0$ choose $\delta$ such that, for $0 < |x - a| < \delta$, the two inequalities hold, $g(x) > L - \varepsilon$ and $h(x) < L + \varepsilon$. Then $L - \varepsilon < f(x) < L + \varepsilon$. $\square$

In Mathlib this is `tendsto_of_tendsto_of_tendsto_of_le_of_le'`, with the hypotheses `∀ᶠ x in l, g x ≤ f x` and `∀ᶠ x in l, f x ≤ h x`.

**Theorem (Composition).** Let $\lim_{x \to a} f(x) = b$ and $\lim_{y \to b} g(y) = c$, and assume $f(x) \ne b$ for $x \ne a$ near $a$. Then $\lim_{x \to a} g(f(x)) = c$.

*Proof.* For $\varepsilon > 0$ choose $\eta$ with $|g(y) - c| < \varepsilon$ for $0 < |y - b| < \eta$. Choose $\delta$ such that $0 < |x - a| < \delta$ gives $|f(x) - b| < \eta$ and $f(x) \ne b$. For such $x$, $y = f(x)$ satisfies $0 < |y - b| < \eta$, so $|g(f(x)) - c| < \varepsilon$. $\square$

::: mathlib
`Filter.Tendsto.comp` · `Mathlib.Order.Filter.Tendsto`

The rule `Tendsto g y z → Tendsto f x y → Tendsto (g ∘ f) x z` has no extra hypothesis, because the hypothesis is in the filters. To use the punctured limit of `g` at `b`, the middle filter is `𝓝[≠] b`, and then `Tendsto f (𝓝[≠] a) (𝓝[≠] b)` says that `f` tends to `b` and that `f x ≠ b` eventually.

<?decl Filter.Tendsto.comp?>
:::

**Theorem (Two one-sided limits).** Let $f$ be defined on $(a - r, a + r) \setminus \{a\}$. Then $\lim_{x \to a} f(x) = L$ if and only if both one-sided limits are $L$.

*Proof.* A $\delta$ for the two-sided limit works for both sides. Conversely, if $\delta_1$ works on the left and $\delta_2$ on the right, then $\delta = \min(\delta_1, \delta_2)$ works for $0 < |x - a| < \delta$. $\square$

In Mathlib the theorem is the identity `nhdsLT_sup_nhdsGT : 𝓝[<] a ⊔ 𝓝[>] a = 𝓝[≠] a` together with `Filter.tendsto_sup`.

### Examples

**Example (A removable hole).** Let $f(x) = (x^3 - 1)/(x - 1)$ for $x \ne 1$. Then $f(x) = x^2 + x + 1$ and $|f(x) - 3| = |x - 1|\,|x + 2|$. If $|x - 1| < 1$ then $|x + 2| < 4$. So $\delta = \min(1, \varepsilon/4)$ works, and $\lim_{x \to 1} f(x) = 3$. In Mathlib the statement is `Tendsto (fun x ↦ (x^3 - 1)/(x - 1)) (𝓝[≠] 1) (𝓝 3)`. A proof replaces the function by `x^2 + x + 1` on `{1}ᶜ` with `tendsto_nhdsWithin_congr` and uses the continuity of a polynomial.

**Example (A limit at infinity).** Let $f(x) = (3x^2 + 1)/(x^2 + 5)$. Then $f(x) - 3 = -14/(x^2 + 5)$, so $|f(x) - 3| < 14/x^2$, and $M = \sqrt{14/\varepsilon}$ works. The filter proof writes $f(x) = (3 + x^{-2})/(1 + 5x^{-2})$ and uses `tendsto_inv_atTop_zero` with the algebra of limits.

**Counterexample (The composition rule needs $f(x) \ne b$).** Let $f(x) = 0$ for all $x$, and $g(y) = 1$ for $y \ne 0$, $g(0) = 0$. Then $f \to 0$ and $g \to 1$ at $0$, but $g(f(x)) = 0$ for all $x$. In Mathlib, `f` tends to `𝓝 0` but not to `𝓝[≠] 0`.

**Counterexample (No limit anywhere).** Let $\chi = \mathbf{1}_{\mathbb{Q}}$. Fix $a$. There are rationals $q_n \to a$ and irrationals $r_n \to a$ with $q_n, r_n \ne a$. Then $\chi(q_n) \to 1$ and $\chi(r_n) \to 0$, so by the sequential characterization $\chi$ has no limit at $a$.

The limit $\lim_{x \to 0} \sin(x)/x = 1$ needs the definition of the sine. Chapter 6 deduces it from the squeeze theorem and the bounds $\cos x \le \sin(x)/x \le 1$ for $0 < |x| < \pi/2$.

### The library around it

The algebra of limits is the family `Filter.Tendsto.add`, `.sub`, `.mul`, `.const_mul`, `.inv₀`, `.div`, `.pow`. The change of the function on a set of the filter is `tendsto_nhdsWithin_congr`.

Common errors of a learner:

- Writing `Tendsto f (𝓝 a) (𝓝 L)` for the limit at `a`. This filter contains `a`, so the statement forces `L = f a`. The textbook limit is `Tendsto f (𝓝[≠] a) (𝓝 L)`.
- Using `Filter.Tendsto.div` when the limit of the denominator is `0`. The limit of `x / x` at `0` needs `tendsto_nhdsWithin_congr`.
- Applying `tendsto_nhds_unique` along `𝓝[s] a` without the fact `(𝓝[s] a).NeBot`.

The reference table at the end of the section lists the declarations of this section.

### Exercises

1. (A) Prove from the definition that $\lim_{x \to 2} (x^2 + x) = 6$, and give $\delta$ for $\varepsilon = 0.1$. Hint: $x^2 + x - 6 = (x - 2)(x + 3)$.
2. (A) Show that $\lim_{x \to 0} x/|x|$ does not exist. Hint: compute the one-sided limits.
3. (A) Show that $\lim_{x \to 0} x \chi(x) = 0$, with $\chi = \mathbf{1}_{\mathbb{Q}}$. Hint: squeeze between $-|x|$ and $|x|$.
4. (B) Prove that if $\lim_{x \to a} f(x) = L > 0$, then $f(x) > L/2$ for $x \ne a$ near $a$. Hint: take $\varepsilon = L/2$; in Mathlib see `Filter.Tendsto.eventually_const_lt`.
5. (C) Let $f$ be increasing on $\mathbb{R}$. Prove that $\lim_{x \to a^-} f(x) = \sup \{ f(x) : x < a \}$. Hint: follow the monotone convergence theorem of Chapter 1.

### Notes and history

Cauchy defined the limit in words in the *Cours d'analyse* (1821). The form with $\varepsilon$ and $\delta$ is due to Weierstrass in his Berlin lectures, and Heine published it in 1872. Henri Cartan introduced filters in 1937. The standard textbook treatment is Rudin, *Principles of Mathematical Analysis*, Chapter 4.

### Reference

<?reference?>
