---
title: Limits of sequences
kind: theory
modules:
  - Mathlib.Analysis.SpecificLimits.Basic
explains:
  E3: [tendsto_pow_atTop_nhds_zero_of_lt_one, tendsto_one_div_atTop_nhds_zero_nat]
  E2: [tendsto_inv_atTop_nhds_zero_nat, tendsto_const_div_atTop_nhds_zero_nat, tendsto_pow_atTop_atTop_of_one_lt, tendsto_pow_atTop_nhds_zero_iff, tendsto_pow_atTop_nhds_zero_of_abs_lt_one, factorial_tendsto_atTop, tendsto_factorial_div_pow_self_atTop, tendsto_pow_const_div_const_pow_of_one_lt]
  E1: auto
families: []
requires: [V02, V13]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Limits of sequences

### Overview

A sequence $(a_n)$ of real numbers converges to $L$ when its terms come and stay as close to $L$ as one wants. This section makes the sentence precise with $\varepsilon$ and $N$ and proves the rules of each computation: a limit is unique, limits respect sums, products and quotients, limits respect inequalities, and a sequence squeezed between two sequences with the same limit has that limit too. Then it computes the four standard limits $1/n \to 0$, $q^n \to 0$ for $|q| < 1$, $n^{1/n} \to 1$ and $a^n/n! \to 0$.

Mathlib states the definition with filters: `Filter.Tendsto a Filter.atTop (nhds L)`.

### Definitions

**Definition (Convergent sequence).** A sequence of real numbers is a function $a : \mathbb{N} \to \mathbb{R}$, written $(a_n)$. The sequence *converges to* $L \in \mathbb{R}$ if for each $\varepsilon > 0$ there is $N \in \mathbb{N}$ such that $|a_n - L| < \varepsilon$ for all $n \ge N$. Then $L$ is a *limit*, written $a_n \to L$ or $\lim_{n \to \infty} a_n = L$. A sequence with no limit is *divergent*. The sequence *tends to $+\infty$* if for each $M$ there is $N$ with $a_n > M$ for all $n \ge N$.

A property $P(n)$ holds *eventually* if there is $N$ such that $P(n)$ holds for all $n \ge N$. So $a_n \to L$ means: for each $\varepsilon > 0$, eventually $|a_n - L| < \varepsilon$. If $P$ and $Q$ hold eventually, then $P \wedge Q$ holds eventually: take the larger of the two values of $N$. Each proof below uses this fact.

**Definition (Filter form of the limit).** The *neighbourhoods* of $L$ are the sets that contain an interval $(L - \varepsilon, L + \varepsilon)$ with $\varepsilon > 0$. The filter $\mathrm{atTop}$ on $\mathbb{N}$ is the family of the sets that contain a tail $\{n : n \ge N\}$. The sequence $a$ *tends to $L$ along $\mathrm{atTop}$* if for each neighbourhood $V$ of $L$ the preimage $a^{-1}(V)$ belongs to $\mathrm{atTop}$.

The two definitions agree. Assume the $\varepsilon$ form, and let $V \supseteq (L - \varepsilon, L + \varepsilon)$. There is $N$ with $|a_n - L| < \varepsilon$ for $n \ge N$, so $a^{-1}(V)$ contains the tail $\{n \ge N\}$. Conversely, assume the filter form and let $\varepsilon > 0$. The preimage of $V = (L - \varepsilon, L + \varepsilon)$ contains a tail $\{n \ge N\}$, and this is the $\varepsilon$ form.

::: mathlib
`Filter.Tendsto` · `Mathlib.Order.Filter.Defs`

`Filter.Tendsto f l₁ l₂` says that the preimage under `f` of each set of the filter `l₂` is a set of the filter `l₁`. The limit of a sequence is `Filter.Tendsto a Filter.atTop (nhds L)`. The same predicate expresses $a_n \to +\infty$ as `Tendsto a atTop atTop`, the limit of a function at a point as `Tendsto f (nhds x) (nhds L)`, and a one-sided limit with `nhdsWithin`. So one definition and one library of lemmas cover all the limits of the volume. The translation to the $\varepsilon$ form is `Metric.tendsto_atTop`, with `dist x y = |x - y|` on `ℝ`. Volume 13 develops filters.

<?decl Filter.Tendsto?>
:::

### Theorems and proofs

**Theorem (Uniqueness of the limit).** If $a_n \to L$ and $a_n \to M$, then $L = M$.

*Proof.* Assume $L \ne M$, and let $\varepsilon = |L - M|/2 > 0$. Eventually $|a_n - L| < \varepsilon$ and $|a_n - M| < \varepsilon$. For such an $n$,
$$|L - M| \le |L - a_n| + |a_n - M| < 2\varepsilon = |L - M|,$$
which is false. So $L = M$. $\square$

::: mathlib
`tendsto_nhds_unique` · `Mathlib.Topology.Separation.Hausdorff`

Uniqueness for any filter that is not empty (the class `l.NeBot`) and any Hausdorff space. The proof above is the Hausdorff argument: the two intervals of radius $\varepsilon$ are disjoint. Because the limit is unique, Mathlib can define `Filter.limUnder atTop a` as a chosen limit, but the library states theorems with `Tendsto`.

<?decl tendsto_nhds_unique?>
:::

**Lemma (Convergent sequences are bounded).** If $a_n \to L$, there is $C$ with $|a_n| \le C$ for all $n$.

*Proof.* With $\varepsilon = 1$ there is $N$ such that $|a_n| < |L| + 1$ for $n \ge N$. Let $C = \max(|a_0|, \ldots, |a_{N-1}|, |L| + 1)$. $\square$

**Theorem (Algebra of limits).** Assume $a_n \to A$ and $b_n \to B$. Then:

1. $a_n + b_n \to A + B$, and $c\, a_n \to c A$ for each $c \in \mathbb{R}$;
2. $a_n b_n \to A B$;
3. if $B \ne 0$, then $b_n \ne 0$ eventually, and $a_n / b_n \to A / B$.

*Proof.* 1. Let $\varepsilon > 0$. Eventually $|a_n - A| < \varepsilon/2$ and $|b_n - B| < \varepsilon/2$, and then $|(a_n + b_n) - (A + B)| < \varepsilon$. For $c \ne 0$, eventually $|a_n - A| < \varepsilon/|c|$, and then $|c a_n - c A| < \varepsilon$.

2. Write $a_n b_n - A B = a_n (b_n - B) + B (a_n - A)$. By the lemma there is $C > 0$ with $|a_n| \le C$ for all $n$. Let $\varepsilon > 0$. Eventually $|b_n - B| < \varepsilon / (2C)$ and $|a_n - A| < \varepsilon / (2|B| + 1)$. Then
$$|a_n b_n - AB| \le C \cdot \frac{\varepsilon}{2C} + |B| \cdot \frac{\varepsilon}{2|B| + 1} < \varepsilon.$$

3. Eventually $|b_n - B| < |B|/2$, and then $|b_n| > |B|/2 > 0$. By part 2 it is enough to prove $1/b_n \to 1/B$. For these $n$,
$$\left| \frac{1}{b_n} - \frac{1}{B} \right| = \frac{|B - b_n|}{|b_n|\,|B|} \le \frac{2}{|B|^2} |b_n - B|,$$
and eventually $|b_n - B| < \varepsilon |B|^2 / 2$, so the left side is less than $\varepsilon$. $\square$

::: mathlib
`Filter.Tendsto.mul` · `Mathlib.Topology.Algebra.Monoid.Defs`

The algebra of limits is the family `Filter.Tendsto.add`, `.sub`, `.mul`, `.const_mul`, `.div` and `.inv₀`, for any filter on the source. From `h : Tendsto a atTop (𝓝 A)` and `h'` the term `h.mul h'` is the product. The proof in Mathlib is the continuity of $(x, y) \mapsto xy$, composed with the pair $(a_n, b_n)$; the computation above is the proof of that continuity. `Filter.Tendsto.div` asks for `B ≠ 0`, as part 3 does.

<?decl Filter.Tendsto.mul?>
:::

**Theorem (Limits and inequalities).** Assume $a_n \to A$, $b_n \to B$, and $a_n \le b_n$ eventually. Then $A \le B$.

*Proof.* Assume $A > B$, and let $\varepsilon = (A - B)/2$. Eventually $a_n > A - \varepsilon$, $b_n < B + \varepsilon$ and $a_n \le b_n$. For such an $n$, $A - \varepsilon < B + \varepsilon$, so $A - B < 2\varepsilon = A - B$, which is false. $\square$

The strict form fails: $0 < 1/n$ for all $n \ge 1$, and both limits are $0$. In Mathlib the theorem is `le_of_tendsto_of_tendsto`.

**Theorem (Squeeze).** Assume $a_n \le b_n \le c_n$ eventually, $a_n \to L$ and $c_n \to L$. Then $b_n \to L$.

*Proof.* Let $\varepsilon > 0$. Eventually $L - \varepsilon < a_n$, $c_n < L + \varepsilon$ and $a_n \le b_n \le c_n$. For such $n$, $L - \varepsilon < b_n < L + \varepsilon$. $\square$

::: mathlib
`tendsto_of_tendsto_of_tendsto_of_le_of_le` · `Mathlib.Topology.Order.Basic`

The squeeze theorem, with the inequalities for all `n`. The primed form asks for them only eventually. The arguments are, in order: the lower limit, the upper limit, the lower inequality, the upper inequality.

<?decl tendsto_of_tendsto_of_tendsto_of_le_of_le?>
:::

**Theorem (Four standard limits).**

1. $1/n \to 0$.
2. If $|q| < 1$, then $q^n \to 0$. If $q > 1$, then $q^n \to +\infty$.
3. $n^{1/n} \to 1$.
4. For each $a \in \mathbb{R}$, $a^n / n! \to 0$.

*Proof.* 1. Let $\varepsilon > 0$. By the Archimedean property there is $N > 1/\varepsilon$. For $n \ge N$, $0 < 1/n \le 1/N < \varepsilon$.

2. Let $0 < |q| < 1$ (the case $q = 0$ is trivial) and write $1/|q| = 1 + h$ with $h > 0$. Bernoulli's inequality $(1 + h)^n \ge 1 + n h$ follows by induction:
$$(1 + h)^{n+1} \ge (1 + nh)(1 + h) = 1 + (n+1)h + n h^2 \ge 1 + (n+1) h.$$
So $|q^n| \le 1/(1 + nh) < 1/(nh)$ for $n \ge 1$. Since $1/(nh) \to 0$, the squeeze theorem gives $q^n \to 0$. If $q = 1 + h > 1$, then $q^n \ge 1 + nh$, which exceeds each $M$ for large $n$.

3. Let $h_n = n^{1/n} - 1 \ge 0$ for $n \ge 1$. By the binomial theorem, for $n \ge 2$,
$$n = (1 + h_n)^n \ge \binom{n}{2} h_n^2 = \frac{n(n-1)}{2} h_n^2,$$
since all the terms are nonnegative. So $0 \le h_n \le \sqrt{2/(n-1)}$, which is less than $\varepsilon$ for $n > 1 + 2/\varepsilon^2$.

4. Choose a natural number $K \ge 2|a|$. For $n \ge K$,
$$\frac{|a|^{n+1}}{(n+1)!} = \frac{|a|}{n+1} \cdot \frac{|a|^n}{n!} \le \frac{1}{2} \cdot \frac{|a|^n}{n!}.$$
By induction, $|a|^n/n! \le C\, (1/2)^{n-K}$ for $n \ge K$, with $C = |a|^K / K!$. The right side tends to $0$ by part 2, and the squeeze theorem gives the claim. $\square$

::: mathlib
`tendsto_one_div_atTop_nhds_zero_nat` · `Mathlib.Analysis.SpecificLimits.Basic`

The limit $1/n \to 0$ for `fun n : ℕ ↦ 1 / (n : 𝕜)`, with a cast of `n` to the field. The term at `n = 0` is the junk value `1 / 0 = 0`, and a limit does not see one term. The forms `tendsto_inv_atTop_nhds_zero_nat` and `tendsto_const_div_atTop_nhds_zero_nat` are next to it.

<?decl tendsto_one_div_atTop_nhds_zero_nat?>
:::

::: mathlib
`tendsto_pow_atTop_nhds_zero_of_lt_one` · `Mathlib.Analysis.SpecificLimits.Basic`

The limit $r^n \to 0$ for $0 \le r < 1$. For a negative ratio use `tendsto_pow_atTop_nhds_zero_of_abs_lt_one`, and `tendsto_pow_atTop_nhds_zero_iff` gives the exact criterion `|r| < 1`. The case $r > 1$ is `tendsto_pow_atTop_atTop_of_one_lt`. The limit $n^k / r^n \to 0$ is `tendsto_pow_const_div_const_pow_of_one_lt`. Part 4 is `FloorSemiring.tendsto_pow_div_factorial_atTop`, and the file also gives `factorial_tendsto_atTop` and `tendsto_factorial_div_pow_self_atTop` for $n!/n^n \to 0$. Part 3 needs the real power of Chapter 5; Mathlib states it as `tendsto_rpow_div`.

<?decl tendsto_pow_atTop_nhds_zero_of_lt_one?>
:::

### Examples

**Example (A rational sequence).** Let $a_n = \dfrac{3n^2 + 5n}{2n^2 + 1}$. Divide by $n^2$: $a_n = \dfrac{3 + 5 (1/n)}{2 + (1/n)^2}$. By the algebra of limits, $a_n \to 3/2$. For the $\varepsilon$ form, compute
$$a_n - \frac{3}{2} = \frac{10n - 3}{2(2n^2+1)},$$
which for $n \ge 1$ is between $0$ and $10n / (4n^2) = 5/(2n)$. So $|a_n - 3/2| < \varepsilon$ for $n > 5/(2\varepsilon)$. For $\varepsilon = 10^{-3}$ the value $N = 2501$ works.

**Example (A squeeze).** Let $b_n = \dfrac{(-1)^n n}{n^2 + 1}$. The sign oscillates, but $|b_n| \le 1/n$ for $n \ge 1$, so $-1/n \le b_n \le 1/n$, and the squeeze theorem gives $b_n \to 0$.

**Counterexample (A bounded divergent sequence).** The sequence $a_n = (-1)^n$ is bounded and has no limit. Assume $a_n \to L$. With $\varepsilon = 1$ there is $N$ with $|a_n - L| < 1$ for $n \ge N$. With $n = 2N$ and $n = 2N + 1$, $|1 - L| < 1$ and $|-1 - L| < 1$, so $2 < 2$, which is false. Section 2 shows what remains true: a bounded sequence has a convergent subsequence.

### The library around it

The lemmas about limits are organised by the filters on the two sides of `Tendsto`. A lemma for `Tendsto f l (nhds a)` with an arbitrary filter `l` applies to sequences, to limits at a point and to one-sided limits. The tactic `filter_upwards` combines several eventual facts, as the proofs above combine the values of $N$. The file `Mathlib.Analysis.SpecificLimits.Basic` lists the standard limits in ordered fields, and `Mathlib.Analysis.SpecificLimits.Normed` gives the forms with a norm.

Common errors of a learner:

- The limit of $1/n$ is about `fun n : ℕ ↦ 1 / (n : ℝ)`. Without the cast, `1 / n` is a division of natural numbers, which is `0` for `n ≥ 2`.
- `Tendsto a atTop (nhds L)` puts the filter of the source first. `Tendsto a (nhds L) atTop` is a different statement.
- Mathlib defines $x / 0 = 0$, but this junk value does not make $a_n / b_n \to A / 0$ true. `Filter.Tendsto.div` needs `B ≠ 0`.
- A hypothesis that holds only for $n \ge 1$ is enough when it is stated with `∀ᶠ n in atTop`.

### Exercises

1. (A) Prove from the definition that $\dfrac{2n + 1}{n + 3} \to 2$. For $\varepsilon = 10^{-2}$, give an explicit $N$.
2. (A) Show that $a_n \to L$ implies $|a_n| \to |L|$, and that the converse fails. Hint: $\big||x| - |y|\big| \le |x - y|$.
3. (B) Show that $\sqrt{n + 1} - \sqrt{n} \to 0$. Hint: multiply by $\sqrt{n+1} + \sqrt{n}$.
4. (B) Let $a > 0$. Show that $a^{1/n} \to 1$. Hint: for $a \ge 1$, compare $a^{1/n}$ with $n^{1/n}$ for $n \ge a$.
5. (B) Show that if $a_n \to L$, then $(a_1 + \cdots + a_n)/n \to L$, and that the converse fails. Hint: split the sum at an index $N$.
6. (C) Let $a_{m+n} \le a_m + a_n$ for all $m, n \ge 1$. Show that $a_n / n$ converges to $\inf_n a_n / n$ or tends to $-\infty$. Hint: write $n = q m + r$ with $1 \le r \le m$. This is the lemma of Fekete, in `Mathlib.Analysis.Subadditive`.

### Notes and history

Cauchy, in the *Cours d'analyse* of 1821, defined a limit in words. The form with $\varepsilon$ and $N$ is due to Weierstrass and his students in Berlin, from the 1860s. Filters are due to Henri Cartan (1937). Mathlib took them from the start, following the Isabelle library, because one predicate `Tendsto` replaces the many kinds of limits of the textbooks.

### Reference

<?reference?>
