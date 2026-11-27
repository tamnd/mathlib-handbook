---
title: Monotone sequences, Bolzano-Weierstrass and Cauchy sequences
kind: theory
modules:
  - Mathlib.Topology.Instances.Real.Lemmas
explains:
  E3: [Real.tendsto_atTop_csSup_of_monotoneOn_bddAbove_nat_Ici, cauchySeq_of_le_geometric]
  E2: [Real.isLUB_of_tendsto_monotone_bddAbove, Real.isGLB_of_tendsto_antitone_bddBelow, Real.tendsto_atTop_csInf_of_antitoneOn_bddBelow_nat_Ici, Real.exists_seq_rat_strictMono_tendsto, Real.mem_closure_iff, dist_le_of_le_geometric_of_tendsto]
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

## Monotone sequences, Bolzano-Weierstrass and Cauchy sequences

### Overview

Often the limit of a sequence is not known in advance: the sequence is defined by a recursion, and the question is whether it converges at all. This section gives three criteria of convergence that do not name the limit. A monotone bounded sequence converges, to its supremum. Each bounded sequence has a convergent subsequence (Bolzano-Weierstrass). A sequence converges if and only if it is a Cauchy sequence. All three rest on the least upper bound property of $\mathbb{R}$ from Volume 2, and all three fail in $\mathbb{Q}$. The section ends with the upper and lower limits of a bounded sequence.

### Definitions

**Definition (Monotone sequence).** A sequence $(a_n)$ is *increasing* (monotone) if $a_n \le a_{n+1}$ for all $n$, and *decreasing* (antitone) if $a_n \ge a_{n+1}$ for all $n$. It is *bounded* if there is $M$ with $|a_n| \le M$ for all $n$.

Mathlib defines `Monotone a` as `∀ m n, m ≤ n → a m ≤ a n`. The lemma `monotone_nat_of_le_succ` gives it from the step form.

**Definition (Subsequence).** A *subsequence* of $(a_n)$ is a sequence $(a_{\varphi(k)})_k$ with $\varphi : \mathbb{N} \to \mathbb{N}$ strictly increasing.

By induction $\varphi(k) \ge k$. So if $a_n \to L$, each subsequence tends to $L$.

**Definition (Cauchy sequence).** A sequence $(a_n)$ is a *Cauchy sequence* if for each $\varepsilon > 0$ there is $N$ such that $|a_m - a_n| < \varepsilon$ for all $m, n \ge N$.

**Definition (Upper and lower limits).** Let $(a_n)$ be bounded. Put $s_n = \sup_{k \ge n} a_k$ and $i_n = \inf_{k \ge n} a_k$. Then $(s_n)$ is decreasing and $(i_n)$ is increasing, and both are bounded. The *upper limit* is $\limsup a_n = \lim s_n = \inf_n s_n$, and the *lower limit* is $\liminf a_n = \lim i_n = \sup_n i_n$. These limits exist by the monotone convergence theorem below. Since $i_n \le s_n$, $\liminf a_n \le \limsup a_n$.

::: mathlib
`Filter.limsup` · `Mathlib.Order.LiminfLimsup`

`Filter.limsup u f` is `sInf {a | ∀ᶠ n in f, u n ≤ a}`, the infimum of the eventual upper bounds (`Filter.limsup_eq`). For a bounded sequence and `f = atTop` this is $\inf_n \sup_{k \ge n} a_k$. For an unbounded sequence the set can be empty, and `sInf ∅ = 0` in `ℝ` (`Real.sInf_empty`). So the lemmas about `limsup` in `ℝ` carry hypotheses `IsBoundedUnder` and `IsCoboundedUnder`, often filled by an `autoParam`.

<?decl Filter.limsup?>
:::

### Theorems and proofs

**Theorem (Monotone convergence).** An increasing sequence that is bounded above converges to $\sup_n a_n$. A decreasing sequence that is bounded below converges to $\inf_n a_n$.

*Proof.* Let $(a_n)$ be increasing and bounded above. The set $\{a_n\}$ is nonempty and bounded above, so it has a least upper bound $S$. Let $\varepsilon > 0$. The number $S - \varepsilon$ is not an upper bound, so there is $N$ with $a_N > S - \varepsilon$. For $n \ge N$, $S - \varepsilon < a_N \le a_n \le S$, so $|a_n - S| < \varepsilon$. For a decreasing sequence, apply this to $(-a_n)$. $\square$

::: mathlib
`tendsto_atTop_ciSup` · `Mathlib.Topology.Order.MonotoneConvergence`

The theorem in the form that most proofs use: from `Monotone f` and `BddAbove (Set.range f)` it gives `Tendsto f atTop (𝓝 (⨆ i, f i))`. It holds in each order with the class `SupConvergenceClass`. In a complete lattice such as `ENNReal`, `tendsto_atTop_iSup` needs no bound. The file of this section gives the form for a sequence monotone from an index `k` on, `Real.tendsto_atTop_csSup_of_monotoneOn_bddAbove_nat_Ici`, and the converse `Real.isLUB_of_tendsto_monotone_bddAbove`: the limit of a monotone sequence is the least upper bound of its range. The decreasing forms are `Real.tendsto_atTop_csInf_of_antitoneOn_bddBelow_nat_Ici` and `Real.isGLB_of_tendsto_antitone_bddBelow`.

<?decl tendsto_atTop_ciSup?>
:::

**Lemma (Monotone subsequence).** Each real sequence has a monotone subsequence.

*Proof.* Call an index $m$ a *peak* if $a_m \ge a_n$ for all $n > m$. If there are infinitely many peaks $m_0 < m_1 < \cdots$, then $a_{m_k} \ge a_{m_{k+1}}$, and $(a_{m_k})$ is decreasing. If there are finitely many peaks, choose $n_0$ larger than all of them. Then $n_0$ is not a peak, so there is $n_1 > n_0$ with $a_{n_1} > a_{n_0}$. The index $n_1$ is not a peak either, and by induction there are $n_0 < n_1 < n_2 < \cdots$ with $(a_{n_k})$ strictly increasing. $\square$

**Theorem (Bolzano-Weierstrass).** Each bounded real sequence has a convergent subsequence.

*Proof.* By the lemma it has a monotone subsequence, which is bounded. By the monotone convergence theorem this subsequence converges. $\square$

::: mathlib
`tendsto_subseq_of_bounded` · `Mathlib.Topology.MetricSpace.Sequences`

The theorem in a proper metric space, a space in which closed balls are compact. From a sequence in a bounded set `s` it gives `a ∈ closure s` and a strictly increasing `φ` with `Tendsto (x ∘ φ) atTop (𝓝 a)`. The proof uses compactness, not peaks; `ℝ` is proper by the theorem of Heine-Borel (Volume 13).

<?decl tendsto_subseq_of_bounded?>
:::

**Theorem (Cauchy criterion).** A real sequence converges if and only if it is a Cauchy sequence.

*Proof.* Let $a_n \to L$ and $\varepsilon > 0$. There is $N$ with $|a_n - L| < \varepsilon/2$ for $n \ge N$, so $|a_m - a_n| \le |a_m - L| + |L - a_n| < \varepsilon$ for $m, n \ge N$.

Conversely, let $(a_n)$ be Cauchy. Step 1: the sequence is bounded. With $\varepsilon = 1$ there is $N$ with $|a_n - a_N| < 1$ for $n \ge N$, so $|a_n| \le \max(|a_0|, \ldots, |a_{N-1}|, |a_N| + 1)$. Step 2: by Bolzano-Weierstrass there are $\varphi$ and $L$ with $a_{\varphi(k)} \to L$. Step 3: let $\varepsilon > 0$. There is $N$ with $|a_m - a_n| < \varepsilon/2$ for $m, n \ge N$, and $K$ with $|a_{\varphi(k)} - L| < \varepsilon/2$ for $k \ge K$. For $n \ge N$ choose $k \ge \max(K, N)$. Then $\varphi(k) \ge N$, so
$$|a_n - L| \le |a_n - a_{\varphi(k)}| + |a_{\varphi(k)} - L| < \varepsilon. \qquad \square$$

The criterion says that $\mathbb{R}$ is *complete*. Volume 2 builds $\mathbb{R}$ from Cauchy sequences of rationals, so there completeness holds by design. The proof above gives it from the least upper bound property instead.

::: mathlib
`cauchySeq_tendsto_of_complete` · `Mathlib.Topology.UniformSpace.Cauchy`

In each complete uniform space, `CauchySeq u` gives `∃ x, Tendsto u atTop (𝓝 x)`. The instance `Real.instCompleteSpace` makes it apply to `ℝ`. `CauchySeq u` is defined with uniform spaces; `Metric.cauchySeq_iff` gives the form with `dist (u m) (u n) < ε`. The converse direction is `Filter.Tendsto.cauchySeq`, with no completeness.

<?decl cauchySeq_tendsto_of_complete?>
:::

**Theorem (Geometric Cauchy bound).** Let $0 \le r < 1$, $C \ge 0$, and $|a_{n+1} - a_n| \le C r^n$ for all $n$. Then $(a_n)$ is Cauchy, and its limit $L$ satisfies $|a_n - L| \le C r^n / (1 - r)$.

*Proof.* For $m > n$, by the triangle inequality,
$$|a_m - a_n| \le \sum_{k=n}^{m-1} C r^k = C r^n \frac{1 - r^{m-n}}{1 - r} \le \frac{C r^n}{1 - r}.$$
Since $r^n \to 0$, the right side is less than $\varepsilon$ for large $n$, so the sequence is Cauchy and has a limit $L$. Fix $n$ and let $m \to \infty$: limits keep $\le$, so $|L - a_n| \le C r^n / (1 - r)$. $\square$

::: mathlib
`cauchySeq_of_le_geometric` · `Mathlib.Analysis.SpecificLimits.Basic`

The first part, in each pseudometric space, with the bound `dist (f n) (f (n + 1)) ≤ C * r ^ n`. The estimate of the distance to the limit is `dist_le_of_le_geometric_of_tendsto`. These two lemmas are the core of the Banach fixed point theorem in Mathlib.

<?decl cauchySeq_of_le_geometric?>
:::

**Theorem (Limits and the upper and lower limits).** A bounded sequence converges if and only if $\liminf a_n = \limsup a_n$, and then the common value is the limit.

*Proof.* If $\liminf a_n = \limsup a_n = L$, the squeeze theorem with $i_n \le a_n \le s_n$ gives $a_n \to L$. Conversely, let $a_n \to L$ and $\varepsilon > 0$. There is $N$ with $L - \varepsilon < a_k < L + \varepsilon$ for $k \ge N$. For $n \ge N$, $L + \varepsilon$ bounds $\{a_k : k \ge n\}$, so $L - \varepsilon < a_n \le s_n \le L + \varepsilon$. So $s_n \to L$, and in the same way $i_n \to L$. $\square$

In Mathlib this is `tendsto_of_liminf_eq_limsup` with its converse `Filter.Tendsto.limsup_eq`.

### Examples

**Example (A contraction to $\sqrt 2$).** Let $b_0 = 1$ and $b_{n+1} = 1 + \dfrac{1}{1 + b_n}$. The first terms are
$$1, \quad \frac{3}{2}, \quad \frac{7}{5}, \quad \frac{17}{12}, \quad \frac{41}{29}, \quad \frac{99}{70}.$$
By induction $1 \le b_n \le 3/2$. For $n \ge 1$,
$$b_{n+1} - b_n = \frac{b_{n-1} - b_n}{(1 + b_n)(1 + b_{n-1})},$$
and the denominator is at least $4$. So $|b_{n+1} - b_n| \le \tfrac12 4^{-n}$. By the geometric Cauchy bound with $C = 1/2$ and $r = 1/4$, the sequence has a limit $L$, with $|b_n - L| \le \tfrac{2}{3} 4^{-n}$. The limit satisfies $L = 1 + 1/(1 + L)$, so $L^2 = 2$ and $L = \sqrt 2$. The sequence is not monotone: it alternates around $\sqrt 2 \approx 1.41421$. The monotone convergence theorem does not apply, and the Cauchy criterion does.

**Counterexample (Completeness fails in $\mathbb{Q}$).** All the terms $b_n$ are rational, and the sequence is Cauchy. In $\mathbb{Q}$ it has no limit, since the only possible limit is the irrational number $\sqrt 2$. The subsequence $(b_{2k})$ is increasing and bounded in $\mathbb{Q}$ with no limit in $\mathbb{Q}$. So the theorems of this section need the completeness of $\mathbb{R}$. Conversely each real number is a limit of rationals: `Real.exists_seq_rat_strictMono_tendsto`.

**Example (Upper and lower limits).** Let $a_n = (-1)^n (1 + 1/(n+1))$. The supremum of the tail from $n$ is its first even term, so $s_n \to 1$ and $\limsup a_n = 1$. In the same way $\liminf a_n = -1$. The two values differ, so the sequence diverges.

### The library around it

The file `Mathlib.Topology.Instances.Real.Lemmas` gives the facts of this section that are special to `ℝ`: monotone convergence from an index on, the limit as a supremum, dense sequences of rationals and the criterion `Real.mem_closure_iff`. The general theorems are in Volume 13. A subsequence in Mathlib is a composition `a ∘ φ` with `StrictMono φ`, and `StrictMono.tendsto_atTop` with `Filter.Tendsto.comp` gives the limit of a subsequence.

Common errors of a learner:

- In `ℝ`, `⨆ n, a n` is the junk value `0` when the sequence is not bounded above (`Real.iSup_of_not_bddAbove`). The hypothesis `BddAbove (Set.range a)` is not optional.
- A sequence with $|a_{n+1} - a_n| \to 0$ need not be Cauchy. The partial sums of the harmonic series in Section 3 are a counterexample.
- The limit of a subsequence is not the limit of the sequence. Step 3 of the Cauchy criterion is the extra argument.
- `Filter.limsup` in `ℝ` has a value for each sequence, junk when the sequence is unbounded.

### Exercises

1. (A) Let $a_1 = \sqrt 2$ and $a_{n+1} = \sqrt{2 + a_n}$. Show that $0 < a_n < 2$, that the sequence is increasing, and that $a_n \to 2$. Hint: $a_{n+1}^2 - a_n^2 = (2 - a_n)(1 + a_n)$.
2. (A) Show that each subsequence of a Cauchy sequence is a Cauchy sequence.
3. (A) Compute $\limsup$ and $\liminf$ of $a_n = \sin(n\pi/2) + 1/n$ for $n \ge 1$.
4. (B) Let $x_0 = 2$ and $x_{n+1} = \tfrac{1}{2}(x_n + 2/x_n)$. Show that $x_n$ decreases to $\sqrt 2$, that $x_{n+1} - \sqrt 2 = (x_n - \sqrt 2)^2 / (2 x_n)$, and compute $x_3$. Hint: the arithmetic mean of $x$ and $2/x$ is at least their geometric mean.
5. (B) Let $(a_n)$ be bounded, and let $L$ be the limit of a convergent subsequence. Show that $\liminf a_n \le L \le \limsup a_n$.
6. (B) Prove the theorem of nested intervals: if $[a_{n+1}, b_{n+1}] \subseteq [a_n, b_n]$ and $b_n - a_n \to 0$, the intersection is one point.
7. (C) Let $f : [0, 1] \to [0, 1]$ satisfy $|f(x) - f(y)| \le \tfrac{1}{2} |x - y|$. Show that $f$ has exactly one fixed point. Hint: apply the geometric Cauchy bound to $x_{n+1} = f(x_n)$.

### Notes and history

Bolzano proved in 1817 that a bounded sequence has a point of accumulation, and Weierstrass made the result a basic tool in his Berlin lectures of the 1860s. Cauchy stated his criterion in the *Cours d'analyse* of 1821 and used it as evident. A proof needs a construction of the real numbers, which came in 1872, from Dedekind with cuts and from Cantor and Méray with Cauchy sequences. The argument with peaks is a later classroom proof.

### Reference

<?reference?>
