---
title: Lp spaces and completeness
kind: theory
modules:
  - Mathlib.MeasureTheory.Function.AEEqFun
  - Mathlib.MeasureTheory.Function.LpSpace.Basic
  - Mathlib.MeasureTheory.Function.LpSpace.Complete
  - Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
  - Mathlib.MeasureTheory.Function.ContinuousMapDense
  - Mathlib.MeasureTheory.Function.L2Space
explains:
  E3: [MeasureTheory.AEEqFun, MeasureTheory.Lp, MeasureTheory.Lp.norm_def, MeasureTheory.Lp.instCompleteSpace, MeasureTheory.Lp.simpleFunc.dense, MeasureTheory.MemLp.exists_hasCompactSupport_eLpNorm_sub_le, MeasureTheory.L2.innerProductSpace]
  E2: [MeasureTheory.AEEqFun.mk, MeasureTheory.AEEqFun.mk_eq_mk, MeasureTheory.Measure.aeEqSetoid, MeasureTheory.MemLp.toLp, MeasureTheory.MemLp.coeFn_toLp, MeasureTheory.Lp.mem_Lp_iff_memLp, MeasureTheory.Lp.instNormedAddCommGroup, MeasureTheory.Lp.ae_tendsto_of_cauchy_eLpNorm, MeasureTheory.Lp.cauchy_complete_eLpNorm, MeasureTheory.Lp.eLpNorm_lim_le_liminf_eLpNorm, MeasureTheory.Lp.simpleFunc, MeasureTheory.MemLp.induction, MeasureTheory.Integrable.induction, MeasureTheory.L2.inner_def, MeasureTheory.memLp_two_iff_integrable_sq]
  E1: auto
families: []
requires: [V13, V18.C04, V18.C05]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Lp spaces and completeness

### Overview

This section identifies functions that agree almost everywhere and obtains a normed space $L^p(\mu)$. The main theorem, due to Riesz and Fischer, is that $L^p(\mu)$ is complete for $1 \le p \le \infty$. The section then proves that simple functions, and on $\mathbb{R}^n$ continuous functions with compact support, are dense for $p < \infty$. It ends with the inner product of $L^2$.

### Definitions

**Definition (Classes of functions).** Two measurable functions are equivalent if they agree $\mu$-almost everywhere. This is an equivalence relation, because a union of two null sets is null. The class of $f$ is written $[f]$.

**Definition ($L^p$).** Let $1 \le p \le \infty$. The space $L^p(\mu)$ is the set of the classes $[f]$ with $f \in \mathcal{L}^p(\mu)$, with $\|[f]\|_p = \|f\|_p$ and the operations $[f] + [g] = [f + g]$ and $c[f] = [cf]$.

These are well defined, because $\|f\|_p$ does not see null sets (Section 1).

### Theorems and proofs

**Proposition 1 (Norm).** For $1 \le p \le \infty$, $\|\cdot\|_p$ is a norm on $L^p(\mu)$.

*Proof.* Homogeneity is direct and the triangle inequality is Minkowski (Section 1, Theorem 3). If $\|f\|_p = 0$, then $\int |f|^p = 0$ for $p < \infty$, or $|f| \le 0$ almost everywhere for $p = \infty$ by Lemma 1 of Section 1. In both cases $f = 0$ almost everywhere, so $[f] = 0$. $\square$

**Lemma 2 (Fast Cauchy sequences converge almost everywhere).** Let $1 \le p \le \infty$ and $f_n \in \mathcal{L}^p(\mu)$ with $B = \sum_n \|f_{n + 1} - f_n\|_p < \infty$. Then $f_n(x)$ converges for almost every $x$.

*Proof.* Let $p < \infty$ and $g_N = \sum_{n < N} |f_{n + 1} - f_n|$. By Minkowski, $\|g_N\|_p \le B$. The $g_N$ increase to $g = \sum_n |f_{n + 1} - f_n|$. By monotone convergence, $\int g^p = \sup_N \int g_N^p \le B^p$. So $g < \infty$ almost everywhere. At such an $x$, the series $\sum_n (f_{n + 1}(x) - f_n(x))$ converges absolutely, so its partial sums $f_N(x) - f_0(x)$ converge.

Let $p = \infty$. By Lemma 1 of Section 1, $|f_{n + 1}(x) - f_n(x)| \le \|f_{n + 1} - f_n\|_\infty$ outside a null set $N_n$. Outside $\bigcup_n N_n$ the series converges absolutely. $\square$

**Theorem 3 (Riesz and Fischer).** For $1 \le p \le \infty$, $L^p(\mu)$ is complete.

*Proof.* Let $(f_n)$ be a Cauchy sequence. Choose $n_1 < n_2 < \dots$ with $\|f_m - f_{n_k}\|_p < 2^{-k}$ for all $m \ge n_k$. Then $\sum_k \|f_{n_{k + 1}} - f_{n_k}\|_p < 1$. By Lemma 2, $f_{n_k}$ converges almost everywhere to a measurable function $f$, defined as $0$ on the exceptional null set.

Let $p < \infty$ and fix $k$. For $j \ge k$, $|f_{n_j} - f_{n_k}|^p \to |f - f_{n_k}|^p$ almost everywhere. Fatou's lemma (Chapter 4, Section 2) gives
$$\int |f - f_{n_k}|^p \, d\mu \le \liminf_{j} \int |f_{n_j} - f_{n_k}|^p \, d\mu \le 2^{-kp}.$$
So $f - f_{n_k} \in \mathcal{L}^p$, hence $f = (f - f_{n_k}) + f_{n_k} \in \mathcal{L}^p$, and $\|f - f_{n_k}\|_p \le 2^{-k} \to 0$. For $p = \infty$, the bound $|f_{n_j} - f_{n_k}| \le 2^{-k}$ holds outside a null set for all $j \ge k$, and the limit in $j$ gives $|f - f_{n_k}| \le 2^{-k}$ almost everywhere.

A Cauchy sequence with a convergent subsequence converges to the same limit, because $\|f_m - f\|_p \le \|f_m - f_{n_k}\|_p + \|f_{n_k} - f\|_p$. $\square$

**Corollary 4.** If $f_n \to f$ in $L^p$, then a subsequence converges to $f$ almost everywhere.

*Proof.* The proof of Theorem 3, applied to the Cauchy sequence $(f_n)$, gives a subsequence that converges almost everywhere and in $L^p$ to some $g$. Then $[g] = [f]$. $\square$

**Theorem 5 (Density of simple functions).** Let $1 \le p < \infty$. The simple functions $\varphi$ with $\mu(\{\varphi \ne 0\}) < \infty$ are dense in $L^p(\mu)$.

*Proof.* Let $f \ge 0$ be in $\mathcal{L}^p$. Choose simple $0 \le \varphi_n \uparrow f$ (Chapter 4, Section 1). Then $|f - \varphi_n|^p \le f^p$, which is integrable, and $|f - \varphi_n|^p \to 0$ pointwise. Dominated convergence (Chapter 5) gives $\|f - \varphi_n\|_p \to 0$. If $c > 0$ is the smallest positive value of $\varphi_n$, then $\{\varphi_n \ne 0\} \subseteq \{f \ge c\}$, which has measure at most $c^{-p} \int f^p < \infty$ by the inequality of Markov. For a real $f$, approximate $f^+$ and $f^-$ separately. For a complex $f$, approximate the real and the imaginary parts. $\square$

**Theorem 6 (Density of continuous functions).** Let $\mu$ be Lebesgue measure on $\mathbb{R}^n$ and $1 \le p < \infty$. The continuous functions with compact support are dense in $L^p(\mu)$.

*Proof.* By Theorem 5 and Minkowski, it is enough to approximate $\mathbf{1}_A$ with $\mu(A) < \infty$. Let $\varepsilon > 0$. By the regularity of Lebesgue measure (Chapter 3, Section 1), there are a compact $K$ and an open $U$ with $K \subseteq A \subseteq U$ and $\mu(U \setminus K) < \varepsilon$. Replace $U$ by its intersection with a bounded open set that contains $K$, so that $\overline{U}$ is compact. By Urysohn's lemma (Volume 13, Chapter 8) there is a continuous $g$ with $0 \le g \le 1$, $g = 1$ on $K$, and $g = 0$ outside a compact subset of $U$. Then $|\mathbf{1}_A - g| \le \mathbf{1}_{U \setminus K}$, so $\|\mathbf{1}_A - g\|_p^p \le \mu(U \setminus K) < \varepsilon$. $\square$

**Proposition 7 ($L^2$).** The formula $\langle f, g \rangle = \int f \bar{g} \, d\mu$ defines an inner product on $L^2(\mu)$ with $\langle f, f \rangle = \|f\|_2^2$. With Theorem 3, $L^2(\mu)$ is a Hilbert space.

*Proof.* By Hölder with $p = q = 2$, $\int |f \bar{g}| \le \|f\|_2 \|g\|_2 < \infty$. The algebraic properties come from the linearity of the integral. $\square$

::: mathlib
`MeasureTheory.AEEqFun` · `Mathlib.MeasureTheory.Function.AEEqFun`

The type `α →ₘ[μ] β` is the quotient of the a.e. strongly measurable functions by the relation `Measure.aeEqSetoid`. The class of `f` is `AEEqFun.mk f hf`, and `AEEqFun.mk_eq_mk` says that two classes are equal if and only if the functions agree almost everywhere.

<?decl MeasureTheory.AEEqFun?>
<?decl MeasureTheory.AEEqFun.mk_eq_mk?>
:::

::: mathlib
`MeasureTheory.Lp` · `Mathlib.MeasureTheory.Function.LpSpace.Basic`

`Lp E p μ` is an `AddSubgroup` of `α →ₘ[μ] E`, the classes with `eLpNorm f p μ < ∞` (`Lp.mem_Lp_iff_memLp`). A function with `hf : MemLp f p μ` gives the element `hf.toLp f`, whose representative agrees with `f` almost everywhere (`MemLp.coeFn_toLp`). The norm is `Lp.norm_def : ‖f‖ = (eLpNorm f p μ).toReal`. The instance `Lp.instNormedAddCommGroup` needs `[Fact (1 ≤ p)]`, a way to give the hypothesis $1 \le p$ to the instance search.

<?decl MeasureTheory.Lp?>
<?decl MeasureTheory.MemLp.toLp?>
<?decl MeasureTheory.Lp.norm_def?>
<?decl MeasureTheory.Lp.instNormedAddCommGroup?>
:::

::: mathlib
`MeasureTheory.Lp.instCompleteSpace` · `Mathlib.MeasureTheory.Function.LpSpace.Complete`

Theorem 3 is the instance `Lp.instCompleteSpace`, for `[CompleteSpace E] [Fact (1 ≤ p)]`. The proof follows the steps above, for sequences with `eLpNorm (f n - f m) p μ < B N` and a summable `B`. Lemma 2 is `ae_tendsto_of_cauchy_eLpNorm`, the use of Fatou is `eLpNorm_lim_le_liminf_eLpNorm`, and `cauchy_complete_eLpNorm` combines them.

<?decl MeasureTheory.Lp.instCompleteSpace?>
<?decl MeasureTheory.Lp.ae_tendsto_of_cauchy_eLpNorm?>
<?decl MeasureTheory.Lp.eLpNorm_lim_le_liminf_eLpNorm?>
:::

### Examples

**Counterexample (Convergence in $L^p$ without convergence almost everywhere).** On $[0, 1]$ write $n = 2^k + j$ with $0 \le j < 2^k$ and let $f_n = \mathbf{1}_{[j 2^{-k}, (j + 1) 2^{-k}]}$. Then $\|f_n\|_p = 2^{-k/p} \to 0$, so $f_n \to 0$ in $L^p$ for every $p < \infty$. For each $x$ and $k \ge 1$, at least one and at most two of the $2^k$ intervals of generation $k$ contain $x$. So $f_n(x) = 1$ and $f_n(x) = 0$ both occur for infinitely many $n$, and $f_n(x)$ converges at no point. The subsequence $f_{2^k} = \mathbf{1}_{[0, 2^{-k}]}$ converges to $0$ at every $x > 0$, as Corollary 4 predicts.

**Counterexample (Density fails for $p = \infty$).** On $[0, 1]$ let $f = \mathbf{1}_{[0, 1/2]}$, and let $g$ be continuous with $c = \|f - g\|_\infty$. Then $g \ge 1 - c$ almost everywhere on $[0, 1/2]$ and $g \le c$ almost everywhere on $(1/2, 1]$. A set of full measure in an interval is dense in it, so continuity gives $g(1/2) \ge 1 - c$ and $g(1/2) \le c$. Hence $c \ge 1/2$. The continuous functions are not dense in $L^\infty$, and Theorem 6 needs $p < \infty$.

### The library around it

::: mathlib
`MeasureTheory.Lp.simpleFunc.dense` · `Mathlib.MeasureTheory.Function.SimpleFuncDenseLp`

`Lp.simpleFunc E p μ` is the subgroup of the classes of simple functions, and `Lp.simpleFunc.dense` is Theorem 5, for `p ≠ ∞`. The induction principle `MemLp.induction` proves a property on $\mathcal{L}^p$ from indicators, disjoint sums, closedness and a.e. equality. Its form for $p = 1$ is `Integrable.induction`, used for Fubini in Chapter 6, Section 2.

<?decl MeasureTheory.Lp.simpleFunc.dense?>
<?decl MeasureTheory.MemLp.induction?>
<?decl MeasureTheory.Integrable.induction?>
:::

::: mathlib
`MeasureTheory.MemLp.exists_hasCompactSupport_eLpNorm_sub_le` · `Mathlib.MeasureTheory.Function.ContinuousMapDense`

Theorem 6 is `MemLp.exists_hasCompactSupport_eLpNorm_sub_le`. It holds for `p ≠ ∞` and a regular measure on a space with topological hypotheses that $\mathbb{R}^n$ satisfies, and gives a continuous `g` with compact support and `eLpNorm (f - g) p μ ≤ ε`.

<?decl MeasureTheory.MemLp.exists_hasCompactSupport_eLpNorm_sub_le?>
:::

::: mathlib
`MeasureTheory.L2.innerProductSpace` · `Mathlib.MeasureTheory.Function.L2Space`

The instance `L2.innerProductSpace` makes `Lp E 2 μ` an inner product space when `E` is one, and `L2.inner_def` gives $\langle f, g \rangle = \int \langle f(a), g(a) \rangle \, d\mu$. For real functions, `memLp_two_iff_integrable_sq` says that $f \in \mathcal{L}^2$ if and only if $f^2$ is integrable.

<?decl MeasureTheory.L2.innerProductSpace?>
<?decl MeasureTheory.L2.inner_def?>
:::

Common errors of a learner:

- Evaluating an element of `Lp` at a point and using the value. Only the class is defined; the representative is a choice.
- Deducing convergence almost everywhere from convergence in $L^p$. Only a subsequence converges.

### Exercises

1. (A) Show that $\|f_n - f\|_p \to 0$ implies $\|f_n\|_p \to \|f\|_p$.
2. (A) Show that the simple functions are dense in $L^\infty(\mu)$. Hint: round the values of a bounded function.
3. (B) Let $\mu(X) < \infty$ and $1 \le p < q \le \infty$. Show that $L^q$ is dense in $L^p$. Hint: bounded functions are in $L^q$; use truncations and dominated convergence.
4. (B) Let $f \in L^p(\mathbb{R})$, $1 \le p < \infty$, and $\tau_h f(x) = f(x - h)$. Show that $\|\tau_h f - f\|_p \to 0$ as $h \to 0$. Hint: Theorem 6 and the uniform continuity of a continuous function with compact support.
5. (B) Show that if $f_n \to f$ in $L^p$ and $f_n \to g$ almost everywhere, then $f = g$ almost everywhere. Hint: Corollary 4.
6. (C) Show that $L^p(0, 1)$ is separable for $1 \le p < \infty$. Hint: the linear combinations with rational coefficients of indicators of intervals with rational endpoints, with Theorem 5 and the regularity of Lebesgue measure.

### Notes and history

Riesz and Fischer proved the completeness of $L^2$ in 1907. In Mathlib, the file on classes of functions has Johannes Hölzl and Zhouhang Zhou as authors, the files on `Lp` and its completeness have Rémy Degenne and Sébastien Gouëzel, the file on the density of simple functions has Zhouhang Zhou, Yury Kudryashov and Heather Macbeth, the file on the density of continuous functions has Heather Macbeth, and the file on $L^2$ has Rémy Degenne.

### Reference

<?reference?>
