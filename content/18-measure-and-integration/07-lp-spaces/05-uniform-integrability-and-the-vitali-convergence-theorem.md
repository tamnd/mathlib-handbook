---
title: Uniform integrability and the Vitali convergence theorem
kind: api
modules:
  - Mathlib.MeasureTheory.Function.UniformIntegrable
  - Mathlib.MeasureTheory.Function.UnifTight
explains:
  E2: [MeasureTheory.UnifIntegrable, MeasureTheory.UniformIntegrable, MeasureTheory.UnifTight, MeasureTheory.tendsto_Lp_finite_of_tendsto_ae, MeasureTheory.tendstoInMeasure_iff_tendsto_Lp_finite, MeasureTheory.tendstoInMeasure_iff_tendsto_Lp, MeasureTheory.uniformIntegrable_iff]
  E1: auto
families: []
requires: [V18.C04, V18.C05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Uniform integrability and the Vitali convergence theorem

### Overview

The dominated convergence theorem of Chapter 5 says that $f_n \to g$ almost everywhere and $|f_n| \le h$ with $h$ integrable give $\int f_n \to \int g$. The domination is sufficient, but it is not necessary. The sequence $f_n = n \, \mathbf{1}_{[1/n, 2/n]} / \log n$ on $[0, 1]$, for example, has no integrable dominating function, but it converges to zero in $L^1$. The right condition is *uniform integrability*: the functions must not put a fixed amount of mass on sets of small measure. On a space of infinite measure a second condition is needed, *uniform tightness*: the functions must not move their mass to infinity.

The theorem of Vitali says that, for $1 \le p < \infty$, a sequence converges in $L^p$ if and only if it converges in measure and is uniformly integrable and uniformly tight. This section explains the three predicates of Mathlib and the forms of the theorem of Vitali. It needs the seminorm `eLpNorm` and the $L^p$ API of this chapter, and convergence in measure and the theorem of Egorov from Chapter 5.

### The library around it

#### Three predicates

Mathlib has three predicates on a family `f : ι → α → β`, all with an exponent `p : ENNReal` and a measure `μ`.

1. `MeasureTheory.UnifIntegrable f p μ` says: for every $\varepsilon > 0$ there is $\delta > 0$ such that $\|\mathbf{1}_s f_i\|_p \le \varepsilon$ for every $i$ and every measurable set $s$ with $\mu(s) \le \delta$. This is the condition of small mass on small sets, with one $\delta$ for the whole family.
2. `MeasureTheory.UniformIntegrable f p μ` adds two conditions to the first one: every `f i` is almost everywhere strongly measurable, and the seminorms `eLpNorm (f i) p μ` have a common finite bound. This is the notion of probability theory.
3. `MeasureTheory.UnifTight f p μ` says: for every $\varepsilon > 0$ there is a set $s$ of finite measure with $\|\mathbf{1}_{s^c} f_i\|_p \le \varepsilon$ for every $i$. This is the condition of no mass at infinity.

The names are close, and the difference matters. `UnifIntegrable` has no bound on the norms. On a finite measure space with no atoms it implies the bound, but on a space with an atom it does not: the constant functions $f_n = n$ on a one-point space form a `UnifIntegrable` family, because the only set of small measure is empty. The lemma `MeasureTheory.UniformIntegrable.unifIntegrable` forgets the extra conditions. The lemma `MeasureTheory.UniformIntegrable.mk` builds the strong predicate from the weak one and a bound, and `MeasureTheory.UniformIntegrable.iSup_eLpNorm_lt` extracts the bound.

The first predicate has several equivalent forms. The lemma `MeasureTheory.unifIntegrable_iff` replaces the indicator by the restricted measure: `eLpNorm (f i) p (μ.restrict s) ≤ ε`. The lemma `MeasureTheory.unifIntegrable_iff_tendsto` says that the supremum over $i$ and over sets of measure at most $\varepsilon$ tends to zero as $\varepsilon \to 0$. The third predicate has forms with $\varepsilon$ in `ℝ`, `NNReal` and `ENNReal`: `MeasureTheory.unifTight_iff_real`, `MeasureTheory.unifTight_iff_nnreal` and `MeasureTheory.unifTight_iff_ennreal`.

#### Single functions and finite families

A single function in $L^p$ is uniformly integrable, and the proof is the base of all the rest. The lemma `MeasureTheory.MemLp.eLpNorm_indicator_le` says: for $1 \le p < \infty$, `f` in $L^p$ and $\varepsilon > 0$, there is $\delta > 0$ such that $\|\mathbf{1}_s f\|_p \le \varepsilon$ for every set with $\mu(s) \le \delta$. The proof cuts $f$ at a large level $M$. The lemma `MeasureTheory.MemLp.eLpNorm_indicator_norm_ge_le` makes the part above $M$ small. The part below $M$ is bounded, and `MeasureTheory.eLpNorm_indicator_le_of_bound` makes its seminorm on a small set small.

Finite families follow from single functions:

| Lean name | Statement |
|---|---|
| `MeasureTheory.unifIntegrable_const` | a constant family of one function in $L^p$ is `UnifIntegrable` |
| `MeasureTheory.unifIntegrable_finite` | a finite family of functions in $L^p$ is `UnifIntegrable` |
| `MeasureTheory.uniformIntegrable_finite` | the same for `UniformIntegrable` |
| `MeasureTheory.unifTight_const` | a constant family of one function in $L^p$ is `UnifTight` |
| `MeasureTheory.unifTight_finite` | a finite family of functions in $L^p$ is `UnifTight` |

All of these need $p \ne \infty$. For $p = \infty$ the function $\mathbf{1}_{[0,1]}$ on the line is not `UnifIntegrable`: its $L^\infty$ seminorm on every set of positive measure is one.

#### Operations on families

The predicates are stable under the usual operations. The lemmas `MeasureTheory.UnifIntegrable.add`, `MeasureTheory.UnifIntegrable.neg` and `MeasureTheory.UnifIntegrable.sub` treat sums and differences. The lemmas `MeasureTheory.UnifTight.add`, `MeasureTheory.UnifTight.neg` and `MeasureTheory.UnifTight.sub` do the same for tightness. The lemmas `MeasureTheory.UnifIntegrable.comp` and `MeasureTheory.UnifTight.comp` reindex a family, so a subsequence of a uniformly integrable sequence is uniformly integrable. The lemma `MeasureTheory.UnifIntegrable.ae_mono` says that a family dominated pointwise by a uniformly integrable family is uniformly integrable. The lemmas `MeasureTheory.unifIntegrable_congr_ae` and `MeasureTheory.unifTight_congr_ae` say that the predicates depend only on the classes of the functions.

For real sequences, `MeasureTheory.uniformIntegrable_average_real` says that the averages $\frac{1}{n} \sum_{i < n} f_i$ of a uniformly integrable sequence are uniformly integrable. The lemma `MeasureTheory.uniformIntegrable_average` is the version with values in a normed space. The laws of large numbers in probability use this lemma.

#### The criterion by truncation

On a finite measure space, `UniformIntegrable` has the form of probability theory. The lemma `MeasureTheory.uniformIntegrable_iff` says: for $1 \le p < \infty$, the family is uniformly integrable if and only if each `f i` is almost everywhere strongly measurable and for every $\varepsilon > 0$ there is $C$ with
$$\|\mathbf{1}_{\{C \le \|f_i\|\}} f_i\|_p \le \varepsilon \quad \text{for all } i.$$
The mass above the level $C$ is uniformly small. The lemmas `MeasureTheory.uniformIntegrable_of` and `MeasureTheory.UniformIntegrable.spec` are the two directions. The prime versions `MeasureTheory.uniformIntegrable_of'` and `MeasureTheory.UniformIntegrable.spec'` take strongly measurable functions and are easier to prove.

A family bounded in $L^q$ for some $q > p$ satisfies this criterion, by the inequality of Chebyshev and Markov of Section 3. This gives the most common way to prove uniform integrability in practice.

#### The theorem of Vitali

The main results relate convergence in $L^p$ to convergence in measure. On a finite measure space tightness is free, and two conditions suffice.

| Lean name | Statement |
|---|---|
| `MeasureTheory.tendsto_Lp_finite_of_tendsto_ae` | $\mu$ finite, $f_n \to g$ a.e., $(f_n)$ `UnifIntegrable`, $g \in L^p$: then $\|f_n - g\|_p \to 0$ |
| `MeasureTheory.tendsto_Lp_finite_of_tendstoInMeasure` | the same with convergence in measure |
| `MeasureTheory.tendstoInMeasure_iff_tendsto_Lp_finite` | $\mu$ finite: convergence in measure and `UnifIntegrable` if and only if convergence in $L^p$ |
| `MeasureTheory.tendsto_Lp_of_tendsto_ae` | any $\mu$: add `UnifTight` |
| `MeasureTheory.tendsto_Lp_of_tendstoInMeasure` | any $\mu$, with convergence in measure |
| `MeasureTheory.tendstoInMeasure_iff_tendsto_Lp` | any $\mu$: convergence in measure, `UnifIntegrable` and `UnifTight` if and only if convergence in $L^p$ |

All of them need $1 \le p < \infty$ and the strong measurability of each $f_n$. The proof for a finite measure uses the theorem of Egorov of Chapter 5: outside a set of small measure the convergence is uniform, and on the small set uniform integrability controls the seminorm. For a general measure, tightness reduces the problem to a set of finite measure.

The converse direction has its own lemmas. `MeasureTheory.unifIntegrable_of_tendsto_Lp` says that a sequence that converges in $L^p$ is `UnifIntegrable`. For limits, `MeasureTheory.UniformIntegrable.memLp_of_ae_tendsto` and `MeasureTheory.UniformIntegrable.integrable_of_ae_tendsto` say that the limit of a uniformly integrable sequence is in $L^p$ and integrable. They are the form of the lemma of Fatou for this setting.

#### Common errors

1. Using `UnifIntegrable` where `UniformIntegrable` is needed. The first predicate has no bound on the norms, and the integrability of a limit needs the bound. Check which predicate a lemma takes.
2. Applying the finite versions of the theorem of Vitali on the line. On a space of infinite measure, uniform integrability is not enough: the functions $\mathbf{1}_{[n, n+1]}$ are uniformly integrable and converge to zero everywhere, but not in $L^1$. Add `UnifTight`.
3. Proving uniform integrability for $p = \infty$. The lemmas need $p \ne \infty$, and even a single bounded function is not uniformly integrable in $L^\infty$.

### Exercises

1. (A) Show that a family of functions with $|f_i| \le h$ for one $h \in L^1$ is `UnifIntegrable` with $p = 1$.
2. (A) Show that the functions $n \, \mathbf{1}_{[0, 1/n]}$ on $[0, 1]$ are not `UnifIntegrable` with $p = 1$.
3. (B) Show that a sequence bounded in $L^2$ on a probability space is `UniformIntegrable` with $p = 1$, with `MeasureTheory.uniformIntegrable_of`.
4. (B) Show that the functions $\mathbf{1}_{[n, n+1]}$ on the line are `UnifIntegrable` but not `UnifTight` with $p = 1$.
5. (B) Deduce the dominated convergence theorem for a finite measure from `MeasureTheory.tendsto_Lp_finite_of_tendsto_ae` with $p = 1$.
6. (C) Prove that on a finite measure space with no atoms, a `UnifIntegrable` family has bounded $L^1$ seminorms.

### Reference

<?reference?>
