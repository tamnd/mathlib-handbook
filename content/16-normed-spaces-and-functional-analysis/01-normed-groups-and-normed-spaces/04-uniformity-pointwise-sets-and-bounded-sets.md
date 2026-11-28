---
title: Uniformity, pointwise sets and bounded sets in normed groups
kind: api
modules:
  - Mathlib.Analysis.Normed.Group.Uniform
  - Mathlib.Analysis.Normed.Group.Pointwise
  - Mathlib.Analysis.Normed.Group.Bounded
  - Mathlib.Analysis.Normed.Group.BallSphere
  - Mathlib.Analysis.Normed.Group.Lemmas
  - Mathlib.Analysis.Normed.Group.Indicator
  - Mathlib.Analysis.Normed.Group.FunctionSeries
  - Mathlib.Analysis.Normed.Group.Tannery
  - Mathlib.Analysis.Normed.Group.ZeroAtInfty
  - Mathlib.Analysis.Normed.Group.CocompactMap
  - Mathlib.Analysis.Normed.Group.RadialFunction
explains:
  E2: [AddMonoidHomClass.isometry_iff_norm, AntilipschitzWith.add_lipschitzWith, add_ball_zero, isBounded_iff_forall_norm_le, comap_norm_atTop, continuous_tsum, tendsto_tsum_of_dominated_convergence, Function.isRadial_def]
  E1: auto
families: []
requires: [V07, V13, V15]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Uniformity, pointwise sets and bounded sets in normed groups

### Overview

Section 1 defines a normed group and its metric $d(x, y) = \|x - y\|$. This metric is invariant under translation, and this fact has many small consequences: the group operations are uniformly continuous, a homomorphism is an isometry when it keeps the norm, the sum of two balls is a ball, and a set is bounded when its norms are bounded. The modules of this section collect these consequences. They are the daily tools of the later chapters, so the section lists them by family and names the pattern of each family.

The section also treats some results on functions with values in a normed group: the norm of an indicator function, the Weierstrass test for a series of functions, the theorem of Tannery on the limit of a series, and functions that tend to $0$ at infinity. It ends with radial functions, the functions that depend only on the norm.

### The library around it

#### The uniform structure

The module `Mathlib.Analysis.Normed.Group.Uniform` proves that a seminormed group is a uniform group. The instances `SeminormedAddCommGroup.to_isUniformAddGroup` and `SeminormedAddCommGroup.toIsTopologicalAddGroup` give this for an additive group, and `SeminormedAddCommGroup.to_lipschitzAdd` says that addition is Lipschitz. The proof is one inequality, `dist_add_add_le`:
$$d(a_1 + a_2, b_1 + b_2) = \|(a_1 - b_1) + (a_2 - b_2)\| \le d(a_1, b_1) + d(a_2, b_2).$$
The lemmas `dist_sub_sub_le` and `edist_add_add_le` are the same bound for subtraction and for the extended distance. The distance to a translate is a norm: `dist_self_add_right` states $d(b, b + a) = \|a\|$, and `dist_self_sub_right` states $d(a, a - b) = \|b\|$.

A homomorphism $f$ of normed groups has $d(f x, f y) = \|f(x - y)\|$. So the metric properties of $f$ reduce to bounds at the origin. The family `AddMonoidHomClass` has the main forms.

| Lean name | Statement |
|---|---|
| `AddMonoidHomClass.isometry_iff_norm` | $f$ is an isometry if and only if $\|f x\| = \|x\|$ for all $x$ |
| `AddMonoidHomClass.lipschitz_of_bound` | $\|f x\| \le C \|x\|$ implies that $f$ is Lipschitz with constant $C$ |
| `AddMonoidHomClass.continuous_of_bound` | the same bound implies that $f$ is continuous |
| `AddMonoidHomClass.antilipschitz_of_bound` | $\|x\| \le K \|f x\|$ implies that $f$ is antilipschitz |
| `antilipschitzWith_iff_exists_mul_le_norm` | $f$ is antilipschitz for some $K$ if and only if $c \|x\| \le \|f x\|$ for some $c > 0$ |

*Proof of the first line.* If $f$ is an isometry, then $\|f x\| = d(f x, f 0) = d(x, 0) = \|x\|$. Conversely, $d(f x, f y) = \|f x - f y\| = \|f(x - y)\| = \|x - y\| = d(x, y)$. $\square$

For a function $f$ that is not a homomorphism, the lemmas `LipschitzWith.norm_sub_le` and `lipschitzWith_iff_norm_sub_le` write the Lipschitz condition as $\|f x - f y\| \le C \|x - y\|$. The norm itself is Lipschitz with constant $1$, by `lipschitzWith_one_norm`, and uniformly continuous, by `uniformContinuous_norm`.

**Perturbation of an antilipschitz map.** Let $f$ be antilipschitz with constant $K_f$ and $g$ Lipschitz with constant $K_g < K_f^{-1}$. Then $f + g$ is antilipschitz with constant $(K_f^{-1} - K_g)^{-1}$. This is `AntilipschitzWith.add_lipschitzWith`. *Proof.* $\|(f + g)x - (f + g)y\| \ge \|f x - f y\| - \|g x - g y\| \ge (K_f^{-1} - K_g)\|x - y\|$. $\square$ The lemma gives the stability of the injective operators with closed range under small perturbations.

The same module has the uniform version of the Cauchy criterion, `NormedAddCommGroup.cauchySeq_iff`, and the fact that a Cauchy sequence has bounded norms, `CauchySeq.norm_bddAbove`. The lemma `Real.isometry_intCast` says that $\mathbb{Z} \to \mathbb{R}$ is an isometry, and `Real.isClosedEmbedding_intCast` that its image is closed. It also puts a norm on the separation quotient: `SeparationQuotient.norm_mk` states $\|[x]\| = \|x\|$, and `SeparationQuotient.instNormedAddCommGroup` makes the quotient a normed group. Section 5 returns to this quotient.

#### Pointwise sums of balls and sets

In a normed group the pointwise sum $s + t = \{a + b : a \in s, b \in t\}$ of a set and a ball is a thickening. The module `Mathlib.Analysis.Normed.Group.Pointwise` states the identities.

| Lean name | Statement |
|---|---|
| `add_ball_zero` | $s + B(0, \delta) = \{x : d(x, s) < \delta\}$ |
| `IsCompact.add_closedBall_zero` | for $s$ compact and $\delta \ge 0$, $s + \bar B(0, \delta) = \{x : d(x, s) \le \delta\}$ |
| `singleton_add_ball` | $\{x\} + B(y, \delta) = B(x + y, \delta)$ |
| `vadd_ball_zero` | $x + B(0, \delta) = B(x, \delta)$ |
| `neg_ball` | $-B(x, \delta) = B(-x, \delta)$ |
| `neg_thickening` | $-s_\delta = (-s)_\delta$ |

*Proof of the first line.* A point $x$ lies in $s + B(0, \delta)$ if and only if $x = a + b$ with $a \in s$ and $\|b\| < \delta$, that is, if and only if $\|x - a\| < \delta$ for some $a \in s$. This is the condition $\inf_{a \in s} d(x, a) < \delta$, because an infimum is below $\delta$ exactly when some value is below $\delta$. $\square$

The closed form needs compactness, because the infimum $d(x, s) \le \delta$ need not be attained otherwise. The names follow the pattern `<set>_add_<set>` and `<set>_sub_<set>`, with the suffix `_zero` when the ball has its center at $0$ and `singleton` when a set is a point. The same module proves that a sum of a bounded set and a bounded set is bounded and that the image of a bounded set under the norm is bounded above: `Bornology.IsBounded.bddAbove_norm` and its converse `BddAbove.isBounded_of_norm`.

The module `Mathlib.Analysis.Normed.Group.BallSphere` gives the negation on the subtypes of the ball, the closed ball and the sphere centered at $0$, with `coe_neg_ball`, `coe_neg_closedBall` and `coe_neg_sphere`. So $-x$ is again a point of the sphere, and the instances `instInvolutiveNegElemSphereOfNat` and `instContinuousNegElemSphereOfNat` say that the negation is an involution and continuous.

#### Bounded sets and the cobounded filter

A set $s$ in a normed group is bounded if and only if its norms are bounded: `isBounded_iff_forall_norm_le` states that $s$ is bounded if and only if there is $C$ with $\|x\| \le C$ for all $x \in s$. *Proof.* A bounded set lies in a ball $B(0, R)$ for some $R$, since $d(x, 0) = \|x\|$. $\square$ The lemmas `Bornology.IsBounded.exists_norm_le` and `Bornology.IsBounded.exists_pos_norm_lt` extract the constant.

The filter `Bornology.cobounded E` holds the complements of bounded sets. It is the filter of "$\|x\| \to \infty$": `comap_norm_atTop` states $\operatorname{comap} \|\cdot\| \, (\mathrm{atTop}) = \operatorname{cobounded} E$. So `tendsto_norm_atTop_iff_cobounded` says that $\|f\| \to \infty$ along a filter $l$ if and only if $f$ tends to the cobounded filter. In a proper space the cocompact filter and the cobounded filter agree, and `tendsto_norm_cocompact_atTop` follows. The lemma `Filter.Tendsto.op_zero_isBoundedUnder_le` is the rule "$0$ times bounded is $0$" for any bounded bilinear operation. The module `Mathlib.Analysis.Normed.Group.Bounded` also has `HasCompactSupport.exists_bound_of_continuous`: a continuous function with compact support has a bounded norm.

The module `Mathlib.Analysis.Normed.Group.Lemmas` holds `eventually_norm_sub_lt`, the statement that $\|x - x_0\| < \varepsilon$ for $x$ near $x_0$, and `AddSubgroup.dense_of_infDist_le`: a subgroup $H$ with $d(g, H) \le \varepsilon \|g\|$ for all $g$ and a fixed $\varepsilon < 1$ is dense. This last lemma is a form of the argument of the lemma of Riesz in Chapter 3.

#### Indicator functions and series of functions

For a set $s$ and a function $f$, the indicator $\mathbf{1}_s f$ is $f$ on $s$ and $0$ outside. The module `Mathlib.Analysis.Normed.Group.Indicator` states that $\|\mathbf{1}_s f(a)\| = \mathbf{1}_s \|f\|(a)$, by `norm_indicator_eq_indicator_norm`, and that $\|\mathbf{1}_s f(a)\| \le \|f(a)\|$, by `norm_indicator_le_norm_self`. The forms for the nonnegative norm and the extended norm are `nnNorm_indicator_eq_indicator_nnNorm` and `eNorm_indicator_eq_indicator_eNorm`.

The module `Mathlib.Analysis.Normed.Group.FunctionSeries` is the Weierstrass test. Let $f_n : \beta \to F$ with $F$ complete and $\|f_n(x)\| \le u_n$ with $\sum u_n < \infty$. Then the series $\sum f_n$ converges uniformly, by `tendstoUniformly_tsum`, and its sum is continuous when each $f_n$ is continuous, by `continuous_tsum`. *Proof of continuity.* The partial sums are continuous and converge uniformly, and a uniform limit of continuous functions is continuous. $\square$ The forms `tendstoUniformlyOn_tsum` and `continuousOn_tsum` work on a set, and `tendstoUniformlyOn_tsum_nat` uses the partial sums over `Finset.range N`.

The module `Mathlib.Analysis.Normed.Group.Tannery` has one theorem, the theorem of Tannery, `tendsto_tsum_of_dominated_convergence`. Let $f_n(k) \to g(k)$ for each $k$, and let $\|f_n(k)\| \le b_k$ for all large $n$ with $\sum_k b_k < \infty$. Then $\sum_k f_n(k) \to \sum_k g(k)$. *Proof sketch.* Fix $\varepsilon > 0$ and choose a finite set $T$ with $\sum_{k \notin T} b_k < \varepsilon$. On $T$ the sum converges term by term. Outside $T$ both tails have norm at most $\varepsilon$, since $\|g(k)\| \le b_k$ in the limit. $\square$ It is the dominated convergence theorem for the counting measure, with a direct proof.

#### Functions that vanish at infinity

A function $f : E \to F$ vanishes at infinity if $f(x) \to 0$ as $\|x\| \to \infty$. The module `Mathlib.Analysis.Normed.Group.ZeroAtInfty` gives the criterion `zero_at_infty_of_norm_le`: if for each $\varepsilon > 0$ there is $r$ with $\|f(x)\| < \varepsilon$ for $\|x\| > r$, then $f$ tends to $0$ along the cocompact filter. The converse for the bundled class is `ZeroAtInftyContinuousMapClass.norm_le`. The module `Mathlib.Analysis.Normed.Group.CocompactMap` does the same for maps that tend to infinity: `Filter.tendsto_cocompact_cocompact_of_norm` and `CocompactMapClass.norm_le`. Both criteria need a proper space, where the compact sets are the closed bounded sets.

#### Radial functions

The module `Mathlib.Analysis.Normed.Group.RadialFunction` defines `Function.IsRadial f`: the value $f(x)$ depends only on $\|x\|$. The lemma `Function.isRadial_def` states this as $\|x\| = \|y\| \Rightarrow f x = f y$. The function `Function.radialPart f : ℝ → F` is a choice of a profile, and `Function.IsRadial.radialPart_norm` states $f(x) = \operatorname{radialPart} f (\|x\|)$. The examples are the norm and its square, `Function.isRadial_norm` and `Function.isRadial_norm_sq`. A radial function is even, by `Function.IsRadial.even`, and it is invariant under each isometry that fixes $0$, by `Function.IsRadial.comp_isometry`.

#### Common errors

1. `IsCompact.add_closedBall_zero` needs a compact set. In an infinite dimensional space, for a closed set that is not compact, the sum $s + \bar B(0, \delta)$ can be strictly smaller than the closed thickening.
2. Many names exist in an old form with `nnnorm` and a new form with `nnNorm`. The old forms are deprecated aliases. Use `nnNorm_indicator_eq_indicator_nnNorm`, not the lower case form.
3. `continuous_tsum` asks for a summable bound $u$ that does not depend on $x$. A bound that depends on $x$ gives only pointwise convergence and no continuity.

### Exercises

1. (A) Prove `dist_add_add_le` from the triangle inequality for the norm.
2. (A) Use `isBounded_iff_forall_norm_le` to prove that the sum of two bounded sets in a normed group is bounded.
3. (A) Show that $x \mapsto \|x\|^2 + 1$ is a radial function and compute its radial part.
4. (B) Prove that $\sum_{n \ge 1} \sin(n x)/n^2$ is a continuous function of $x \in \mathbb{R}$ with `continuous_tsum`.
5. (B) Prove that in a proper normed group the sum of a closed set and a closed ball $\bar B(0, \delta)$ is the closed thickening of the set.
6. (C) Use the theorem of Tannery to prove that $(1 + x/n)^n \to e^x$ from the binomial expansion.

### Reference

<?reference?>
