---
title: Change of variables and Lebesgue differentiation
kind: theory
modules:
  - Mathlib.MeasureTheory.Function.Jacobian
  - Mathlib.MeasureTheory.Function.JacobianOneDim
  - Mathlib.MeasureTheory.Covering.Vitali
  - Mathlib.MeasureTheory.Covering.VitaliFamily
  - Mathlib.MeasureTheory.Covering.Differentiation
  - Mathlib.MeasureTheory.Covering.Besicovitch
  - Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
  - Mathlib.MeasureTheory.Covering.DensityTheorem
  - Mathlib.MeasureTheory.Covering.LiminfLimsup
  - Mathlib.MeasureTheory.Covering.OneDim
  - Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
explains:
  E3: [MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul, MeasureTheory.lintegral_abs_det_fderiv_eq_addHaar_image, Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall, VitaliFamily, VitaliFamily.ae_tendsto_average, LocallyIntegrable.ae_hasDerivAt_integral]
  E2: [MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero, MeasureTheory.addHaar_image_le_mul_of_det_lt, MeasureTheory.integral_target_eq_integral_abs_det_fderiv_smul, MeasureTheory.integral_image_eq_integral_abs_deriv_smul, VitaliFamily.filterAt, Vitali.vitaliFamily, Besicovitch.vitaliFamily, Besicovitch.ae_tendsto_rnDeriv, VitaliFamily.ae_tendsto_rnDeriv, VitaliFamily.ae_tendsto_lintegral_eNorm_sub_div_of_integrable, VitaliFamily.ae_tendsto_measure_inter_div_of_measurableSet, IntervalIntegrable.ae_hasDerivAt_integral]
  E1: auto
families: []
requires: [V15, V18.C03, V18.C04, V18.C05, V18.C06, V18.C07]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Change of variables and Lebesgue differentiation

### Overview

This section works in $\mathbb{R}^n$ with Lebesgue measure $\lambda$. It states the change of variables formula, with the absolute value of the Jacobian determinant, and gives the steps of its proof. It then proves the covering lemma of Vitali, the maximal inequality and the Lebesgue differentiation theorem. In dimension one, the theorem gives the first form of the fundamental theorem of Section 1 almost everywhere, without continuity.

### Definitions

**Definition (Jacobian determinant).** Let $s \subseteq \mathbb{R}^n$ and let $f : s \to \mathbb{R}^n$ have the derivative $f'(x)$, a linear map, at each $x \in s$ within $s$. The Jacobian determinant of $f$ at $x$ is $\det f'(x)$.

**Definition (Average).** For a measurable set $B$ with $0 < \lambda(B) < \infty$ and $f$ integrable on $B$, the average of $f$ on $B$ is $\frac{1}{\lambda(B)} \int_B f \, d\lambda$, written $\operatorname{avg}_B f$.

**Definition (Lebesgue point).** A point $x$ is a Lebesgue point of $f$ if $\operatorname{avg}_{B(x, r)} |f - f(x)| \to 0$ as $r \to 0^+$, where $B(x, r)$ is the closed ball.

**Definition (Maximal function).** For $f$ integrable on $\mathbb{R}^n$, $Mf(x) = \sup_{r > 0} \operatorname{avg}_{B(x, r)} |f|$.

### Theorems and proofs

**Theorem 1 (Change of variables).** Let $s \subseteq \mathbb{R}^n$ be measurable, and let $f$ be injective on $s$ with the derivative $f'(x)$ within $s$ at each $x \in s$. Then for each measurable $A \subseteq s$,
$$\lambda(f(A)) = \int_A |\det f'(x)| \, dx,$$
and for each $g$ with values in a complete normed space,
$$\int_{f(s)} g \, d\lambda = \int_s |\det f'(x)| \, g(f(x)) \, dx.$$

*Proof plan.* The proof has four steps.

1. For a linear map $T$, $\lambda(T(A)) = |\det T| \, \lambda(A)$. This is the scaling law of Chapter 3, Section 2.
2. Let $T$ be linear and $m > |\det T|$. There is $\delta > 0$ such that $\lambda(f(t)) \le m \, \lambda(t)$ for each $t$ on which $\|f(y) - f(z) - T(y - z)\| \le \delta \|y - z\|$. A lower bound holds in the same way when $T$ is invertible.
3. Cut $s$ into countably many disjoint measurable pieces $t_k$. On each $t_k$, $f$ is close to a linear map $T_k$ in the sense of step 2, and $|\det f'|$ is close to $|\det T_k|$. Sum the bounds of step 2 over $k$ and let the error go to $0$. This gives the formula for $\lambda(f(A))$. The points where $\det f'(x) = 0$ need a separate argument: their image is a null set, a result of the type of the lemma of Sard.
4. The formula for sets is the formula for $g = \mathbf{1}_{f(A)}$. Pass to simple functions by linearity, to nonnegative measurable functions by monotone convergence (Chapter 4) and to integrable functions by the decomposition $g = g^+ - g^-$ (Chapter 5). $\square$

**Corollary 2 (Dimension one).** Let $s \subseteq \mathbb{R}$ be measurable, and let $f$ be injective on $s$ with derivative $f'$ within $s$. Then $\int_{f(s)} g = \int_s |f'(x)| \, g(f(x)) \, dx$.

*Proof.* Multiplication by $c$ has determinant $c$. Apply Theorem 1. $\square$

**Lemma 3 (Vitali covering lemma, finite form).** Let $B_1, \dots, B_N$ be closed balls in $\mathbb{R}^n$. There are disjoint balls $B_{i_1}, \dots, B_{i_k}$ among them such that each $B_j$ is contained in some $3B_{i_l}$, the ball with the same center and three times the radius.

*Proof.* Choose $B_{i_1}$ with the largest radius and remove all balls that meet it. Repeat with the balls that remain until none remains. The chosen balls are disjoint. Let $B_j$ be a ball. It was removed at some step $l$ because it meets $B_{i_l}$, and the radius of $B_j$ is at most that of $B_{i_l}$, because $B_{i_l}$ was the largest ball then. If $y \in B_j \cap B_{i_l}$ and $x$ is the center of $B_{i_l}$ with radius $r$, then each point of $B_j$ has a distance at most $2r$ from $y$, so at most $3r$ from $x$. $\square$

Mathlib proves the general form for an arbitrary family of balls in a metric space with bounded radii, with each factor $\tau > 3$.

**Theorem 4 (Maximal inequality).** For $f$ integrable on $\mathbb{R}^n$ and $t > 0$,
$$\lambda(\{Mf > t\}) \le \frac{3^n}{t} \int |f| \, d\lambda.$$

*Proof.* Let $K$ be a compact subset of $\{Mf > t\}$. Each $x \in K$ is the center of a ball $B_x$ with $\int_{B_x} |f| > t \, \lambda(B_x)$, and finitely many of them cover $K$. Lemma 3 gives disjoint balls $B_1, \dots, B_k$ among them with $K \subseteq \bigcup 3B_i$. Then
$$\lambda(K) \le \sum_i 3^n \lambda(B_i) \le \frac{3^n}{t} \sum_i \int_{B_i} |f| \le \frac{3^n}{t} \int |f|.$$
The set $\{Mf > t\}$ is open, so measurable. Inner regularity (Chapter 3, Section 1) gives the claim. $\square$

**Theorem 5 (Lebesgue differentiation theorem).** Let $f$ be locally integrable on $\mathbb{R}^n$. Then for almost every $x$,
$$\operatorname{avg}_{B(x, r)} f \to f(x) \quad (r \to 0^+).$$

*Proof.* The property is local, so assume that $f$ is integrable. Let $\Omega f(x) = \limsup_{r \to 0} |\operatorname{avg}_{B(x, r)} f - f(x)|$. Let $\eta > 0$. By the density of continuous functions with compact support in $L^1$ (Chapter 7, Section 2), there is such a $g$ with $\int |f - g| < \eta$. For continuous $g$, $\Omega g = 0$ everywhere. With $h = f - g$, $\Omega f \le \Omega h \le Mh + |h|$. For $t > 0$, Theorem 4 and the inequality of Markov give
$$\lambda(\{\Omega f > 2t\}) \le \lambda(\{Mh > t\}) + \lambda(\{|h| > t\}) \le \frac{3^n + 1}{t} \eta.$$
This holds for each $\eta$, so $\{\Omega f > 2t\}$ is null for each $t > 0$. The union over $t = 1/k$ is null. $\square$

The same argument, applied to $|f - q|$ for each rational $q$, shows that almost every point is a Lebesgue point of $f$.

**Corollary 6 (Differentiation of the integral).** Let $f : \mathbb{R} \to \mathbb{R}$ be locally integrable. For almost every $x$ and every $c$, the function $F(u) = \int_c^u f$ has the derivative $f(x)$ at $x$.

*Proof.* Let $x$ be a Lebesgue point of $f$. For $h \ne 0$, $\frac{F(x + h) - F(x)}{h} - f(x)$ is the average of $f - f(x)$ on the interval between $x$ and $x + h$. That interval is contained in $B(x, |h|)$ and has half its measure. Thus the norm of the difference is at most $2 \operatorname{avg}_{B(x, |h|)} |f - f(x)|$, which tends to $0$. $\square$

### Examples

**Example (The area of an ellipse).** Let $D$ be the closed unit disc in $\mathbb{R}^2$. By Tonelli (Chapter 6) and the computed integral $\int_{-1}^1 \sqrt{1 - x^2} \, dx = \frac{\pi}{2}$ of `integral_sqrt_one_sub_sq`, $\lambda(D) = \int_{-1}^{1} 2\sqrt{1 - x^2} \, dx = \pi$. Let $a, b > 0$ and $T(x, y) = (ax, by)$. The ellipse $E = T(D)$ has $\lambda(E) = |\det T| \, \lambda(D) = \pi a b$, by Theorem 1 with $f = T$ and $f' = T$ constant.

**Counterexample (Injectivity is needed).** Let $f(x) = x^2$ on $s = [-1, 1]$, with $f'(x) = 2x$, and let $g = 1$. Then $f(s) = [0, 1]$ and $\int_{f(s)} g = 1$. The right side of Corollary 2 is $\int_{-1}^1 |2x| \, dx = 2$. The map covers $[0, 1]$ twice.

### The library around it

::: mathlib
`MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul` · `Mathlib.MeasureTheory.Function.Jacobian`

Theorem 1 for an additive Haar measure on a finite dimensional real space. The set version is `MeasureTheory.lintegral_abs_det_fderiv_eq_addHaar_image`.

<?decl MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul?>
:::

Step 2 is `MeasureTheory.addHaar_image_le_mul_of_det_lt`, stated with `ApproximatesLinearOn`, and the image of the points with $\det f' = 0$ is null by `MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero`. The form for a partial homeomorphism is `MeasureTheory.integral_target_eq_integral_abs_det_fderiv_smul`, and Corollary 2 is `MeasureTheory.integral_image_eq_integral_abs_deriv_smul`.

::: mathlib
`integral_comp_polarCoord_symm` · `Mathlib.Analysis.SpecialFunctions.PolarCoord`

Polar coordinates in the plane, a case of Theorem 1 with Jacobian determinant $r$. Volume 15 explains `polarCoord`.

<?decl integral_comp_polarCoord_symm?>
:::

Mathlib states differentiation for a `VitaliFamily μ`. Such a family gives to each point $x$ a set of closed sets around $x$, with small sets in it, and with a covering property: from each fine cover of a set, a disjoint subfamily covers almost all of it. The filter `VitaliFamily.filterAt` lets the set shrink to $x$. The family `Vitali.vitaliFamily` of balls exists for a measure with a doubling condition, from `Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall`. The family `Besicovitch.vitaliFamily` exists for all locally finite measures on a finite dimensional space, from the covering theorem of Besicovitch.

::: mathlib
`VitaliFamily.ae_tendsto_average` · `Mathlib.MeasureTheory.Covering.Differentiation`

Theorem 5 for a Vitali family and a locally integrable function.

<?decl VitaliFamily.ae_tendsto_average?>
:::

The theorem in this form follows from `VitaliFamily.ae_tendsto_rnDeriv`: for a second measure $\rho$, the ratio $\rho(a)/\mu(a)$ tends to the derivative of Radon and Nikodym of Chapter 4, Section 3. With balls this is `Besicovitch.ae_tendsto_rnDeriv`. Lebesgue points are `VitaliFamily.ae_tendsto_lintegral_eNorm_sub_div_of_integrable`, and density points of a measurable set are `VitaliFamily.ae_tendsto_measure_inter_div_of_measurableSet`. Corollary 6 is `LocallyIntegrable.ae_hasDerivAt_integral`, with the version `IntervalIntegrable.ae_hasDerivAt_integral` on an interval. The index of this edition has no declaration for the maximal function of Hardy and Littlewood or for Theorem 4. The proof in Mathlib uses the covering property of the family in its place.

Four further files supply the families. The file `Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace` proves the covering theorem of Besicovitch in every finite dimensional real normed space: the instance `Besicovitch.instHasBesicovitchCovering` holds there. The key bound is `Besicovitch.card_le_multiplicity`: a family of points in the ball of radius $2$ with pairwise distances at least $1$ has at most `Besicovitch.multiplicity E` elements. The file `Mathlib.MeasureTheory.Covering.DensityTheorem` treats a uniformly locally doubling measure, which gives balls of radius $2r$ at most a fixed multiple of the measure of balls of radius $r$. For such a measure, `IsUnifLocDoublingMeasure.vitaliFamily` is a Vitali family of closed balls. The density theorem of Lebesgue in this setting is `IsUnifLocDoublingMeasure.ae_tendsto_measure_inter_div`, and the convergence of averages is `IsUnifLocDoublingMeasure.ae_tendsto_average`. The file `Mathlib.MeasureTheory.Covering.LiminfLimsup` applies the density theorem to limits superior of thickenings: `blimsup_thickening_mul_ae_eq` says that multiplying the radii $r_i \to 0$ by a constant $M > 0$ changes the set only on a null set. This is a step towards the theorem of Gallagher on Diophantine approximation. The file `Mathlib.MeasureTheory.Covering.OneDim` shows that the intervals $[x, y]$ with $y \downarrow x$ tend to $x$ along the Vitali family of the line, `Real.tendsto_Icc_vitaliFamily_right`, and `Real.tendsto_Icc_vitaliFamily_left` treats the intervals on the left.

Common errors of a learner:

- Theorem 1 uses $|\det f'|$, not $\det f'$. The sign belongs to oriented integrals, as in Section 1 when $b < a$.
- `integral_image_eq_integral_abs_det_fderiv_smul` needs `InjOn f s`. Without it the formula is false, as the second example shows.

### Exercises

1. (A) Compute the measure of the image of $[0, 1]^2$ under $(x, y) \mapsto (2x + y, x - 3y)$.
2. (A) Show that $\int_{(0, \infty)} g(e^t) e^t \, dt = \int_{(1, \infty)} g$ for $g \ge 0$ measurable, with Corollary 2.
3. (A) Let $A \subseteq \mathbb{R}^n$ be measurable and $c > 0$. Show $\lambda(cA) = c^n \lambda(A)$ with Theorem 1.
4. (B) Let $A \subseteq \mathbb{R}$ be measurable. Show that for almost every $x \in A$, $\lambda(A \cap [x - r, x + r]) / (2r) \to 1$. *Hint:* apply Theorem 5 to $\mathbf{1}_A$.
5. (B) Let $f = \mathbf{1}_{[0, 1]}$ on $\mathbb{R}$. Show that $Mf$ is not integrable, although $f$ is. *Hint:* for $|x| > 1$, use the ball $B(x, |x| + 1)$ to get $Mf(x) \ge \frac{1}{2(|x| + 1)}$.
6. (B) Use Theorem 1 with polar coordinates to show $\int_{\mathbb{R}^2} e^{-(x^2 + y^2)} \, dx \, dy = \pi$. *Hint:* the Jacobian determinant is $r$, and the set $\{r = 0\}$ is null.
7. (C) Prove that if $f$ is locally integrable on $\mathbb{R}$ and $\int_a^b f = 0$ for all $a < b$, then $f = 0$ almost everywhere. *Hint:* use Corollary 6.

### Notes and history

The differentiation theorem carries the name of Lebesgue, the covering lemma that of Vitali, and the maximal function those of Hardy and Littlewood.

In Mathlib the change of variables formula, Vitali families, the Vitali and Besicovitch coverings and the differentiation theorem are by Sébastien Gouëzel. The density theorem for doubling measures in `Mathlib.MeasureTheory.Covering.DensityTheorem` is by Oliver Nash, and the derivative of the integral almost everywhere in `Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm` is by Yizheng Zhu.

### Reference

<?reference?>
