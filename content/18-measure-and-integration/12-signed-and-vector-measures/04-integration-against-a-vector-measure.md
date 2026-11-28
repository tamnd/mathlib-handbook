---
title: Integration against a vector measure
kind: api
modules:
  - Mathlib.MeasureTheory.VectorMeasure.Integral
  - Mathlib.MeasureTheory.VectorMeasure.SetIntegral
  - Mathlib.MeasureTheory.VectorMeasure.WithDensityVec
  - Mathlib.MeasureTheory.VectorMeasure.IntegrationByParts
  - Mathlib.MeasureTheory.VectorMeasure.Prod
explains:
  E2: [MeasureTheory.VectorMeasure.integral, MeasureTheory.VectorMeasure.Integrable, MeasureTheory.VectorMeasure.transpose, MeasureTheory.VectorMeasure.integral_indicator_const, MeasureTheory.VectorMeasure.norm_integral_le_lintegral_norm, MeasureTheory.VectorMeasure.tendsto_integral_of_dominated_convergence, MeasureTheory.VectorMeasure.withDensity, BoundedVariationOn.setIntegral_Icc_rightLim_vectorMeasure_eq_sub, MeasureTheory.VectorMeasure.prod, MeasureTheory.VectorMeasure.integral_prod]
  E1: auto
families: []
requires: [V16, V18.C02, V18.C04, V18.C05, V18.C06]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Integration against a vector measure

### Overview

A function $f$ with values in $E$ and a vector measure $\mu$ with values in $F$ give two vectors at each point, $f(x) \in E$ and the mass $\mu(dx) \in F$. To combine them into one value, the integral needs a bilinear map $B : E \times F \to G$. Then

$$\int f \, d[B; \mu] = \int B(f(x), \mu(dx)) \in G.$$

On simple functions this is the finite sum $\sum_k B(e_k, \mu(A_k))$. For $E = \mathbb{R}$ and $B$ the scalar multiplication, it is the integral of a real function against a vector measure. For $F = \mathbb{R}$, with $\mu$ a signed measure and $B$ the scalar multiplication in the other order, it is the integral of a vector function against a signed measure. For a finite measure $\mu$, it is the Bochner integral of Chapter 5.

The integral uses the variation $|\mu|$ of Section 3 as the reference measure: $f$ is integrable when $\int \|f\| \, d|\mu| < \infty$. This section gives the definition, the convergence theorems, vector measures with a density, integration by parts for functions of bounded variation, and the product of two vector measures with its Fubini theorem.

### The library around it

#### The definition

The integral `MeasureTheory.VectorMeasure.integral μ f B` takes the vector measure $\mu$, the function $f$ and the continuous bilinear map `B : E →L[ℝ] F →L[ℝ] G`. Its notation is `∫ᵛ x, f x ∂[B; μ]`, and `∫ᵛ x in s, f x ∂[B; μ]` is the integral on a set. Two shorter notations fix $B$ to a scalar multiplication: `∂•μ` for a real function against a vector measure and `∂<•μ` for a vector function against a signed measure.

The predicate `MeasureTheory.VectorMeasure.Integrable μ f` is integrability with respect to the variation, `MeasureTheory.Integrable f μ.variation`. The definition is a case of the extension of Chapter 5, Section 7. The set function $A \mapsto (e \mapsto B(e, \mu(A)))$ is the vector measure `MeasureTheory.VectorMeasure.transpose μ B`, with values in the continuous linear maps $E \to G$. Its norm is dominated by $\|B\| \, |\mu|$, and `MeasureTheory.VectorMeasure.integral_eq_setToFun` shows that the integral is `MeasureTheory.setToFun` for this set function and the measure $|\mu|$. As for the Bochner integral, the value is $0$ for a function that is not integrable, `MeasureTheory.VectorMeasure.integral_undef`, and when $G$ is not complete.

#### Values and rules

On an indicator function, `MeasureTheory.VectorMeasure.integral_indicator_const` gives

$$\int \mathbf{1}_A \, e \, d[B; \mu] = B(e, \mu(A))$$

for a measurable $A$ of finite variation. Against a point mass, the integral is $B(f(a), v)$, `MeasureTheory.VectorMeasure.integral_dirac`. The integral is linear in $f$, in $\mu$ and in $B$, with the rules `MeasureTheory.VectorMeasure.integral_add`, `MeasureTheory.VectorMeasure.integral_add_vectorMeasure` and `MeasureTheory.VectorMeasure.integral_add_cbm`. For a finite measure, the integral against `μ.toSignedMeasure` is the Bochner integral, `MeasureTheory.VectorMeasure.integral_toSignedMeasure`.

The basic estimate is `MeasureTheory.VectorMeasure.norm_integral_le_lintegral_norm`:

$$\Big\|\int f \, d[B; \mu]\Big\| \le \|B\| \int \|f\| \, d|\mu|.$$

The dominated convergence theorem holds with the variation as the reference measure, `MeasureTheory.VectorMeasure.tendsto_integral_of_dominated_convergence`: if $f_n \to f$ almost everywhere for $|\mu|$, and $\|f_n\| \le g$ with $g$ integrable for $|\mu|$, then the integrals converge. The continuity of integrals with a parameter is `MeasureTheory.VectorMeasure.continuous_of_dominated`.

The file `Mathlib.MeasureTheory.VectorMeasure.SetIntegral` has the rules for integrals on sets, with the same names as for the Bochner integral: `MeasureTheory.VectorMeasure.setIntegral_union`, `MeasureTheory.VectorMeasure.setIntegral_compl` and the countable additivity `MeasureTheory.VectorMeasure.hasSum_setIntegral_iUnion`. A continuous linear map commutes with the integral, `MeasureTheory.VectorMeasure.continuousLinearMap_apply_integral`.

#### Densities with respect to a vector measure

The set function $A \mapsto \int_A f \, d[B; \mu]$ is a new vector measure, `MeasureTheory.VectorMeasure.withDensity μ f B`, with values given by `MeasureTheory.VectorMeasure.withDensity_apply`. This generalizes `MeasureTheory.Measure.withDensityᵥ` of Section 1, where $\mu$ is a measure. If $B$ preserves norms, $\|B(x, y)\| = \|x\| \|y\|$, the variation of the new measure is the measure with density $\|f\|_e$ with respect to the variation of `MeasureTheory.VectorMeasure.transpose μ B`, `MeasureTheory.VectorMeasure.variation_withDensity`. For the multiplication of real or complex numbers, this variation is $|\mu|$ itself. For a measure $\mu$, the variation of `μ.withDensityᵥ f` is the measure with density $\|f\|$, `MeasureTheory.Measure.variation_withDensityᵥ`.

#### Integration by parts

For two functions $f$ and $g$ of bounded variation on $\mathbb{R}$, Section 3 gives the vector measures $df$ and $dg$. The file `Mathlib.MeasureTheory.VectorMeasure.IntegrationByParts` proves the formula for Stieltjes integrals with left and right limits. On a closed interval, `BoundedVariationOn.setIntegral_Icc_rightLim_vectorMeasure_eq_sub` gives

$$\int_{[a, b]} B(f(x^+), dg) = B(f(b^+), g(b^+)) - B(f(a^-), g(a^-)) - \int_{[a, b]} B(df, g(x^-)).$$

The limits matter at the common jumps of $f$ and $g$: one integral uses right limits and the other left limits. The same formula holds for the other kinds of intervals, for example `BoundedVariationOn.setIntegral_Ioc_rightLim_vectorMeasure_eq_sub`. The proof shows that the measure of the product $B(f, g)$ is $B(df, g^+) + B(f^-, dg)$, `BoundedVariationOn.vectorMeasure_bilinear_comp_eq`, and compares the two measures on intervals, `MeasureTheory.VectorMeasure.ext_of_Icc`.

#### Products and the theorem of Fubini

The product of two vector measures needs a bilinear map $A : E \times F \to H$ to combine the values. The product `MeasureTheory.VectorMeasure.prod μ ν A` has the value $A(\mu(S), \nu(T))$ on a rectangle $S \times T$, `MeasureTheory.VectorMeasure.prod_apply`. It exists under the class `MeasureTheory.VectorMeasure.HasProd`, which holds when $H$ is complete and one of the two variations is finite. Without this class the product is $0$.

The theorem of Fubini is `MeasureTheory.VectorMeasure.integral_prod`. For $f$ integrable for $|\mu| \otimes |\nu|$, with finite variations and four bilinear maps that satisfy a compatibility condition,

$$\int f \, d[D; \mu \otimes_A \nu] = \int \Big( \int f(x, y) \, d[B; \nu](y) \Big) d[C; \mu](x).$$

The condition $D(x, A(y, z)) = C(B(x, z), y)$ says that both sides combine the three vectors in the same way. The exchange of the two iterated integrals is `MeasureTheory.VectorMeasure.integral_integral_swap`. The bound $|\mu \otimes \nu| \le |\mu| \otimes |\nu|$ up to the norm of $A$ is `MeasureTheory.VectorMeasure.variation_prod_le`.

#### Common errors

1. Forgetting the bilinear map. The integral `MeasureTheory.VectorMeasure.integral` has the argument $B$, and the notation `∂[B; μ]` shows it. For scalar functions, use the short notations with a fixed scalar multiplication.
2. Taking integrability with respect to a measure other than the variation. The hypotheses of the convergence theorems are almost everywhere for `μ.variation`, and `MeasureTheory.VectorMeasure.Integrable μ f` means `MeasureTheory.Integrable f μ.variation`.
3. Using the integration by parts formula without the limits. When $f$ and $g$ jump at the same point, $\int f \, dg + \int g \, df$ is not $fg(b) - fg(a)$ with the values of $f$ and $g$; the formula needs $f(x^+)$ in one integral and $g(x^-)$ in the other.

### Exercises

1. (A) Compute $\int x \, d[B; \mu]$ for $\mu = \delta_1 - \delta_2$ on $\mathbb{R}$ and $B$ the multiplication of real numbers, with `MeasureTheory.VectorMeasure.integral_dirac`.
2. (A) For a finite measure $\mu$ and an integrable $f$, check `MeasureTheory.VectorMeasure.norm_integral_le_lintegral_norm` against the usual bound for the Bochner integral.
3. (B) Let $g$ be the indicator of $[0, \infty)$ and $f = g$. Compute both sides of `BoundedVariationOn.setIntegral_Icc_rightLim_vectorMeasure_eq_sub` on $[-1, 1]$ with $B$ the multiplication.
4. (B) Show that `MeasureTheory.VectorMeasure.withDensity` applied to a signed measure $s$ and the function $\mathbf{1}_P$, with $P$ a Hahn set, gives the positive part $s^+$ as a signed measure.
5. (B) For signed measures $\mu$ on $X$ and $\nu$ on $Y$, compute `MeasureTheory.VectorMeasure.prod μ ν A` on a rectangle with $A$ the multiplication, and show that its variation is at most $|\mu| \otimes |\nu|$.
6. (C) Explain why the product of two vector measures with infinite variation may fail to exist, and which hypothesis of `MeasureTheory.VectorMeasure.HasProd` excludes this.

### Reference

<?reference?>
