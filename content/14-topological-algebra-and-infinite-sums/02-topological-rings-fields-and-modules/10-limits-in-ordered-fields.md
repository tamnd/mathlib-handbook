---
title: Limits in ordered fields
kind: api
modules:
  - Mathlib.Topology.Algebra.Order.Field
  - Mathlib.Topology.Algebra.Order.Floor
  - Mathlib.Topology.Algebra.Order.LiminfLimsup
  - Mathlib.Topology.Algebra.Order.Polynomial
explains:
  E2: [IsStrictOrderedRing.toIsTopologicalDivisionRing, Filter.Tendsto.atTop_mul_pos, tendsto_inv_atTop_zero, bdd_le_mul_tendsto_zero, tendsto_floor_right, ContinuousOn.comp_fract, limsup_add_le, Polynomial.tendsto_atTop_of_leadingCoeff_nonneg, Polynomial.div_tendsto_atTop_leadingCoeff_div_of_degree_eq, Polynomial.div_tendsto_atTop_zero_of_degree_lt]
  E1: auto
families: []
requires: [V13.C01, V13.C04, V13.C05, V14.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Limits in ordered fields

### Overview

A linearly ordered field with the order topology, such as $\mathbb{Q}$ or $\mathbb{R}$, is a topological field. In such a field the limits of first year calculus have a home: limits of products when one factor tends to infinity, the limit of $1/x$ at infinity and at zero, the limits of the floor function at an integer, and the limits of a polynomial or a rational function at infinity. This section describes the library of these limits.

The four modules have a common pattern. Each result is a lemma about `Filter.Tendsto` with the filters `Filter.atTop`, `Filter.atBot` and one sided neighbourhoods, and each result has a twin for the other direction.

### The library around it

#### The order topology makes a topological field

Let $\mathbb{k}$ be a field with a linear order, `IsStrictOrderedRing 𝕜` and `OrderTopology 𝕜`. The instance `IsStrictOrderedRing.toIsTopologicalDivisionRing` says that addition, multiplication and inversion away from $0$ are continuous. The instance `IsStrictOrderedRing.toContinuousInv₀` is the part about inversion, and `IsStrictOrderedRing.topologicalRing` is the part about the ring operations.

The lemma `IsTopologicalRing.of_norm` gives a way to prove that a ring is a topological ring. It takes a function $\lVert \cdot \rVert : R \to \mathbb{k}$ with values in an ordered field that is nonnegative and submultiplicative, and whose balls $\{x \mid \lVert x \rVert < \varepsilon\}$ form a basis at $0$. The proof is the estimate of the product $xy - x_0 y_0$ by norms.

#### Products and quotients with infinite limits

The rules for products in which one factor tends to infinity need the sign of the other factor.

| Lean name | Statement |
|---|---|
| `Filter.Tendsto.atTop_mul_pos` | if $f \to \infty$ and $g \to C > 0$, then $f g \to \infty$ |
| `Filter.Tendsto.atTop_mul_neg` | if $f \to \infty$ and $g \to C < 0$, then $f g \to -\infty$ |
| `Filter.Tendsto.pos_mul_atTop` | the same with the factors in the other order |
| `Filter.Tendsto.div_atTop` | if $f \to a$ and $g \to \infty$, then $f / g \to 0$ |
| `Filter.Tendsto.const_div_atTop` | $c / g \to 0$ when $g \to \infty$ |
| `Filter.Tendsto.inv_tendsto_atTop` | if $f \to \infty$, then $1/f \to 0$ |
| `Filter.Tendsto.inv_tendsto_nhdsGT_zero` | if $f \to 0$ from the right, then $1/f \to \infty$ |
| `bdd_le_mul_tendsto_zero` | if $b \le f \le B$ and $g \to 0$, then $f g \to 0$ |

The proof of `Filter.Tendsto.atTop_mul_pos` is short: eventually $g > C/2$, so $f g \ge (C/2) f$, and $(C/2) f \to \infty$. The lemma `bdd_le_mul_tendsto_zero` is the rule that a bounded function times a function that tends to $0$ tends to $0$; `bdd_le_mul_tendsto_zero'` has the bound in the form $\lvert f \rvert \le C$.

The ratio of two functions also controls their limits. If $f/g \to 1$, then $f \to \infty$ if and only if $g \to \infty$ (`Filter.tendsto_atTop_iff_of_tendsto_div_nhds_one`), and the same holds for $-\infty$ and for finite limits (`Filter.tendsto_atBot_iff_of_tendsto_div_nhds_one` and `Filter.tendsto_nhds_iff_of_tendsto_div_nhds_one`).

#### Inversion near zero and near infinity

Inversion exchanges the neighbourhoods of $0$ and the neighbourhoods of infinity. The lemma `tendsto_inv_atTop_zero` says that $1/x \to 0$ as $x \to \infty$, and `tendsto_inv_atTop_nhdsGT_zero` adds that the values are positive. In the other direction, `tendsto_inv_nhdsGT_zero` says that $1/x \to \infty$ as $x \to 0^{+}$, and `tendsto_inv_nhdsLT_zero` says that $1/x \to -\infty$ as $x \to 0^{-}$. The filter equations `inv_atTop₀` and `inv_nhdsGT_zero` state the same facts as equalities of filters.

Powers have the same pattern. The lemma `tendsto_pow_neg_atTop` says that $x^{-n} \to 0$ for $n \ne 0$, and `tendsto_zpow_atTop_zero` is the form for negative integer powers. The lemma `tendsto_const_mul_pow_nhds_iff` says that $c x^n$ has a finite limit $d$ at infinity, for $c \ne 0$, if and only if $n = 0$ and $c = d$.

#### Floor, ceiling and fractional part

Let $\alpha$ be an ordered ring with a floor function and the order topology. The floor function is constant on each interval $[n, n + 1)$, so it is continuous there (`continuousOn_floor`), and it jumps at each integer.

1. `tendsto_floor_right n` says that $\lfloor x \rfloor \to n$ as $x \to n^{+}$.
2. `tendsto_floor_left n` says that $\lfloor x \rfloor \to n - 1$ as $x \to n^{-}$.
3. `tendsto_ceil_left n` and `tendsto_ceil_right n` are the forms for the ceiling, with limits $n$ and $n + 1$.
4. `tendsto_fract_right n` says that the fractional part tends to $0$ from the right at $n$, and `tendsto_fract_left n` says that it tends to $1$ from the left.
5. `tendsto_floor_atTop` and `tendsto_floor_atBot` say that the floor tends to $\pm\infty$ with $x$.

The forms with *pure*, such as `tendsto_floor_right_pure`, are stronger: near $n$ on the right, $\lfloor x \rfloor$ is exactly $n$, so the limit holds for the filter of the single point $n$. The lemma `ContinuousOn.comp_fract` is the main tool for periodic functions. If $f$ is continuous on $[0, 1]$ and $f(0) = f(1)$, then $x \mapsto f(\operatorname{fract} x)$ is continuous on all of $\mathbb{R}$. The lemma `FloorSemiring.tendsto_pow_div_factorial_atTop` says that $c^n / n! \to 0$ for each $c$.

#### Limit superior and limit inferior of sums and products

In a conditionally complete linearly ordered field, the limit superior is subadditive and the limit inferior is superadditive, under boundedness conditions.

| Lean name | Statement |
|---|---|
| `limsup_add_le` | $\limsup (u + v) \le \limsup u + \limsup v$ |
| `le_liminf_add` | $\liminf u + \liminf v \le \liminf (u + v)$ |
| `le_limsup_add` | $\limsup u + \liminf v \le \limsup (u + v)$ |
| `liminf_add_le` | $\liminf (u + v) \le \limsup u + \liminf v$ |
| `limsup_mul_le` | for $v \ge 0$, $\limsup (u v) \le \limsup u \cdot \limsup v$ |
| `limsup_const_add` | $\limsup (c + u) = c + \limsup u$ |
| `limsup_const_sub` | $\limsup (c - u) = c - \liminf u$ |

The boundedness hypotheses of the first lemmas have a default proof by the tactic *isBoundedDefault*, which closes them in a complete lattice. In $\mathbb{R}$ they are real hypotheses: a sequence that is not bounded above has the value $0$ as its limit superior in Mathlib, and the inequalities can fail.

#### Polynomials at infinity

Let $P$ be a polynomial over an ordered field. The behaviour of $P(x)$ as $x \to \infty$ depends on the degree and the leading coefficient.

| Lean name | Statement |
|---|---|
| `Polynomial.tendsto_atTop_of_leadingCoeff_nonneg` | if $\deg P > 0$ and the leading coefficient is $\ge 0$, then $P(x) \to \infty$ |
| `Polynomial.tendsto_atTop_iff_leadingCoeff_nonneg` | the converse also holds |
| `Polynomial.tendsto_nhds_iff` | $P(x) \to c$ if and only if $P$ is the constant $c$ |
| `Polynomial.abs_tendsto_atTop` | if $\deg P > 0$, then $\lvert P(x) \rvert \to \infty$ |
| `Polynomial.isBoundedUnder_abs_atTop_iff` | $\lvert P \rvert$ is bounded at infinity if and only if $\deg P \le 0$ |
| `Polynomial.tendsTo_atTop_div_nhds_one` | $P(x) / (a x^n) \to 1$, with $a$ the leading coefficient and $n$ the degree |

For a quotient $P/Q$, the degrees decide the limit. If $\deg P < \deg Q$, then $P(x)/Q(x) \to 0$ (`Polynomial.div_tendsto_atTop_zero_of_degree_lt`). If the degrees are equal, then $P(x)/Q(x)$ tends to the quotient of the leading coefficients (`Polynomial.div_tendsto_atTop_leadingCoeff_div_of_degree_eq`). If $\deg P > \deg Q$, then the quotient tends to $\pm\infty$, with the sign of the quotient of the leading coefficients (`Polynomial.div_tendsto_atTop_of_degree_gt` and `Polynomial.div_tendsto_atBot_of_degree_gt`). The proofs divide $P$ and $Q$ by their leading terms and use `Polynomial.tendsTo_atTop_div_nhds_one`.

#### Common errors

1. `Filter.Tendsto.atTop_mul_pos` needs a strictly positive limit $C$. For $C = 0$ the product can have each behaviour, as $x \cdot (1/x)$ and $x^2 \cdot (1/x)$ show.
2. Some names in `Mathlib.Topology.Algebra.Order.Polynomial` spell *tendsTo* with a capital T, such as `Polynomial.tendsTo_atTop_div_nhds_one`. A search for *tendsto* does not find them.
3. `tendsto_floor_left n` has the limit $n - 1$, not $n$. The floor function is right continuous, not left continuous.

### Exercises

1. (A) Prove that $x^2 - 3x + 1 \to \infty$ as $x \to \infty$ with `Polynomial.tendsto_atTop_of_leadingCoeff_nonneg`.
2. (A) Use `Polynomial.div_tendsto_atTop_leadingCoeff_div_of_degree_eq` to compute the limit of $(2x^2 + 1)/(3x^2 - x)$ at infinity.
3. (B) Prove that $\sin(x)/x \to 0$ as $x \to \infty$ with `bdd_le_mul_tendsto_zero` and `tendsto_inv_atTop_zero`.
4. (B) Show that $x \mapsto \sin(2 \pi \operatorname{fract} x)$ is continuous on $\mathbb{R}$ with `ContinuousOn.comp_fract`.
5. (C) Give bounded sequences $u$ and $v$ with $\limsup (u + v) < \limsup u + \limsup v$, and explain how `limsup_add_le` applies.

### Reference

<?reference?>
