---
title: Powers of nonnegative, extended and complex numbers
kind: api
modules:
  - Mathlib.Analysis.SpecialFunctions.Pow.NNReal
  - Mathlib.Analysis.SpecialFunctions.Pow.Complex
  - Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
  - Mathlib.Analysis.SpecialFunctions.Sqrt
  - Mathlib.Analysis.MeanInequalitiesPow
explains:
  E2: [NNReal.rpow_add, ENNReal.mul_rpow_eq_ite, Complex.mul_cpow, Nat.nthRoot_eq_of_le_of_lt, Real.hasDerivAt_sqrt, NNReal.add_rpow_le_rpow_add, Real.rpow_arith_mean_le_arith_mean_rpow]
  E1: auto
families: []
requires: [V02, V13, V15.C03]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Powers of nonnegative, extended and complex numbers

### Overview

The previous section defined the real power $x^y$ for real $x$ and $y$. Its laws need hypotheses such as $0 \le x$, because a negative base has no good real power. Many proofs in analysis only use nonnegative numbers: norms, measures, the terms of a series with positive terms. For these numbers Mathlib has the types `NNReal` (written $\mathbb{R}_{\ge 0}$) and `ENNReal` (written $[0, \infty]$), and each type has its own power function with an exponent in $\mathbb{R}$. On `NNReal` the hypothesis $0 \le x$ is in the type, so the lemmas are shorter. On `ENNReal` the value $\infty$ is allowed, and the lemmas must say what $\infty^y$ and $0^y$ are for a negative $y$.

This section also treats the complex power $z^w = \exp(w \log z)$, the integer root `Nat.nthRoot`, the derivative of the square root, and the inequalities between power means. The last group gives the inequalities $a^p + b^p \le (a + b)^p$ for $p \ge 1$ and $(a + b)^p \le a^p + b^p$ for $0 \le p \le 1$, which are the first step to the triangle inequality in $L^p$. The section uses the real powers, the logarithm and the inequality of arithmetic and geometric means of the previous sections, and the inverse function rule for derivatives of Chapter 3.

### The library around it

#### Powers in `NNReal`

The module `Mathlib.Analysis.SpecialFunctions.Pow.NNReal` defines `NNReal.rpow x y` as the real power $(x : \mathbb{R})^y$, which is nonnegative, seen as an element of `NNReal`. The instance `NNReal.instPowReal` gives the notation `x ^ y`, and `NNReal.rpow_eq_pow` rewrites `x.rpow y` to it. The simp normal form is `x ^ y`. The bridge to the real numbers is `NNReal.coe_rpow`: $\uparrow(x^y) = (\uparrow x)^y$. Most proofs in the module cast to $\mathbb{R}$ with this lemma and apply the lemma of the same name in the namespace `Real`.

The special values follow the real power: `NNReal.rpow_zero` gives $x^0 = 1$, `NNReal.zero_rpow` gives $0^y = 0$ for $y \ne 0$, and `NNReal.zero_rpow_def` states $0^y = 1$ if $y = 0$ and $0^y = 0$ otherwise. The casts `NNReal.rpow_natCast` and `NNReal.rpow_intCast` say that the real power at an integer exponent is the monoid power.

The laws of exponents come in three strengths.

| Lean name | Statement | Hypothesis |
|---|---|---|
| `NNReal.mul_rpow` | $(xy)^z = x^z y^z$ | none |
| `NNReal.div_rpow` | $(x/y)^z = x^z / y^z$ | none |
| `NNReal.inv_rpow` | $(x^{-1})^y = (x^y)^{-1}$ | none |
| `NNReal.rpow_mul` | $x^{yz} = (x^y)^z$ | none |
| `NNReal.rpow_neg` | $x^{-y} = (x^y)^{-1}$ | none |
| `NNReal.rpow_add` | $x^{y+z} = x^y x^z$ | $x \ne 0$ |
| `NNReal.rpow_add'` | $x^{y+z} = x^y x^z$ | $y + z \ne 0$ |
| `NNReal.rpow_add_of_nonneg` | $x^{y+z} = x^y x^z$ | $0 \le y$, $0 \le z$ |
| `NNReal.rpow_sub` | $x^{y-z} = x^y / x^z$ | $x \ne 0$ |

The real versions of the first lines need $0 \le x$ and $0 \le y$. In `NNReal` these hypotheses are automatic. The variants with a prime replace the hypothesis on the base by a hypothesis on the exponent, and the variants `NNReal.rpow_add_natCast`, `NNReal.rpow_sub_one` and `NNReal.rpow_add_intCast` treat an integer step in the exponent.

**Theorem.** For $x \in \mathbb{R}_{\ge 0}$ with $x \ne 0$ and real $y, z$, $x^{y+z} = x^y x^z$.

*Proof.* Cast to $\mathbb{R}$ with `NNReal.coe_rpow` and the cast of a product. The real number $\uparrow x$ is positive, so `Real.rpow_add` gives $(\uparrow x)^{y+z} = (\uparrow x)^y (\uparrow x)^z$. The cast is injective, so the equation holds in `NNReal`. $\square$

The hypothesis is needed. For $x = 0$, $y = 1$, $z = -1$ the left side is $0^0 = 1$ and the right side is $0 \cdot 0 = 0$. When $y + z \ne 0$ the left side is $0$ and one of $y$, $z$ is not zero, so the right side is $0$ as well. This is the content of `NNReal.rpow_add'`.

The order lemmas follow the naming scheme of the real powers. For a fixed exponent $z > 0$ the map $x \mapsto x^z$ is strictly increasing (`NNReal.strictMono_rpow_of_pos`), and `NNReal.rpow_le_rpow`, `NNReal.rpow_lt_rpow` and `NNReal.rpow_le_rpow_iff` state it. For $z < 0$ the map is decreasing on the positive numbers (`NNReal.rpow_lt_rpow_of_neg`, `NNReal.rpow_le_rpow_iff_of_neg`). For a fixed base the lemmas `NNReal.rpow_le_rpow_of_exponent_le` ($1 \le x$) and `NNReal.rpow_le_rpow_of_exponent_ge` ($x \le 1$) compare two exponents. For $y > 0$ the map $x \mapsto x^y$ is an order isomorphism `NNReal.orderIsoRpow`, with inverse the power $1/y$ (`NNReal.orderIsoRpow_symm_eq`). The lemmas `NNReal.rpow_inv_rpow`, `NNReal.rpow_rpow_inv`, `NNReal.le_rpow_inv_iff` and `NNReal.rpow_inv_le_iff` move a root from one side of an equation or an inequality to the other. For a fixed exponent the map is also a monoid morphism `NNReal.rpowMonoidHom`, and `NNReal.finsetProd_rpow` and `NNReal.list_prod_map_rpow` move a power through a product. The square root is a power: `NNReal.sqrt_eq_rpow` states $\sqrt{x} = x^{1/2}$.

The module also holds the real versions `Real.finsetProd_rpow` and `Real.multiset_prod_map_rpow` for products of nonnegative reals, and `Real.nnnorm_rpow_of_nonneg` for the norm of a power. It registers extensions of the tactics `positivity` (for goals `0 < x ^ y` in both types) and `norm_num` (for powers with a numeral base and a rational exponent).

#### Powers in `ENNReal`

The power `ENNReal.rpow` on $[0, \infty]$ extends the power of `NNReal` by cases. Three lemmas give the definition.

1. `ENNReal.zero_rpow_def`: $0^y$ is $0$ for $y > 0$, $1$ for $y = 0$ and $\infty$ for $y < 0$.
2. `ENNReal.top_rpow_def`: $\infty^y$ is $\infty$ for $y > 0$, $1$ for $y = 0$ and $0$ for $y < 0$.
3. `ENNReal.coe_rpow_def`: for $x \in \mathbb{R}_{\ge 0}$, $(\uparrow x)^y$ is $\infty$ when $x = 0$ and $y < 0$, and $\uparrow(x^y)$ otherwise.

These values are not junk values. They make $x \mapsto x^y$ monotone on all of $[0, \infty]$ for $y > 0$, and they give $0^{-1} = \infty$, in agreement with the inverse of `ENNReal` (`ENNReal.rpow_neg_one`). The lemmas `ENNReal.rpow_eq_zero_iff` and `ENNReal.rpow_eq_top_iff` list the cases: $x^y = \infty$ exactly when $x = 0$ and $y < 0$, or $x = \infty$ and $y > 0$.

The laws of exponents need more care, because the product $0 \cdot \infty$ is $0$ in `ENNReal`. The lemma `ENNReal.rpow_add` needs $x \ne 0$ and $x \ne \infty$, and `ENNReal.rpow_add_of_nonneg` needs nonnegative exponents. The law $(xy)^z = x^z y^z$ holds except in one case.

**Theorem.** For $x, y \in [0, \infty]$ and real $z$, $(xy)^z$ is $\infty$ when $\{x, y\} = \{0, \infty\}$ and $z < 0$, and is $x^z y^z$ in all other cases.

*Proof sketch.* When $x$ and $y$ are finite, both sides are casts of powers in `NNReal`, and `NNReal.mul_rpow` applies. When $x = \infty$ and $y \ne 0$, the product is $\infty$, and both sides are $\infty$, $1$ or $0$ by `ENNReal.top_rpow_def` and the sign of $z$. In the exceptional case $xy = 0$, so the left side is $0^z = \infty$, while the right side is $0^z \cdot \infty^z = \infty \cdot 0 = 0$. $\square$

This is `ENNReal.mul_rpow_eq_ite`. The common special cases are `ENNReal.mul_rpow_of_nonneg` ($0 \le z$), `ENNReal.mul_rpow_of_ne_top` and `ENNReal.mul_rpow_of_ne_zero`. In the same way, `ENNReal.rpow_le_rpow` and `ENNReal.rpow_lt_rpow_iff` give monotonicity, `ENNReal.orderIsoRpow` is the order isomorphism for $y > 0$, and `ENNReal.rpow_left_bijective` states that $x \mapsto x^y$ is a bijection for $y \ne 0$. The lemmas `ENNReal.iSup_rpow_of_pos` and `ENNReal.iInf_rpow_of_pos` move a positive power through a supremum or an infimum, which a proof about $\limsup$ in $L^p$ uses.

The casts connect the three types: `ENNReal.coe_rpow_of_nonneg`, `ENNReal.ofReal_rpow_of_nonneg`, `ENNReal.toReal_rpow` and `ENNReal.toNNReal_rpow`. A proof usually checks that the numbers are finite with `ENNReal.rpow_ne_top_of_nonneg` and then moves to `NNReal` or to $\mathbb{R}$ with these casts.

#### Complex powers

The module `Mathlib.Analysis.SpecialFunctions.Pow.Complex` defines `Complex.cpow`. By `Complex.cpow_def`, $0^0 = 1$, $0^w = 0$ for $w \ne 0$, and $z^w = \exp(w \log z)$ for $z \ne 0$ (`Complex.cpow_def_of_ne_zero`). Here `Complex.log` is the principal branch, with imaginary part `Complex.arg z` in $(-\pi, \pi]$. The usual laws hold with hypotheses that come from the branch.

1. `Complex.cpow_add` and `Complex.cpow_sub` need only $z \ne 0$, because $\exp$ turns sums into products.
2. `Complex.cpow_nat_mul` and `Complex.cpow_int_mul` give $z^{nw} = (z^w)^n$ with no hypothesis, because the outer power is a monoid power.
3. `Complex.cpow_mul` gives $z^{wu} = (z^w)^u$ when the imaginary part of $w \log z$ is in $(-\pi, \pi]$.
4. `Complex.conj_cpow` and `Complex.inv_cpow` need `z.arg ≠ Real.pi`, so they fail on the negative real axis. The versions `Complex.conj_cpow_eq_ite` and `Complex.inv_cpow_eq_ite` hold for all $z$, with a case split.

**Theorem.** If $\arg a + \arg b \in (-\pi, \pi]$, then $(ab)^r = a^r b^r$ for every complex $r$.

*Proof sketch.* If $a = 0$ or $b = 0$, both sides are $0^r$ or $0$, by `Complex.cpow_def`. Otherwise $\log(ab)$ and $\log a + \log b$ have the same exponential $ab$. Their imaginary parts are $\arg(ab)$ and $\arg a + \arg b$, and both are in $(-\pi, \pi]$ by the hypothesis. Two logarithms of the same number differ by a multiple of $2\pi i$, so they are equal. Then $\exp(r \log(ab)) = \exp(r \log a)\exp(r \log b)$. $\square$

This is `Complex.mul_cpow`. Without the hypothesis the law fails: for $a = b = -1$ and $r = 1/2$, the left side is $1^{1/2} = 1$ and the right side is $i \cdot i = -1$. The lemmas `Complex.mul_cpow_of_pi_lt` and `Complex.mul_cpow_of_le_neg_pi` give the correction factor $\exp(\mp 2\pi i r)$. When one factor is a nonnegative real number the law always holds (`Complex.mul_cpow_ofReal_nonneg`, `Complex.ofReal_mul_cpow`, `Complex.natCast_mul_cpow`). For roots, `Complex.cpow_nat_inv_pow` gives $(z^{1/n})^n = z$ for $n \ne 0$, and `Complex.pow_cpow_nat_inv` gives $(z^n)^{1/n} = z$ when $\arg z \in (-\pi/n, \pi/n]$. The consequence `Complex.isSquare` states that every complex number is a square.

#### Integer roots

The function `Nat.nthRoot n a` computes $\lfloor a^{1/n} \rfloor$ for natural numbers with an integer Newton iteration. The module `Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas` proves that it is the floor of the real root. The main lemmas are the Galois connection `Nat.le_nthRoot_iff`: $b \le \mathrm{nthRoot}_n(a) \iff b^n \le a$ for $n \ne 0$, and its dual `Nat.nthRoot_lt_iff`. From them come `Nat.pow_nthRoot_le` and `Nat.lt_pow_nthRoot_add_one`, which say $r^n \le a < (r + 1)^n$ for $r = \mathrm{nthRoot}_n(a)$.

**Theorem.** If $a^n \le b < (a + 1)^n$, then $\mathrm{nthRoot}_n(b) = a$.

*Proof.* For $n = 0$ the hypothesis says $1 \le b < 1$, which is false. For $n \ne 0$, `Nat.le_nthRoot_iff` and $a^n \le b$ give $a \le \mathrm{nthRoot}_n(b)$, and `Nat.nthRoot_lt_iff` and $b < (a + 1)^n$ give $\mathrm{nthRoot}_n(b) < a + 1$. $\square$

This is `Nat.nthRoot_eq_of_le_of_lt`, and `Nat.nthRoot_pow` is the special case $b = a^n$. The function has a junk value at $n = 0$: `Nat.nthRoot_zero_left` gives $\mathrm{nthRoot}_0(a) = 1$. The lemma `Nat.exists_pow_eq_iff` decides whether $a$ is a perfect $n$-th power, and the instance `Nat.instDecidableExistsPowEq` lets the tactic decide check it.

#### The derivative of the square root

The module `Mathlib.Analysis.SpecialFunctions.Sqrt` computes the derivative of $\sqrt{x}$ away from $0$.

**Theorem.** For $x \ne 0$, the function $\sqrt{\cdot}$ has the derivative $1/(2\sqrt{x})$ at $x$.

*Proof sketch.* For $x > 0$, the map $t \mapsto t^2$ is a homeomorphism of $(0, \infty)$ onto itself with inverse $\sqrt{\cdot}$. This is `Real.sqPartialHomeomorph`. Its derivative at $\sqrt{x}$ is $2\sqrt{x} \ne 0$, so the inverse function rule of Chapter 3 gives the derivative $1/(2\sqrt{x})$ of the inverse at $x$. For $x < 0$, $\sqrt{t} = 0$ on a neighborhood of $x$, so the derivative is $0$, and $1/(2\sqrt{x}) = 1/0 = 0$ in Mathlib. $\square$

This is `Real.hasDerivAt_sqrt`, with the strict version `Real.hasStrictDerivAt_sqrt` and the smoothness `Real.contDiffAt_sqrt`. At $x = 0$ the square root is not differentiable, and every lemma has the hypothesis $f(x) \ne 0$. The rest of the module is a family of chain rules with the names of Chapter 3: `HasDerivAt.sqrt`, `HasDerivWithinAt.sqrt`, `deriv_sqrt`, `derivWithin_sqrt`, and for functions on a normed space `HasFDerivAt.sqrt`, `fderiv_sqrt`, `DifferentiableAt.sqrt`, `ContDiff.sqrt`.

#### Power means

The module `Mathlib.Analysis.MeanInequalitiesPow` compares weighted means. Let $w_i \ge 0$ with $\sum_i w_i = 1$ and let $z_i \ge 0$.

**Theorem.** For $p \ge 1$, $\left(\sum_i w_i z_i\right)^p \le \sum_i w_i z_i^p$.

*Proof.* The function $t \mapsto t^p$ is convex on $[0, \infty)$ for $p \ge 1$ (`convexOn_rpow`). Jensen's inequality `ConvexOn.map_sum_le` for a convex function and weights with sum $1$ is the claim. $\square$

This is `Real.rpow_arith_mean_le_arith_mean_rpow`. The module repeats it for the other exponents and types, with one scheme of names: `Real.pow_arith_mean_le_arith_mean_pow` for natural exponents, `Real.pow_arith_mean_le_arith_mean_pow_of_even` for even exponents and arbitrary real $z_i$, `Real.zpow_arith_mean_le_arith_mean_zpow` for integer exponents and positive $z_i$, and the copies in `NNReal` and `ENNReal`. The form with a root, `Real.arith_mean_le_rpow_mean`, states that the arithmetic mean is at most the power mean $\left(\sum_i w_i z_i^p\right)^{1/p}$.

The second family compares $(a + b)^p$ with $a^p + b^p$.

**Theorem.** For $a, b \in \mathbb{R}_{\ge 0}$ and $p \ge 1$, $a^p + b^p \le (a + b)^p$.

*Proof.* If $a + b = 0$, both sides are $0$. Otherwise put $s = a/(a + b)$ and $t = b/(a + b)$. Then $s, t \in [0, 1]$ and $s + t = 1$. For $u \in [0, 1]$ and $p \ge 1$, $u^p \le u$, so $s^p + t^p \le s + t = 1$. Multiply by $(a + b)^p$ and use `NNReal.div_rpow`. $\square$

This is `NNReal.add_rpow_le_rpow_add`. For $0 \le p \le 1$ the inequality turns around: `NNReal.rpow_add_le_add_rpow` gives $(a + b)^p \le a^p + b^p$. The versions for finite sums are `NNReal.sum_rpow_le_rpow_sum` and `NNReal.rpow_sum_le_sum_rpow`. The lemma `NNReal.rpow_sum_rpow_le` states that $\left(\sum_i f_i^q\right)^{1/q} \le \left(\sum_i f_i^p\right)^{1/p}$ for $0 < p \le q$: the $\ell^p$ norm of a finite vector decreases in $p$. Convexity gives `NNReal.rpow_add_le_mul_rpow_add_rpow`: $(a + b)^p \le 2^{p-1}(a^p + b^p)$ for $p \ge 1$. In `ENNReal` the constant of the quasi triangle inequality of $L^p$ is `ENNReal.LpAddConst p`, equal to $2^{1/p - 1}$ for $0 < p < 1$ and to $1$ otherwise, and `ENNReal.rpow_add_le_mul_rpow_add_rpow''` uses it.

#### Common errors

1. Using `NNReal.rpow_add` at a base that can be $0$. Use `NNReal.rpow_add'` when the sum of the exponents is not zero, or `NNReal.rpow_add_of_nonneg` for nonnegative exponents.
2. Moving a power through a product in `ENNReal` with a negative exponent. The law fails at $0 \cdot \infty$; use `ENNReal.mul_rpow_of_nonneg` or check that the factors are finite or nonzero.
3. Using `Complex.mul_cpow`, `Complex.conj_cpow` or `Complex.inv_cpow` without the hypothesis on the argument. A negative real base often breaks it, because its argument is $\pi$.

### Exercises

1. (A) Compute in `ENNReal` the values $0^{-2}$, $\infty^{1/2}$, $\infty^{-3}$ and $(0 \cdot \infty)^{-1}$, and compare the last one with $0^{-1} \cdot \infty^{-1}$.
2. (A) Show that $\mathrm{nthRoot}_3(1000) = 10$ and $\mathrm{nthRoot}_3(999) = 9$ with `Nat.nthRoot_eq_of_le_of_lt`.
3. (A) Find the derivative of $\sqrt{1 + x^2}$ on $\mathbb{R}$ with `HasDerivAt.sqrt`, and explain why the hypothesis $f(x) \ne 0$ holds.
4. (B) Show that $(-8)^{1/3}$, as a complex power, is $1 + i\sqrt{3}$ and not $-2$. Hint: $\arg(-8) = \pi$.
5. (B) For $a, b \ge 0$ and $p \ge 1$, prove $(a + b)^p \le 2^{p-1}(a^p + b^p)$ from the power mean inequality with weights $1/2$ and $1/2$.
6. (C) For $0 < p \le q$ and $f_1, \dots, f_n \ge 0$, prove $\left(\sum_i f_i^q\right)^{1/q} \le \left(\sum_i f_i^p\right)^{1/p}$. Hint: reduce to $\sum_i f_i^p = 1$, so that each $f_i \le 1$.

### Reference

<?reference?>
