---
title: Liouville numbers, metric approximation and Siegel's lemma
kind: api
modules:
  - Mathlib.NumberTheory.Transcendental.Liouville.Basic
  - Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleNumber
  - Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleWith
  - Mathlib.NumberTheory.Transcendental.Liouville.Measure
  - Mathlib.NumberTheory.Transcendental.Liouville.Residual
  - Mathlib.NumberTheory.Transcendental.Lindemann.AnalyticalPart
  - Mathlib.NumberTheory.WellApproximable
  - Mathlib.NumberTheory.SiegelsLemma
  - Mathlib.NumberTheory.NumberField.House
explains:
  E2: [Liouville.transcendental, liouville_liouvilleNumber, LiouvilleWith.irrational, volume_setOfPred_liouville, dense_liouville, AddCircle.exists_norm_nsmul_le, Int.Matrix.exists_ne_zero_int_vec_norm_le, NumberField.one_le_house_of_isIntegral]
  E1: auto
families: []
requires: [V12.C04, V12.C08, V13, V18]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Liouville numbers, metric approximation and Siegel's lemma

### Overview

A real number $x$ is algebraic when it is a root of a nonzero polynomial with integer coefficients, and transcendental otherwise. Liouville found the first explicit transcendental numbers by a simple principle: an algebraic number of degree $d$ cannot be approximated by rationals $a/b$ much better than $b^{-d}$. A number that has better and better approximations is therefore transcendental. This section describes the Mathlib form of this argument, the constant $\sum_i m^{-i!}$, and the finer predicate `LiouvilleWith p x` with a fixed exponent $p$.

The same modules answer the question how large the set of Liouville numbers is. It is a dense $G_\delta$ set, so it is large in the sense of Baire category, but it has Lebesgue measure zero. The module on well approximable numbers puts this in a general frame and proves Gallagher's zero one law. The section ends with two tools of transcendence theory: Siegel's lemma, which gives small integer solutions of linear systems, and the house of an algebraic number. Section 4.3 gave Dirichlet's approximation theorem $|x - a/b| < 1/b^2$; the previous section of this chapter gave the predicate `Irrational`.

### The library around it

#### Liouville numbers are transcendental

`Liouville x` says: for every $n \in \mathbb{N}$ there are integers $a$ and $b > 1$ with $x \ne a/b$ and $|x - a/b| < 1/b^n$. The docstring notes that $x \ne a/b$ replaces the classical $0 < |x - a/b|$. The lemma `Liouville.frequently_exists_num` gives the form with infinitely many denominators $b$.

**Proposition (Liouville's inequality).** Let $\alpha$ be an irrational root of a nonzero $f \in \mathbb{Z}[X]$ of degree $d$. There is $A > 0$ with $|\alpha - a/b| \ge A / b^d$ for all $a \in \mathbb{Z}$ and $b \ge 1$.

*Proof.* Near $\alpha$, $f$ has no other root, so there is $\varepsilon > 0$ such that $f(y) \ne 0$ for $0 < |y - \alpha| \le \varepsilon$. Let $M$ bound $|f'|$ on $[\alpha - \varepsilon, \alpha + \varepsilon]$. If $|\alpha - a/b| \le \varepsilon$, then $f(a/b) \ne 0$, and $b^d f(a/b)$ is a nonzero integer, so $|f(a/b)| \ge b^{-d}$. By the mean value theorem, $b^{-d} \le |f(\alpha) - f(a/b)| \le M |\alpha - a/b|$. If $|\alpha - a/b| > \varepsilon$, then $|\alpha - a/b| > \varepsilon b^{-d}$. Take $A = \min(1/M, \varepsilon)$. $\square$

The Lean form is `Liouville.exists_pos_real_of_irrational_root`, with the denominator written $b + 1$ for $b \in \mathbb{N}$. Its proof uses a general metric lemma, `Liouville.exists_one_le_pow_mul_dist`, which separates the estimate from the polynomial.

**Theorem (Liouville).** A Liouville number is transcendental.

*Proof.* Let $x$ be a Liouville number. It is irrational (`Liouville.irrational`): if $x = p/q$, then for $a/b \ne x$, $|x - a/b| \ge 1/(qb)$, and this is not less than $1/b^n$ for $b^{n-1} > q$. Suppose that $x$ is a root of a nonzero $f$ of degree $d$. With $A$ from the proposition, choose $n$ with $2^{n-d} > 1/A$. A Liouville approximation $a/b$ with this $n$ gives $A/b^d \le |x - a/b| < 1/b^n$, so $b^{n-d} < 1/A$, which is false for $b \ge 2$. $\square$

In Lean, `Liouville.transcendental` concludes `Transcendental ℤ x`.

#### Liouville's constant

`liouvilleNumber m` is the sum $\sum_{i \ge 0} m^{-i!}$, by `tsum`. The series converges for $m > 1$ (`LiouvilleNumber.summable`); for other $m$ the value of the sum is the junk value $0$. The module splits the sum into `LiouvilleNumber.partialSum m k`, the terms with $i \le k$, and `LiouvilleNumber.remainder m k`, the rest, and `LiouvilleNumber.partialSum_add_remainder` adds them back.

**Theorem.** For an integer $m \ge 2$, `liouvilleNumber m` is a Liouville number, so it is transcendental.

*Proof.* The partial sum is $p_k / m^{k!}$ for an integer $p_k$, since $i! \mid k!$ for $i \le k$ (`LiouvilleNumber.partialSum_eq_rat`). The remainder is positive (`LiouvilleNumber.remainder_pos`), so $x \ne p_k/m^{k!}$. It is at most a geometric series with first term $m^{-(k+1)!}$ and ratio $1/m$, so it is at most $\frac{m}{m - 1} m^{-(k+1)!} \le 2 m^{-(k+1)!}$, and this is less than $(m^{k!})^{-k}$ (`LiouvilleNumber.remainder_lt`). With $b = m^{k!}$, $|x - p_k/b| < b^{-k}$ for every $k$. $\square$

The Lean statements are `liouville_liouvilleNumber` and `transcendental_liouvilleNumber`. The inequality steps are `LiouvilleNumber.remainder_lt'` and `LiouvilleNumber.aux_calc`.

#### Liouville numbers with an exponent

`LiouvilleWith p x` says that there is $C$ such that for infinitely many $n \in \mathbb{N}$ there is $m \in \mathbb{Z}$ with $x \ne m/n$ and $|x - m/n| < C/n^p$. The exponent measures the quality of the approximation.

1. For $p \le 1$ the condition holds for every $x$ (`liouvilleWith_one` and `LiouvilleWith.mono`, which lowers the exponent).
2. For $p > 1$ it implies irrationality (`LiouvilleWith.irrational`): if $x = a/b$, then $|x - m/n| \ge 1/(bn)$ for $m/n \ne x$, and $1/(bn) < C/n^p$ fails for large $n$. Dirichlet's theorem of Section 4.3 gives the converse for $p = 2$.
3. A number is Liouville if and only if it is `LiouvilleWith p` for every $p$ (`forall_liouvilleWith_iff`, with one direction `Liouville.liouvilleWith`).

The predicate is invariant under the affine maps with rational coefficients. The lemmas form one family with the same naming pattern as the closure rules of `Irrational`: `LiouvilleWith.add_rat`, `LiouvilleWith.rat_add`, `LiouvilleWith.sub_int`, `LiouvilleWith.mul_rat`, `LiouvilleWith.nat_mul`, `LiouvilleWith.neg`, and the forms with `_iff`, such as `LiouvilleWith.add_rat_iff` and `LiouvilleWith.mul_int_iff`. The forms for a product need a nonzero factor. The lemma `LiouvilleWith.frequently_lt_rpow_neg` drops the constant $C$ at the cost of a smaller exponent: for $q < p$, the inequality $|x - m/n| < n^{-q}$ holds for infinitely many $n$.

#### How many Liouville numbers there are

The set of Liouville numbers is an intersection of open sets: `setOfPred_liouville_eq_iInter_iUnion` writes it as $\bigcap_n \bigcup_{a, b > 1} B(a/b, b^{-n}) \setminus \{a/b\}$, and `setOfPred_liouville_eq_irrational_inter_iInter_iUnion` writes it as the irrational numbers intersected with $\bigcap_n \bigcup_{a, b > 1} B(a/b, b^{-n})$. The rational numbers form a countable set, so the set of irrational numbers is a $G_\delta$ set, and the Liouville numbers are a $G_\delta$ set too (`IsGδ.setOfPred_liouville`).

**Theorem.** The Liouville numbers are dense in $\mathbb{R}$, and almost every real number is not a Liouville number.

*Proof.* Each open set $U_n = \bigcup_{a, b > 1} B(a/b, b^{-n})$ contains every rational number, so it is dense. The irrational numbers are a dense $G_\delta$ set. By the Baire category theorem, a countable intersection of dense $G_\delta$ sets is dense, which gives `dense_liouville`. For the measure, fix $p > 2$ and an integer $m$. The set of $x \in [m, m + 1]$ with $|x - a/b| < b^{-p}$ for some $a$ has measure at most $(b + 1) \cdot 2 b^{-p}$. The sum over $b$ converges since $p - 1 > 1$, so by the Borel and Cantelli lemma, almost no $x$ has such approximations for infinitely many $b$. So almost no $x$ is `LiouvilleWith p` for $p > 2$, and in particular almost no $x$ is a Liouville number. $\square$

The measure statements are `ae_not_liouvilleWith` (for almost every $x$, no exponent $p > 2$ works), `volume_iUnion_setOfPred_liouvilleWith`, `ae_not_liouville` and `volume_setOfPred_liouville`. The category statement is `eventually_residual_liouville`: the set of Liouville numbers is in the filter `residual ℝ` of sets that contain a dense $G_\delta$ set. Together they give `Real.disjoint_residual_ae`: the filter of residual sets and the filter of sets of full measure are disjoint, so on $\mathbb{R}$ the two notions of a large set do not agree.

#### Well approximable points and Gallagher's theorem

The module `Mathlib.NumberTheory.WellApproximable` works in a seminormed group $A$. For $n \in \mathbb{N}$ and $\delta > 0$, `approxOrderOf A n δ` is the set of points at distance less than $\delta$ from an element of order exactly $n$ (`mem_approxOrderOf_iff`). For a sequence $\delta_n$, `wellApproximable A δ` is the set of points in infinitely many of the sets `approxOrderOf A n (δ n)`, as a `Filter.blimsup` (`mem_wellApproximable_iff`). The additive forms are `approxAddOrderOf` and `addWellApproximable`.

On the circle $\mathbb{R}/\mathbb{Z}$, the elements of order $n$ are the fractions $m/n$ with $\gcd(m, n) = 1$. So `UnitAddCircle.mem_addWellApproximable_iff` says that $x$ is well approximable if and only if $\|x - m/n\| < \delta_n$ for infinitely many $n$ and some $m$ coprime to $n$: this is the classical notion of approximation by reduced fractions. The lemmas `approxOrderOf.image_pow_subset`, `approxOrderOf.smul_subset_of_coprime` and their additive forms describe how the sets move under the maps $y \mapsto y^m$ and $y \mapsto a y$.

**Theorem (Gallagher).** Let $\delta_n \to 0$. Then the set of well approximable points of the circle has measure $0$ or full measure.

The proof in Mathlib uses, for each prime $p$, the ergodicity of the maps $y \mapsto p y$ and $y \mapsto p y + 1/p$ on the circle. It is not given here. The Lean statement is `AddCircle.addWellApproximable_ae_empty_or_univ`.

The module also proves Dirichlet's approximation theorem on the circle. `AddCircle.exists_norm_nsmul_le` says that for $\xi$ in $\mathbb{R}/T\mathbb{Z}$ and $n \ge 1$ there is $1 \le j \le n$ with $\|j\xi\| \le T/(n + 1)$. The proof is the pigeonhole principle: the $n + 1$ points $0, \xi, \dots, n\xi$ cut the circle into $n + 1$ arcs of total length $T$, so two of the points are at distance at most $T/(n + 1)$, and their difference is $\pm j\xi$ for some $1 \le j \le n$. The form `NormedAddCommGroup.exists_norm_nsmul_le` works in a compact connected group with a Haar measure.

#### Siegel's lemma

**Theorem (Siegel's lemma).** Let $A$ be an $m \times n$ matrix with integer entries, $0 < m < n$. Then $A t = 0$ has a solution $t \in \mathbb{Z}^n$, $t \ne 0$, with $\|t\|_\infty \le (n \max(1, \|A\|))^{m/(n - m)}$, where $\|A\|$ is the largest absolute value of an entry.

*Idea of the proof.* Let $B \ge 1$ be an integer and consider the $(B + 1)^n$ vectors $t$ with entries in $\{0, \dots, B\}$. Each coordinate of $A t$ lies in an interval of length at most $n B \|A\|$, so $A t$ takes at most $(n B \|A\| + 1)^m$ values. For the $B$ of the statement, $(B + 1)^n$ is larger. By the pigeonhole principle, two vectors $t_1 \ne t_2$ have $A t_1 = A t_2$, and $t = t_1 - t_2$ is a solution with $\|t\|_\infty \le B$. $\square$

The Lean statement is `Int.Matrix.exists_ne_zero_int_vec_norm_le`, for `A : Matrix α β ℤ` with `Fintype.card α < Fintype.card β`. The norm on matrices is the sup norm of the instance `Matrix.seminormedAddCommGroup`, which is not a global instance; the module opens it locally. The variant `Int.Matrix.exists_ne_zero_int_vec_norm_le'` assumes $A \ne 0$ and drops the maximum with $1$, using `Int.Matrix.one_le_norm_A_of_ne_zero`.

#### The house of an algebraic number

For $\alpha$ in a number field $K$, `NumberField.house α` is the largest absolute value $\max_\sigma |\sigma(\alpha)|$ over the embeddings $\sigma : K \to \mathbb{C}$. Lean defines it as the norm of the image of $\alpha$ under the canonical embedding of Chapter 8, and `NumberField.house_eq_sup'` gives the maximum form. The house behaves like a norm: it is nonnegative (`NumberField.house_nonneg`), subadditive (`NumberField.house_add_le`, `NumberField.house_sum_le_sum_house`) and submultiplicative (`NumberField.house_mul_le`, `NumberField.house_prod_le`), with equality for powers (`NumberField.house_pow`) and for integers (`NumberField.house_intCast`, `NumberField.house_nat_mul`). Each embedding is bounded by it (`NumberField.norm_embedding_le_house`).

**Proposition.** A nonzero algebraic integer $\alpha$ has house at least $1$.

*Proof.* The norm $N(\alpha) = \prod_\sigma \sigma(\alpha)$ is a nonzero integer, so $|N(\alpha)| \ge 1$. If $|\sigma(\alpha)| < 1$ for all $\sigma$, the product would have absolute value less than $1$. So $|\sigma(\alpha)| \ge 1$ for some $\sigma$. $\square$

This is `NumberField.one_le_house_of_isIntegral`, and `NumberField.exists_conjugate_one_le_norm` is the form with the conjugate. The bound `NumberField.norm_norm_le_norm_mul_house_pow` says $|N(\alpha)| \le |\sigma(\alpha)| \cdot \overline{|\alpha|}^{\,n - 1}$, where $n = [K : \mathbb{Q}]$ and $\overline{|\alpha|}$ is the house. The coordinates of an algebraic integer in the integral basis are bounded by a constant times its house (`NumberField.house.basis_repr_norm_le_const_mul_house`). With this bound, Siegel's lemma passes to systems with coefficients in $\mathcal{O}_K$: `NumberField.house.exists_ne_zero_int_vec_house_le` gives a nonzero solution in $\mathcal{O}_K$ whose entries have a house bounded in terms of the houses of the coefficients.

#### The analytic part of the Lindemann and Weierstrass theorem

The module `Mathlib.NumberTheory.Transcendental.Lindemann.AnalyticalPart` has one theorem, `LindemannWeierstrass.exp_polynomial_approx`. For $f \in \mathbb{Z}[X]$ with $f(0) \ne 0$ it gives a constant $c$ and, for each prime $p > |f(0)|$, an integer $n_p$ prime to $p$ and a polynomial $g_p$ of degree at most $p \deg f - 1$ with $|n_p e^r - p\, g_p(r)| \le c^p/(p - 1)!$ for each complex root $r$ of $f$. This is the analytic estimate in the proof of the Lindemann and Weierstrass theorem. The algebraic part and the theorem itself are not in this edition of the index.

#### Common errors

1. `Liouville x` asks for a denominator $b > 1$, but `LiouvilleWith p x` puts no condition on the constant $C$ and on the denominator $n$. The lemma `LiouvilleWith.exists_pos` gives the form with $C > 0$ and $1 \le n$.
2. `Liouville.transcendental` concludes `Transcendental ℤ x`, with integer coefficients, while `Transcendental.irrational` takes `Transcendental ℚ x`. The two conditions are equivalent, but a proof must pass from one ring to the other.
3. `Int.Matrix.exists_ne_zero_int_vec_norm_le` uses the sup norm on matrices and vectors. The instance is local, so a statement with `‖A‖` needs the same instance in scope.

### Exercises

1. (A) Show that $\sum_{i \ge 0} 10^{-i!}$ is irrational with `Liouville.irrational`, and write its first ten decimal digits.
2. (A) Show from the definition that if $x$ is a Liouville number, then so is $x + q$ for each rational $q$.
3. (B) Show that $\sum_{i \ge 0} 2^{-3^i}$ is `LiouvilleWith p` for every $p < 3$.
4. (B) Show that every real number is a sum of two Liouville numbers. Use that $\{x - y : y \text{ Liouville}\}$ is a dense $G_\delta$ set.
5. (B) Apply Siegel's lemma to the $1 \times 3$ matrix $(1\ 2\ 3)$ and find a small solution by hand.
6. (B) Prove Liouville's inequality for $\alpha = \sqrt2$ with $A = \frac14$ directly, from $|a^2 - 2b^2| \ge 1$.

### Reference

<?reference?>
