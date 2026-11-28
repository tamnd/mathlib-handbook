---
title: Polynomials in analysis
kind: api
modules:
  - Mathlib.Analysis.Polynomial.Basic
  - Mathlib.Analysis.Polynomial.Order
  - Mathlib.Analysis.Calculus.LocalExtr.Polynomial
  - Mathlib.Analysis.Polynomial.SignRight
  - Mathlib.Analysis.Polynomial.CauchyIndex
  - Mathlib.Analysis.Polynomial.CauchyBound
  - Mathlib.Analysis.Polynomial.Norm
  - Mathlib.Analysis.Polynomial.Fourier
  - Mathlib.Analysis.Polynomial.MahlerMeasure
  - Mathlib.Analysis.Polynomial.Factorization
explains:
  E2: [Polynomial.isEquivalent_atTop_lead, Polynomial.zero_lt_eval_of_roots_lt_of_leadingCoeff_nonneg, Polynomial.card_roots_le_derivative, Polynomial.signRight_mul, Polynomial.IsRoot.norm_lt_cauchyBound, Polynomial.mahlerMeasure_mul, Polynomial.mahlerMeasure_X_sub_C]
  E1: auto
families: []
requires: [V02, V06, V13, V15.C02, V15.C03, V15.C05, V15.C07]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Polynomials in analysis

### Overview

A polynomial is an algebraic object: Volume 6 defines `Polynomial R` as a ring of finite sums $\sum a_i X^i$, and Volume 11 studies its roots over fields. A real or complex polynomial is also a function, and analysis asks questions about this function. How fast does it grow? Where is it positive? How many real roots does it have? How large can its roots be? How large are its coefficients compared with its values on the unit circle? The modules of this section answer these questions.

The answers use the tools of this volume. The growth of $P(x)$ is a statement about asymptotic equivalence from Chapter 7. The sign of $P$ comes from the intermediate value theorem of Chapter 2. The bound on the number of real roots comes from Rolle's theorem of Chapter 3. The sign of $P$ just to the right of a point gives the Cauchy index of a rational function, the main quantity of Sturm's theorem. Last, the Mahler measure of a complex polynomial is an integral of $\log |P|$ over the unit circle, and it connects the roots with the coefficients.

In Lean, `Polynomial.eval x P` is the value $P(x)$. All the lemmas below state facts about this function of $x$.

### The library around it

#### Growth at infinity

The module `Mathlib.Analysis.Polynomial.Basic` compares polynomial functions at infinity. Over an ordered normed field such as $\mathbb{R}$, a polynomial is asymptotic to its leading term.

**Theorem.** For $P = a_n X^n + \dots + a_0$, $P(x) \sim a_n x^n$ as $x \to \infty$.

*Proof.* For $a_n = 0$ the polynomial is $0$ and both sides are $0$. Otherwise $P(x) - a_n x^n = \sum_{i < n} a_i x^i$, and each term is $o(x^n)$ because $x^i / x^n = x^{i - n} \to 0$. A finite sum of $o(x^n)$ terms is $o(x^n)$, and $x^n = O(a_n x^n)$. So $P(x) - a_n x^n = o(a_n x^n)$, which is the definition of $\sim$. $\square$

This is `Polynomial.isEquivalent_atTop_lead`, and `Polynomial.isEquivalent_atBot_lead` is the version at $-\infty$. The quotient form `Polynomial.isEquivalent_atTop_div` states $P(x)/Q(x) \sim (a_n/b_m)\,x^{n - m}$, with an integer exponent. The comparison lemmas follow one pattern: `Polynomial.isBigO_atTop_of_degree_le` gives $P = O(Q)$ when $\deg P \le \deg Q$, and `Polynomial.isLittleO_atTop_of_degree_lt` gives $P = o(Q)$ when $\deg P < \deg Q$. The versions for the filter `Bornology.cobounded`, such as `Polynomial.isEquivalent_cobounded_leading_monomial` and `Polynomial.isBigO_cobounded_pow_natDegree`, work over a normed ring with `NormMulClass` and use the filter `Bornology.cobounded`, the filter of complements of bounded sets. For $\mathbb{C}$ this is the limit $|z| \to \infty$.

Two integer results use the growth. `Polynomial.finite_abs_eval_le_of_degree_lt` states that $\{x \in \mathbb{Z} : |P(x)| \le |Q(x)|\}$ is finite when $\deg Q < \deg P$. `Polynomial.dvd_of_infinite_eval_dvd_eval` states that a monic $Q \in \mathbb{Z}[X]$ divides $P$ when $Q(a) \mid P(a)$ for infinitely many integers $a$. The proof divides with remainder, $P = QS + R$ with $\deg R < \deg Q$. Then $Q(a) \mid R(a)$ for infinitely many $a$, and the growth bound forces $R(a) = 0$ for infinitely many $a$, so $R = 0$.

#### The sign of a real polynomial

The module `Mathlib.Analysis.Polynomial.Order` gives the sign of a real polynomial away from its roots. The basic fact is `Polynomial.sign_eval_eq_of_forall_ne_zero`: if $P$ has no root in the interval between $a$ and $b$, then $P(a)$ and $P(b)$ have the same sign. This is the intermediate value theorem in contrapositive form.

**Theorem.** If every real root of $P$ is less than $x$ and the leading coefficient of $P$ is nonnegative, then $P(x) > 0$.

*Proof.* The leading coefficient is nonnegative, so $P$ is $0$ or it is positive. The polynomial $0$ has every real number as a root, and a root $y = x$ contradicts the hypothesis, so $P \ne 0$ and $a_n > 0$. By the theorem on growth, $P(y) \sim a_n y^n$, so $P(y) > 0$ for some large $y \ge x$. $P$ has no root in $[x, y]$, so $P(x)$ has the sign of $P(y)$. $\square$

This is `Polynomial.zero_lt_eval_of_roots_lt_of_leadingCoeff_nonneg`. The family has eight members, by the strictness of the inequality, the sign of the leading coefficient and the side of the roots. To the left of all the roots the sign is multiplied by $(-1)^n$, and the lemmas such as `Polynomial.zero_lt_negOnePow_mul_eval_of_lt_roots_of_leadingCoeff_nonneg` state this with `Int.negOnePow`.

#### Rolle's theorem and the number of real roots

The module `Mathlib.Analysis.Calculus.LocalExtr.Polynomial` applies Rolle's theorem to polynomials.

**Theorem.** A real polynomial $p$ has at most one more root than $p'$, counted with multiplicity.

*Proof sketch.* Let $x_1 < \dots < x_k$ be the distinct roots of $p$, with multiplicities $m_1, \dots, m_k$. A root of multiplicity $m$ of $p$ is a root of multiplicity $m - 1$ of $p'$. Rolle's theorem gives a root of $p'$ strictly between $x_i$ and $x_{i+1}$, and it is not a root of $p$. So $p'$ has at least $\sum (m_i - 1) + (k - 1)$ roots, and $p$ has $\sum m_i$ roots, one more. $\square$

This is `Polynomial.card_roots_le_derivative`. The version for distinct roots is `Polynomial.card_roots_toFinset_le_derivative`, and the sharper `Polynomial.card_roots_toFinset_le_card_roots_derivative_sdiff_roots_succ` counts only the roots of $p'$ that are not roots of $p$. For a polynomial over a ring $F$ with an algebra map to $\mathbb{R}$, `Polynomial.card_rootSet_le_derivative` counts the real roots with `Polynomial.rootSet`. A consequence is the bound of Descartes type: if $p^{(j)}$ has no real root, then $p$ has at most $j$ real roots.

#### The sign to the right of a point

The module `Mathlib.Analysis.Polynomial.SignRight` defines `Polynomial.signRight x p`, the sign of $p$ just to the right of $x$. The definition is algebraic: it is the sign of the lowest nonzero coefficient of the Taylor expansion $p(x + h) = c_k h^k + c_{k+1} h^{k+1} + \dots$. So it makes sense over every ordered commutative ring. Over an ordered field with the order topology, `Polynomial.eventually_sign_eq_signRight` connects it with the values: for $y > x$ close to $x$, the sign of $p(y)$ is `signRight x p`. The values are `Polynomial.signRight_zero` (the zero polynomial has sign $0$), `Polynomial.signRight_C`, `Polynomial.signRight_X_sub_C` (the sign $1$) and `Polynomial.signRight_of_eval_ne_zero`, which gives the sign of $p(x)$ when $p(x) \ne 0$.

**Theorem.** `signRight x (p * q)` is `signRight x p * signRight x q`.

*Proof.* The Taylor expansion at $x$ is a ring homomorphism. The lowest coefficient of a product is the product of the lowest coefficients, because an ordered ring has no zero divisors. The sign is multiplicative. $\square$

This is `Polynomial.signRight_mul`. Other rules are `Polynomial.signRight_neg`, `Polynomial.signRight_mul_self` and `Polynomial.signRight_derivative_mul`: at a root $x$ of $p \ne 0$, the product $p' p$ is positive to the right of $x$. This holds because $p$ moves away from $0$ just after its root.

#### The Cauchy index

The module `Mathlib.Analysis.Polynomial.CauchyIndex` works with a rational function `f : RatFunc K` over an ordered field. The jump `RatFunc.jump f x` is $1$ if $f$ goes from $-\infty$ to $+\infty$ at $x$, $-1$ if it goes from $+\infty$ to $-\infty$, and $0$ otherwise. The definition uses only algebra: the jump is nonzero only at a root of odd multiplicity of the denominator, and then it is `signRight x` of the numerator times the denominator. The Cauchy index `RatFunc.cauchyIndex f a b` is the sum of the jumps at the poles in $(a, b)$.

The API computes jumps and indices. `RatFunc.jump_div` gives the jump of $q/p$ from any representation as a quotient. `RatFunc.jump_eq_zero_of_eval_denom_ne_zero` and `RatFunc.jump_algebraMap` state that there is no jump away from the poles, so a polynomial has index $0$ (`RatFunc.cauchyIndex_algebraMap`). Adding a polynomial does not change the index (`RatFunc.cauchyIndex_add_algebraMap`), so $q/p$ can be replaced by $(q \bmod p)/p$ (`RatFunc.cauchyIndex_div_mod`). This is the step of the Euclidean algorithm in the proof of Sturm's theorem. The key link is `RatFunc.jump_derivative_mul_div`: at a root $x$ of $p$, the jump of $p' q / p$ is the sign of $q(x)$. With $q = 1$, the index of $p'/p$ on $(a, b)$ is the number of distinct roots of $p$ in $(a, b)$.

#### Bounds for the roots

The module `Mathlib.Analysis.Polynomial.CauchyBound` defines the Cauchy bound `Polynomial.cauchyBound p` over a normed division ring:
$$B(p) = \frac{\max_{i < n} |a_i|}{|a_n|} + 1.$$

**Theorem.** Every root $z$ of $p \ne 0$ satisfies $|z| < B(p)$.

*Proof.* Put $M = \max_{i < n} |a_i| / |a_n|$. For $M = 0$ the polynomial is $a_n X^n$, its only root is $0$, and $0 < 1 \le B(p)$. Let $M > 0$ and $|z| \ge M + 1$, so $|z| > 1$. Then
$$\Bigl|\sum_{i<n} a_i z^i\Bigr| \le |a_n| M \frac{|z|^n - 1}{|z| - 1} < |a_n| \frac{M}{|z| - 1} |z|^n \le |a_n|\,|z|^n.$$
So $|p(z)| > 0$ and $z$ is not a root. $\square$

This is `Polynomial.IsRoot.norm_lt_cauchyBound`. The values `Polynomial.cauchyBound_X_sub_C` ($|a| + 1$ for $X - a$), `Polynomial.cauchyBound_one` and `Polynomial.one_le_cauchyBound` show the conventions: the bound is at least $1$, and the zero polynomial has bound $1$ (`Polynomial.cauchyBound_zero`). The bound does not change under scaling by $x \ne 0$ (`Polynomial.cauchyBound_smul`).

#### Norms of coefficients and the unit circle

The module `Mathlib.Analysis.Polynomial.Norm` defines `Polynomial.supNorm p`, the largest norm of a coefficient (`Polynomial.supNorm_eq_iSup`). It is attained (`Polynomial.exists_eq_supNorm`), it bounds each coefficient (`Polynomial.le_supNorm`), and it is $0$ only for $p = 0$ (`Polynomial.supNorm_eq_zero_iff`).

The module `Mathlib.Analysis.Polynomial.Fourier` views a complex polynomial as a function on the circle. The algebra map `Polynomial.toAddCircle` sends $p$ to the continuous function $\theta \mapsto p(e^{i\theta})$ on `AddCircle (2 * π)`, and it sends $X^n$ to the Fourier character `AddCircle.fourier n` (`Polynomial.toAddCircle_X_pow_eq_fourier`). So the Fourier coefficients of this function are the coefficients of $p$ for $n \ge 0$ and $0$ for $n < 0$ (`Polynomial.fourierCoeff_toAddCircle`). Parseval's identity of Volume 19 gives `Polynomial.sum_sq_norm_coeff_eq_circleAverage`:
$$\sum_i |a_i|^2 = \frac{1}{2\pi} \int_0^{2\pi} |p(e^{i\theta})|^2 \, d\theta.$$

#### The Mahler measure

The module `Mathlib.Analysis.Polynomial.MahlerMeasure` defines `Polynomial.logMahlerMeasure p` as the average of $\log |p|$ over the unit circle (`Polynomial.logMahlerMeasure_def`, with `Real.circleAverage`), and `Polynomial.mahlerMeasure p` as its exponential for $p \ne 0$ and $0$ for $p = 0$:
$$M(p) = \exp\Bigl(\frac{1}{2\pi}\int_0^{2\pi} \log |p(e^{i\theta})|\, d\theta\Bigr).$$

**Theorem.** $M(pq) = M(p)\,M(q)$.

*Proof.* If $p$ or $q$ is $0$, both sides are $0$. Otherwise $\log|pq| = \log|p| + \log|q|$ at each point of the circle where $p$ and $q$ do not vanish, which is all but finitely many points. Both functions are integrable (`Polynomial.intervalIntegrable_mahlerMeasure`), so the averages add, and $\exp$ turns the sum into a product. $\square$

This is `Polynomial.mahlerMeasure_mul`, with `Polynomial.logMahlerMeasure_mul_eq_add_logMahlerMeasure` for the logarithms. For a linear factor, Jensen's formula from Volume 19 gives $\frac{1}{2\pi}\int_0^{2\pi} \log|e^{i\theta} - z|\,d\theta = \log^+ |z|$, so $M(X - z) = \max(1, |z|)$. These are `Polynomial.logMahlerMeasure_X_sub_C` and `Polynomial.mahlerMeasure_X_sub_C`. A product over the factorization of $p$ gives the formula with the roots:
$$M(p) = |a_n| \prod_{\alpha} \max(1, |\alpha|),$$
which is `Polynomial.mahlerMeasure_eq_leadingCoeff_mul_prod_roots`. So $M(p) \ge |a_n|$ (`Polynomial.leadingCoeff_le_mahlerMeasure`).

The Mahler measure bounds the coefficients from both sides. Landau's inequality `Polynomial.mahlerMeasure_le_sqrt_sum_sq_norm_coeff` states $M(p) \le (\sum |a_i|^2)^{1/2}$: Jensen's inequality for the concave function $\log$ bounds the average of $\log|p|^2$ by the log of the average of $|p|^2$, and Parseval computes that average. In the other direction, `Polynomial.norm_coeff_le_choose_mul_mahlerMeasure` states $|a_k| \le \binom{n}{k} M(p)$, because $a_k$ is $\pm a_n$ times an elementary symmetric function of the roots. Mignotte's bound `Polynomial.norm_coeff_le_choose_mul_mahlerMeasure_of_one_le_mahlerMeasure` applies this to a factor $g$ of $gh$ with $M(h) \ge 1$. Number theory uses these bounds for polynomials with integer coefficients, through `Polynomial.mapMahlerMeasure`, which maps the coefficients to $\mathbb{C}$ first.

The module `Mathlib.Analysis.Polynomial.Factorization` splits a monic polynomial over an algebraically closed field into a linear factor and a monic cofactor, and a monic real polynomial of degree at least $2$ into a quadratic factor and a monic cofactor.

#### Common errors

1. `Polynomial.eval x P` takes the point first and the polynomial second. The function of $x$ is `fun x => P.eval x`, and the asymptotic lemmas are stated for this function.
2. The zero polynomial has every point as a root. The lemmas of `Mathlib.Analysis.Polynomial.Order` have the hypothesis "every root is less than $x$", and for $P = 0$ this hypothesis fails at $x$ itself. Do not expect a separate hypothesis `P ≠ 0`.
3. `Polynomial.signRight x p` is the sign to the right of $x$, not at $x$. At a root it is not $0$ unless $p = 0$ (`Polynomial.signRight_eq_zero_iff`).

### Exercises

1. (A) Compute `Polynomial.cauchyBound` for $X^2 - 3X + 2$ and check that both roots are below it.
2. (A) Show that $(x^3 + x)/(2x^3 - 1) \to 1/2$ as $x \to \infty$ with the quotient form of the growth theorem.
3. (B) Show that $x^5 - 5x + 1$ has at most three real roots, with the bound of Rolle type applied to its derivative.
4. (B) Compute the Mahler measure of $2X^2 - 5X + 2$ from its roots, and check Landau's inequality for it.
5. (B) Compute the jumps and the Cauchy index on $(-2, 2)$ of $p'/p$ for $p = X^3 - X$, and compare with the number of roots of $p$ in $(-2, 2)$.
6. (C) Prove that $M(p) \le \sum_i |a_i|$ for a complex polynomial $p$. Hint: bound $|p(e^{i\theta})|$ pointwise, then use the monotonicity of $\log$ and of the average.

### Reference

<?reference?>
