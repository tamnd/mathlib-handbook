---
title: Cauchy estimates, Liouville and the fundamental theorem of algebra
kind: theory
modules:
  - Mathlib.Analysis.Complex.Liouville
  - Mathlib.Analysis.Complex.Polynomial.Basic
  - Mathlib.Analysis.Complex.Polynomial.GaussLucas
explains:
  E3: [Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le, Differentiable.apply_eq_apply_of_bounded, Complex.exists_root, Polynomial.rootSet_derivative_subset_convexHull_rootSet]
  E2: [Complex.norm_deriv_le_of_forall_mem_sphere_norm_le, Differentiable.exists_const_forall_eq_of_bounded, Differentiable.exists_eq_const_of_bounded, Differentiable.apply_eq_of_tendsto_cocompact, Differentiable.isConst_of_isBigO_one, Differentiable.exists_eq_polynomial_eval_of_isBigO_pow, Differentiable.isBigO_pow_iff_exists_eq_polynomial_eval, Complex.isAlgClosed, Irreducible.degree_le_two, Polynomial.mul_star_dvd_of_aeval_eq_zero_im_ne_zero, Polynomial.derivRootWeight, Polynomial.derivRootWeight_nonneg, Polynomial.sum_derivRootWeight_pos]
  E1: auto
families: []
requires: [V19.C01, V19.C02, V17.C03, V17.C07]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Cauchy estimates, Liouville and the fundamental theorem of algebra

### Overview

The Cauchy formula for derivatives bounds $f^{(n)}(c)$ by the maximum of $|f|$ on a circle about $c$, divided by $R^n$. For an entire function the radius $R$ can be arbitrarily large. A bounded entire function is constant (Liouville). An entire function of polynomial growth is a polynomial. A polynomial without roots would give a bounded entire function $1/p$, so every nonconstant complex polynomial has a root. The section ends with a geometric fact about polynomials: the roots of $p'$ lie in the convex hull of the roots of $p$.

The section uses the Cauchy formula for derivatives from Chapter 2, Section 3, and the fact that a function with zero derivative on $\mathbb{C}$ is constant (Volume 17, Chapter 3).

### Definitions

A function $f : \mathbb{C} \to \mathbb{C}$ is *bounded* if $|f(z)| \le M$ for some $M$ and all $z$. It has *polynomial growth of order* $n$ if $|f(z)| \le A + B|z|^n$ for some constants $A, B$ and all $z$.

**Definition (Convex hull).** The *convex hull* of a finite set $S = \{z_1, \dots, z_k\} \subseteq \mathbb{C}$ is the set of sums $\sum_j \lambda_j z_j$ with $\lambda_j \ge 0$ real and $\sum_j \lambda_j = 1$.

::: mathlib
`Bornology.IsBounded` · `Mathlib.Topology.Bornology.Basic`

Mathlib states boundedness of $f$ as `Bornology.IsBounded (Set.range f)`: the image is a bounded set. For growth conditions it uses asymptotic notation along a filter, as in `f =O[Filter.cocompact E] 1` (bounded outside compact sets) or `f =O[Bornology.cobounded ℂ] fun z ↦ z ^ n`. In `ℂ` the two filters agree, because closed bounded sets are compact.

<?decl Bornology.IsBounded?>
:::

### Theorems and proofs

**Theorem (Cauchy estimates).** Let $f$ be continuous on $\bar D(c, R)$, $R > 0$, and holomorphic on $D(c, R)$, with $|f(z)| \le M$ for $|z - c| = R$. Then for every $n \ge 0$,
$$|f^{(n)}(c)| \le \frac{n!\,M}{R^n}.$$

*Proof.* By Chapter 2, Section 3, $f^{(n)}(c) = \frac{n!}{2\pi i}\oint_{C(c,R)} \frac{f(z)}{(z - c)^{n+1}}\,dz$. On the circle, $|f(z)/(z - c)^{n+1}| \le M/R^{n+1}$. The circle has length $2\pi R$. So
$$|f^{(n)}(c)| \le \frac{n!}{2\pi}\cdot 2\pi R\cdot\frac{M}{R^{n+1}} = \frac{n!\,M}{R^n}. \qquad \square$$

::: mathlib
`Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le` · `Mathlib.Analysis.Complex.Liouville`

The statement takes `n : ℕ`, `0 < R`, `DiffContOnCl ℂ f (ball c R)` and `∀ z ∈ sphere c R, ‖f z‖ ≤ C`, and gives `‖iteratedDeriv n f c‖ ≤ n ! * C / R ^ n`. The bound is on the sphere only, which is all the proof uses. The case $n = 1$ is `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le`, with the bound `C / R`; it does not need `E` to be complete.

<?decl Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le?>
:::

**Theorem (Liouville).** A bounded entire function is constant.

*Proof.* Let $|f| \le M$ on $\mathbb{C}$, and let $c \in \mathbb{C}$. For every $R > 0$, the Cauchy estimate with $n = 1$ gives $|f'(c)| \le M/R$. Let $R \to \infty$: $f'(c) = 0$. So $f' = 0$ on $\mathbb{C}$. The plane is convex, so the mean value inequality (Volume 17, Chapter 3) gives $|f(z) - f(w)| \le 0 \cdot |z - w|$ for all $z, w$. $\square$

**Theorem (Polynomial growth).** Let $f$ be entire with $|f(z)| \le A + B|z|^n$ for all $z$. Then $f$ is a polynomial of degree at most $n$.

*Proof.* Let $k > n$. The Cauchy estimate on $C(0, R)$ gives
$$|f^{(k)}(0)| \le \frac{k!\,(A + BR^n)}{R^k} \to 0 \qquad (R \to \infty).$$
So $f^{(k)}(0) = 0$ for $k > n$. By Chapter 2, Section 3, an entire function equals its Taylor series at $0$ on all of $\mathbb{C}$, so $f(z) = \sum_{k \le n} f^{(k)}(0) z^k/k!$. $\square$

::: mathlib
`Differentiable.apply_eq_apply_of_bounded` · `Mathlib.Analysis.Complex.Liouville`

The statement is `Differentiable ℂ f → Bornology.IsBounded (Set.range f) → ∀ z w, f z = f w`, for `f : E → F` between complex normed spaces. The domain may be any complex normed space, not only `ℂ`: Mathlib applies the one-variable case to $t \mapsto f(z + t(w - z))$ on the complex line through $z$ and $w$. The forms `Differentiable.exists_eq_const_of_bounded` and `Differentiable.isConst_of_isBigO_one` give the constant. The growth theorem is `Differentiable.exists_eq_polynomial_eval_of_isBigO_pow`. A related form, `Differentiable.apply_eq_of_tendsto_cocompact`, says that an entire function with a limit $c$ at infinity is the constant $c$.

<?decl Differentiable.apply_eq_apply_of_bounded?>
:::

**Theorem (Fundamental theorem of algebra).** Every polynomial $p \in \mathbb{C}[z]$ of degree $n \ge 1$ has a root in $\mathbb{C}$.

*Proof.* Write $p(z) = a_n z^n + \dots + a_0$ with $a_n \ne 0$, and assume that $p$ has no root. First, $|p(z)| \to \infty$. Indeed, for $|z| \ge 1$,
$$|p(z)| \ge |a_n||z|^n - \sum_{k < n}|a_k||z|^k \ge |z|^n\Big(|a_n| - \frac{1}{|z|}\sum_{k<n}|a_k|\Big).$$
So there is $R_0 \ge 1$ with $|p(z)| \ge |a_n||z|^n/2 \ge |a_n|/2$ for $|z| \ge R_0$. The function $g = 1/p$ is entire, since $p$ has no zero and $1/w$ is holomorphic on $\mathbb{C} \setminus \{0\}$. It is bounded: by $2/|a_n|$ for $|z| \ge R_0$, and on the compact disc $\bar D(0, R_0)$ because it is continuous. By Liouville, $g$ is constant, so $p$ is constant. This contradicts $n \ge 1$, since then $|p(z)| \to \infty$. $\square$

By induction on the degree, $p(z) = a_n\prod_{j=1}^n(z - z_j)$: $\mathbb{C}$ is algebraically closed.

**Corollary (Real polynomials).** An irreducible polynomial in $\mathbb{R}[x]$ has degree $1$ or $2$.

*Proof.* Let $p \in \mathbb{R}[x]$ be irreducible, so $\deg p \ge 1$, and let $z$ be a complex root. Since the coefficients are real, $p(\bar z) = \overline{p(z)} = 0$. If $z$ is real then $x - z$ divides $p$, so $p$ has degree $1$ up to a unit. If not, then $z \ne \bar z$, and $(x - z)(x - \bar z) = x^2 - 2\operatorname{Re}(z)x + |z|^2$ has real coefficients and divides $p$ in $\mathbb{C}[x]$, hence in $\mathbb{R}[x]$ by division with remainder. Then $p$ has degree $2$. $\square$

::: mathlib
`Complex.exists_root` · `Mathlib.Analysis.Complex.Polynomial.Basic`

The statement is `0 < f.degree → ∃ z, f.IsRoot z` for `f : ℂ[X]`. Mathlib proves it with Liouville, as above. The instance `Complex.isAlgClosed : IsAlgClosed ℂ` follows and gives the factorization through the general theory of algebraically closed fields. The corollary is `Irreducible.degree_le_two`, and the quadratic factor is `Polynomial.mul_star_dvd_of_aeval_eq_zero_im_ne_zero`.

<?decl Complex.exists_root?>
:::

**Theorem (Gauss-Lucas).** Let $p \in \mathbb{C}[z]$ have degree at least $1$. Then every root of $p'$ lies in the convex hull of the roots of $p$.

*Proof.* Let $z_1, \dots, z_k$ be the distinct roots, with multiplicities $m_1, \dots, m_k$, so $p = a\prod_j (z - z_j)^{m_j}$. Let $p'(w) = 0$. If $p(w) = 0$, then $w$ is a root of $p$ and lies in the hull. Otherwise, the logarithmic derivative gives
$$0 = \frac{p'(w)}{p(w)} = \sum_{j=1}^k \frac{m_j}{w - z_j} = \sum_{j=1}^k \frac{m_j\,(\bar w - \bar z_j)}{|w - z_j|^2}.$$
Conjugate, and put $\mu_j = m_j/|w - z_j|^2 > 0$: $\sum_j \mu_j (w - z_j) = 0$. So $w = \sum_j \lambda_j z_j$ with $\lambda_j = \mu_j/\sum_i \mu_i$. The $\lambda_j$ are positive and sum to $1$. $\square$

::: mathlib
`Polynomial.rootSet_derivative_subset_convexHull_rootSet` · `Mathlib.Analysis.Complex.Polynomial.GaussLucas`

The statement is `0 < P.degree → (derivative P).rootSet ℂ ⊆ convexHull ℝ (P.rootSet ℂ)`. The convex hull is over `ℝ`, since $\mathbb{C}$ is a real vector space here. The weights of the proof are `Polynomial.derivRootWeight`, with `Polynomial.derivRootWeight_nonneg` and `Polynomial.sum_derivRootWeight_pos`.

<?decl Polynomial.rootSet_derivative_subset_convexHull_rootSet?>
:::

### Examples

**Example.** The function $\sin$ is entire and not constant, so by Liouville it is unbounded on $\mathbb{C}$. Indeed $|\sin(iy)| = |\sinh y| \to \infty$.

**Example.** Let $f$ be entire with $\operatorname{Re} f \le 0$. Then $g = e^f$ is entire with $|g| = e^{\operatorname{Re} f} \le 1$, so $g$ is constant. Then $g' = f' g = 0$ and $g \ne 0$, so $f' = 0$ and $f$ is constant.

**Example.** The Cauchy estimates for $f(z) = e^z$ on $C(0, R)$ give $1 = |f^{(n)}(0)| \le n!\,e^R/R^n$. The right side is smallest at $R = n$, where it equals $n!\,e^n/n^n$. So $n^n \le n!\,e^n$, a weak form of Stirling's formula.

**Example.** For $p(z) = z^3 - 1$, the roots are the cube roots of unity, and $p'(z) = 3z^2$ has the double root $0$. The point $0$ is the centroid of the triangle of roots.

**Example.** For $p(z) = (z - 1)^2(z + 1)$, $p'(z) = (z - 1)(3z + 1)$. The roots of $p'$ are $1$ and $-1/3$, both in the segment $[-1, 1]$. The weights for $w = -1/3$ are $\mu_1 = 2/(16/9) = 9/8$ and $\mu_2 = 1/(4/9) = 9/4$, so $\lambda_1 = 1/3$, $\lambda_2 = 2/3$, and indeed $\tfrac13 \cdot 1 + \tfrac23\cdot(-1) = -1/3$.

### The library around it

Common errors of a learner:

- Using `Differentiable ℂ f` with a bound on `‖f z‖` but no bound in `Set.range f`. Convert with `isBounded_iff_forall_norm_le`.
- Confusing `degree` and `natDegree`. `Complex.exists_root` uses `0 < f.degree`, which excludes the zero polynomial, whose degree is `⊥`.
- Applying Liouville to a function that is holomorphic only on a large disc. It needs the whole plane: $1/(z - 10)$ is bounded on $D(0, 1)$ and not constant.

### Exercises

1. (A) Use the Cauchy estimates to show that $|f'(0)| \le 1$ for $f$ holomorphic on a neighbourhood of $\bar D(0, 1)$ with $|f| \le 1$.
2. (A) Let $f$ be entire with $|f(z)| \le 3|z|^{1/2}$ for $|z| \ge 1$. Show that $f$ is constant.
3. (B) Let $f$ be entire, and let $f(\mathbb{C})$ miss an open disc $D(a, r)$. Show that $f$ is constant. Hint: consider $1/(f - a)$.
4. (B) Let $f$ be entire with $f(z + 1) = f(z)$ and $f(z + i) = f(z)$ for all $z$. Show that $f$ is constant.
5. (B) Let $p$ be a polynomial whose roots all lie in the half-plane $\operatorname{Re} z < 0$. Show that the roots of $p'$ lie there too.
6. (B) Show that every polynomial in $\mathbb{R}[x]$ of odd degree has a real root, using the corollary and induction.
7. (C) Let $f$ be entire with $|f(z)| \le e^{|z|}$. Show that $|f^{(n)}(0)| \le n!\,e^n/n^n$. Deduce that the Taylor coefficients $a_n$ satisfy $|a_n|^{1/n} \le e/n$.

### Notes and history

Gauss gave proofs of the fundamental theorem of algebra, the first in his doctoral dissertation of 1799. The proof by Liouville's theorem came much later. The theorem on the roots of $p'$ is named after Gauss and Lucas.

### Reference

<?reference?>
