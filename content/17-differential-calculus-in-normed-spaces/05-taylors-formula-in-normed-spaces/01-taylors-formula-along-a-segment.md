---
title: Taylor's formula along a segment
kind: theory
modules:
  - Mathlib.Analysis.Calculus.Taylor
  - Mathlib.Analysis.Calculus.TaylorIntegral
explains:
  E3: [taylorWithinEval, map_add_eq_sum_add_integral_iteratedFDeriv]
  E2: [taylor_mean_remainder_bound, taylor_integral_remainder, ContDiffAt.deriv_fderiv_add_smul, DifferentiableAt.deriv_comp_add_smul, taylor_isLittleO_univ, taylor_within_apply, exists_taylor_mean_remainder_bound]
  E1: auto
families: []
requires: [V17.C03, V17.C04, V15.C04]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Taylor's formula along a segment

### Overview

Volume 15, Chapter 4 proved Taylor's theorem for a function of one real variable. This section proves it for a map $f : U \to F$ on an open set $U$ of a normed space $E$. The Taylor polynomial of degree $n$ at $x$ is
$$T_n(h) = \sum_{k=0}^{n} \frac{1}{k!} D^k f(x)(h, \dots, h),$$
with the iterated derivatives of Chapter 4. The method is a reduction to one variable: on the segment from $x$ to $x + h$, the curve $g(t) = f(x + th)$ has the derivatives $g^{(k)}(t) = D^k f(x + th)(h, \dots, h)$.

The values of $f$ lie in a normed space, so the mean value theorem with an intermediate point fails (Chapter 3). The section replaces it by a comparison inequality and proves three forms of the remainder: a bound with $(n+1)!$, an integral, and the Peano form $o(\|h\|^n)$.

### Definitions

Write $h^k$ for the $k$-tuple $(h, \dots, h)$, so that $D^k f(x)h^k$ is the value of $D^k f(x)$ on the diagonal. By the definition of the norm of a multilinear map, $\|D^k f(x)h^k\| \le \|D^k f(x)\|\,\|h\|^k$.

**Definition (Taylor polynomial).** Let $f$ be $n$ times differentiable at $x$. The *Taylor polynomial of degree $n$ of $f$ at $x$* is $T_n(h) = \sum_{k=0}^n \frac{1}{k!} D^k f(x)h^k$, and the *remainder* is $R_n(h) = f(x + h) - T_n(h)$.

Each term $h \mapsto D^k f(x)h^k$ is a homogeneous polynomial of degree $k$ in $h$. For $E = \mathbb{R}^d$ it is $\sum_{i_1, \dots, i_k} \partial_{i_1} \cdots \partial_{i_k} f(x)\, h_{i_1} \cdots h_{i_k}$. For $E = \mathbb{R}$ it is $f^{(k)}(x)h^k$, and $T_n$ is the Taylor polynomial of Volume 15.

::: mathlib
`taylorWithinEval` · `Mathlib.Analysis.Calculus.Taylor`

Mathlib has the Taylor polynomial only in one variable, but with values in any real normed space: for `f : ℝ → E`, `taylorWithinEval f n s x₀ x` is the Taylor polynomial of degree `n` at `x₀`, built from the derivatives within the set `s`, evaluated at `x`. The lemma `taylor_within_apply` unfolds it to `∑ k ∈ Finset.range (n + 1), ((k ! : ℝ)⁻¹ * (x - x₀) ^ k) • iteratedDerivWithin k f s x₀`. The set `s` is often `Set.Icc a b`, so that the theorem applies to a function that is smooth only on a closed interval.

<?decl taylorWithinEval?>
<?decl taylor_within_apply?>
:::

### Theorems and proofs

**Lemma (Derivatives along a segment).** Let $f$ be $C^m$ on $U$, let $x \in U$, $h \in E$, and let $g(t) = f(x + th)$ on the open set $I = \{t \in \mathbb{R} : x + th \in U\}$. Then $g$ is $C^m$ on $I$ and $g^{(k)}(t) = D^k f(x + th)h^k$ for $k \le m$.

*Proof.* Induction on $k$. For $k = 0$ this is the definition of $g$. Assume it for $k < m$. Let $\mathrm{ev}_h : L^k(E; F) \to F$ be the evaluation $A \mapsto A h^k$. It is continuous linear. So $g^{(k)} = \mathrm{ev}_h \circ D^k f \circ \gamma$ with $\gamma(t) = x + th$. Since $D^k f$ is differentiable, the chain rule gives
$$g^{(k+1)}(t) = \mathrm{ev}_h\big(D(D^k f)(x + th)\,h\big) = \big(D(D^k f)(x + th)\,h\big)(h, \dots, h) = D^{k+1} f(x + th)h^{k+1},$$
by the definition of $D^{k+1} f$ in Chapter 4. Continuity of $g^{(k)}$ follows from that of $D^k f$. $\square$

**Lemma (Comparison).** Let $G : [0, 1] \to F$ and $\varphi : [0, 1] \to \mathbb{R}$ be continuous, differentiable on $(0, 1)$, with $\|G'(t)\| \le \varphi'(t)$ for $0 < t < 1$. Then $\|G(1) - G(0)\| \le \varphi(1) - \varphi(0)$.

*Proof.* View $F$ as a real normed space. By the Hahn-Banach theorem (Volume 16) there is a continuous linear $\ell : F \to \mathbb{R}$ with $\|\ell\| \le 1$ and $\ell(G(1) - G(0)) = \|G(1) - G(0)\|$. Let $u(t) = \ell(G(t)) - \varphi(t)$. It is continuous on $[0, 1]$, differentiable on $(0, 1)$, and
$$u'(t) = \ell(G'(t)) - \varphi'(t) \le \|G'(t)\| - \varphi'(t) \le 0.$$
By the mean value theorem of Volume 15, Chapter 3, $u(1) \le u(0)$, that is, $\|G(1) - G(0)\| - \varphi(1) + \varphi(0) \le 0$. $\square$

With $\varphi(t) = Ct$ this is the mean value inequality of Chapter 3.

**Theorem (Taylor's formula with a bound on the remainder).** Let $f$ be $C^{n+1}$ on $U$ and let the segment $[x, x + h]$ lie in $U$. Put $M = \sup_{0 \le t \le 1} \|D^{n+1} f(x + th)h^{n+1}\|$. Then
$$\Big\|f(x + h) - \sum_{k=0}^{n} \frac{1}{k!} D^k f(x)h^k\Big\| \le \frac{M}{(n+1)!} \le \frac{\|h\|^{n+1}}{(n+1)!}\sup_{y \in [x, x+h]} \|D^{n+1} f(y)\|.$$

*Proof.* The set $I$ of the first lemma is open and contains $[0, 1]$, and $g$ is $C^{n+1}$ on $I$. Let
$$G(t) = \sum_{k=0}^{n} \frac{(1 - t)^k}{k!}\, g^{(k)}(t).$$
Then $G(1) = g(1) = f(x + h)$ and $G(0) = \sum_k g^{(k)}(0)/k! = T_n(h)$. Differentiate each term with the product rule:
$$\frac{d}{dt}\Big(\frac{(1 - t)^k}{k!}g^{(k)}(t)\Big) = \frac{(1 - t)^k}{k!}g^{(k+1)}(t) - \frac{(1 - t)^{k-1}}{(k-1)!}g^{(k)}(t),$$
where the second term is absent for $k = 0$. The sum over $k = 0, \dots, n$ telescopes:
$$G'(t) = \frac{(1 - t)^n}{n!}\, g^{(n+1)}(t).$$
So $\|G'(t)\| \le M(1 - t)^n/n! = \varphi'(t)$ with $\varphi(t) = -M(1 - t)^{n+1}/(n+1)!$. The comparison lemma gives $\|G(1) - G(0)\| \le \varphi(1) - \varphi(0) = M/(n+1)!$. The second inequality is $\|D^{n+1}f(y)h^{n+1}\| \le \|D^{n+1} f(y)\|\,\|h\|^{n+1}$. $\square$

The same function $G$ gives the integral form. It needs the integral of a continuous curve in a Banach space and the fundamental theorem of calculus $G(1) - G(0) = \int_0^1 G'(t)\,dt$ for a $C^1$ curve, which Volume 18 proves.

**Theorem (Integral remainder).** Let $F$ be a Banach space, $f$ of class $C^{n+1}$ on $U$ and $[x, x + h] \subseteq U$. Then
$$f(x + h) = \sum_{k=0}^{n} \frac{1}{k!} D^k f(x)h^k + \frac{1}{n!}\int_0^1 (1 - t)^n\, D^{n+1} f(x + th)h^{n+1}\,dt.$$

*Proof.* Apply the fundamental theorem of calculus to $G$ and insert the formula for $G'$ and the first lemma. $\square$

**Theorem (Peano form).** Let $n \ge 1$ and let $f$ be $C^n$ on a ball $B(x, r) \subseteq U$. Then
$$f(x + h) = \sum_{k=0}^{n} \frac{1}{k!} D^k f(x)h^k + o(\|h\|^n) \quad (h \to 0).$$

*Proof.* Let $\|h\| < r$ and $g(t) = f(x + th)$. Let $G_{n-1}(t) = \sum_{k=0}^{n-1} \frac{(1-t)^k}{k!}g^{(k)}(t)$ be the function of the proof above for $n - 1$, so $G_{n-1}'(t) = \frac{(1-t)^{n-1}}{(n-1)!}g^{(n)}(t)$, and let $K(t) = -\frac{(1-t)^n}{n!}D^n f(x)h^n$, so $K'(t) = \frac{(1-t)^{n-1}}{(n-1)!}D^n f(x)h^n$ and $K(1) - K(0) = \frac{1}{n!}D^n f(x)h^n$. Then
$$R_n(h) = \big(G_{n-1}(1) - G_{n-1}(0)\big) - \big(K(1) - K(0)\big),$$
and
$$\big\|(G_{n-1} - K)'(t)\big\| = \frac{(1-t)^{n-1}}{(n-1)!}\big\|\big(D^n f(x + th) - D^n f(x)\big)h^n\big\| \le \frac{(1-t)^{n-1}}{(n-1)!}\,\varepsilon(h)\,\|h\|^n,$$
where $\varepsilon(h) = \sup_{\|y - x\| \le \|h\|}\|D^n f(y) - D^n f(x)\|$. The comparison lemma with $\varphi(t) = -(1-t)^n\varepsilon(h)\|h\|^n/n!$ gives $\|R_n(h)\| \le \varepsilon(h)\|h\|^n/n!$. Since $D^n f$ is continuous at $x$, $\varepsilon(h) \to 0$ as $h \to 0$. $\square$

::: mathlib
`map_add_eq_sum_add_integral_iteratedFDeriv` · `Mathlib.Analysis.Calculus.TaylorIntegral`

This is the integral remainder in normed spaces. With `[CompleteSpace F]` and the hypothesis `∀ t ∈ Set.Icc 0 1, ContDiffAt ℝ (n + 1) f (x + t • y)`, it states `f (x + y) = ∑ k ∈ Finset.range (n + 1), (k ! : ℝ)⁻¹ • iteratedFDeriv ℝ k f x (fun _ ↦ y) + (n ! : ℝ)⁻¹ • ∫ t in 0..1, (1 - t) ^ n • iteratedFDeriv ℝ (n + 1) f (x + t • y) (fun _ ↦ y)`. The diagonal $h^k$ is `fun _ ↦ y`. The first lemma of the section is `ContDiffAt.deriv_fderiv_add_smul`, with the case $k = 0$ `DifferentiableAt.deriv_comp_add_smul : deriv (fun s ↦ f (x + s • y)) t = fderiv 𝕜 f (x + t • y) y`.

<?decl map_add_eq_sum_add_integral_iteratedFDeriv?>
<?decl ContDiffAt.deriv_fderiv_add_smul?>
:::

::: mathlib
`taylor_mean_remainder_bound` · `Mathlib.Analysis.Calculus.Taylor`

For `f : ℝ → E` of class $C^{n+1}$ on `Icc a b` and a bound `C` on `iteratedDerivWithin (n + 1) f (Icc a b)`, it gives `‖f x - taylorWithinEval f n (Icc a b) a x‖ ≤ C * (x - a) ^ (n + 1) / n !`. The constant is $1/n!$, weaker than the $1/(n+1)!$ above. The existence form is `exists_taylor_mean_remainder_bound`. The integral form in one variable is `taylor_integral_remainder`, and the Peano form `taylor_isLittleO_univ` for `ContDiff ℝ n f`.

<?decl taylor_mean_remainder_bound?>
<?decl taylor_integral_remainder?>
<?decl taylor_isLittleO_univ?>
:::

The index of this edition has no declaration for the bound with $(n+1)!$ in several variables, and none for the Peano form for maps on a normed space $E$.

### Examples

**Example ($e^x \cos y$ at $0$).** Let $f(x, y) = e^x\cos y$. Its derivatives at $0$ up to order $2$ are $f = 1$, $\partial_x f = 1$, $\partial_y f = 0$, $\partial_x^2 f = 1$, $\partial_x\partial_y f = 0$, $\partial_y^2 f = -1$. So $T_2(h) = 1 + h_1 + \frac12(h_1^2 - h_2^2)$. Since $f = \operatorname{Re} e^{x + iy}$, $D^3 f(p)h^3 = \operatorname{Re}\big(e^{p_1 + ip_2}(h_1 + ih_2)^3\big)$, so $|D^3 f(p)h^3| \le e^{p_1}|h|^3$ with the Euclidean norm. For $h = (0.1, 0.1)$ the theorem gives $|R_2(h)| \le e^{0.1}(0.02)^{3/2}/6 \approx 0.00052$. The true values are $f(h) = 1.0996497$ and $T_2(h) = 1.1$, so $R_2(h) \approx -0.00035$.

**Example (A cube in a Banach algebra).** Let $f(a) = a^3$ in a Banach algebra $\mathbb{A}$. Expanding the product,
$$(a + h)^3 = a^3 + (a^2h + aha + ha^2) + (ah^2 + hah + h^2a) + h^3.$$
The terms of degree $k$ in $h$ are $\frac{1}{k!}D^k f(a)h^k$, so the Taylor formula of degree $3$ is exact, and $R_2(h) = h^3$. The order of the factors stays: $D f(a)h = a^2h + aha + ha^2$ is $3a^2h$ only when $a$ and $h$ commute.

**Example (Inversion at $1$).** In a Banach algebra let $\iota(a) = a^{-1}$, which is $C^\infty$ near $1$ by Chapter 4. For $\|h\| < 1$ the Neumann series gives $(1 + h)^{-1} = \sum_{k \ge 0}(-h)^k$. Comparing with Taylor's formula (Exercise 4), $\frac{1}{k!}D^k\iota(1)h^k = (-h)^k$, and $R_n(h) = \sum_{k > n}(-h)^k$, with $\|R_n(h)\| \le \|h\|^{n+1}/(1 - \|h\|)$.

### The library around it

The file `Mathlib.Analysis.Calculus.Taylor` works with one real variable and values in a normed space. It lists the generalization to higher dimensions as future work. The file `Mathlib.Analysis.Calculus.TaylorIntegral` provides the reduction to the segment and the integral formula in several variables. To get a bound in several variables from it, estimate the integral with the norm of the integrand.

Common errors of a learner:

- Writing $D^k f(x)h^k$ as $(Df(x)h)^k$. For $k \ge 2$ these are different objects, and the second is not defined for $F$ a general space.
- Forgetting the factor $(n !)^{-1}$ in front of the integral, or using $(n+1)!$ there.
- Expecting an intermediate point $\xi$ with $R_n(h) = \frac{1}{(n+1)!}D^{n+1}f(\xi)h^{n+1}$ for vector values. It exists when $F = \mathbb{R}$, by Volume 15 applied to $g$, and fails in general: $e^{it}$ on $[0, 2\pi]$.

### Exercises

1. (A) Compute $T_2$ at $0$ for $f(x, y) = e^{xy} + \cos x$.
2. (A) Let $U$ be convex and open, and let $D^{n+1} f = 0$ on $U$. Show that $f(x + h) = T_n(h)$ for $x, x + h \in U$.
3. (B) Let $f$ be $C^3$ on a convex open set $U$ with $\|D^3 f\| \le M$. Show that $\|Df(x + h) - Df(x) - D^2f(x)h\| \le \frac{M}{2}\|h\|^2$. Hint: apply the theorem to $Df$.
4. (B) Show that $D^k\iota(1)h^k = (-1)^k k!\,h^k$ for the inversion $\iota$ of a Banach algebra. Hint: compare the Peano form with the Neumann series, and use that a homogeneous polynomial of degree $k$ that is $o(\|h\|^k)$ is $0$.
5. (B) Let $H$ be a real Hilbert space and $f(x) = \|x\|^4$. Expand $\|x + h\|^4 = (\|x\|^2 + 2\langle x, h\rangle + \|h\|^2)^2$ and read off $D^k f(x)h^k$ for $k = 1, \dots, 4$.
6. (C) Let $f$ be $C^2$ on a real Hilbert space $H$, with $f \ge 0$ and $\|D^2 f\| \le M$, $M > 0$. Show that $\|\nabla f(x)\|^2 \le 2M f(x)$. Hint: apply the theorem with $n = 1$ and $h = -\nabla f(x)/M$.

### Notes and history

Brook Taylor published the series that has his name in 1715, and Lagrange gave the remainder with an intermediate point. The form with the multilinear maps $D^k f(x)$ and the integral remainder is the one of the books on calculus in Banach spaces, for example Dieudonné, *Foundations of Modern Analysis*, Chapter VIII. The comparison lemma with a general $\varphi$ is also there, as a form of the mean value theorem.

### Reference

<?reference?>
