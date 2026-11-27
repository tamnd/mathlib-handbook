---
title: Analytic functions are smooth
kind: theory
modules:
  - Mathlib.Analysis.Analytic.ChangeOrigin
  - Mathlib.Analysis.Calculus.FDeriv.Analytic
  - Mathlib.Analysis.Analytic.IteratedFDeriv
explains:
  E3: [FormalMultilinearSeries.changeOrigin, HasFPowerSeriesOnBall.changeOrigin, HasFPowerSeriesOnBall.fderiv, AnalyticAt.contDiffAt]
  E2: [HasFPowerSeriesOnBall.analyticAt_of_mem, HasFPowerSeriesOnBall.analyticOnNhd, isOpen_analyticAt, FormalMultilinearSeries.changeOrigin_radius, HasFPowerSeriesAt.hasStrictFDerivAt, HasFPowerSeriesAt.fderiv_eq, AnalyticAt.fderiv, AnalyticAt.differentiableAt, HasFPowerSeriesOnBall.factorial_smul, HasFPowerSeriesOnBall.hasSum_iteratedFDeriv, HasFPowerSeriesOnBall.iteratedFDeriv_eq_sum, FormalMultilinearSeries.derivSeries, AnalyticOnNhd.iteratedFDeriv]
  E1: auto
families: []
requires: [V17.C04, V17.C05, V15.C04]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Analytic functions are smooth

### Overview

This section proves three facts about a function with a power series expansion on a ball. First, it is analytic at every point of that ball: the series can be re-expanded around any point inside, by the change of origin. Second, its derivative is again analytic, given by an explicit series. Third, it is $C^\infty$, and its coefficients are determined by its derivatives: $k!\,p_k(y^k) = D^k f(x)(y^k)$. The last fact shows that the smooth function $e^{-1/x}$ of Chapter 4 is not analytic.

Throughout, $E$ is a normed space and $F$ a Banach space over $\mathbb{K}$, and $p$ is a formal multilinear series with radius $R = R(p)$.

### Definitions

For $z, w \in E$, $n \ge 0$ and a subset $S \subseteq \{1, \dots, n\}$, let $v_S(z, w) \in E^n$ be the tuple with $w$ in the slots of $S$ and $z$ in the other slots. By multilinearity,
$$p_n\big((z + w)^n\big) = \sum_{S \subseteq \{1, \dots, n\}} p_n\big(v_S(z, w)\big),$$
a sum of $2^n$ terms. The terms with $|S| = k$ are $k$-linear in $w$.

**Definition (Change of origin).** The *change of origin* of $p$ at $z$ is the formal multilinear series $p^{(z)}$ with
$$p^{(z)}_k(w_1, \dots, w_k) = \sum_{n \ge k}\ \sum_{|S| = k} p_n\big(v_S(z; w_1, \dots, w_k)\big),$$
where $v_S(z; w_1, \dots, w_k)$ puts $w_1, \dots, w_k$ in the slots of $S$ in increasing order and $z$ elsewhere.

There are $\binom{n}{k}$ sets $S$ of size $k$, so $\|p^{(z)}_k\| \le \sum_{n \ge k}\binom{n}{k}\|p_n\|\,\|z\|^{n-k}$. This series converges when $\|z\| < R$, as the next proof shows.

::: mathlib
`FormalMultilinearSeries.changeOrigin` · `Mathlib.Analysis.Analytic.ChangeOrigin`

`p.changeOrigin x k = (p.changeOriginSeries k).sum x`. For each `k`, `p.changeOriginSeries k` is itself a formal multilinear series with values in `E [×k]→L[𝕜] F`, whose `l`-th term collects the sets `S` of size `k` in `Fin (k + l)`. The radius bound is `FormalMultilinearSeries.changeOrigin_radius : p.radius - ‖x‖₊ ≤ (p.changeOrigin x).radius`.

<?decl FormalMultilinearSeries.changeOrigin?>
:::

**Definition (Derivative series).** The *derivative series* of $p$ is the formal multilinear series $p'$ from $E$ to $L(E, F)$ with
$$p'_l(z_1, \dots, z_l)(w) = \sum_{j=1}^{l+1} p_{l+1}(z_1, \dots, z_{j-1}, w, z_j, \dots, z_l).$$

On the diagonal, $p'_l(z^l)(w)$ is the sum of the $l + 1$ terms $p_{l+1}(z, \dots, w, \dots, z)$ with $w$ in one slot. This is the part of $p^{(z)}_1(w)$ that comes from $n = l + 1$. The bound $\|p'_l\| \le (l + 1)\|p_{l+1}\|$ is immediate.

### Theorems and proofs

**Theorem (Change of origin).** Let $f$ have the expansion $p$ on $B(x, r)$, and let $\|z\| < r$. Then $f$ has the expansion $p^{(z)}$ on $B(x + z, r - \|z\|)$. In particular, $f$ is analytic at every point of $B(x, r)$, and the set of points where a function is analytic is open.

*Proof.* Let $\|w\| < r - \|z\|$, so $\|z\| + \|w\| < r \le R$. Consider the family of vectors $p_n(v_S(z, w))$ indexed by the pairs $(n, S)$ with $S \subseteq \{1, \dots, n\}$. Its norms satisfy
$$\sum_n \sum_S \|p_n(v_S(z, w))\| \le \sum_n \sum_S \|p_n\|\,\|z\|^{n - |S|}\|w\|^{|S|} = \sum_n \|p_n\|\big(\|z\| + \|w\|\big)^n,$$
by the binomial theorem, and the last sum is finite by Section 1. So the family is absolutely summable in the Banach space $F$, and its sum does not depend on the order or the grouping of the terms.

Group by $n$. The inner sum is $p_n((z + w)^n)$, and $\sum_n p_n((z + w)^n) = f(x + z + w)$ because $\|z + w\| < r$. Group by $k = |S|$ instead. The inner sum is $p^{(z)}_k(w^k)$, and this inner series converges absolutely by the same bound. So
$$f\big((x + z) + w\big) = \sum_k p^{(z)}_k(w^k).$$
For the radius, let $0 \le \rho < r - \|z\|$. The bound on $\|p^{(z)}_k\|$ gives
$$\sum_k \|p^{(z)}_k\|\,\rho^k \le \sum_k \sum_{n \ge k}\binom{n}{k}\|p_n\|\,\|z\|^{n-k}\rho^k = \sum_n \|p_n\|\big(\|z\| + \rho\big)^n < \infty,$$
so $\|p^{(z)}_k\|\rho^k$ is bounded and $\rho \le R(p^{(z)})$. Hence $R(p^{(z)}) \ge r - \|z\|$, and $f$ has the expansion $p^{(z)}$ on the ball. Each point of $B(x, r)$ is a point $x + z$ with $\|z\| < r$. If $f$ is analytic at $x$, it is analytic on a ball around $x$, so the set of such points is open. $\square$

::: mathlib
`HasFPowerSeriesOnBall.changeOrigin` · `Mathlib.Analysis.Analytic.ChangeOrigin`

From `hf : HasFPowerSeriesOnBall f p x r` and `h : (‖y‖₊ : ℝ≥0∞) < r` it gives `HasFPowerSeriesOnBall f (p.changeOrigin y) (x + y) (r - ‖y‖₊)`. The consequences are `HasFPowerSeriesOnBall.analyticAt_of_mem`, analyticity at each point of `Metric.eball x r`, `HasFPowerSeriesOnBall.analyticOnNhd`, and `isOpen_analyticAt 𝕜 f : IsOpen {x | AnalyticAt 𝕜 f x}`.

<?decl HasFPowerSeriesOnBall.changeOrigin?>
:::

**Theorem (The derivative of a power series).** Let $f$ have the expansion $p$ on $B(x, r)$. Then $f$ is differentiable at $x$, with $Df(x) = p_1$. Also, $Df$ has the expansion $p'$ on $B(x, r)$.

*Proof.* Choose $0 < s < r$ with $\|p_n\| s^n \le C$ for all $n$. For $\|y\| \le s/2$,
$$\|f(x + y) - p_0 - p_1(y)\| = \Big\|\sum_{n \ge 2} p_n(y^n)\Big\| \le C\sum_{n \ge 2}\Big(\frac{\|y\|}{s}\Big)^n \le \frac{2C}{s^2}\,\|y\|^2.$$
Since $f(x) = p_0$, this says that $f$ is differentiable at $x$ with $Df(x) = p_1$.

Let $\|z\| < r$. By the change of origin, $f$ has the expansion $p^{(z)}$ at $x + z$, so $Df(x + z) = p^{(z)}_1$ by the first part. The coefficient $p^{(z)}_1(w)$ is the sum over $n \ge 1$ and over the $n$ one-element sets $S = \{j\}$, so
$$Df(x + z)(w) = \sum_{l \ge 0}\ \sum_{j=1}^{l+1} p_{l+1}(z, \dots, z, w, z, \dots, z) = \sum_{l \ge 0} p'_l(z^l)(w).$$
The series converges in $L(E, F)$, which is complete, since $\|p'_l\|\,\|z\|^l \le (l + 1)\|p_{l+1}\|\,\|z\|^l$. This sum is finite by the proof of the change of origin. The same bound shows that $R(p') \ge R(p)$: for $\rho < s < R$, $(l + 1)\|p_{l+1}\|\rho^l \le (C/s)(l + 1)(\rho/s)^l \to 0$. $\square$

::: mathlib
`HasFPowerSeriesOnBall.fderiv` · `Mathlib.Analysis.Calculus.FDeriv.Analytic`

With `[CompleteSpace F]`, from `HasFPowerSeriesOnBall f p x r` it gives `HasFPowerSeriesOnBall (fderiv 𝕜 f) p.derivSeries x r`. The series `FormalMultilinearSeries.derivSeries` is $p'$. The first part of the theorem is `HasFPowerSeriesAt.hasStrictFDerivAt`, with the derivative `continuousMultilinearCurryFin1 𝕜 E F (p 1)`: the equivalence `continuousMultilinearCurryFin1` turns a $1$-linear map into a linear map. `HasFPowerSeriesAt.fderiv_eq` gives `fderiv` itself, and `AnalyticAt.fderiv` says that `fderiv 𝕜 f` is analytic at `x`. Note that the derivative is strict: `AnalyticAt.differentiableAt` is a corollary.

<?decl HasFPowerSeriesOnBall.fderiv?>
:::

**Theorem (Analytic functions are smooth).** If $f$ is analytic at $x$, then $f$ is $C^\infty$ on a neighbourhood of $x$.

*Proof.* The proof is by induction on $k$ of this claim: for every Banach space $G$ and every $g : E \to G$ analytic on an open set $U$, the map $g$ is $C^k$ on $U$. For $k = 0$, $g$ is continuous at each point of $U$ by Section 1. Assume the claim for $k$, and let $g$ be analytic on $U$. By the last theorem, $g$ is differentiable on $U$, and $Dg : E \to L(E, G)$ is analytic on $U$, with values in the Banach space $L(E, G)$. By the hypothesis of induction, $Dg$ is $C^k$ on $U$. By Chapter 4, a map that is differentiable with a $C^k$ derivative is $C^{k+1}$, so $g$ is $C^{k+1}$ on $U$.

Now let $f$ be analytic at $x$. By the change of origin it is analytic on an open ball $U$ around $x$, and so it is $C^k$ on $U$ for every $k$. $\square$

::: mathlib
`AnalyticAt.contDiffAt` · `Mathlib.Analysis.Calculus.ContDiff.Defs`

With `[CompleteSpace F]`, `AnalyticAt 𝕜 f x` gives `ContDiffAt 𝕜 n f x` for every `n : WithTop ℕ∞`. This includes `n = ω`, and in Mathlib `ContDiff 𝕜 ω f` means analytic, so the theorem is a statement about all smoothness classes at once. The induction in Mathlib uses `AnalyticOnNhd.iteratedFDeriv`: all the iterated derivatives of an analytic function are analytic.

<?decl AnalyticAt.contDiffAt?>
:::

**Theorem (The coefficients are the derivatives).** Let $f$ have the expansion $p$ on $B(x, r)$. Then for every $k$ and every $y \in E$
$$k!\,p_k(y^k) = D^k f(x)(y^k).$$
If $\mathbb{K}$ is $\mathbb{R}$ or $\mathbb{C}$, then $f(x + y) = \sum_k \frac{1}{k!}D^k f(x)(y^k)$ for $\|y\| < r$: the Taylor series of $f$ at $x$ converges to $f$ on the ball.

*Proof.* Fix $y \ne 0$ and put $g(t) = f(x + ty)$ for $t \in \mathbb{K}$ with $|t|\,\|y\| < r$. Then $g(t) = \sum_n a_n t^n$ with $a_n = p_n(y^n) \in F$, a power series in one variable. By the last theorem in one variable, $g'(t) = \sum_n (n + 1)a_{n+1}t^n$ near $0$. This is again a power series, and by induction $g^{(k)}(t) = \sum_n \frac{(n + k)!}{n!}a_{n+k}t^n$. At $t = 0$, $g^{(k)}(0) = k!\,a_k$. By Chapter 5, $g^{(k)}(0) = D^k f(x)(y^k)$. The second claim follows by division by $k!$. $\square$

Only the values on the diagonal are determined, as the example of Section 1 requires. The full multilinear map is fixed only after symmetrization: $D^k f(x)(v_1, \dots, v_k) = \sum_{\sigma} p_k(v_{\sigma(1)}, \dots, v_{\sigma(k)})$, the sum over the permutations of $\{1, \dots, k\}$.

::: mathlib
`HasFPowerSeriesOnBall.factorial_smul` · `Mathlib.Analysis.Calculus.FDeriv.Analytic`

With `[CompleteSpace F]`, it gives `n ! • p n (fun _ => y) = iteratedFDeriv 𝕜 n f x (fun _ => y)`. The factorial acts as a natural number, so no division appears. With `[CharZero 𝕜]`, `HasFPowerSeriesOnBall.hasSum_iteratedFDeriv` is the convergence of the Taylor series. The symmetrized formula is `HasFPowerSeriesOnBall.iteratedFDeriv_eq_sum` in `Mathlib.Analysis.Analytic.IteratedFDeriv`.

<?decl HasFPowerSeriesOnBall.factorial_smul?>
:::

### Examples

**Counterexample (A smooth function that is not analytic).** Let $f(x) = e^{-1/x}$ for $x > 0$ and $f(x) = 0$ for $x \le 0$. Chapter 4 proves that $f$ is $C^\infty$ on $\mathbb{R}$. All its derivatives at $0$ are $0$, because $f$ vanishes on $(-\infty, 0]$. If $f$ were analytic at $0$ with an expansion $\sum a_k x^k$, the last theorem would give $a_k = f^{(k)}(0)/k! = 0$ for every $k$, so $f = 0$ on a neighbourhood of $0$. But $f(x) > 0$ for $x > 0$. So $f$ is not analytic at $0$. In Mathlib this function is `expNegInvGlue`, with `expNegInvGlue.contDiff` and `expNegInvGlue.zero_of_nonpos`.

**Example (The derivative of the inverse).** In a Banach algebra $\mathcal{A}$ with $\|1\| = 1$, the map $f(z) = (1 - z)^{-1}$ has the expansion $p_n(z_1, \dots, z_n) = z_1 \cdots z_n$ on $B(0, 1)$. The derivative series gives, for $\|z\| < 1$,
$$Df(z)(w) = \sum_{l \ge 0}\sum_{j=1}^{l+1} z^{j-1}\,w\,z^{l+1-j} = \sum_{a, b \ge 0} z^a\,w\,z^b = (1 - z)^{-1}\,w\,(1 - z)^{-1}.$$
The middle equality puts $a = j - 1$ and $b = l + 1 - j$. Chapter 2 found the derivative of inversion: $D\,\mathrm{Inv}(T)(H) = -T^{-1}HT^{-1}$. With $T = 1 - z$ and $H = -w$, it gives the same answer.

**Example (The exponential).** Let $\exp z = \sum_n z^n/n!$ in a Banach algebra. The derivative series gives
$$D\exp(z)(w) = \sum_{n \ge 1}\frac{1}{n!}\sum_{j=1}^{n} z^{j-1}\,w\,z^{n-j}.$$
If $z$ and $w$ commute, each inner sum is $n z^{n-1}w$, and $D\exp(z)(w) = \exp(z)\,w$. In general they do not, and the formula is not $\exp(z)w$. At $z = 0$ only $n = 1$ contributes, and $D\exp(0) = \mathrm{id}$.

### The library around it

The change of origin is in `Mathlib.Analysis.Analytic.ChangeOrigin`, the derivatives in `Mathlib.Analysis.Calculus.FDeriv.Analytic`, and the formula over permutations in `Mathlib.Analysis.Analytic.IteratedFDeriv`. Most statements need `[CompleteSpace F]`, because the new coefficients are sums of series in a space of multilinear maps.

Common errors of a learner:

- Forgetting completeness. Without `CompleteSpace F` the change of origin is not available, and `AnalyticAt.contDiffAt` does not apply.
- Expecting the radius to stay the same after a change of origin. It can grow, and Mathlib only gives the lower bound $R - \|z\|$.
- Using `factorial_smul` off the diagonal. It is a statement about `fun _ => y`. For general arguments use `iteratedFDeriv_eq_sum`.

### Exercises

1. (A) Use the theorem on the coefficients to compute $D^3 f(0)(y^3)$ for $f(z) = (1 - z)^{-1}$ in a Banach algebra.
2. (A) Show that the change of origin of the geometric series of $\mathbb{K}$ at $z$, $|z| < 1$, has the coefficients $(1 - z)^{-k-1}$, and that its radius is $1 - |z|$ for $0 \le z < 1$ in $\mathbb{R}$.
3. (B) Prove that the derivative series of $p$ has the same radius as $p$ when $E = \mathbb{K}$. Hint: $(l + 1)^{1/l} \to 1$ and Cauchy and Hadamard.
4. (B) Let $\mathbb{K} = \mathbb{R}$, let $f$ have an expansion on $B(x, r)$, and let $D^k f(x) = 0$ for every $k \ge 1$. Show that $f$ is constant on $B(x, r)$.
5. (B) Let $f(x) = \sum_{n \ge 0} e^{-n}\cos(n^2 x)$ on $\mathbb{R}$. Show that $f$ is $C^\infty$, that $|f^{(2k)}(0)| \ge e^{-k}k^{4k}$, and that the Taylor series of $f$ at $0$ has radius $0$. Hint: the series of the derivatives converge uniformly (Chapter 3), and $(2k)! \le (2k)^{2k}$.
6. (C) Let $\mathcal{A}$ be a commutative Banach algebra. Prove $\exp(z + w) = \exp z \exp w$ by the change of origin of the series of $\exp$ at $z$.

### Notes and history

Weierstrass based the theory of functions of a complex variable on power series and on their continuation by the change of origin, which is the first theorem of this section. Cauchy had shown earlier that a smooth function need not be the sum of its Taylor series, with the function $e^{-1/x^2}$.

### Reference

<?reference?>
