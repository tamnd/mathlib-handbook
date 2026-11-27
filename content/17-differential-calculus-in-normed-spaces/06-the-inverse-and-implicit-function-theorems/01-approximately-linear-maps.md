---
title: Approximately linear maps
kind: theory
modules:
  - Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn
explains:
  E3: [ApproximatesLinearOn, ApproximatesLinearOn.surjOn_closedBall_of_nonlinearRightInverse, ApproximatesLinearOn.toOpenPartialHomeomorph]
  E2: [ApproximatesLinearOn.lipschitzWith, ApproximatesLinearOn.antilipschitzWith, ApproximatesLinearOn.injOn, ApproximatesLinearOn.open_image, ApproximatesLinearOn.surjective, ApproximatesLinearOn.toHomeomorph, ApproximatesLinearOn.approximatesLinearOn_iff_lipschitzOnWith]
  E1: auto
families: []
requires: [V17.C01, V17.C02, V17.C03, V13.C03]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Approximately linear maps

### Overview

The inverse function theorem says that a map whose derivative at a point is invertible is invertible near the point. The bridge from one point to a set is this condition on $s$: $f$ differs from a fixed invertible linear map $A$ by a map with a small Lipschitz constant. This section proves that such a map is injective on $s$, open, and onto explicit balls, with a Lipschitz inverse. Section 2 shows that a strictly differentiable map satisfies the condition near the point, and so deduces the inverse function theorem.

Throughout, $E$ and $F$ are normed spaces over $\mathbb{K}$, $A : E \to F$ is a continuous linear equivalence (Volume 16), and
$$N = \|A^{-1}\|$$
is the operator norm of its inverse.

### Definitions

**Definition (Approximately linear map).** Let $f : E \to F$, let $A \in L(E, F)$, let $s \subseteq E$ and let $c \ge 0$. The map $f$ *approximates $A$ on $s$ with the constant $c$* if
$$\|f(x) - f(y) - A(x - y)\| \le c\,\|x - y\| \quad \text{for all } x, y \in s.$$

The condition says that the map $f - A$ is $c$-Lipschitz on $s$, because $(f - A)(x) - (f - A)(y) = f(x) - f(y) - A(x - y)$. An affine map $x \mapsto Ax + b$ has $c = 0$. For a $C^1$ map, the mean value inequality of Chapter 3 gives the condition with $c = \sup_{z \in s}\|Df(z) - A\|$ on a convex set $s$.

::: mathlib
`ApproximatesLinearOn` · `Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn`

`ApproximatesLinearOn f f' s c` is the predicate `∀ x ∈ s, ∀ y ∈ s, ‖f x - f y - f' (x - y)‖ ≤ c * ‖x - y‖`. The linear map `f' : E →L[𝕜] F` need not be invertible in the definition, and the constant `c` is a nonnegative real number of type `ℝ≥0`. The theorem `ApproximatesLinearOn.approximatesLinearOn_iff_lipschitzOnWith` is the remark above: the predicate holds if and only if `f - f'` is `LipschitzOnWith c` on `s`.

<?decl ApproximatesLinearOn?>
:::

### Theorems and proofs

**Theorem (Contraction principle).** Let $X$ be a nonempty complete metric space and $T : X \to X$ a contraction: $d(Tx, Ty) \le K\,d(x,y)$ with $K < 1$. Then $T$ has exactly one fixed point $x^*$, and $d(x, x^*) \le d(x, T x)/(1 - K)$ for each $x \in X$.

*Proof.* Take $x_0 \in X$ and put $x_{n+1} = T x_n$. By induction, $d(x_{n+1}, x_n) \le K^n d(x_1, x_0)$. For $m > n$ the triangle inequality gives
$$d(x_m, x_n) \le \sum_{j=n}^{m-1} K^j d(x_1, x_0) \le \frac{K^n}{1 - K}\, d(x_1, x_0),$$
so $(x_n)$ is a Cauchy sequence. Let $x^*$ be its limit. Since $T$ is continuous, $T x^* = \lim T x_n = \lim x_{n+1} = x^*$. If $T y = y$ also, then $d(x^*, y) = d(T x^*, T y) \le K d(x^*, y)$, and $K < 1$ forces $d(x^*, y) = 0$. Finally $d(x, x^*) \le d(x, T x) + d(T x, T x^*) \le d(x, Tx) + K d(x, x^*)$, which gives the bound. $\square$

::: mathlib
`ContractingWith` · `Mathlib.Topology.MetricSpace.Contracting`

`ContractingWith K f` says `K < 1` and `LipschitzWith K f`. In a nonempty complete metric space, `ContractingWith.fixedPoint K f hf` is the fixed point, with `ContractingWith.fixedPoint_isFixedPt` and the uniqueness `ContractingWith.fixedPoint_unique`.

<?decl ContractingWith.fixedPoint?>
:::

**Theorem (Two-sided Lipschitz bounds).** Let $f$ approximate $A$ on $s$ with the constant $c$. Then for all $x, y \in s$
$$\big(N^{-1} - c\big)\,\|x - y\| \;\le\; \|f(x) - f(y)\| \;\le\; \big(\|A\| + c\big)\,\|x - y\|.$$
If $c < N^{-1}$, then $f$ is injective on $s$.

*Proof.* Write $f(x) - f(y) = A(x - y) + r$ with $\|r\| \le c\|x - y\|$. The upper bound is the triangle inequality and $\|A(x - y)\| \le \|A\|\|x - y\|$. For the lower bound, $\|x - y\| = \|A^{-1}A(x - y)\| \le N\|A(x - y)\|$, so $\|A(x - y)\| \ge N^{-1}\|x - y\|$. So $\|f(x) - f(y)\| \ge (N^{-1} - c)\|x - y\|$. If $c < N^{-1}$ and $f(x) = f(y)$, the lower bound gives $\|x - y\| \le 0$, so $x = y$. $\square$

::: mathlib
`ApproximatesLinearOn.antilipschitzWith` · `Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn`

For `f' : E ≃L[𝕜] F` and the hypothesis `Subsingleton E ∨ c < ‖(f'.symm : F →L[𝕜] E)‖₊⁻¹`, it gives `AntilipschitzWith (N⁻¹ - c)⁻¹` for the restriction of `f` to `s`. The upper bound is `ApproximatesLinearOn.lipschitzWith`, with the constant `‖f'‖₊ + c`, and injectivity is `ApproximatesLinearOn.injOn`. The disjunct `Subsingleton E` covers the space $E = 0$, where $N = 0$.

<?decl ApproximatesLinearOn.antilipschitzWith?>
:::

The next theorem finds a preimage of each point near $f(b)$ as a fixed point of a contraction. The scheme is Newton's method with a frozen derivative: to solve $f(x) = y$, correct $x$ by $A^{-1}(y - f(x))$.

**Theorem (Surjectivity onto a ball).** Let $E$ be a Banach space, let $f$ approximate $A$ on $s$ with the constant $c$, and let $c < N^{-1}$. Let $\varepsilon \ge 0$ and $b \in E$ with $\bar B(b, \varepsilon) \subseteq s$. Then
$$f\big(\bar B(b, \varepsilon)\big) \supseteq \bar B\big(f(b), (N^{-1} - c)\,\varepsilon\big).$$

*Proof.* Fix $y$ with $\|y - f(b)\| \le (N^{-1} - c)\varepsilon$ and define
$$T(x) = x + A^{-1}\big(y - f(x)\big), \qquad x \in \bar B(b, \varepsilon).$$
A point $x$ is a fixed point of $T$ if and only if $A^{-1}(y - f(x)) = 0$, that is, $f(x) = y$, because $A^{-1}$ is injective. For $x, x' \in \bar B(b, \varepsilon)$,
$$T(x) - T(x') = (x - x') - A^{-1}\big(f(x) - f(x')\big) = -A^{-1}\big(f(x) - f(x') - A(x - x')\big),$$
so $\|T(x) - T(x')\| \le N c \|x - x'\|$. Here $K = Nc < 1$, and $T$ sends the ball into itself:
$$\|T(x) - b\| \le \|T(x) - T(b)\| + \|T(b) - b\| \le Nc\,\varepsilon + N\|y - f(b)\| \le Nc\,\varepsilon + N(N^{-1} - c)\varepsilon = \varepsilon.$$
A closed ball of a Banach space is a nonempty complete metric space. The contraction principle gives a fixed point $x \in \bar B(b, \varepsilon)$, and $f(x) = y$. $\square$

::: mathlib
`ApproximatesLinearOn.surjOn_closedBall_of_nonlinearRightInverse` · `Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn`

The conclusion is `SurjOn f (closedBall b ε) (closedBall (f b) ((f'symm.nnNorm⁻¹ - c) * ε))`. The linear map `f'` need only be surjective, and `f'symm : f'.NonlinearRightInverse` is a right inverse that is bounded but not linear. By the open mapping theorem of Volume 16, every surjective continuous linear map between Banach spaces has one. There is no hypothesis on `c`: if `c` is too large, the radius is not positive and the statement says nothing.

<?decl ApproximatesLinearOn.surjOn_closedBall_of_nonlinearRightInverse?>
:::

**Theorem (Open image and Lipschitz inverse).** Let $E$ be a Banach space, $s \subseteq E$ open, and let $f$ approximate $A$ on $s$ with $c < N^{-1}$. Then $f(s)$ is open, $f$ is a bijection of $s$ onto $f(s)$, and the inverse $g : f(s) \to s$ is Lipschitz with the constant $(N^{-1} - c)^{-1}$. So $f$ is a homeomorphism of $s$ onto the open set $f(s)$.

*Proof.* Let $x \in s$. Since $s$ is open, there is $\varepsilon > 0$ with $\bar B(x, \varepsilon) \subseteq s$. By the previous theorem, $f(s)$ contains the ball $\bar B(f(x), (N^{-1} - c)\varepsilon)$, whose radius is positive. So $f(s)$ is a neighbourhood of each of its points, and it is open. The map $f$ is injective on $s$ by the two-sided bounds, so $g$ exists. For $u = f(x)$ and $v = f(y)$ in $f(s)$, the lower bound reads $\|g(u) - g(v)\| = \|x - y\| \le (N^{-1} - c)^{-1}\|u - v\|$. A Lipschitz map is continuous, and $f$ is continuous on $s$ by the upper bound. $\square$

::: mathlib
`ApproximatesLinearOn.toOpenPartialHomeomorph` · `Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn`

From `hf : ApproximatesLinearOn f (f' : E →L[𝕜] F) s c`, the hypothesis on `c` and `IsOpen s`, it builds an `OpenPartialHomeomorph E F` with source `s` and target `f '' s`. The forward map is `f` itself. The openness of the image is `ApproximatesLinearOn.open_image`.

<?decl ApproximatesLinearOn.toOpenPartialHomeomorph?>
:::

**Corollary (Global inversion).** Let $E$ be a Banach space and let $f$ approximate $A$ on all of $E$ with $c < N^{-1}$. Then $f$ is a homeomorphism of $E$ onto $F$, with a Lipschitz inverse.

*Proof.* For each $y \in F$ and $b = 0$, the ball $\bar B(f(0), (N^{-1} - c)\varepsilon)$ contains $y$ for $\varepsilon$ large enough, and it lies in $f(\bar B(0, \varepsilon)) \subseteq f(E)$. So $f$ is surjective. The previous theorem with $s = E$ gives the rest. $\square$

::: mathlib
`ApproximatesLinearOn.toHomeomorph` · `Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn`

With `ApproximatesLinearOn f (f' : E →L[𝕜] F) univ c`, a complete space `E` and the hypothesis on `c`, it gives a `Homeomorph E F` whose forward map is `f`. The surjectivity is `ApproximatesLinearOn.surjective`.

<?decl ApproximatesLinearOn.toHomeomorph?>
:::

### Examples

**Example (A perturbation of the identity on $\mathbb{R}^2$).** Let $f(x, y) = \big(x + \tfrac12 \sin y,\ y + \tfrac12 \sin x\big)$ on $\mathbb{R}^2$ with the Euclidean norm, and $A = I$, so $N = 1$. The map $f - I$ has the derivative $\begin{pmatrix} 0 & \frac12 \cos y \\ \frac12 \cos x & 0 \end{pmatrix}$. This matrix maps $(h, k)$ to $(\frac12 k\cos y, \frac12 h\cos x)$, so its operator norm is at most $\frac12$. The mean value inequality of Chapter 3 shows that $f - I$ is $\frac12$-Lipschitz on $\mathbb{R}^2$. So $f$ approximates $I$ on $\mathbb{R}^2$ with $c = \frac12 < 1 = N^{-1}$. By the corollary, $f$ is a homeomorphism of $\mathbb{R}^2$, and its inverse is $2$-Lipschitz.

**Example (A local inverse in a Banach algebra).** Let $\mathcal{A}$ be a Banach algebra with $\|1\| = 1$ and $f(x) = x + x^2$. On $s = \bar B(0, r)$ with $A = \mathrm{id}$,
$$f(x) - f(y) - (x - y) = x^2 - y^2 = x(x - y) + (x - y)y,$$
an identity that holds without commutativity. So $\|f(x) - f(y) - (x - y)\| \le (\|x\| + \|y\|)\|x - y\| \le 2r\|x - y\|$, and $f$ approximates the identity on $s$ with $c = 2r$. For $r = \frac14$, $c = \frac12$ and $N = 1$. The theorem on balls with $b = 0$ and $\varepsilon = \frac14$ gives
$$f\big(\bar B(0, \tfrac14)\big) \supseteq \bar B\big(0, \tfrac12 \cdot \tfrac14\big) = \bar B(0, \tfrac18).$$
So each $z$ with $\|z\| \le \frac18$ is $x + x^2$ for exactly one $x$ with $\|x\| \le \frac14$.

**Counterexample (The condition $c < N^{-1}$ is sharp).** Let $f(x) = \max(x, 0)$ on $\mathbb{R}$ and $A = 1$, so $N = 1$. Then $f(x) - x = \max(-x, 0)$ is $1$-Lipschitz, and $f$ approximates $A$ on $\mathbb{R}$ with $c = 1 = N^{-1}$. The map $f$ is not injective, and its image $[0, \infty)$ is not open.

### The library around it

The file of this section has two layers. The first layer works with any `f' : E →L[𝕜] F`: `ApproximatesLinearOn.mono_set` and `mono_num` shrink the set and enlarge the constant, `lipschitzWith` and `continuousOn` give regularity, and the surjectivity results take a `NonlinearRightInverse`. The second layer assumes `f' : E ≃L[𝕜] F` and gives `injOn`, `antilipschitzWith`, the partial equivalence `toPartialEquiv`, `toOpenPartialHomeomorph` and `toHomeomorph`. Section 2 obtains the set and the constant at once from `HasStrictFDerivAt.approximates_deriv_on_nhds`.

Common errors of a learner:

- Treating $c$ as small in absolute terms. The condition is $c < \|A^{-1}\|^{-1}$, so a map close to a nearly singular $A$ needs a very small $c$.
- Writing `c * ‖f'.symm‖ < 1` in a Lean statement. The library expects `c < ‖(f'.symm : F →L[𝕜] E)‖₊⁻¹`, often in the form `Subsingleton E ∨ c < ...`.

### Exercises

1. (A) Let $f$ approximate $A$ on $s$ with the constant $c$ and $g$ approximate $B$ on $s$ with the constant $c'$. Show that $f + g$ approximates $A + B$ on $s$ with the constant $c + c'$.
2. (A) Let $f(x) = 2x + \frac12 \arctan x$ on $\mathbb{R}$. Show that $f$ approximates $A = 2$ on $\mathbb{R}$ with $c = \frac12$. Deduce that $f$ is a homeomorphism of $\mathbb{R}$ with a $\frac23$-Lipschitz inverse.
3. (B) In the example in a Banach algebra, show that $f(x) = x + x^2$ approximates the identity on $\bar B(0, r)$ for each $r < \frac12$, and compute the radius of the ball around $0$ that the theorem puts into $f(\bar B(0, r))$. Find the $r$ that makes it largest. Hint: maximize $(1 - 2r)r$.
4. (B) Let $f$ approximate $A$ on an open convex set $s$ with $c < N^{-1}$, and let $f$ be differentiable on $s$. Show that $\|Df(x) - A\| \le c$ for $x \in s$, and deduce that $Df(x)$ is invertible, with $\|Df(x)^{-1}\| \le (N^{-1} - c)^{-1}$. Hint: write $Df(x) = A(I - A^{-1}(A - Df(x)))$ and use the Neumann series of Volume 16.
5. (C) Let $E$ be the space of finitely supported real sequences with the sup norm. Find a contraction $T : \bar B(0, 1) \to \bar B(0, 1)$ without a fixed point. Hint: $T(x) = (\frac12, \frac12 x_1, \frac12 x_2, \dots)$; its fixed point in $\ell^\infty$ has infinite support.

### Notes and history

The contraction principle is due to Banach (1922), and the iteration behind it goes back to Picard's method of successive approximations for differential equations. The use of an approximately linear map as the core of the inverse function theorem is the standard route in Banach spaces, found for example in Dieudonné, *Foundations of Modern Analysis*, Chapter X.

### Reference

<?reference?>
