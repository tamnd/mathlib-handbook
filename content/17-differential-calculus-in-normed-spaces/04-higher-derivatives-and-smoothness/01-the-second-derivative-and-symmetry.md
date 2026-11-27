---
title: The second derivative and its symmetry
kind: theory
modules:
  - Mathlib.Analysis.Calculus.FDeriv.Symmetric
explains:
  E3: [second_derivative_symmetric, IsSymmSndFDerivAt]
  E2: [second_derivative_symmetric_of_eventually, ContDiffAt.isSymmSndFDerivAt, Convex.second_derivative_within_at_symmetric, Convex.taylor_approx_two_segment, minSmoothness]
  E1: auto
families: []
requires: [V17.C01, V17.C02, V17.C03]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The second derivative and its symmetry

### Overview

The derivative of a map $f : U \to F$ is again a map, $Df : U \to L(E, F)$, with values in a normed space. So $Df$ can have a derivative, and this derivative is the second derivative $D^2 f(x)$. It is a continuous linear map from $E$ to $L(E, F)$, that is, a continuous bilinear map $E \times E \to F$. In $\mathbb{R}^n$ its matrix is the Hessian, the matrix of the second partial derivatives.

The main theorem is the symmetry of the second derivative, the theorem of Schwarz: $D^2 f(x)(v, w) = D^2 f(x)(w, v)$, or $\partial_i \partial_j f = \partial_j \partial_i f$. The section proves it under the hypothesis of Mathlib: $f$ is differentiable near $x$, and $Df$ is differentiable at $x$. A classical example shows that the order of the partial derivatives matters when the hypothesis fails.

### Definitions

Let $E, F$ be normed spaces over $\mathbb{K}$, let $U \subseteq E$ be open, and let $f : U \to F$ be differentiable on $U$.

**Definition (Second derivative).** The map $f$ is *twice differentiable at $x \in U$* if the map $Df : U \to L(E, F)$ is differentiable at $x$. Its derivative
$$D^2 f(x) = D(Df)(x) \in L(E, L(E, F))$$
is the *second derivative* of $f$ at $x$. For $v, w \in E$ write $D^2 f(x)(v, w)$ for $D^2 f(x)(v)(w) \in F$.

The space $L(E, L(E, F))$ is isometric to the space $L^2(E; F)$ of continuous bilinear maps $E \times E \to F$, by $B \mapsto ((v, w) \mapsto B(v)(w))$. Volume 16 proves this.

**Lemma (The second derivative as an iterated directional derivative).** Let $f$ be twice differentiable at $x$. Then for all $v, w \in E$,
$$D^2 f(x)(v, w) = \frac{d}{ds}\Big|_{s=0} \big( Df(x + sv)\, w \big), \qquad Df(y)\,w = \frac{d}{dt}\Big|_{t=0} f(y + tw).$$

*Proof.* The second formula is the chain rule of Chapter 2 for $t \mapsto f(y + tw)$, with the derivative $w$ of $t \mapsto y + tw$. For the first, the evaluation $\mathrm{ev}_w : L(E, F) \to F$, $A \mapsto A w$, is linear with $\|A w\| \le \|A\|\,\|w\|$, so it is continuous linear and is its own derivative. The map $s \mapsto Df(x + sv)\,w$ is $\mathrm{ev}_w \circ Df \circ (s \mapsto x + sv)$. The chain rule gives the derivative $\mathrm{ev}_w(D(Df)(x)\, v) = D^2 f(x)(v)(w)$ at $s = 0$. $\square$

**Definition (Hessian).** Let $E = \mathbb{R}^n$ with the standard basis $e_1, \dots, e_n$, and $F = \mathbb{R}$. Write $\partial_i \partial_j f$ for $\partial_i(\partial_j f)$. The *Hessian* of $f$ at $x$ is the $n \times n$ matrix $H_f(x) = (\partial_i \partial_j f(x))_{i,j}$.

By the lemma, $D^2 f(x)(e_i, e_j) = \partial_i \partial_j f(x)$. Bilinearity gives, for $v = \sum v_i e_i$ and $w = \sum w_j e_j$,
$$D^2 f(x)(v, w) = \sum_{i, j} v_i w_j\, \partial_i \partial_j f(x) = v^{\mathsf T} H_f(x)\, w.$$

::: mathlib
`IsSymmSndFDerivAt` · `Mathlib.Analysis.Calculus.FDeriv.Symmetric`

Mathlib has no separate name for the second derivative. It is `fderiv 𝕜 (fderiv 𝕜 f) x`, a term of `E →L[𝕜] E →L[𝕜] F`, and `fderiv 𝕜 (fderiv 𝕜 f) x v w` is $D^2 f(x)(v, w)$ in the order of this section. The predicate `IsSymmSndFDerivAt 𝕜 f x` says that this term is symmetric: `∀ v w, fderiv 𝕜 (fderiv 𝕜 f) x v w = fderiv 𝕜 (fderiv 𝕜 f) x w v`. Because `fderiv` has the junk value $0$, the predicate is true, with no content, where $Df$ is not differentiable.

<?decl IsSymmSndFDerivAt?>
:::

### Theorems and proofs

**Theorem (Schwarz).** Let $E, F$ be real normed spaces, $U \subseteq E$ open, $x \in U$, and let $f : U \to F$ be differentiable on $U$ with $Df$ differentiable at $x$. Then for all $v, w \in E$,
$$D^2 f(x)(v, w) = D^2 f(x)(w, v).$$

*Proof.* The plan: the second difference
$$\Delta(t) = f(x + tv + tw) - f(x + tv) - f(x + tw) + f(x)$$
is symmetric in $v$ and $w$. Step 1 shows that $\Delta(t) = t^2 B(v)(w) + o(t^2)$ as $t \to 0^+$, where $B = D^2 f(x)$. Exchanging $v$ and $w$ gives $\Delta(t) = t^2 B(w)(v) + o(t^2)$, and Step 2 compares the two expansions.

Step 1. Fix $v, w$ and let $\varepsilon > 0$. Since $Df$ is differentiable at $x$ with derivative $B$, there is $\delta > 0$ with $B(x, \delta) \subseteq U$ and
$$\|Df(y) - Df(x) - B(y - x)\| \le \varepsilon \|y - x\| \quad \text{for } \|y - x\| < \delta.$$
Let $t > 0$ with $t(\|v\| + \|w\|) < \delta$. For $s \in [0, t]$ put $g(s) = f(x + tv + sw) - f(x + sw)$. The points $y_1 = x + tv + sw$ and $y_2 = x + sw$ have $\|y_i - x\| \le t(\|v\| + \|w\|) < \delta$, so they lie in $U$. By the chain rule $g$ is differentiable on $[0, t]$ with
$$g'(s) = Df(y_1)\,w - Df(y_2)\,w.$$
Write $Df(y_i) = Df(x) + B(y_i - x) + \rho_i$ with $\|\rho_i\| \le \varepsilon \|y_i - x\|$. Since $y_1 - y_2 = tv$ and $B$ is linear,
$$g'(s) = t\, B(v)(w) + \rho_1 w - \rho_2 w, \qquad \|\rho_1 w - \rho_2 w\| \le 2 \varepsilon t (\|v\| + \|w\|)\, \|w\|.$$
Put $k(s) = g(s) - s\, t\, B(v)(w)$. Then $\|k'(s)\| \le 2 \varepsilon t (\|v\| + \|w\|) \|w\|$ on $[0, t]$. The mean value inequality of Chapter 3 gives $\|k(t) - k(0)\| \le 2 \varepsilon t^2 (\|v\| + \|w\|)\|w\|$. Now $g(t) - g(0) = \Delta(t)$, so $k(t) - k(0) = \Delta(t) - t^2 B(v)(w)$, and
$$\|\Delta(t) - t^2 B(v)(w)\| \le 2 \varepsilon t^2 (\|v\| + \|w\|)\, \|w\|.$$

Step 2. The expression $\Delta(t)$ does not change when $v$ and $w$ are exchanged. So Step 1 with $v$ and $w$ exchanged gives $\|\Delta(t) - t^2 B(w)(v)\| \le 2 \varepsilon t^2 (\|v\| + \|w\|) \|v\|$ for the same small $t$. The triangle inequality gives
$$t^2 \|B(v)(w) - B(w)(v)\| \le 2 \varepsilon t^2 (\|v\| + \|w\|)^2.$$
Divide by $t^2 > 0$. The bound $\|B(v)(w) - B(w)(v)\| \le 2 \varepsilon (\|v\| + \|w\|)^2$ holds for every $\varepsilon > 0$, so $B(v)(w) = B(w)(v)$. $\square$

The proof needs $D^2 f$ only at $x$, and $Df$ near $x$, because $g'$ must exist on $[0, t]$.

::: mathlib
`second_derivative_symmetric` · `Mathlib.Analysis.Calculus.FDeriv.Symmetric`

The hypotheses are `∀ y, HasFDerivAt f (f' y) y` and `HasFDerivAt f' f'' x`; the conclusion is `f'' v w = f'' w v`. The field is any `𝕜` with `[IsRCLikeNormedField 𝕜]`, that is $\mathbb{R}$ or $\mathbb{C}$. The local form `second_derivative_symmetric_of_eventually` asks for `∀ᶠ y in 𝓝 x, HasFDerivAt f (f' y) y`; it is the theorem of this section. `Convex.second_derivative_within_at_symmetric` is the form within a convex set with nonempty interior. The Mathlib proof is the proof above: `Convex.taylor_approx_two_segment` is Step 1, written with `=o[𝓝[>] 0]`.

<?decl second_derivative_symmetric?>
<?decl second_derivative_symmetric_of_eventually?>
:::

**Corollary (Symmetry of $C^2$ maps).** If $Df$ exists on $U$ and is differentiable on $U$, then $D^2 f(x)$ is symmetric at every $x \in U$. In particular, if $f : U \subseteq \mathbb{R}^n \to \mathbb{R}$ has continuous second partial derivatives on $U$, then $\partial_i \partial_j f = \partial_j \partial_i f$ on $U$, and the Hessian is a symmetric matrix.

*Proof.* The first claim is the theorem at each point. For the second, each $\partial_j f$ has continuous partial derivatives, so it is differentiable by the theorem of Chapter 1, Section 2, and so continuous. The same theorem shows that $f$ is differentiable, and the coordinates $y \mapsto Df(y)e_j = \partial_j f(y)$ of $Df$ are differentiable. So $Df$ is differentiable on $U$, and $D^2 f(x)(e_i, e_j) = \partial_i \partial_j f(x)$ gives the result. $\square$

::: mathlib
`ContDiffAt.isSymmSndFDerivAt` · `Mathlib.Analysis.Calculus.FDeriv.Symmetric`

`ContDiffAt 𝕜 n f x → minSmoothness 𝕜 2 ≤ n → IsSymmSndFDerivAt 𝕜 f x`. The function `minSmoothness 𝕜 n` is `n` over $\mathbb{R}$ or $\mathbb{C}$ and `ω` (analytic) over other fields, such as the $p$-adic numbers, where the proof by the mean value inequality is not available.

<?decl ContDiffAt.isSymmSndFDerivAt?>
:::

### Examples

**Example (A Hessian).** Let $f(x, y) = x^3 y + y^2$ on $\mathbb{R}^2$. Then $\partial_x f = 3x^2 y$ and $\partial_y f = x^3 + 2y$. The second partial derivatives are
$$\partial_x \partial_x f = 6xy, \quad \partial_x \partial_y f = 3x^2, \quad \partial_y \partial_x f = 3x^2, \quad \partial_y \partial_y f = 2.$$
The two mixed derivatives agree, as the corollary predicts. At $(1, 2)$ the Hessian is $\begin{pmatrix} 12 & 3 \\ 3 & 2 \end{pmatrix}$, and $D^2 f(1, 2)(v, w) = 12 v_1 w_1 + 3 (v_1 w_2 + v_2 w_1) + 2 v_2 w_2$.

**Example (The square in a Banach algebra).** Let $A$ be a Banach algebra, not necessarily commutative, and $f(X) = X^2$. Chapter 2 computed $Df(X)H = XH + HX$. So $Df(X) = L_X + R_X$, where $L_X H = XH$ and $R_X H = HX$. The map $X \mapsto L_X + R_X$ is continuous linear, so it is its own derivative: $D(Df)(X)K = L_K + R_K$. Hence
$$D^2 f(X)(K, H) = KH + HK.$$
This is symmetric in $H$ and $K$, although $HK \neq KH$ in general.

**Counterexample (The order of partial derivatives matters).** Let
$$f(x, y) = \frac{xy(x^2 - y^2)}{x^2 + y^2} \text{ for } (x, y) \neq 0, \qquad f(0, 0) = 0.$$
For $(x, y) \neq 0$ the quotient rule gives
$$\partial_x f(x, y) = \frac{y(x^4 + 4x^2y^2 - y^4)}{(x^2 + y^2)^2}.$$
At $(0, y)$ with $y \neq 0$ this is $y \cdot (-y^4)/y^4 = -y$. At the origin, $f(h, 0) = 0$ for all $h$, so $\partial_x f(0, 0) = 0$. So $\partial_x f(0, y) = -y$ for all $y$, and $\partial_y \partial_x f(0, 0) = -1$. Since $f(y, x) = -f(x, y)$, the same computation gives $\partial_y f(x, 0) = x$ for all $x$, so $\partial_x \partial_y f(0, 0) = 1$. The mixed partial derivatives at $0$ are $1$ and $-1$.

The map $f$ is of class $C^1$: the numerator of $\partial_x f$ has $|x^4 + 4x^2y^2 - y^4| \le 2(x^2 + y^2)^2$, so $|\partial_x f(x, y)| \le 2|y| \to 0$, and the same holds for $\partial_y f$. By the theorem of Schwarz, $Df$ is not differentiable at $0$, although all four second partial derivatives exist there. They are not continuous at $0$.

### The library around it

The file `Mathlib.Analysis.Calculus.FDeriv.Symmetric` states the theorem with `HasFDerivAt`, with `fderiv` through `IsSymmSndFDerivAt`, and within a convex set. The link to the iterated derivative of Section 2 is `isSymmSndFDerivAt_iff_iteratedFDeriv`: the symmetry of `fderiv 𝕜 (fderiv 𝕜 f) x` is the invariance of `iteratedFDeriv 𝕜 2 f x` under the swap of its two arguments.

Common errors of a learner:

- Reading `fderiv ℝ (fderiv ℝ f) x v w` as $\partial_w \partial_v f$. The first argument `v` is the direction of the outer derivative: the term is $\partial_v \partial_w f$.
- Expecting the symmetry of the Hessian from the existence of the second partial derivatives alone. The counterexample has all of them.
- Forgetting the side goal `minSmoothness ℝ 2 ≤ n`. Over $\mathbb{R}$ it simplifies with `minSmoothness_of_isRCLikeNormedField`.

### Exercises

1. (A) Compute the Hessian of $f(x, y, z) = xyz + x^2 z$ at $(1, 1, 1)$ and check that it is symmetric.
2. (A) Let $H$ be a real Hilbert space and $f(x) = \|x\|^2$. Show that $D^2 f(x)(v, w) = 2\langle v, w \rangle$ for every $x$. Hint: Chapter 1 computed $Df(x)h = 2\langle x, h\rangle$.
3. (B) Show that no function $f$ of class $C^2$ on $\mathbb{R}^2$ has $\partial_x f = y$ and $\partial_y f = -x$. Find all $C^2$ functions with $\partial_x f = y$ and $\partial_y f = x$.
4. (B) Let $A$ be a Banach algebra and $f(X) = X^3$. Compute $Df(X)$ and $D^2 f(X)(K, H)$, and check that the result is symmetric in $H$ and $K$.
5. (B) Let $f$ satisfy the hypotheses of the theorem. Show that $\Delta(t)/t^2 \to D^2 f(x)(v, w)$ as $t \to 0^+$.
6. (C) Let $f$ be three times differentiable on $U$, with $D^3 f = D(D^2 f)$. Show that $D^3 f(x)(u, v, w)$ does not change under any permutation of $u, v, w$. Hint: the symmetry in $v, w$ comes from the theorem applied to $f$ at each point near $x$; the symmetry in $u, v$ comes from the theorem applied to $y \mapsto Df(y)w$. The transpositions $(1\,2)$ and $(2\,3)$ generate the symmetric group $S_3$.

### Notes and history

Euler and Clairaut used the symmetry of mixed partial derivatives in the eighteenth century, with incomplete arguments. H. A. Schwarz gave a proof in 1873 for continuous mixed derivatives. The form with $Df$ differentiable at one point is the form of the books on calculus in Banach spaces, for example Dieudonné, *Foundations of Modern Analysis*, Chapter VIII. The counterexample is usually credited to Peano.

### Reference

<?reference?>
