---
title: Critical points and the second derivative test
kind: theory
modules: []
explains:
  E1: [IsLocalMin.hasFDerivAt_eq_zero, IsLocalMax.hasFDerivAt_eq_zero, IsLocalMin.fderiv_eq_zero, IsLocalExtr.fderiv_eq_zero, IsLocalExtr.hasLineDerivAt_eq_zero, IsLocalMinOn.hasFDerivWithinAt_nonneg, convexOn_of_deriv2_nonneg]
families: []
requires: [V17.C03, V17.C04, V15.C04]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Critical points and the second derivative test

### Overview

This section applies Taylor's formula of Section 1 to the extrema of a real function $f : U \to \mathbb{R}$ on an open set $U$ of a real normed space $E$. At a local extremum the derivative is $0$ (Fermat). At a critical point, the second derivative decides more. If the quadratic form $h \mapsto D^2 f(x)(h, h)$ is bounded below by $m\|h\|^2$ with $m > 0$, the point is a strict local minimum. In finite dimension it is enough that the form is positive definite. An example in $\ell^2$ shows that this fails in infinite dimension.

The section ends with convexity: a $C^2$ function with $D^2 f \ge 0$ on a convex set is convex. Volume 15, Chapter 4 proved the second derivative test and this criterion in one variable.

### Definitions

Let $f : U \to \mathbb{R}$ and $x \in U$. The point $x$ is a *local minimum* of $f$ if $f(y) \ge f(x)$ for all $y$ in a neighbourhood of $x$, and a *strict local minimum* if $f(y) > f(x)$ for $y \ne x$ in a neighbourhood. Local maxima are defined in the same way. A *local extremum* is a local minimum or a local maximum.

**Definition (Critical point).** A point $x$ where $f$ is differentiable is a *critical point* of $f$ if $Df(x) = 0$.

Let $f$ be twice differentiable at $x$. By Chapter 4, $D^2 f(x)$ is a symmetric bilinear form when $f$ is $C^2$ near $x$. Its *quadratic form* is $Q(h) = D^2 f(x)(h, h)$. For $E = \mathbb{R}^d$, $Q(h) = h^{\mathsf T}H_f(x)h$ with the Hessian matrix $H_f(x)$.

**Definition (Definite forms).** A quadratic form $Q$ on $E$ is *positive semidefinite* if $Q(h) \ge 0$ for all $h$, *positive definite* if $Q(h) > 0$ for all $h \ne 0$, and *coercive* if there is $m > 0$ with $Q(h) \ge m\|h\|^2$ for all $h$. It is *indefinite* if it takes both signs.

A coercive form is positive definite. The converse holds in finite dimension (lemma below), and fails in $\ell^2$: the form $Q(h) = \sum_n h_n^2/n$ is positive definite, but $Q(e_n) = 1/n \to 0$ on the unit vectors $e_n$.

### Theorems and proofs

**Theorem (Fermat).** Let $f : U \to \mathbb{R}$ have a local extremum at $x \in U$ and be differentiable at $x$. Then $Df(x) = 0$.

*Proof.* Let $h \in E$ and $g(t) = f(x + th)$, defined for $|t|$ small. Then $g$ has a local extremum at $0$, and by the chain rule $g'(0) = Df(x)h$. By the theorem of Fermat in one variable (Volume 15, Chapter 3), $g'(0) = 0$. So $Df(x)h = 0$ for every $h$. $\square$

::: mathlib
`IsLocalMin.hasFDerivAt_eq_zero` · `Mathlib.Analysis.Calculus.LocalExtr.Basic`

For `f : E → ℝ` and `f' : StrongDual ℝ E`, `IsLocalMin.hasFDerivAt_eq_zero : IsLocalMin f a → HasFDerivAt f f' a → f' = 0`. The type `StrongDual ℝ E` is `E →L[ℝ] ℝ`. The forms with `fderiv` are `IsLocalMin.fderiv_eq_zero` and `IsLocalExtr.fderiv_eq_zero : IsLocalExtr f a → fderiv ℝ f a = 0`. These need no differentiability hypothesis: if $f$ is not differentiable at `a`, then `fderiv ℝ f a = 0` by the junk value. The directional form is `IsLocalExtr.hasLineDerivAt_eq_zero`. For a minimum on a set `s`, `IsLocalMinOn.hasFDerivWithinAt_nonneg` gives `0 ≤ f' y` for each `y` in the positive tangent cone of `s` at `a`.

<?decl IsLocalMin.hasFDerivAt_eq_zero?>
<?decl IsLocalMax.hasFDerivAt_eq_zero?>
<?decl IsLocalExtr.fderiv_eq_zero?>
<?decl IsLocalMinOn.hasFDerivWithinAt_nonneg?>
:::

**Theorem (Second order necessary condition).** Let $f$ be $C^2$ on a ball around $x$, and let $x$ be a local minimum of $f$. Then $Df(x) = 0$ and $D^2 f(x)(h, h) \ge 0$ for every $h \in E$.

*Proof.* Fermat gives $Df(x) = 0$. Fix $h$. By the Peano form of Section 1 with $n = 2$,
$$f(x + th) - f(x) = \tfrac12 t^2 D^2 f(x)(h, h) + r(t), \qquad r(t)/t^2 \to 0 \text{ as } t \to 0.$$
The left side is $\ge 0$ for small $t$. Divide by $t^2$ and let $t \to 0$: $\frac12 D^2 f(x)(h, h) \ge 0$. $\square$

**Theorem (Second derivative test).** Let $f$ be $C^2$ on a ball around $x$ with $Df(x) = 0$, and let $Q(h) = D^2 f(x)(h, h)$.

1. If $Q$ is coercive, then $x$ is a strict local minimum.
2. If $-Q$ is coercive, then $x$ is a strict local maximum.
3. If $Q$ is indefinite, then $x$ is not a local extremum.

*Proof.* (1) Let $Q(h) \ge m\|h\|^2$ with $m > 0$. By the Peano form, $f(x + h) - f(x) = \frac12 Q(h) + r(h)$ with $r(h) = o(\|h\|^2)$. Choose $\delta > 0$ with $|r(h)| \le \frac{m}{4}\|h\|^2$ for $\|h\| < \delta$. Then for $0 < \|h\| < \delta$,
$$f(x + h) - f(x) \ge \tfrac{m}{2}\|h\|^2 - \tfrac{m}{4}\|h\|^2 = \tfrac{m}{4}\|h\|^2 > 0.$$
(2) Apply (1) to $-f$. (3) If $x$ is a local minimum, then $Q \ge 0$ by the necessary condition. If it is a local maximum, then $-Q \ge 0$. An indefinite form satisfies neither. $\square$

**Lemma (Finite dimension).** Let $E$ be finite-dimensional. A positive definite quadratic form $Q(h) = B(h, h)$, with $B$ bilinear, is coercive.

*Proof.* On a finite-dimensional space every bilinear form is continuous, and the unit sphere $S$ is compact (Volume 16). So the continuous function $Q$ attains its minimum $m$ on $S$ at some $h_0 \in S$, and $m = Q(h_0) > 0$. For $h \ne 0$, $h/\|h\| \in S$ and $Q(h) = \|h\|^2 Q(h/\|h\|) \ge m\|h\|^2$. $\square$

**Corollary.** In $\mathbb{R}^d$, a critical point where the Hessian matrix is positive definite is a strict local minimum.

**Lemma (Two variables).** The form $Q(h) = a h_1^2 + 2b h_1 h_2 + c h_2^2$, with the matrix $\begin{pmatrix} a & b \\ b & c \end{pmatrix}$, is positive definite if and only if $a > 0$ and $ac - b^2 > 0$. It is indefinite if $ac - b^2 < 0$.

*Proof.* If $a > 0$, complete the square: $aQ(h) = (ah_1 + bh_2)^2 + (ac - b^2)h_2^2$. If also $ac - b^2 > 0$, both terms are $\ge 0$ and their sum is $0$ only for $h_2 = 0$ and $h_1 = 0$. Conversely, if $Q$ is positive definite, then $a = Q(1, 0) > 0$, and $Q(-b, a) = a(ac - b^2) > 0$ gives $ac - b^2 > 0$. If $ac - b^2 < 0$: when $a \ne 0$, $Q(1, 0) = a$ and $Q(-b, a) = a(ac - b^2)$ have opposite signs; when $a = 0$, $b \ne 0$ and $Q(h_1, 1) = 2bh_1 + c$ takes both signs. $\square$

**Theorem (Convexity from the second derivative).** Let $U \subseteq E$ be open and convex, and let $f$ be $C^2$ on $U$ with $D^2 f(y)(h, h) \ge 0$ for all $y \in U$ and $h \in E$. Then $f$ is convex on $U$.

*Proof.* Let $x, y \in U$ and $\varphi(t) = f(x + t(y - x))$. It is defined and $C^2$ on an open interval that contains $[0, 1]$, because $U$ is open and convex. By the lemma on derivatives along a segment of Section 1, $\varphi''(t) = D^2 f(x + t(y - x))(y - x, y - x) \ge 0$. By Volume 15, Chapter 4, $\varphi$ is convex on $[0, 1]$. So $f((1 - t)x + ty) = \varphi(t) \le (1 - t)\varphi(0) + t\varphi(1) = (1 - t)f(x) + tf(y)$. $\square$

::: mathlib
`convexOn_of_deriv2_nonneg` · `Mathlib.Analysis.Convex.Deriv`

This is the one-variable criterion of Volume 15: for `f : ℝ → ℝ` on a convex set `D`, continuity on `D`, differentiability of `f` and `deriv f` on `interior D`, and `0 ≤ deriv^[2] f x` on `interior D` give `ConvexOn ℝ D f`. The proof above composes it with the affine map $t \mapsto x + t(y - x)$; the lemma `ConvexOn.comp_affineMap` handles this step in the other direction.

<?decl convexOn_of_deriv2_nonneg?>
:::

The index of this edition has no declaration for the second derivative test for maps on a normed space $E$, and none for convexity from $D^2 f \ge 0$ in several variables. The one-variable test is `isLocalMin_of_deriv_deriv_pos` of Volume 15.

### Examples

**Example (A strict minimum).** Let $f(x, y) = x^2 + xy + y^2 - 3x$. Then $Df(x, y) = (2x + y - 3,\ x + 2y)$. The equations give $x = -2y$ and $-3y - 3 = 0$, so the only critical point is $(2, -1)$, with $f(2, -1) = 4 - 2 + 1 - 6 = -3$. The Hessian is constant, $\begin{pmatrix} 2 & 1 \\ 1 & 2 \end{pmatrix}$, with $a = 2 > 0$ and $ac - b^2 = 3 > 0$. So $(2, -1)$ is a strict local minimum. By the convexity theorem $f$ is convex, and with Exercise 4 the minimum is global: $f \ge -3$ on $\mathbb{R}^2$.

**Example (A saddle).** Let $f(x, y) = x^2 - y^2$. The only critical point is $0$, and $Q(h) = 2h_1^2 - 2h_2^2$ is indefinite. Along the $x$-axis $f$ has a minimum at $0$ and along the $y$-axis a maximum. So $0$ is not a local extremum.

**Example (Degenerate critical points).** For $f(x, y) = x^4 + y^4$ and $g(x, y) = x^4 - y^4$, the origin is critical and both Hessians are $0$. The origin is a strict minimum of $f$, but $g(0, t) = -t^4 < 0 < g(t, 0)$, so it is not an extremum of $g$. A semidefinite or zero Hessian does not decide.

**Counterexample (Positive definite is not enough in $\ell^2$).** On the real Hilbert space $\ell^2$ let
$$f(x) = \sum_{n \ge 1}\Big(\frac{x_n^2}{n} - x_n^4\Big).$$
Here $q(x) = \sum x_n^2/n = B(x, x)$ with $B(x, y) = \sum x_n y_n/n$, and $|B(x, y)| \le \|x\|\|y\|$. Also $p(x) = \sum x_n^4 = A(x, x, x, x)$ with $A(x, y, z, w) = \sum x_n y_n z_n w_n$, and $|A(x, y, z, w)| \le \|x\|\|y\|\|z\|\|w\|$ by the Cauchy-Schwarz inequality and $|x_n y_n| \le \|x\|\|y\|$. So $f = q - p$ is $C^\infty$ by Chapter 4. Since $|p(h)| \le \|h\|^4$, $Df(0) = 0$ and $D^2 f(0)(h, h) = 2\sum h_n^2/n$, which is positive definite. But for $x = (2/\sqrt{n})\,e_n$,
$$f(x) = \frac{4}{n^2} - \frac{16}{n^2} = -\frac{12}{n^2} < 0 = f(0), \qquad \|x\| = \frac{2}{\sqrt n} \to 0.$$
So $0$ is not a local minimum. The form is not coercive, and the quartic term wins along the directions $e_n$ with large $n$.

### The library around it

Mathlib states local extrema with filters: `IsLocalMin f a` is `IsMinFilter f (𝓝 a) a`, that is, `∀ᶠ y in 𝓝 a, f a ≤ f y`. To use the second derivative test of this section in Lean, combine `IsLocalMin` with the integral Taylor formula `map_add_eq_sum_add_integral_iteratedFDeriv` of Section 1 and the symmetry of Chapter 4. Positive definiteness of a matrix is `Matrix.PosDef`.

Common errors of a learner:

- Concluding a minimum from a critical point with a positive definite Hessian in an infinite-dimensional space. The test needs a coercive form.

### Exercises

1. (A) Find and classify the critical points of $f(x, y) = x^3 - 3x + y^2$.
2. (A) Show that $0$ is a critical point of $f(x, y) = x^2 + y^3$ with a positive semidefinite Hessian, and that it is not a local extremum.
3. (B) Let $f$ be $C^2$ and convex on an open convex set $U$. Show that $D^2 f(y)(h, h) \ge 0$ for $y \in U$. Hint: restrict to a line and use Volume 15.
4. (B) Let $f$ be convex and differentiable on an open convex set $U$, with $Df(x) = 0$. Show that $f(y) \ge f(x)$ for all $y \in U$. Hint: $\frac{f(x + t(y - x)) - f(x)}{t} \le f(y) - f(x)$ for $0 < t \le 1$.
5. (B) Let $H$ be a real Hilbert space, $A$ a bounded self-adjoint operator with $\langle Ah, h\rangle \ge m\|h\|^2$, $m > 0$, and $b \in H$. Let $f(x) = \frac12\langle Ax, x\rangle - \langle b, x\rangle$, and let $Ax_0 = b$. Show that $Df(x)h = \langle Ax - b, h\rangle$ and that $f(x_0 + h) - f(x_0) = \frac12\langle Ah, h\rangle$. Conclude that $x_0$ is the unique global minimum.
6. (C) For the function $f$ of the counterexample in $\ell^2$, show that the restriction $t \mapsto f(th)$ has a strict local minimum at $0$ for every $h \ne 0$.

### Notes and history

Fermat used the vanishing of the derivative at an extremum in the seventeenth century. For a symmetric $d \times d$ matrix, the criterion of Sylvester says that it is positive definite if and only if all leading principal minors are positive. In the calculus of variations the space is infinite-dimensional, and examples of the type of the counterexample in $\ell^2$ are the reason why the sufficient conditions there ask for a coercive second variation.

### Reference

<?reference?>
