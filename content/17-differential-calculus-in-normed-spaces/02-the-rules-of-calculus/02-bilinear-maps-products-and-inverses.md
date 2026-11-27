---
title: Bilinear maps, products and the inverse in a Banach algebra
kind: theory
modules:
  - Mathlib.Analysis.Calculus.FDeriv.Bilinear
  - Mathlib.Analysis.Calculus.FDeriv.Mul
  - Mathlib.Analysis.Calculus.FDeriv.CompCLM
  - Mathlib.Analysis.Calculus.FDeriv.Pow
explains:
  E3: [IsBoundedBilinearMap.hasFDerivAt, HasFDerivAt.mul', hasFDerivAt_ringInverse]
  E2: [IsBoundedBilinearMap.fderiv, HasFDerivAt.mul, HasFDerivAt.smul, hasFDerivAt_pow', hasFDerivAt_pow, HasFDerivAt.clm_comp, HasFDerivAt.clm_apply, fderiv_inverse, hasFDerivAt_inv']
  E1: auto
families: []
requires: [V17.C01, V07.C04, V15.C03]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Bilinear maps, products and the inverse in a Banach algebra

### Overview

The product rule $(fg)' = f'g + fg'$ of Volume 15 comes from one fact: multiplication is bilinear. This section proves that a continuous bilinear map $B$ is differentiable, with $DB(x, y)(h, k) = B(h, y) + B(x, k)$. With the chain rule of Section 1 this gives the product rule in a normed algebra and the rules for maps with values in a space of operators. In a noncommutative algebra the order of the factors matters, and the derivative of $x^n$ is not $nx^{n-1}h$. The section then proves that the inverse $x \mapsto x^{-1}$ in a Banach algebra has the derivative $h \mapsto -x^{-1}hx^{-1}$, and computes the derivative of the determinant: $D\det(A)H = \operatorname{tr}(\operatorname{adj}(A)H)$.

### Definitions

**Definition (Bounded bilinear map).** Let $E$, $F$, $G$ be normed spaces over $\mathbb{K}$. A map $B : E \times F \to G$ is *bounded bilinear* if it is linear in each variable and there is a constant $C$ with $\|B(u, v)\| \le C\|u\|\,\|v\|$ for all $u, v$.

As for linear maps, a bilinear map is continuous if and only if it is bounded. The examples are the product of a normed algebra, the scalar multiplication $\mathbb{K} \times E \to E$, a real inner product, the composition $L(F, G) \times L(E, F) \to L(E, G)$ with $\|S \circ T\| \le \|S\|\,\|T\|$, and the evaluation $L(E, F) \times E \to F$ with $\|T u\| \le \|T\|\,\|u\|$.

**Definition (Normed algebra and Banach algebra).** A *normed algebra* over $\mathbb{K}$ is a $\mathbb{K}$-algebra $A$ with a norm such that $\|ab\| \le \|a\|\,\|b\|$. A *Banach algebra* is a complete normed algebra with a unit $1$. Examples are $M_n(\mathbb{K})$ with an operator norm and $L(E, E)$ for a Banach space $E$.

::: mathlib
`IsBoundedBilinearMap.hasFDerivAt` · `Mathlib.Analysis.Calculus.FDeriv.Bilinear`

`IsBoundedBilinearMap 𝕜 b` is a structure on a function `b : E × F → G` with the four laws of linearity and a bound. The lemma says `HasFDerivAt b (h.deriv p) p`, and `IsBoundedBilinearMap.fderiv` gives the `fderiv` form. For a bilinear map in the curried form `B : E →L[𝕜] F →L[𝕜] G`, use `ContinuousLinearMap.hasFDerivAt_of_bilinear`.

<?decl IsBoundedBilinearMap.hasFDerivAt?>
<?decl IsBoundedBilinearMap.fderiv?>
<?decl IsBoundedBilinearMap.deriv?>
:::

### Theorems and proofs

**Theorem (Derivative of a bilinear map).** Let $B : E \times F \to G$ be bounded bilinear. Then $B$ is differentiable at each $(x, y)$, and
$$DB(x, y)(h, k) = B(h, y) + B(x, k).$$

*Proof.* The map $L(h, k) = B(h, y) + B(x, k)$ is linear, and $\|L(h, k)\| \le C(\|y\| + \|x\|)\|(h, k)\|$, so $L$ is continuous. By bilinearity,
$$B(x + h, y + k) = B(x, y) + B(h, y) + B(x, k) + B(h, k).$$
So the remainder is $B(h, k)$, and $\|B(h, k)\| \le C\|h\|\,\|k\| \le C\|(h, k)\|^2$ for the max norm. This is $o(\|(h, k)\|)$. $\square$

**Theorem (Product rule).** Let $A$ be a normed algebra and $f, g : E \to A$ differentiable at $x$. Then $fg$ is differentiable at $x$, and
$$D(fg)(x)h = f(x)\,\big(Dg(x)h\big) + \big(Df(x)h\big)\,g(x).$$
If $A$ is commutative this is $f(x)Dg(x) + g(x)Df(x)$.

*Proof.* The product $m(a, b) = ab$ is bounded bilinear with $C = 1$. Write $fg = m \circ (f, g)$. By the theorem on maps into products and the chain rule of Section 1, the derivative at $x$ is $Dm(f(x), g(x)) \circ (Df(x), Dg(x))$. By the theorem above it sends $h$ to $m(Df(x)h, g(x)) + m(f(x), Dg(x)h)$. $\square$

The same proof with the scalar multiplication gives, for $c : E \to \mathbb{K}$ and $f : E \to F$,
$$D(cf)(x)h = c(x)\,Df(x)h + \big(Dc(x)h\big)\,f(x).$$

::: mathlib
`HasFDerivAt.mul'` · `Mathlib.Analysis.Calculus.FDeriv.Mul`

In a normed ring `𝔸` with `[NormedAlgebra 𝕜 𝔸]`, `HasFDerivAt a a' x → HasFDerivAt b b' x → HasFDerivAt (a * b) (a x • b' + a' <• b x) x`. Here `a x • b'` is the map `h ↦ a x * b' h`, and `a' <• b x` is `h ↦ a' h * b x`. In a commutative algebra `HasFDerivAt.mul` gives `c x • d' + d x • c'`. The rule for a scalar factor is `HasFDerivAt.smul`, with derivative `c x • f' + c'.smulRight (f x)`.

<?decl HasFDerivAt.mul'?>
<?decl HasFDerivAt.mul?>
<?decl HasFDerivAt.smul?>
:::

**Theorem (Powers).** Let $A$ be a normed algebra with unit and $n \ge 1$. The map $p_n(x) = x^n$ is differentiable at each $x$, with
$$Dp_n(x)h = \sum_{i=0}^{n-1} x^{n-1-i}\,h\,x^i.$$
If $A$ is commutative, $Dp_n(x)h = nx^{n-1}h$.

*Proof.* By induction on $n$. For $n = 1$ the map is the identity, with derivative $h$. Assume the formula for $n$. Since $x^{n+1} = x^n \cdot x$, the product rule gives
$$Dp_{n+1}(x)h = x^n h + \Big(\sum_{i=0}^{n-1} x^{n-1-i} h x^i\Big)x = x^n h + \sum_{j=1}^{n} x^{n-j} h x^j,$$
with $j = i + 1$. The term $x^n h$ is the term $j = 0$, so the sum is $\sum_{j=0}^{n} x^{n-j} h x^j$, the formula for $n + 1$. $\square$

::: mathlib
`hasFDerivAt_pow'` · `Mathlib.Analysis.Calculus.FDeriv.Pow`

The noncommutative form is `HasFDerivAt (fun x => x ^ n) (∑ i ∈ Finset.range n, x ^ (n.pred - i) •> ContinuousLinearMap.id 𝕜 _ <• x ^ i) x`. In a commutative normed algebra `hasFDerivAt_pow` gives `(n • x ^ (n - 1)) • ContinuousLinearMap.id 𝕜 𝔸`.

<?decl hasFDerivAt_pow'?>
<?decl hasFDerivAt_pow?>
:::

**Theorem (Maps with values in operators).** Let $c : E \to L(F, G)$, $d : E \to L(H, F)$ and $u : E \to F$ be differentiable at $x$. Then $y \mapsto c(y) \circ d(y)$ and $y \mapsto c(y)u(y)$ are differentiable at $x$, with
$$D(c \circ d)(x)h = c(x) \circ \big(Dd(x)h\big) + \big(Dc(x)h\big) \circ d(x), \qquad D(cu)(x)h = c(x)\big(Du(x)h\big) + \big(Dc(x)h\big)u(x).$$

*Proof.* Composition and evaluation are bounded bilinear with $C = 1$. Apply the product rule argument with these maps in place of $m$. $\square$

::: mathlib
`HasFDerivAt.clm_comp` · `Mathlib.Analysis.Calculus.FDeriv.CompCLM`

The derivative of `fun y => (c y).comp (d y)` is `(compL 𝕜 F G H (c x)).comp d' + ((compL 𝕜 F G H).flip (d x)).comp c'`, where `compL` is composition as a continuous bilinear map. `HasFDerivAt.clm_apply` gives the derivative `(c x).comp u' + c'.flip (u x)` of `fun y => c y (u y)`. Chapter 4 uses them for second derivatives, with values in `E →L[𝕜] E →L[𝕜] F`.

<?decl HasFDerivAt.clm_comp?>
<?decl HasFDerivAt.clm_apply?>
:::

**Theorem (Inverse in a Banach algebra).** Let $A$ be a Banach algebra with $\|1\| = 1$ and $x \in A$ invertible. Then the map $y \mapsto y^{-1}$ is defined on a neighbourhood of $x$ and is differentiable at $x$, with
$$D(y \mapsto y^{-1})(x)h = -x^{-1}hx^{-1}.$$

*Proof.* Volume 16 proves the Neumann series: if $\|a\| < 1$, then $1 - a$ is invertible and $(1 - a)^{-1} = \sum_{n \ge 0} a^n$. Let $\|h\| \le 1/(2\|x^{-1}\|)$ and $a = -x^{-1}h$, so $\|a\| \le \|x^{-1}\|\,\|h\| \le \frac12$. Then $x + h = x(1 - a)$ is invertible, and
$$(x + h)^{-1} = (1 - a)^{-1}x^{-1} = \sum_{n \ge 0} a^n x^{-1} = x^{-1} - x^{-1}hx^{-1} + \sum_{n \ge 2} a^n x^{-1}.$$
The map $h \mapsto -x^{-1}hx^{-1}$ is continuous and linear. The remainder satisfies
$$\Big\|\sum_{n \ge 2} a^n x^{-1}\Big\| \le \|x^{-1}\|\sum_{n \ge 2} \|a\|^n = \frac{\|x^{-1}\|\,\|a\|^2}{1 - \|a\|} \le 2\|x^{-1}\|^3\|h\|^2.$$
This is $o(\|h\|)$. $\square$

For $A = \mathbb{K}$ the formula is $-h/x^2$, the derivative of $1/x$ of Volume 15. The two factors $x^{-1}$ stand on both sides of $h$, and in a noncommutative algebra they cannot be combined into $x^{-2}h$.

::: mathlib
`hasFDerivAt_ringInverse` · `Mathlib.Analysis.Calculus.FDeriv.Mul`

`Ring.inverse : R → R` is the total function equal to the inverse on units and to `0` elsewhere. For a unit `x : Rˣ` of a normed ring with `[NormedAlgebra 𝕜 R]` and `[HasSummableGeomSeries R]`, the lemma states `HasFDerivAt Ring.inverse (-mulLeftRight 𝕜 R ↑x⁻¹ ↑x⁻¹) x`, where `mulLeftRight 𝕜 R a b` is the map `h ↦ a * h * b`. `HasSummableGeomSeries` holds in each complete normed ring. `fderiv_inverse` is the `fderiv` form, and `hasFDerivAt_inv'` is the version for `Inv.inv` in a normed division ring.

<?decl hasFDerivAt_ringInverse?>
<?decl fderiv_inverse?>
<?decl hasFDerivAt_inv'?>
<?decl Ring.inverse?>
:::

**Theorem (Jacobi's formula).** Let $\det : M_n(\mathbb{K}) \to \mathbb{K}$. Then $\det$ is differentiable at each $A$, and
$$D\det(A)H = \operatorname{tr}\big(\operatorname{adj}(A)H\big).$$
In particular $D\det(I)H = \operatorname{tr} H$, and $D\det(A)H = \det(A)\operatorname{tr}(A^{-1}H)$ for an invertible $A$.

*Proof.* The determinant is a polynomial in the $n^2$ entries, so its partial derivatives exist and are continuous, and by the theorem of Section 2 of Chapter 1 it is differentiable, with $D\det(A)H = \sum_{i,j} \frac{\partial\det}{\partial a_{ij}}(A)\,h_{ij}$. Fix $i, j$. The cofactor expansion along row $i$ is $\det A = \sum_k a_{ik}C_{ik}$, where the cofactor $C_{ik}$ does not depend on the entries of row $i$. So $\det$ is affine in $a_{ij}$ with slope $C_{ij}$, and $\partial\det/\partial a_{ij} = C_{ij}$. The adjugate is the transposed matrix of cofactors, $\operatorname{adj}(A)_{ji} = C_{ij}$. So
$$D\det(A)H = \sum_{i,j} \operatorname{adj}(A)_{ji}h_{ij} = \sum_j \big(\operatorname{adj}(A)H\big)_{jj} = \operatorname{tr}\big(\operatorname{adj}(A)H\big).$$
For $A = I$, $\operatorname{adj}(I) = I$. For an invertible $A$, $\operatorname{adj}(A) = \det(A)A^{-1}$ by $A\operatorname{adj}(A) = \det(A)I$ (Volume 7). $\square$

::: mathlib
`Matrix.det_one_add_smul` · `Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff`

The index of this edition has no declaration for the Fréchet derivative of `Matrix.det`. Mathlib has the first-order expansion along a line, `det (1 + r • M) = 1 + trace M * r + (...) * r ^ 2`, and the polynomial form `Matrix.derivative_det_one_add_X_smul`: the derivative of `det (1 + X • M)` at `0` is `trace M`. A proof of the theorem in Mathlib must also choose a norm on `Matrix n n 𝕜`. The matrix norms are not global instances, and a user activates one locally, for example `Matrix.linftyOpNormedRing`.

<?decl Matrix.det_one_add_smul?>
<?decl Matrix.derivative_det_one_add_X_smul?>
<?decl Matrix.linftyOpNormedRing?>
:::

### Examples

**Example (The square of a matrix).** For $n = 2$ the theorem on powers gives $D(X^2)(X)H = XH + HX$. For $X^3$ it gives $X^2H + XHX + HX^2$. With $X = \begin{pmatrix} 0 & 1 \\ 0 & 0 \end{pmatrix}$ and $H = \begin{pmatrix} 0 & 0 \\ 1 & 0 \end{pmatrix}$, $X^2 = 0$ and $XHX = X$, so $D(X^3)(X)H = X \neq 0$, while the formula $3X^2H$ would give $0$.

**Example (The inverse of a matrix).** Let $A = \begin{pmatrix} 2 & 0 \\ 0 & 1 \end{pmatrix}$ and $H = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$. Then $A^{-1} = \operatorname{diag}(\frac12, 1)$ and
$$-A^{-1}HA^{-1} = -\begin{pmatrix} 0 & \frac12 \\ \frac12 & 0 \end{pmatrix}.$$
A direct check: $(A + tH)^{-1} = \frac{1}{2 - t^2}\begin{pmatrix} 1 & -t \\ -t & 2 \end{pmatrix}$, whose derivative at $t = 0$ is $\begin{pmatrix} 0 & -\frac12 \\ -\frac12 & 0 \end{pmatrix}$.

**Example (Jacobi's formula in dimension 2).** For $A = \begin{pmatrix} a & b \\ c & d \end{pmatrix}$, $\det A = ad - bc$ and $D\det(A)H = d\,h_{11} + a\,h_{22} - c\,h_{12} - b\,h_{21}$. The adjugate is $\begin{pmatrix} d & -b \\ -c & a \end{pmatrix}$, and $\operatorname{tr}(\operatorname{adj}(A)H) = dh_{11} - bh_{21} - ch_{12} + ah_{22}$, the same value.



### The library around it

The file `FDeriv.Bilinear` proves the derivative of `IsBoundedBilinearMap` once, and `FDeriv.Mul` and `FDeriv.CompCLM` deduce the rules for products, scalar multiples, composites and evaluation from it.

Common errors of a learner:

- Writing $D(fg)(x)h = Df(x)h \cdot g(x) + Dg(x)h \cdot f(x)$ in a noncommutative algebra. The factor $f(x)$ must stay on the left of $Dg(x)h$.
- Using `HasFDerivAt.mul` for matrices. It needs a commutative algebra; matrices need `HasFDerivAt.mul'`.
- Forgetting that `Ring.inverse` is $0$ off the units, so a statement about it at a non-unit says nothing about inverses.
- Trying to differentiate a function of matrices without a norm instance on `Matrix n n 𝕜`.

### Exercises

1. (A) Let $E$ be a real inner product space and $f, g : \mathbb{R} \to E$ differentiable. Show that $\frac{d}{dt}\langle f(t), g(t)\rangle = \langle f'(t), g(t)\rangle + \langle f(t), g'(t)\rangle$.
2. (A) Compute $D(X \mapsto X^{\mathsf T}X)(X)H$ on $M_n(\mathbb{R})$.
3. (B) Let $A$ be a Banach algebra and $f(x) = x^{-2}$ on the invertible elements. Compute $Df(x)h$, and check the result in $\mathbb{R}$.
4. (B) Let $\gamma : \mathbb{R} \to M_n(\mathbb{R})$ be differentiable with $\gamma(t)$ invertible. Show that $\frac{d}{dt}\det\gamma(t) = \det\gamma(t)\operatorname{tr}\big(\gamma(t)^{-1}\gamma'(t)\big)$. Deduce that $\det e^{tM} = e^{t\operatorname{tr}M}$.
5. (B) Let $B : E \times E \to F$ be bounded bilinear and $q(x) = B(x, x)$. Show that $Dq(x)h = B(h, x) + B(x, h)$, and recover the quadratic form of Chapter 1.
6. (C) Show that the set of invertible elements of a Banach algebra is open, and that the map $x \mapsto x^{-1}$ on it is continuous, from the estimates of the proof. Deduce that $D(y \mapsto y^{-1})$ depends continuously on $x$, as a map into $L(A, A)$.

### Notes and history

Carl Gustav Jacob Jacobi published the formula for the derivative of a determinant in 1841, in his memoir on functional determinants. The Neumann series is named after Carl Neumann, who used it for integral equations in the nineteenth century.

### Reference

<?reference?>
