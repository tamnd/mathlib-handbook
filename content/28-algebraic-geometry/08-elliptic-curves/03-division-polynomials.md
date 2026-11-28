---
title: Division polynomials
kind: theory
modules:
  - Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
  - Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
explains:
  E3: [WeierstrassCurve.ψ₂, WeierstrassCurve.Ψ₃, WeierstrassCurve.preΨ₄, WeierstrassCurve.ψ, WeierstrassCurve.preΨ, WeierstrassCurve.φ, WeierstrassCurve.Φ, WeierstrassCurve.natDegree_ΨSq, WeierstrassCurve.leadingCoeff_Φ]
  E2: [WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.ψ₂_sq, WeierstrassCurve.Ψ₂Sq_eq, WeierstrassCurve.ψ_even, WeierstrassCurve.ψ_odd, WeierstrassCurve.ψ_four, WeierstrassCurve.preΨ_even, WeierstrassCurve.preΨ_odd, WeierstrassCurve.ΨSq, WeierstrassCurve.Ψ, WeierstrassCurve.Φ_two, WeierstrassCurve.Φ_three, WeierstrassCurve.φ_two, WeierstrassCurve.Affine.CoordinateRing.mk_ψ, WeierstrassCurve.Affine.CoordinateRing.mk_φ, WeierstrassCurve.map_ψ, WeierstrassCurve.coeff_preΨ, WeierstrassCurve.natDegree_preΨ, WeierstrassCurve.leadingCoeff_preΨ, WeierstrassCurve.leadingCoeff_ΨSq, WeierstrassCurve.natDegree_Φ, WeierstrassCurve.natDegree_Ψ₃, WeierstrassCurve.natDegree_Ψ₂Sq]
  E1: auto
families: []
requires: [V06.C05, V09.C06]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Division polynomials

### Overview

The points $P$ with $nP = O$ form the $n$-torsion subgroup $E[n]$ of an elliptic curve. They are the zeros of the $n$-th division polynomial $\psi_n$, a polynomial in $x$ and $y$ with coefficients in $\mathbb{Z}[a_1, a_2, a_3, a_4, a_6]$. Together with polynomials $\phi_n$ and $\omega_n$, the division polynomials give the coordinates of $nP$ as rational functions of the coordinates of $P$. They are the main tool to count torsion points, to study the Galois action on them, and to compute in Schoof's algorithm for point counting over finite fields.

The division polynomials satisfy a quadratic recursion, the recursion of an elliptic divisibility sequence. Mathlib defines them by this recursion, over each commutative ring, and proves their degrees and leading coefficients. This section gives the definitions, the recursion, the polynomials $\psi_2$, $\psi_3$, $\psi_4$ written out, the link with $2$-torsion and $3$-torsion, and the degree theorem. It ends with the place where Mathlib stops.

### Definitions

Let $W$ be a Weierstrass curve over a commutative ring $R$, with the quantities $b_2, b_4, b_6, b_8$ of Section 1.

**Definition (The first division polynomials).** Put
$$\psi_2 = 2Y + a_1 X + a_3 \in R[X, Y], \qquad \Psi_2^{[2]} = 4X^3 + b_2 X^2 + 2b_4 X + b_6 \in R[X],$$
$$\Psi_3 = 3X^4 + b_2 X^3 + 3b_4 X^2 + 3b_6 X + b_8,$$
$$\tilde\Psi_4 = 2X^6 + b_2 X^5 + 5b_4 X^4 + 10 b_6 X^3 + 10 b_8 X^2 + (b_2 b_8 - b_4 b_6) X + (b_4 b_8 - b_6^2).$$

The bivariate $\psi_2$ is the partial derivative $W_Y$, and $\Psi_2^{[2]}$ is the $2$-torsion polynomial of Section 1.

**Definition (Elliptic divisibility sequence).** Let $S$ be a commutative ring and $b, c, d \in S$. The *normalised elliptic divisibility sequence* $W(n)$ with parameters $b, c, d$ is the sequence indexed by $\mathbb{Z}$ with
$$W(0) = 0, \quad W(1) = 1, \quad W(2) = b, \quad W(3) = c, \quad W(4) = db, \quad W(-n) = -W(n),$$
$$W(2m + 1) = W(m + 2) W(m)^3 - W(m - 1) W(m + 1)^3,$$
$$W(2m)\, b = W(m - 1)^2 W(m) W(m + 2) - W(m - 2) W(m) W(m + 1)^2.$$
The second rule fixes $W(2m)$ only when $b$ is not a zero divisor. Mathlib avoids division: it defines an auxiliary sequence $\tilde W(n)$ with parameter $b^4$ in place of $b$ and puts $W(n) = \tilde W(n) \cdot b$ for even $n$ and $W(n) = \tilde W(n)$ for odd $n$.

**Definition (Division polynomials).** The *division polynomials* $\psi_n \in R[X, Y]$ are the elliptic divisibility sequence with $b = \psi_2$, $c = \Psi_3$ and $d = \tilde\Psi_4$. So $\psi_0 = 0$, $\psi_1 = 1$, $\psi_3 = \Psi_3$ and $\psi_4 = \tilde\Psi_4 \psi_2$. The polynomials
$$\phi_n = X \psi_n^2 - \psi_{n+1} \psi_{n-1}$$
give the $x$-coordinate of $nP$.

**Definition (Univariate forms).** The auxiliary sequence with $b^4$ replaced by $(\Psi_2^{[2]})^2$ is a sequence $\tilde\Psi_n \in R[X]$. Put $\Psi_n = \tilde\Psi_n \psi_2$ for $n$ even and $\Psi_n = \tilde\Psi_n$ for $n$ odd. Also put $\Psi_n^{[2]} = \tilde\Psi_n^2 \Psi_2^{[2]}$ for $n$ even and $\Psi_n^{[2]} = \tilde\Psi_n^2$ for $n$ odd, and
$$\Phi_n = X \Psi_n^{[2]} - \tilde\Psi_{n+1} \tilde\Psi_{n-1} \cdot \begin{cases} 1 & n \text{ even}, \\ \Psi_2^{[2]} & n \text{ odd}. \end{cases}$$

The univariate forms are the images of $\psi_n^2$, $\psi_n$ and $\phi_n$ in the coordinate ring, written with the square of $\psi_2$ removed, as the next lemma shows.

**Definition (The polynomials ωₙ).** The module docstring defines $\omega_n = \bigl(\psi_{2n}/\psi_n - \psi_n (a_1 \phi_n + a_3 \psi_n^2)\bigr)/2$, a polynomial since $\psi_n$ divides $\psi_{2n}$. Classically $nP = (\phi_n / \psi_n^2, \ \omega_n / \psi_n^3)$. The index of this edition has no declaration for $\omega_n$; the module docstring lists it as a TODO.

### Theorems and proofs

**Lemma (The square of ψ₂).** In $R[X, Y]$, $\psi_2^2 = \Psi_2^{[2]} + 4 W(X, Y)$, where $W(X, Y)$ is the Weierstrass polynomial. So in the coordinate ring, $\psi_2^2 = \Psi_2^{[2]}$.

*Proof.* $\psi_2^2 = 4Y^2 + 4a_1 XY + 4a_3 Y + (a_1 X + a_3)^2$. Replace $4(Y^2 + a_1 XY + a_3 Y)$ by $4W(X, Y) + 4(X^3 + a_2 X^2 + a_4 X + a_6)$. The rest is $4X^3 + (a_1^2 + 4a_2) X^2 + (2a_1 a_3 + 4a_4) X + (a_3^2 + 4a_6) = \Psi_2^{[2]}$. $\square$

**Proposition (Univariate forms).** In the coordinate ring of $W$, the images of $\psi_n$, $\psi_n^2$ and $\phi_n$ equal the images of $\Psi_n$, $\Psi_n^{[2]}$ and $\Phi_n$.

*Proof.* By the definition through the auxiliary sequence, $\psi_n$ is $\tilde W(n)$ for the parameters $(\psi_2^4, \Psi_3, \tilde\Psi_4)$, times $\psi_2$ when $n$ is even. The auxiliary sequence is a polynomial in its parameters, and by the lemma $\psi_2^4$ maps to $(\Psi_2^{[2]})^2$. So the image of $\psi_n$ is the image of $\tilde\Psi_n$, times $\psi_2$ for even $n$, which is $\Psi_n$. Squaring and the lemma give $\psi_n^2 \mapsto \Psi_n^{[2]}$. For $\phi_n$: when $n$ is even, $n + 1$ and $n - 1$ are odd, and $\psi_{n+1}\psi_{n-1}$ maps to $\tilde\Psi_{n+1}\tilde\Psi_{n-1}$. When $n$ is odd, both are even, and the product has the extra factor $\psi_2^2 \mapsto \Psi_2^{[2]}$. $\square$

**Proposition (The first cases).** $\Phi_2 = X^4 - b_4 X^2 - 2b_6 X - b_8$, and $X \Psi_2^{[2]} - \Phi_2 = \Psi_3$. Also $\Phi_3 = X \Psi_3^2 - \tilde\Psi_4 \Psi_2^{[2]}$.

*Proof.* For $n = 2$, $\tilde\Psi_3 \tilde\Psi_1 = \Psi_3$, so $\Phi_2 = X \Psi_2^{[2]} - \Psi_3 = 4X^4 + b_2 X^3 + 2b_4 X^2 + b_6 X - \Psi_3 = X^4 - b_4 X^2 - 2b_6 X - b_8$. For $n = 3$, $\tilde\Psi_4 \tilde\Psi_2 = \tilde\Psi_4$, and $n$ is odd. $\square$

**Proposition (Torsion of order 2 and 3).** Let $F$ be a field and $P = (x, y)$ a point of $W$ over $F$. Then $2P = O$ if and only if $\psi_2(x, y) = 0$, and then $\Psi_2^{[2]}(x) = 0$. If $\psi_2(x, y) \neq 0$, then $x(2P) = \Phi_2(x)/\Psi_2^{[2]}(x)$, and $3P = O$ if and only if $\Psi_3(x) = 0$.

*Proof.* $\psi_2(x, y) = 2y + a_1 x + a_3 = y - \bar y$, with $\bar y$ as in Section 2. So $\psi_2(x, y) = 0$ if and only if $P = -P$, that is $2P = O$. By the lemma, $\psi_2(x, y)^2 = \Psi_2^{[2]}(x)$ on the curve.

The formula for $x(2P)$ is the tangent construction of Section 2. Mathlib proves it for each Weierstrass curve. Here is the proof for $Y^2 = X^3 + AX + B$, where $b_2 = 0$, $b_4 = 2A$, $b_6 = 4B$ and $b_8 = -A^2$. The slope is $\ell = (3x^2 + A)/(2y)$, so
$$x(2P) = \ell^2 - 2x = \frac{(3x^2 + A)^2 - 8x y^2}{4y^2} = \frac{x^4 - 2Ax^2 - 8Bx + A^2}{4(x^3 + Ax + B)} = \frac{\Phi_2(x)}{\Psi_2^{[2]}(x)}.$$

For $3$-torsion, $3P = O$ means $2P = -P$. Since $2P \neq O$, the point $2P$ is affine, and $2P = \pm P$ if and only if $x(2P) = x$. The case $2P = P$ gives $P = O$, which is excluded. So $3P = O$ if and only if $\Phi_2(x) = x \Psi_2^{[2]}(x)$, that is $\Psi_3(x) = 0$ by the last proposition. $\square$

**Theorem (Degrees and leading coefficients).** Let $n \ge 0$ and put $d(n) = (n^2 - 4)/2$ for even $n \ge 2$, $d(n) = (n^2 - 1)/2$ for odd $n$, and $c(n) = n/2$ for even $n$, $c(n) = n$ for odd $n$. Then $\deg \tilde\Psi_n \le d(n)$ and the coefficient of $X^{d(n)}$ in $\tilde\Psi_n$ is $c(n)$. As a consequence, $\Phi_n$ is monic of degree $n^2$ when $R \neq 0$, and $\Psi_n^{[2]}$ has degree $n^2 - 1$ and leading coefficient $n^2$ when $R$ has no zero divisors and $n \neq 0$ in $R$.

*Proof.* Put $d(0) = 0$. Note that the coefficient of $X^{a+b}$ in $fg$ is the product of the coefficients of $X^a$ in $f$ and $X^b$ in $g$ when $\deg f \le a$ and $\deg g \le b$. The cases $n \le 4$ are $0, 1, 1, \Psi_3, \tilde\Psi_4$, with $(d, c) = (0, 0), (0, 1), (0, 1), (4, 3), (6, 2)$. For $n \ge 5$ use strong induction and the recursion
$$\tilde\Psi_{2m+1} = \tilde\Psi_{m+2} \tilde\Psi_m^3 \cdot \varepsilon - \tilde\Psi_{m-1} \tilde\Psi_{m+1}^3 \cdot \varepsilon', \qquad \tilde\Psi_{2m} = \tilde\Psi_{m-1}^2 \tilde\Psi_m \tilde\Psi_{m+2} - \tilde\Psi_{m-2} \tilde\Psi_m \tilde\Psi_{m+1}^2,$$
where $\varepsilon = (\Psi_2^{[2]})^2$ and $\varepsilon' = 1$ for $m$ even, and the reverse for $m$ odd. The factor $(\Psi_2^{[2]})^2$ has degree at most $6$ and coefficient $16$ at $X^6$.

Take $n = 2m + 1$ with $m$ even. The first product has degree at most $\frac{(m+2)^2 - 4}{2} + \frac{3(m^2 - 4)}{2} + 6 = 2m^2 + 2m$, and the second at most $\frac{(m-1)^2 - 1}{2} + \frac{3((m+1)^2 - 1)}{2} = 2m^2 + 2m$, which is $d(2m+1)$. The coefficient of $X^{d(n)}$ is
$$\tfrac{m+2}{2} \bigl(\tfrac{m}{2}\bigr)^3 \cdot 16 - (m - 1)(m + 1)^3 = (m + 2) m^3 - (m - 1)(m + 1)^3 = 2m + 1,$$
since $(m - 1)(m + 1)^3 = m^4 + 2m^3 - 2m - 1$. For $m$ odd the degrees add up in the same way, and the coefficient is again $(m + 2) m^3 - 16 \cdot \frac{m - 1}{2} (\frac{m + 1}{2})^3 = 2m + 1$.

Take $n = 2m$. For $m$ even the two products have degree at most $2m^2 - 2 = d(2m)$, and the coefficient is $\frac{m}{4}\bigl((m - 1)^2 (m + 2) - (m - 2)(m + 1)^2\bigr) = \frac{m}{4}\bigl((m^3 - 3m + 2) - (m^3 - 3m - 2)\bigr) = m$. For $m$ odd the coefficient is $\frac{m}{4}$ times the same bracket, again $m = c(2m)$.

For $\Psi_n^{[2]}$: if $n$ is odd, it is $\tilde\Psi_n^2$, of degree at most $n^2 - 1$ with coefficient $n^2$. If $n$ is even, it is $\tilde\Psi_n^2 \Psi_2^{[2]}$, of degree at most $n^2 - 4 + 3$ with coefficient $(n/2)^2 \cdot 4 = n^2$. Without zero divisors and with $n^2 \neq 0$ these are the degree and leading coefficient. For $\Phi_n$: the term $X \Psi_n^{[2]}$ has coefficient $n^2$ at $X^{n^2}$. If $n$ is even, $\tilde\Psi_{n+1}\tilde\Psi_{n-1}$ has degree at most $\frac{(n+1)^2 - 1 + (n-1)^2 - 1}{2} = n^2$ with coefficient $(n+1)(n-1)$. If $n$ is odd, $\tilde\Psi_{n+1}\tilde\Psi_{n-1}\Psi_2^{[2]}$ has degree at most $\frac{(n+1)^2 + (n-1)^2 - 8}{2} + 3 = n^2$ with coefficient $\frac{n+1}{2} \cdot \frac{n-1}{2} \cdot 4 = n^2 - 1$. In both cases the coefficient of $X^{n^2}$ in $\Phi_n$ is $n^2 - (n^2 - 1) = 1$. $\square$

**Remark (Multiplication by n).** Over a field, for an elliptic curve and a point $P$ with $nP \neq O$, the classical theorem states $x(nP) = \phi_n(P)/\psi_n(P)^2$, and $nP = O$ for an affine $P$ if and only if $\psi_n(P) = 0$. For $n = 2$ this is the proposition above. The index of this edition has no declaration for the general formula for $x(nP)$, and none for the description of $E[n]$ by $\psi_n$.

### Examples

**Example (The curve y² = x³ − x).** Here $b_2 = 0$, $b_4 = -2$, $b_6 = 0$, $b_8 = -1$. Then
$$\psi_2 = 2y, \qquad \Psi_2^{[2]} = 4x^3 - 4x, \qquad \psi_3 = 3x^4 - 6x^2 - 1,$$
$$\tilde\Psi_4 = 2x^6 - 10x^4 - 10x^2 + 2, \qquad \psi_4 = 4y(x^6 - 5x^4 - 5x^2 + 1).$$
For $\tilde\Psi_4$: $5b_4 = -10$, $10 b_8 = -10$, $b_2 b_8 - b_4 b_6 = 0$ and $b_4 b_8 - b_6^2 = 2$. The roots of $\Psi_2^{[2]}$ are $0, 1, -1$, the $x$-coordinates of the points of order $2$. The point $(i, 1 - i)$ of order $4$ from Section 2 has $x^6 - 5x^4 - 5x^2 + 1 = -1 - 5 + 5 + 1 = 0$ at $x = i$.

**Example (Doubling on y² = x³ − x).** $\Phi_2 = x^4 + 2x^2 + 1 = (x^2 + 1)^2$, so $x(2P) = (x^2 + 1)^2/(4x^3 - 4x)$. At $x = i$ the numerator is $0$, so $x(2P) = 0$, as in Section 2. Check: $x \Psi_2^{[2]} - \Phi_2 = 4x^4 - 4x^2 - x^4 - 2x^2 - 1 = 3x^4 - 6x^2 - 1 = \Psi_3$.

**Example (Points of order 3).** The points of order $3$ on $y^2 = x^3 - x$ over $\mathbb{C}$ have $3x^4 - 6x^2 - 1 = 0$, so $x^2 = 1 \pm 2/\sqrt{3}$. This gives $4$ values of $x$ and $8$ points, since $y \neq 0$ for each of them. With $O$ they form $E[3] \cong (\mathbb{Z}/3)^2$, of order $9$.

**Example (Order 4 over F₅).** Over $\mathbb{F}_5$, $\tilde\Psi_4 \equiv 2x^6 + 2 = 2(x^6 + 1)$. At $x = 2$, $64 + 1 = 65 \equiv 0$, and at $x = 3$, $729 + 1 = 730 \equiv 0$. These are the $x$-coordinates of the four points $(2, \pm 1)$, $(3, \pm 2)$ of order $4$ found in Section 2.

**Example (The fifth polynomial).** The recursion with $m = 2$ gives $\psi_5 = \psi_4 \psi_2^3 - \psi_1 \psi_3^3$. In the univariate form, $\tilde\Psi_5 = \tilde\Psi_4 (\Psi_2^{[2]})^2 - \Psi_3^3$, of degree $12 = (25 - 1)/2$ with leading coefficient $2 \cdot 16 - 27 = 5$.

### The library around it

::: mathlib
`WeierstrassCurve.ψ` · `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic`

`ψ n` is `normEDS W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) n` for `n : ℤ`. The recursions are `ψ_even` and `ψ_odd`, in the form of the definition, and `ψ_four` is `C W.preΨ₄ * W.ψ₂`. The definition `φ` and the lemma `φ_two` give $\phi_n$. `map_ψ` is compatibility with ring maps.

<?decl WeierstrassCurve.ψ?>
:::

::: mathlib
`WeierstrassCurve.preΨ` · `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic`

`Ψ₂Sq`, `Ψ₃` and `preΨ₄` are the polynomials of the first definition, and `Ψ₂Sq_eq` identifies `Ψ₂Sq` with the $2$-torsion polynomial. `preΨ` is `preNormEDS (W.Ψ₂Sq ^ 2) W.Ψ₃ W.preΨ₄`, with `preΨ_even` and `preΨ_odd`. `ΨSq`, `Ψ` and `Φ` are the univariate forms, with `Φ_two` and `Φ_three`. `ψ₂_sq` is the lemma on the square of $\psi_2$, and `Affine.CoordinateRing.mk_ψ` and `mk_φ` state the proposition on univariate forms.

<?decl WeierstrassCurve.preΨ?>
:::

::: mathlib
`normEDS` · `Mathlib.NumberTheory.EllipticDivisibilitySequence`

The general sequence, with `preNormEDS` as the auxiliary sequence. The file also defines the predicate `IsEllipticDvdSequence`.

<?decl normEDS?>
:::

::: mathlib
`WeierstrassCurve.natDegree_ΨSq` · `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree`

`coeff_preΨ` and `natDegree_preΨ_le` are the first part of the theorem, with natural number division as in $d(n)$ and $c(n)$. `natDegree_preΨ` and `leadingCoeff_preΨ` need `(n : R) ≠ 0`. `natDegree_ΨSq` and `leadingCoeff_ΨSq` need `[NoZeroDivisors R]`, and `natDegree_Φ` and `leadingCoeff_Φ` need only `[Nontrivial R]`. `natDegree_Ψ₂Sq` and `natDegree_Ψ₃` need $4 \neq 0$ and $3 \neq 0$.

<?decl WeierstrassCurve.natDegree_ΨSq?>
:::

::: mathlib
`WeierstrassCurve.Affine.addX_self_of_Y_ne` · `Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula`

This is the doubling formula $x(2P) = \Phi_2(x)/\Psi_2^{[2]}(x)$ in the general form, stated with $b_4$, $b_6$ and $b_8$.

<?decl WeierstrassCurve.Affine.addX_self_of_Y_ne?>
:::

Common errors of a learner: `ψ` lives in `R[X][Y]`, a polynomial ring in $Y$ over $R[X]$, while `preΨ`, `ΨSq` and `Φ` live in `R[X]`. `ΨSq n` is not the square of `Ψ n` in `R[X][Y]`; it equals it only in the coordinate ring. The leading coefficient of `preΨ n` for even $n$ is $n/2$, not $n$, because the factor $\psi_2$ has been taken out. In characteristic $2$, $\Psi_2^{[2]}$ has degree less than $3$.

### Exercises

1. (A) Compute $\Psi_3$ and $\tilde\Psi_4$ for $y^2 = x^3 + 1$. *Hint:* $b_6 = 4$ and $b_2 = b_4 = b_8 = 0$.
2. (A) Check that $\Phi_2$ is monic of degree $4$ and that $\Psi_2^{[2]}$ has leading coefficient $4 = 2^2$. *Hint:* Use the formulas above.
3. (B) Show that the polynomial $\Psi_3$ of $y^2 = x^3 + 1$ has the root $x = 0$, and find the points of order $3$ with $x = 0$. *Hint:* $\Psi_3 = 3x^4 + 12x$.
4. (B) Prove the even and odd recursions for $\tilde\Psi_n$ from those for $\psi_n$ and the lemma on $\psi_2^2$. *Hint:* Count the even indices in each product.
5. (B) Compute $\Phi_3 = X\Psi_3^2 - \tilde\Psi_4 \Psi_2^{[2]}$ for $y^2 = x^3 - x$ and check that it is monic of degree $9$. *Hint:* The result is $x^9 + 12x^7 + 30x^5 - 36x^3 + 9x$.
6. (C) Over $\mathbb{F}_p$ with $p \ge 5$, show that $\Psi_n^{[2]}$ has degree $n^2 - 1$ when $p \nmid n$, and degree less than $p^2 - 1$ for $n = p$. *Hint:* The coefficient of $X^{n^2 - 1}$ is $n^2$, and the degree is at most $n^2 - 1$.
7. (C) Assume $\# E[n] = n^2$ and that the roots of $\tilde\Psi_n$ are the $x$-coordinates of the points of $E[n] \setminus E[2]$, each simple. Check that $\deg \Psi_n^{[2]} = n^2 - 1$ agrees with this count, for $n$ odd and for $n$ even. *Hint:* The points $P$ and $-P$ have the same $x$-coordinate, and $E[2]$ has $3$ affine points.

### Notes and history

Division polynomials are classical and go back to the study of the multiplication formulas for elliptic functions in the nineteenth century. Silverman, The Arithmetic of Elliptic Curves (1986), gives the recursion and the formula for $nP$ as an exercise in Chapter III. The Mathlib file on elliptic divisibility sequences cites the memoir of Ward (1948) on these sequences.

The Mathlib Author of `AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic` and `DivisionPolynomial.Degree` is David Kurniadi Angdinata.

### Reference

<?reference?>
