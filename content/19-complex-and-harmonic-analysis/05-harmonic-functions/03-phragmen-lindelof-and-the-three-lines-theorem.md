---
title: Phragmen-Lindelof and the three lines theorem
kind: theory
modules:
  - Mathlib.Analysis.Complex.PhragmenLindelof
  - Mathlib.Analysis.Complex.Hadamard
explains:
  E3: [PhragmenLindelof.vertical_strip, PhragmenLindelof.eqOn_vertical_strip, "Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip₀₁'"]
  E2: [PhragmenLindelof.horizontal_strip, PhragmenLindelof.eqOn_horizontal_strip, PhragmenLindelof.quadrant_I, PhragmenLindelof.right_half_plane_of_tendsto_zero_on_real, PhragmenLindelof.right_half_plane_of_bounded_on_real, PhragmenLindelof.isBigO_sub_exp_exp, Complex.HadamardThreeLines.verticalStrip, Complex.HadamardThreeLines.verticalClosedStrip, Complex.HadamardThreeLines.sSupNormIm, Complex.HadamardThreeLines.interpStrip, Complex.HadamardThreeLines.norm_le_interpStrip_of_mem_verticalClosedStrip₀₁, "Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'"]
  E1: auto
families: []
requires: [V19.C02, V19.C03, V15.C06]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Phragmen-Lindelof and the three lines theorem

### Overview

The maximum modulus principle of Chapter 3, Section 2 says: on a bounded domain, a holomorphic function that is continuous up to the boundary takes the maximum of $|f|$ on the boundary. On an unbounded domain this fails. The Phragmen-Lindelof principle restores it under a growth condition at infinity. The allowed growth depends on the domain. This section proves the principle in a vertical strip, gives its forms for half planes and quadrants, and deduces Hadamard's three lines theorem: on a strip, the logarithm of the maximum of $|f|$ on the vertical line $\operatorname{Re} z = x$ is a convex function of $x$.

### Definitions

**Definition (Strip).** For $a < b$, the open vertical strip is $S(a, b) = \{z : a < \operatorname{Re} z < b\}$. Its closure $\overline{S}(a, b)$ adds the two lines $\operatorname{Re} z = a$ and $\operatorname{Re} z = b$.

**Definition (Holomorphic up to the boundary).** A function $f$ is holomorphic up to the boundary on an open set $U$ when it is complex differentiable on $U$ and continuous on the closure $\overline{U}$.

**Definition (Supremum on a line).** For $f$ bounded on the closed strip and $a \le x \le b$, let $M(x) = \sup_{y \in \mathbb{R}} |f(x + iy)|$.

::: mathlib
`Complex.HadamardThreeLines.sSupNormIm` · `Mathlib.Analysis.Complex.Hadamard`

`sSupNormIm f x` is the supremum of `‖f‖` on the line `re z = x`, the function $M(x)$. The strips `verticalStrip l u` and `verticalClosedStrip l u` are the open and the closed strip $l < \operatorname{Re} z < u$ and $l \le \operatorname{Re} z \le u$. The hypothesis "holomorphic up to the boundary" is `DiffContOnCl ℂ f U`.

<?decl Complex.HadamardThreeLines.sSupNormIm?>
:::

### Theorems and proofs

**Theorem (Phragmen-Lindelof in a strip).** Let $f$ be holomorphic up to the boundary on $S(a, b)$, with values in a complex normed space. Suppose $|f| \le C$ on the two lines $\operatorname{Re} z = a$ and $\operatorname{Re} z = b$, and suppose there are $c < \pi/(b - a)$, $A$ and $B$ with
$$|f(z)| \le A \exp\big(B e^{c|\operatorname{Im} z|}\big)$$
for $z \in S(a, b)$ with $|\operatorname{Im} z|$ large. Then $|f| \le C$ on $\overline{S}(a, b)$.

*Proof.* Step 1, normalization. The affine map $z \mapsto a + (b - a)(z + \pi/2)/\pi$ sends $S(-\pi/2, \pi/2)$ onto $S(a, b)$ and multiplies $\operatorname{Im} z$ by $(b - a)/\pi$. So take $a = -\pi/2$, $b = \pi/2$ and $c < 1$. Replacing $c$ by a larger number and $B$ by $\max(B, 0)$ keeps the bound, so assume $0 < c < 1$ and $B \ge 0$. Choose $d$ with $c < d < 1$. Also $C \ge 0$, because the boundary lines are not empty. Fix $C' > C$.

Step 2, the auxiliary function. For $\varepsilon > 0$ let $g_\varepsilon(z) = \exp(-\varepsilon \cos(dz))$. For $z = x + iy$,
$$\operatorname{Re} \cos(dz) = \cos(dx) \cosh(dy) \ge \delta \cosh(dy), \qquad \delta = \cos(d\pi/2) > 0,$$
on the closed strip, since $|dx| \le d\pi/2 < \pi/2$. So $|g_\varepsilon(z)| = \exp(-\varepsilon \cos(dx) \cosh(dy)) \le \exp(-\varepsilon\delta\cosh(dy)) \le 1$.

Step 3, the product. Let $h = g_\varepsilon f$. It is holomorphic up to the boundary on the strip, and $|h| \le |f| \le C$ on the two lines. For $|y|$ large,
$$|h(z)| \le A \exp\big(B e^{c|y|} - \tfrac12 \varepsilon\delta e^{d|y|}\big),$$
since $\cosh(dy) \ge e^{d|y|}/2$. As $d > c$, the exponent tends to $-\infty$. So there is $Y$ with $|h| \le C'$ on the strip for $|y| \ge Y$.

Step 4, the maximum principle on a rectangle. On the rectangle $|x| < \pi/2$, $|y| < Y$, the function $h$ is holomorphic, continuous on the closure, and $|h| \le C'$ on the boundary: on the vertical sides by Step 3 and on the horizontal sides by the choice of $Y$. By the maximum modulus principle, $|h| \le C'$ on the rectangle, so on the whole closed strip.

Step 5, the limit. For each $z$ in the closed strip, $|f(z)| \le C'/|g_\varepsilon(z)| = C' \exp(\varepsilon \cos(dx)\cosh(dy))$. Let $\varepsilon \to 0$ and then $C' \to C$. $\square$

**Corollary (Uniqueness).** Let $f$ and $g$ satisfy the growth condition of the theorem on $S(a, b)$ and agree on the two boundary lines. Then $f = g$ on $\overline{S}(a, b)$.

*Proof.* The function $f - g$ satisfies the growth condition, with the larger of the two constants $c$ and of the two constants $B$. On the lines $|f - g| = 0$. The theorem with $C = 0$ gives $f - g = 0$. $\square$

::: mathlib
`PhragmenLindelof.vertical_strip` · `Mathlib.Analysis.Complex.PhragmenLindelof`

The growth condition is `∃ c < π / (b - a), ∃ B, f =O[comap (abs ∘ im) atTop ⊓ 𝓟 (re ⁻¹' Ioo a b)] fun z ↦ exp (B * exp (c * |z.im|))`. The filter means "large $|\operatorname{Im} z|$ inside the strip", and the constant $A$ is the constant of `IsBigO`. The growth of a difference is `PhragmenLindelof.isBigO_sub_exp_exp`, and the uniqueness is `PhragmenLindelof.eqOn_vertical_strip`.

<?decl PhragmenLindelof.vertical_strip?>
<?decl PhragmenLindelof.eqOn_vertical_strip?>
:::

The same method works on other domains. On a sector of opening $\pi/\alpha$ the allowed growth is $\exp(B|z|^c)$ with $c < \alpha$, and the auxiliary function is $\exp(-\varepsilon z^{d})$ with $c < d < \alpha$. For a quadrant, $\alpha = 2$. For the right half plane, $\alpha = 1$, but Mathlib allows $c < 2$ by asking a little more on the real axis: the function must be bounded there, or tend to $0$. One proof splits the half plane into two quadrants.

::: mathlib
`PhragmenLindelof.quadrant_I` · `Mathlib.Analysis.Complex.PhragmenLindelof`

The growth is `exp (B * ‖z‖ ^ c)` with `c < 2`, and the bounds are on the two half axes. There are versions `quadrant_II` to `quadrant_IV`. The half plane forms are `PhragmenLindelof.right_half_plane_of_bounded_on_real` and `PhragmenLindelof.right_half_plane_of_tendsto_zero_on_real`, and the horizontal strip is `PhragmenLindelof.horizontal_strip`.

<?decl PhragmenLindelof.quadrant_I?>
:::

**Theorem (Hadamard three lines).** Let $f$ be holomorphic up to the boundary on $S(0, 1)$ and bounded on $\overline{S}(0, 1)$. Let $|f| \le M_0$ on $\operatorname{Re} z = 0$ and $|f| \le M_1$ on $\operatorname{Re} z = 1$, with $M_0, M_1 > 0$. Then for $0 \le \operatorname{Re} z = x \le 1$,
$$|f(z)| \le M_0^{1 - x} M_1^{x}.$$

*Proof.* Let $h(z) = M_0^{z - 1} M_1^{-z} f(z)$, where $M^w = e^{w \log M}$ for $M > 0$. The factor is entire and $|M_0^{z - 1} M_1^{-z}| = M_0^{x - 1} M_1^{-x}$, which is bounded for $0 \le x \le 1$. So $h$ is holomorphic up to the boundary and bounded on the closed strip. A bounded function satisfies the growth condition with $c = 0$, $B = 0$. On the line $x = 0$, $|h| \le M_0^{-1} M_0 = 1$, and on $x = 1$, $|h| \le M_1^{-1} M_1 = 1$. The theorem gives $|h| \le 1$, which is the claim. $\square$

**Corollary (Convexity).** For $f$ as in the theorem with $M(x) > 0$ for all $x \in [0, 1]$, the function $x \mapsto \log M(x)$ is convex on $[0, 1]$.

*Proof.* Let $0 \le x_0 < x_1 \le 1$ and $x = (1 - t)x_0 + t x_1$. The map $w \mapsto x_0 + (x_1 - x_0)w$ sends $S(0, 1)$ onto $S(x_0, x_1)$. Apply the theorem to $w \mapsto f(x_0 + (x_1 - x_0)w)$ with $M_0 = M(x_0)$, $M_1 = M(x_1)$, at $\operatorname{Re} w = t$. This gives $M(x) \le M(x_0)^{1 - t} M(x_1)^t$. Take logarithms. $\square$

::: mathlib
`Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip₀₁'` · `Mathlib.Analysis.Complex.Hadamard`

With `BddAbove (norm ∘ f '' verticalClosedStrip 0 1)` and bounds `a`, `b` on the two lines, it gives `‖f z‖ ≤ a ^ (1 - z.re) * b ^ z.re`. The form with $M(0)$ and $M(1)$ is `Complex.HadamardThreeLines.norm_le_interpStrip_of_mem_verticalClosedStrip₀₁`, where `interpStrip f z` is $M(0)^{1 - z} M(1)^{z}$, with a special case when a supremum is $0$. A general strip `l < u` is `Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'`.

<?decl Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip₀₁'?>
:::

### Examples

**Example (The growth limit is sharp).** On $S(-\pi/2, \pi/2)$, of width $\pi$, let $f(z) = \exp(e^{-iz})$. For $z = \pm\pi/2 + iy$, $e^{-iz} = e^{y} e^{\mp i\pi/2} = \mp i e^{y}$, so $|f(z)| = |\exp(\mp i e^y)| = 1$. On the imaginary axis, $f(iy) = \exp(e^{y})$, which is unbounded. Here $|f(z)| \le \exp(e^{|\operatorname{Im} z|})$, the growth with $c = 1 = \pi/(b - a)$. So the condition $c < \pi/(b - a)$ cannot be relaxed to $c \le \pi/(b - a)$.

**Example (Three lines for a Gaussian).** Let $f(z) = e^{z^2}$. Then $|f(x + iy)| = e^{x^2 - y^2}$, which is bounded on $\overline{S}(0, 1)$, and $M(x) = e^{x^2}$. The theorem gives $e^{x^2} \le e^{0 \cdot (1 - x)} e^{1 \cdot x} = e^x$, which holds for $0 \le x \le 1$. Here $\log M(x) = x^2$ is convex, as the corollary says.

### The library around it

The two files are independent. `Mathlib.Analysis.Complex.PhragmenLindelof` has each domain with an `eqOn` form for uniqueness, and `Mathlib.Analysis.Complex.Hadamard` proves the three lines theorem by the method of this section.

Common errors of a learner:

- Forgetting the boundedness hypothesis `BddAbove` in the three lines theorem. The function $\exp(e^{-iz})$ above, shifted to $S(0, 1)$ and scaled, shows that some growth condition is needed.
- Writing the growth condition with $|z|$ in place of $|\operatorname{Im} z|$ for a strip. The real part is bounded in the strip, so only $\operatorname{Im} z$ goes to infinity.
- Applying the strip theorem with $c = \pi/(b - a)$. The inequality is strict.

### Exercises

1. (A) Let $f$ be bounded and holomorphic up to the boundary on $S(0, 1)$, with $|f| \le 1$ on both lines. Show that $|f| \le 1$ on the strip.
2. (A) Check the three lines bound for $f(z) = e^{-z}$ on $S(0, 1)$.
3. (B) Let $f$ be holomorphic up to the boundary and bounded on the first quadrant, with $f \to 0$ along both half axes. Show that $|f|$ is bounded by its supremum on the axes. Explain why Mathlib asks only $c < 2$.
4. (B) Show that the function $\exp(e^{-iz})$ of the example is $O(\exp(B e^{c|\operatorname{Im} z|}))$ for $c = 1$ and not for any $c < 1$.
5. (B) Let $f$ be holomorphic up to the boundary on the right half plane, bounded there, and $|f(iy)| \le 1$ for all real $y$. Show that $|f| \le 1$ on the half plane.
6. (C) Prove the Hadamard three circles theorem: for $f$ holomorphic on an annulus $r_1 < |z| < r_2$ and continuous on its closure, $\log \max_{|z| = r} |f(z)|$ is a convex function of $\log r$. Hint: apply the maximum principle to $z^k f(z)^m$ for suitable integers.
7. (C) Let $\varphi(s) = \sum_{n=1}^N a_n n^{-s}$ be a finite Dirichlet sum, not identically $0$. Show that $\log \sup_y |\varphi(x + iy)|$ is a convex function of $x \in \mathbb{R}$. Hint: $\varphi$ is bounded on every closed vertical strip.

### Notes and history

The principle appears in a 1908 paper of Phragmen and Lindelof. The three circles theorem carries the name of Hadamard, and the three lines theorem is its form for a strip, through the map $z \mapsto e^z$. Thorin's proof of the Riesz-Thorin interpolation theorem rests on the three lines theorem.

### Reference

<?reference?>
