---
title: Operations on smooth maps and bump functions
kind: theory
modules:
  - Mathlib.Analysis.Calculus.ContDiff.Basic
  - Mathlib.Analysis.Calculus.ContDiff.Comp
  - Mathlib.Analysis.Calculus.ContDiff.Operations
  - Mathlib.Analysis.Calculus.BumpFunction.Basic
  - Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
  - Mathlib.Analysis.Calculus.ContDiff.Polynomial
  - Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
  - Mathlib.Analysis.Calculus.ContDiff.WithLp
  - Mathlib.Analysis.Calculus.AddTorsor.AffineMap
  - Mathlib.Analysis.Calculus.AddTorsor.Coord
explains:
  E3: [ContDiff.comp, ContDiffBump]
  E2: [ContDiff.add, ContDiff.mul, ContDiff.inv, contDiffAt_ringInverse, IsBoundedBilinearMap.contDiff, ContinuousLinearMap.contDiff, ContDiff.prodMk, ContDiff.clm_comp, HasContDiffBump, ContDiffBump.contDiff, ContDiffBump.one_of_mem_closedBall, ContDiffBump.support_eq]
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

## Operations on smooth maps and bump functions

### Overview

To show that a map is $C^n$, one rarely computes $D^n f$. One builds the map from linear and bilinear maps by composition, products and inverses, and this section proves that these operations preserve $C^n$. The proofs are inductions with the recursive form of Section 2: write $Df$ as a composition of maps of the same kind.

The second half constructs smooth functions with compact support from $e^{-1/x}$. They do not exist in every Banach space, so Mathlib states their existence as a class of the space.

### Definitions

For an open set $U \subseteq E$, a map $f : U \to F$ is $C^n$ on $U$ if the conditions of Section 2 hold on $U$. The proofs below are for maps on $E$ and hold on open sets without change.

**Definition (Bounded bilinear map).** A map $b : E \times F \to G$ is a *bounded bilinear map* if it is bilinear and there is $C$ with $\|b(x, y)\| \le C\|x\|\|y\|$.

Examples are the product of a normed algebra, the scalar product of a Hilbert space, the evaluation $L(E, F) \times E \to F$, and the composition $L(F, G) \times L(E, F) \to L(E, G)$, $(S, T) \mapsto S \circ T$.

**Definition (Bump function).** Let $E$ be a real normed space, $c \in E$ and $0 < r < R$. A *bump function* for $(c, r, R)$ is a map $\varphi : E \to [0, 1]$ of class $C^\infty$ with $\varphi = 1$ on the closed ball $\bar B(c, r)$ and $\{\varphi \ne 0\} = B(c, R)$.

::: mathlib
`ContDiffBump` · `Mathlib.Analysis.Calculus.BumpFunction.Basic`

A term `f : ContDiffBump c` holds only two radii `f.rIn < f.rOut`, with `0 < f.rIn`. The function comes from the class `HasContDiffBump E`, which says that the space has a smooth family of bump functions; under it `f` coerces to `E → ℝ`. The lemmas are `ContDiffBump.contDiff`, `ContDiffBump.one_of_mem_closedBall` ($f = 1$ on the closed ball of radius `rIn`) and `ContDiffBump.support_eq` (the support is the open ball of radius `rOut`).

<?decl ContDiffBump?>
<?decl HasContDiffBump?>
:::

### Theorems and proofs

**Theorem (Linear and bilinear maps).** A continuous linear map $A : E \to F$ is $C^\infty$. A bounded bilinear map $b : E \times F \to G$ is $C^\infty$.

*Proof.* $DA(x) = A$ for every $x$, so $DA$ is constant. A constant map is $C^\infty$ by induction, since its derivative is the constant $0$. So $A$ is $C^\infty$. For $b$, Chapter 2 gives $Db(x, y)(h, k) = b(x, k) + b(h, y)$. The map $(x, y) \mapsto Db(x, y)$ is linear from $E \times F$ to $L(E \times F, G)$, and $\|Db(x, y)\| \le C(\|x\| + \|y\|)$, so it is continuous linear. By the first part it is $C^\infty$, so $b$ is $C^\infty$. $\square$

**Lemma (Composition with a linear map; pairs).** Let $f : E \to F$ and $g : E \to G$ be $C^n$, and let $A \in L(F, G')$. Then $A \circ f$ and $x \mapsto (f(x), g(x))$ are $C^n$.

*Proof.* Induction on $n$ for all spaces at the same time. For $n = 0$ both maps are continuous. Let $f, g$ be $C^{n+1}$. By Chapter 2, $D(A \circ f)(x) = A_*(Df(x))$, where $A_* : L(E, F) \to L(E, G')$, $T \mapsto A \circ T$, is continuous linear. Since $Df$ is $C^n$, the hypothesis applied to $A_*$ and $Df$ gives that $D(A \circ f)$ is $C^n$. For the pair, $D(f, g)(x) = J(Df(x), Dg(x))$, where $J : L(E, F) \times L(E, G) \to L(E, F \times G)$, $J(S, T)h = (Sh, Th)$, is continuous linear. By the hypothesis $x \mapsto (Df(x), Dg(x))$ is $C^n$, and then $J \circ (Df, Dg)$ is $C^n$. $\square$

**Theorem (Chain rule for $C^n$).** Let $n \in \mathbb{N} \cup \{\infty\}$. If $f : E \to F$ and $g : F \to G$ are $C^n$, then $g \circ f$ is $C^n$.

*Proof.* For $n = \infty$ apply the finite case to each $n$. For finite $n$, induction on $n$, for all spaces $E, F, G$ at the same time. For $n = 0$, a composition of continuous maps is continuous.

Let $f$ and $g$ be $C^{n+1}$. Then $g \circ f$ is differentiable, and the chain rule of Chapter 2 gives
$$D(g \circ f)(x) = Dg(f(x)) \circ Df(x) = \Phi\big(Dg(f(x)), Df(x)\big),$$
where $\Phi : L(F, G) \times L(E, F) \to L(E, G)$ is the composition, a bounded bilinear map. Now:

1. $Dg$ is $C^n$, and $f$ is $C^{n+1}$, hence $C^n$. By the induction hypothesis, $Dg \circ f$ is $C^n$.
2. $Df$ is $C^n$, so the pair $x \mapsto (Dg(f(x)), Df(x))$ is $C^n$ by the lemma.
3. $\Phi$ is $C^\infty$, hence $C^n$. By the induction hypothesis again, $\Phi \circ (Dg \circ f, Df)$ is $C^n$.

So $D(g \circ f)$ is $C^n$, and $g \circ f$ is $C^{n+1}$. $\square$

The induction hypothesis is used twice, for different spaces. This is why the statement must be proved for all spaces at once.

**Corollary (Algebraic operations).** Let $f, g : E \to F$ be $C^n$. Then $f + g$ and $\lambda f$ are $C^n$. If $F = \mathbb{A}$ is a normed algebra, $fg$ is $C^n$. If $L : E \to L(F, G)$ is $C^n$, then $x \mapsto L(x)f(x)$ is $C^n$.

*Proof.* Each map is $b \circ (f, g)$ for a bounded bilinear or a continuous linear map $b$: the addition $F \times F \to F$, the product of $\mathbb{A}$ and the evaluation. Apply the lemma, the theorem on bilinear maps and the chain rule. $\square$

**Theorem (Inversion).** Let $\mathbb{A}$ be a Banach algebra with unit and $U$ its open set of units. The map $\iota : U \to \mathbb{A}$, $\iota(a) = a^{-1}$, is $C^\infty$.

*Proof.* Chapter 2 shows that $\iota$ is differentiable with $D\iota(a)h = -a^{-1}ha^{-1}$. Let $Q : \mathbb{A} \times \mathbb{A} \to L(\mathbb{A}, \mathbb{A})$, $Q(a, b)h = -ahb$. It is bilinear with $\|Q(a, b)\| \le \|a\|\|b\|$. So $D\iota = Q \circ (\iota, \iota)$. Show by induction that $\iota$ is $C^n$ on $U$. It is continuous, as it is differentiable. If $\iota$ is $C^n$, then $(\iota, \iota)$ is $C^n$ and $Q \circ (\iota, \iota) = D\iota$ is $C^n$, so $\iota$ is $C^{n+1}$. $\square$

The case $\mathbb{A} = \mathbb{K}$ shows that $1/f$ is $C^n$ when $f$ is $C^n$ without zeros.

::: mathlib
`ContDiff.comp` · `Mathlib.Analysis.Calculus.ContDiff.Comp`

`ContDiff.comp : ContDiff 𝕜 n g → ContDiff 𝕜 n f → ContDiff 𝕜 n (g ∘ f)`, for every `n : WithTop ℕ∞`, with the local form `ContDiffAt.comp`. The linear and bilinear cases are `ContinuousLinearMap.contDiff` and `IsBoundedBilinearMap.contDiff`, the pairs `ContDiff.prodMk`. The family `ContDiff.clm_comp` gives `ContDiff 𝕜 n fun x ↦ (g x).comp (f x)`.

<?decl ContDiff.comp?>
<?decl IsBoundedBilinearMap.contDiff?>
<?decl ContDiff.clm_comp?>
:::

::: mathlib
`ContDiff.inv` · `Mathlib.Analysis.Calculus.ContDiff.Operations`

The algebraic rules are `ContDiff.add`, `ContDiff.mul` (in a normed algebra), `ContDiff.inv` (in a normed field, with the hypothesis `∀ x, f x ≠ 0`) and `contDiffAt_ringInverse`. The last one states `ContDiffAt 𝕜 n Ring.inverse ↑x` at a unit `x : Rˣ` of a normed algebra with summable geometric series, for instance a complete one. Here `Ring.inverse` sends a non-unit to $0$.

<?decl ContDiff.mul?>
<?decl ContDiff.inv?>
<?decl contDiffAt_ringInverse?>
:::

**Lemma (A smooth function that vanishes on a half-line).** Let $f(x) = e^{-1/x}$ for $x > 0$ and $f(x) = 0$ for $x \le 0$. Then $f$ is $C^\infty$ on $\mathbb{R}$, $f > 0$ on $(0, \infty)$, and $f^{(k)}(0) = 0$ for every $k$.

*Proof.* Volume 15, Chapter 4 proves this. By Section 2, $C^\infty$ on $\mathbb{R}$ is the class $C^\infty$ of Volume 15. $\square$

**Corollary (Smooth transition).** The function $\psi(x) = f(x)/(f(x) + f(1 - x))$ is $C^\infty$ on $\mathbb{R}$, with $0 \le \psi \le 1$, $\psi(x) = 0$ for $x \le 0$, $\psi(x) = 1$ for $x \ge 1$, and $\psi(x) > 0$ for $x > 0$.

*Proof.* The denominator is positive: if $x > 0$ then $f(x) > 0$, and if $x \le 0$ then $1 - x \ge 1$ and $f(1 - x) > 0$. So $\psi$ is $C^\infty$ by the rules for sums, products and inverses. For $x \le 0$ the numerator is $0$. For $x \ge 1$, $f(1 - x) = 0$ and $\psi(x) = 1$. Since $f \ge 0$, $0 \le \psi \le 1$. $\square$

**Theorem (Bump functions in inner product spaces).** Let $H$ be a real inner product space, $c \in H$ and $0 < r < R$. Then
$$\varphi(y) = \psi\Big(\frac{R - \|y - c\|}{R - r}\Big)$$
is a bump function for $(c, r, R)$.

*Proof.* Let $t(y) = (R - \|y - c\|)/(R - r)$. Then $t(y) \ge 1$ if and only if $\|y - c\| \le r$, and $t(y) > 0$ if and only if $\|y - c\| < R$. So $\varphi = 1$ on $\bar B(c, r)$, $\varphi = 0$ outside $B(c, R)$, and $\varphi > 0$ on $B(c, R)$. For smoothness: on $\{y \ne c\}$, the map $y \mapsto \|y - c\| = \sqrt{\langle y - c, y - c\rangle}$ is $C^\infty$: the scalar product is bounded bilinear and $\sqrt{\cdot}$ is $C^\infty$ on $(0, \infty)$. So $\varphi$ is $C^\infty$ there by the chain rule. On the ball $B(c, r)$, $\varphi = 1$ is constant. Since $C^\infty$ is a local property, $\varphi$ is $C^\infty$ on $H$. $\square$

The norm is not differentiable at $c$, which is why the argument needs the plateau $\varphi = 1$ near $c$. In a general Banach space a bump function need not exist: $\ell^1$ has none of class $C^1$. The proof needs the geometry of Banach spaces and is not given here.

### Examples

**Example (Determinant and inverse matrix).** On $M_n(\mathbb{R})$, $\det$ is a polynomial in the entries, a sum of products of coordinate functions, which are continuous linear. So $\det$ is $C^\infty$. By the inversion theorem, $A \mapsto A^{-1}$ is $C^\infty$ on $GL_n(\mathbb{R})$. Its derivative at $I$ is $H \mapsto -H$.

**Example (A smooth Urysohn function).** Let $K \subseteq \mathbb{R}^d$ be compact and $U \supseteq K$ open. For each $x \in K$ pick $r_x > 0$ with $\bar B(x, 3r_x) \subseteq U$, and a bump $\varphi_x$ for $(x, r_x, 2r_x)$. The balls $B(x, r_x)$ cover $K$, so finitely many $B(x_i, r_i)$ cover it. Put $\varphi = 1 - \prod_i (1 - \varphi_i)$. It is $C^\infty$ with values in $[0, 1]$. On $K$ some $\varphi_i = 1$, so $\varphi = 1$. Outside $\bigcup_i B(x_i, 2r_i)$ every $\varphi_i = 0$, so $\varphi = 0$. So $\varphi$ is $1$ on $K$ and has compact support in $U$.

### The library around it

The proof of `ContDiff.comp` in Mathlib does not use the induction above. It goes through `ContDiffWithinAt.comp`, which writes the Taylor series of $g \circ f$ explicitly with `FormalMultilinearSeries.taylorComp`, the formula of Faà di Bruno (`HasFTaylorSeriesUpToOn.comp`). For bump functions, `hasContDiffBump_of_innerProductSpace` is the instance of the theorem above. A second instance covers finite-dimensional real spaces. In finite dimension `exists_contDiff_tsupport_subset` gives a smooth function with compact support in a neighbourhood $s$ of $x$, with value $1$ at $x$. The function $f$ of the lemma is `expNegInvGlue` and $\psi$ is `Real.smoothTransition`.

Several small modules apply the operations to special maps. When $E$ is finite-dimensional and $𝕜$ is complete, a map $f : D \to (E \to_L F)$ is $C^n$ if and only if each $x \mapsto f(x)\,y$ is $C^n$ (`contDiff_clm_apply_iff`, in `Mathlib.Analysis.Calculus.ContDiff.FiniteDimension`). So `contDiff_succ_iff_fderiv_apply` tests the derivative on fixed vectors: $f$ is $C^{n+1}$ if and only if $f$ is differentiable, each $x \mapsto Df(x)\,y$ is $C^n$, and $f$ is analytic when $n = \omega$. A polynomial $P$ with coefficients in an algebra over $𝕜$ is smooth as the map $x \mapsto P(x)$ (`Polynomial.contDiff_aeval`). For $p$ in `ℝ≥0∞`, the maps `WithLp.toLp p` and `WithLp.ofLp` are smooth, and a map into `PiLp p E` is $C^n$ if and only if each coordinate is (`contDiff_piLp`), in `Mathlib.Analysis.Calculus.ContDiff.WithLp`. Continuous affine maps are smooth (`ContinuousAffineMap.contDiff`), and so is the interpolation $(p, q, t) \mapsto p + t(q - p)$ (`AffineMap.contDiff_lineMap_uncurry`, `ContDiff.lineMap`). In finite dimension the barycentric coordinates of an affine basis are smooth (`contDiff_barycentric_coord`).

For a normed algebra $𝕜'$ over $𝕜$, a map that is $C^n$ over $𝕜'$ has the same iterated derivatives over $𝕜$, after the restriction of scalars of the multilinear maps: `ContDiffAt.restrictScalars_iteratedFDeriv`, with the forms `ContDiffAt.restrictScalars_iteratedFDeriv_eventuallyEq` and `ContDiffWithinAt.restrictScalars_iteratedFDerivWithin_eventuallyEq`, in `Mathlib.Analysis.Calculus.ContDiff.RestrictScalars`. For example, the real iterated derivatives of a holomorphic map are its complex ones.

Common errors of a learner:

- Forgetting the hypothesis of nonvanishing in `ContDiff.inv`. Without it, `f⁻¹` is the junk inverse and is not smooth.
- Using `ContDiff.comp` with two different orders `n`. Lower one with `ContDiff.of_le` first.
- Expecting `ContDiffBump c` to be a function. It is a pair of radii, and the function needs the instance `HasContDiffBump E`.

### Exercises

1. (A) Show that $x \mapsto \sin(\|x\|^2)$ is $C^\infty$ on a real Hilbert space, and compute its derivative.
2. (A) Show that the smooth transition $\psi$ is strictly increasing on $[0, 1]$. Hint: compute $\psi'$ on $(0, 1)$ and use $f' > 0$ on $(0, \infty)$.
3. (B) Let $\mathbb{A}$ be a Banach algebra. Show that $a \mapsto a^n$ is $C^\infty$, and that $D(a \mapsto a^n)(a)h = \sum_{i=0}^{n-1} a^i h a^{n-1-i}$.
4. (B) Compute $D^2\iota(a)(k, h)$ for the inversion of a Banach algebra. Hint: the result is $a^{-1}ka^{-1}ha^{-1} + a^{-1}ha^{-1}ka^{-1}$.
5. (B) Let $a < b$. Construct a $C^\infty$ function on $\mathbb{R}$ that is positive exactly on $(a, b)$, and a $C^\infty$ function that is $0$ on $(-\infty, a]$, $1$ on $[b, \infty)$ and increasing.
6. (C) Let $\mathcal{U} = (U_i)$ be a finite open cover of a compact set $K \subseteq \mathbb{R}^d$. Construct $C^\infty$ functions $\chi_i \ge 0$ with compact support in $U_i$ and $\sum_i \chi_i = 1$ on $K$. Hint: take Urysohn functions $\psi_i$ for compact sets $K_i \subseteq U_i$ that cover $K$, and divide $\psi_i \varphi$ by $\sum_j \psi_j$, with $\varphi$ a Urysohn function for $K$ in $\{\sum_j \psi_j > 0\}$.

### Notes and history

Cauchy used $e^{-1/x^2}$ in 1823 as a smooth function that is not the sum of its Taylor series (Volume 15, Chapter 4).

### Reference

<?reference?>
