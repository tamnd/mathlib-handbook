---
title: The exponential, the trigonometric functions and the argument
kind: theory
modules:
  - Mathlib.Analysis.Complex.Exponential
  - Mathlib.Analysis.Complex.Trigonometric
  - Mathlib.Analysis.Complex.Arg
  - Mathlib.Analysis.Complex.Angle
  - Mathlib.Analysis.Complex.Circle
explains:
  E3: [Complex.exp, Complex.exp_add, Complex.exp_mul_I, Complex.norm_add_eq_iff, Circle]
  E2: [Complex.exp_def, Complex.isCauSeq_exp, Complex.exp_zero, Complex.exp_ne_zero, Complex.exp_neg, Complex.exp_conj, Complex.exp_bound, Complex.expMonoidHom, Complex.ofReal_exp, Real.exp, Complex.norm_exp, Complex.exp_re, Complex.cos, Complex.sin, Complex.cosh, Complex.sinh, Complex.two_cos, Complex.two_sin, Complex.cos_mul_I, Complex.cos_add, Complex.sin_add, Complex.cos_sq_add_sin_sq, Complex.cosh_sq_sub_sinh_sq, Complex.cos_add_sin_mul_I_pow, Real.cos, Real.sin, Complex.sameRay_iff, Complex.angle_eq_abs_arg, Complex.norm_sub_le_angle, Complex.mul_angle_le_norm_sub, Circle.exp, Circle.coe_exp, Circle.exp_add, Circle.instCompactSpace, Circle.coe_inv_eq_conj]
  E1: auto
families: []
requires: [V15.C01, V15.C05, V15.C06, V16.C01]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The exponential, the trigonometric functions and the argument

### Overview

This section defines the exponential by its power series, proves $e^{z+w} = e^z e^w$, and derives from it the trigonometric and hyperbolic functions. Euler's formula $e^{iy} = \cos y + i \sin y$ then connects the exponential with the geometry of the plane: it gives the polar form $z = |z| e^{i\theta}$, the argument $\theta$, and the angle between two complex numbers. The last part studies the unit circle as a compact group.

The section uses the normed field $\mathbb{C}$ of Section 1, and the real functions $\exp$, $\sin$, $\cos$ and the number $\pi$ of Volume 15, Chapters 5 and 6.

### Definitions

**Definition (Exponential).** For $z \in \mathbb{C}$,
$$e^z = \exp z = \sum_{n=0}^{\infty} \frac{z^n}{n!}.$$

The series converges absolutely by the ratio test, and $\mathbb{C}$ is complete.

**Definition (Trigonometric and hyperbolic functions).** For $z \in \mathbb{C}$,
$$\cos z = \frac{e^{iz} + e^{-iz}}{2}, \quad \sin z = \frac{e^{iz} - e^{-iz}}{2i}, \quad \cosh z = \frac{e^{z} + e^{-z}}{2}, \quad \sinh z = \frac{e^{z} - e^{-z}}{2}.$$

**Definition (Unit circle).** The *unit circle* is $\mathbb{T} = \{z \in \mathbb{C} : |z| = 1\}$. It is a subgroup of the multiplicative group $\mathbb{C}^\times$, since $|zw| = |z||w|$ and $|z^{-1}| = |z|^{-1}$.

**Definition (Argument and angle).** The *argument* $\arg z$ of a nonzero $z$ is the unique $\theta \in (-\pi, \pi]$ with $z = |z| e^{i\theta}$; Mathlib also puts $\arg 0 = 0$. The *angle* between nonzero $x$ and $y$ is $\angle(x, y) = |\arg(x/y)| \in [0, \pi]$.

::: mathlib
`Complex.exp` · `Mathlib.Analysis.Complex.Exponential`

Mathlib defines `Complex.exp z` as the limit of the Cauchy sequence of partial sums: `Complex.exp_def : exp z = (exp' z).lim`, where `exp' z` is a `CauSeq` and `Complex.isCauSeq_exp` proves the Cauchy property. The order is reversed from Volume 15: `Real.exp x = (exp x).re`, and `Real.sin`, `Real.cos` are defined in the same way.

<?decl Complex.exp?>
:::

### Theorems and proofs

**Theorem (Addition formula).** For $z, w \in \mathbb{C}$, $e^{z + w} = e^z e^w$. Hence $e^z \ne 0$, $e^{-z} = 1/e^z$, and $\overline{e^z} = e^{\bar z}$.

*Proof.* Both series $\sum z^n/n!$ and $\sum w^n/n!$ converge absolutely. By the theorem on the Cauchy product (Volume 15, Chapter 1), their product is the sum of the series $\sum_n c_n$ with
$$c_n = \sum_{k=0}^{n} \frac{z^k}{k!} \frac{w^{n-k}}{(n-k)!} = \frac{1}{n!} \sum_{k=0}^{n} \binom{n}{k} z^k w^{n-k} = \frac{(z + w)^n}{n!},$$
by the binomial theorem, which holds in any commutative ring. So $e^z e^w = e^{z+w}$. With $w = -z$ this gives $e^z e^{-z} = e^0 = 1$, so $e^z \ne 0$ and $e^{-z} = 1/e^z$. Conjugation is continuous and maps the partial sums of $e^z$ to those of $e^{\bar z}$. $\square$

**Theorem (Tail estimate).** For $|z| \le 1$ and $n \ge 1$,
$$\Big| e^z - \sum_{m=0}^{n-1} \frac{z^m}{m!} \Big| \le |z|^n \frac{n+1}{n!\, n}.$$

*Proof.* The left side is at most $\sum_{m \ge n} |z|^m/m!$. For $m = n + k$, $m! \ge n!\,(n+1)^k$ and $|z|^m \le |z|^n$. So the sum is at most
$$\frac{|z|^n}{n!} \sum_{k \ge 0} \frac{1}{(n+1)^k} = \frac{|z|^n}{n!} \cdot \frac{n+1}{n}. \qquad \square$$

With $n = 1$ it gives $|e^z - 1| \le 2|z|$ for $|z| \le 1$, so $\exp$ is continuous at $0$, and by the addition formula everywhere.

**Theorem (Euler's formula).** For $z \in \mathbb{C}$, $e^{iz} = \cos z + i \sin z$, $\cos^2 z + \sin^2 z = 1$, and $\cos(iz) = \cosh z$. For real $y$, $\cos y$ and $\sin y$ are real, $|e^{iy}| = 1$, and $|e^{x + iy}| = e^x$.

*Proof.* The definitions give $\cos z + i \sin z = \tfrac12(e^{iz} + e^{-iz}) + \tfrac12(e^{iz} - e^{-iz}) = e^{iz}$. Multiply this with the same formula for $-z$, using that $\cos$ is even and $\sin$ is odd:
$$1 = e^{iz}e^{-iz} = (\cos z + i\sin z)(\cos z - i \sin z) = \cos^2 z + \sin^2 z.$$
Next $\cos(iz) = \tfrac12(e^{-z} + e^{z}) = \cosh z$. For real $y$, the addition formula for conjugates gives $\overline{e^{iy}} = e^{-iy}$, so $\overline{\cos y} = \cos y$ and $\overline{\sin y} = \sin y$. Then $|e^{iy}|^2 = e^{iy}\overline{e^{iy}} = e^0 = 1$. Finally $|e^{x+iy}| = |e^x||e^{iy}| = e^x$, because $e^x$ is a positive real for real $x$. $\square$

The addition formulas for $\cos$ and $\sin$ follow from $e^{i(z+w)} = e^{iz}e^{iw}$ and the definitions. De Moivre's formula $(\cos z + i \sin z)^n = \cos nz + i \sin nz$ is $(e^{iz})^n = e^{inz}$.

::: mathlib
`Complex.exp_mul_I` · `Mathlib.Analysis.Complex.Trigonometric`

The statement is `exp (x * I) = cos x + sin x * I` for `x : ℂ`. The modulus is `Complex.norm_exp : ‖exp z‖ = Real.exp z.re`, and `Complex.exp_re` gives `(exp x).re = Real.exp x.re * Real.cos x.im`. De Moivre is `Complex.cos_add_sin_mul_I_pow`.

<?decl Complex.exp_mul_I?>
:::

**Theorem (Periodicity).** $e^z = 1$ if and only if $z = 2\pi i k$ for some $k \in \mathbb{Z}$. Hence $\exp$ is periodic with period $2\pi i$, and $e^z = e^w$ if and only if $z - w \in 2\pi i\mathbb{Z}$.

*Proof.* Write $z = x + iy$. If $e^z = 1$ then $e^x = |e^z| = 1$, so $x = 0$. Then $\cos y + i \sin y = 1$, so $\cos y = 1$ and $\sin y = 0$. By Volume 15, Chapter 6, this holds exactly when $y \in 2\pi \mathbb{Z}$. Conversely $e^{2\pi i k} = \cos 2\pi k + i \sin 2\pi k = 1$. The last claim follows from $e^z/e^w = e^{z-w}$. $\square$

::: mathlib
`Complex.exp_eq_one_iff` · `Mathlib.Analysis.SpecialFunctions.Complex.Log`

The periodicity needs $\pi$, so it lives in the special functions of Volume 15: `Complex.exp_periodic : Function.Periodic exp (2 * π * I)` and `Complex.exp_eq_one_iff : exp x = 1 ↔ ∃ n : ℤ, x = n * (2 * π * I)`. The polar form is `Complex.norm_mul_exp_arg_mul_I : ‖x‖ * exp (arg x * I) = x`, and the logarithm `Complex.log` is a right inverse of `exp` with values in the strip $-\pi < \operatorname{Im} \le \pi$.

<?decl Complex.exp_eq_one_iff?>
<?decl Complex.arg?>
:::

**Theorem (Equality in the triangle inequality).** For $x, y \in \mathbb{C}$, $|x + y| = |x| + |y|$ if and only if $x = 0$, or $y = 0$, or $\arg x = \arg y$.

*Proof.* Expand $|x + y|^2 = |x|^2 + |y|^2 + 2\operatorname{Re}(x \bar y)$. Equality in the triangle inequality holds if and only if $\operatorname{Re}(x \bar y) = |x||y| = |x \bar y|$. And $\operatorname{Re} u = |u|$ holds exactly when $u$ is a nonnegative real. Let $x, y \ne 0$ and write $x = |x|e^{i\alpha}$, $y = |y| e^{i\beta}$. Then $x\bar y = |x||y| e^{i(\alpha - \beta)}$, and it is a positive real if and only if $e^{i(\alpha - \beta)} = 1$. By periodicity, $\alpha - \beta \in 2\pi\mathbb{Z}$, and since $\alpha, \beta \in (-\pi, \pi]$, this means $\alpha = \beta$. $\square$

**Theorem (Angle and chord).** For $|x| = |y| = 1$, with $\theta = \angle(x, y)$,
$$\frac{2}{\pi}\,\theta \le |x - y| \le \theta.$$

*Proof.* Put $u = x/y$. Then $|u| = 1$, $|x - y| = |u - 1|$ and $u = e^{\pm i\theta}$. Compute $|e^{i\theta} - 1|^2 = (\cos\theta - 1)^2 + \sin^2\theta = 2 - 2\cos\theta = 4\sin^2(\theta/2)$. Since $\theta/2 \in [0, \pi/2]$, $|x - y| = 2\sin(\theta/2)$. On $[0, \pi/2]$ the sine is concave, so it lies above its chord: $\sin t \ge 2t/\pi$. It also satisfies $\sin t \le t$ (Volume 15, Chapter 6). Put $t = \theta/2$. $\square$

::: mathlib
`Complex.norm_add_eq_iff` · `Mathlib.Analysis.Complex.Arg`

The statement is `‖x + y‖ = ‖x‖ + ‖y‖ ↔ x = 0 ∨ y = 0 ∨ x.arg = y.arg`. The angle is the unoriented angle of Euclidean geometry, `InnerProductGeometry.angle`, and `Complex.angle_eq_abs_arg` gives `angle x y = |(x / y).arg|`. The two bounds are `Complex.norm_sub_le_angle` and `Complex.mul_angle_le_norm_sub`.

<?decl Complex.norm_add_eq_iff?>
:::

**Theorem (The circle group).** $\mathbb{T}$ is a compact abelian topological group, and $t \mapsto e^{it}$ is a continuous surjective homomorphism $\mathbb{R} \to \mathbb{T}$ with kernel $2\pi\mathbb{Z}$. On $\mathbb{T}$, $z^{-1} = \bar z$.

*Proof.* $\mathbb{T}$ is the preimage of $1$ under the continuous norm, so it is closed. It is bounded, so it is compact by Section 1. The map $t \mapsto e^{it}$ lands in $\mathbb{T}$ by Euler's formula, and it is a homomorphism by the addition formula. Its kernel is $2\pi\mathbb{Z}$ by periodicity. For surjectivity, let $z = a + ib \in \mathbb{T}$. Then $a^2 + b^2 = 1$, and Volume 15, Chapter 6 gives $t$ with $\cos t = a$ and $\sin t = b$. Finally $z \bar z = |z|^2 = 1$. $\square$

::: mathlib
`Circle` · `Mathlib.Analysis.Complex.Circle`

`Circle` is a type whose elements are complex numbers of norm one, with a coercion `Circle → ℂ`. It carries `CommGroup`, `IsTopologicalGroup` and `CompactSpace` instances, and `Circle.coe_inv_eq_conj` says that the inverse is the conjugate. `Circle.exp : C(ℝ, Circle)` is the parametrization, with `Circle.coe_exp : ↑(exp t) = Complex.exp (t * I)` and `Circle.exp_add`. Its surjectivity `Circle.exp_surjective` lives in the special functions. Chapter 7 uses it as the target of `Real.fourierChar`.

<?decl Circle?>
<?decl Circle.exp_surjective?>
:::

### Examples

**Example.** $e^{i\pi} = \cos\pi + i\sin\pi = -1$. So $e^{i\pi} + 1 = 0$, and $e^{i\pi/2} = i$.

**Example.** $\cos i = \cosh 1 = (e + e^{-1})/2 \approx 1.543$. So $\cos$ is not bounded on $\mathbb{C}$: $\cos(iy) = \cosh y \to \infty$. Chapter 3 shows that this must happen: a bounded entire function is constant.

**Example.** $|e^{2 + 3i}| = e^2$, and $\arg e^{2 + 3i} = 3$, since $3 \in (-\pi, \pi]$. But $\arg e^{4i} = 4 - 2\pi$, since $4 > \pi$.

### The library around it

Common errors of a learner:

- Writing `exp (I * x)`. The lemmas use `exp (x * I)`; rewrite with `mul_comm` first.
- Expecting `Complex.arg` and `Complex.log` in `Mathlib.Analysis.Complex`. They are in `Mathlib.Analysis.SpecialFunctions.Complex`, together with the periodicity of `exp`.
- Assuming $\arg(zw) = \arg z + \arg w$. It holds only modulo $2\pi$.

### Exercises

1. (A) Compute $e^{\pi i/3}$ and $(1 + i\sqrt 3)^6$. Hint: $1 + i\sqrt 3 = 2e^{\pi i/3}$.
2. (A) Show that $|\sin(x + iy)|^2 = \sin^2 x + \sinh^2 y$. Hint: use the addition formula and $\sin(iy) = i\sinh y$.
3. (B) Find all $z$ with $\cos z = 2$. Hint: put $w = e^{iz}$ and solve $w^2 - 4w + 1 = 0$.
4. (B) Show that the zeros of $\sin$ on $\mathbb{C}$ are the real numbers $k\pi$. Hint: $\sin z = 0$ means $e^{2iz} = 1$.
5. (B) Show that $\exp : \mathbb{C} \to \mathbb{C}^\times$ is onto. Hint: use the polar form and $\exp$ on $\mathbb{R}$.
6. (C) Show that a continuous homomorphism $\chi : \mathbb{R} \to \mathbb{T}$ has the form $\chi(t) = e^{i\lambda t}$ for some real $\lambda$. Hint: lift $\chi$ near $0$ through $t \mapsto e^{it}$, and show that the lift is additive.

### Notes and history

Euler published the formula $e^{ix} = \cos x + i \sin x$ in his *Introductio in analysin infinitorum* of 1748.

### Reference

<?reference?>
