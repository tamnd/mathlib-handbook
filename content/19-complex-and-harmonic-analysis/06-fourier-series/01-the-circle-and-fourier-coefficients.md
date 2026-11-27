---
title: The circle and Fourier coefficients
kind: theory
modules:
  - Mathlib.Analysis.Fourier.AddCircle
explains:
  E3: [AddCircle.fourier, AddCircle.haarAddCircle, AddCircle.fourierCoeff, AddCircle.fourierCoeffOn, AddCircle.fourierCoeffOn_of_hasDerivAt]
  E2: [AddCircle.fourier_coe_apply, AddCircle.fourier_add, AddCircle.fourier_norm, AddCircle.volume_eq_smul_haarAddCircle, AddCircle.integral_haarAddCircle, AddCircle.fourierCoeff_eq_intervalIntegral, AddCircle.fourierCoeff_liftIco_eq, AddCircle.fourierCoeff_fourier, AddCircle.fourierCoeff_const, AddCircle.fourierCoeff_congr_ae, AddCircle.orthonormal_fourier, AddCircle.hasDerivAt_fourier]
  E1: auto
families: []
requires: [V13, V15, V16.C06, V18.C05, V18.C07, V18.C08, V19.C01]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The circle and Fourier coefficients

### Overview

A function $f : \mathbb{R} \to \mathbb{C}$ with period $T$ is the same thing as a function on the quotient group $\mathbb{R}/T\mathbb{Z}$. Fourier analysis writes such a function as a sum of the simplest periodic functions, the exponentials $e^{2\pi i n x/T}$ with $n \in \mathbb{Z}$. The coefficient of $e^{2\pi i n x/T}$ is an average of $f$ against the conjugate exponential. This section sets up the circle as a group with a probability measure, defines the exponentials as continuous characters, defines the Fourier coefficients, and proves the two facts on which the rest of the chapter rests: the characters are orthonormal, and differentiation multiplies the $n$-th coefficient by $2\pi i n/T$.

The normalisation of this chapter is the one of Mathlib. The circle carries the Haar measure of total mass $1$, so the coefficient is a mean value:
$$\hat f(n) = \frac{1}{T}\int_0^T e^{-2\pi i n x/T} f(x)\,dx.$$
The sign in the exponent is negative in the coefficient and positive in the character.

### Definitions

**Definition (The circle).** Let $T > 0$. The *additive circle* of period $T$ is the quotient group $\mathbb{R}/T\mathbb{Z}$ with the quotient topology. It is a compact abelian topological group. A function on it is a function on $\mathbb{R}$ with period $T$.

The circle carries two natural measures. The image of Lebesgue measure on $[0, T)$ has total mass $T$. The Haar measure normalised to total mass $1$ is $\mu_T = T^{-1}$ times the first one. So for an integrable $f$,
$$\int f\,d\mu_T = \frac{1}{T}\int_a^{a+T} f(x)\,dx \quad \text{for every } a \in \mathbb{R}.$$

::: mathlib
`AddCircle.haarAddCircle` · `Mathlib.Analysis.Fourier.AddCircle`

The type `AddCircle T` is defined in `Mathlib.Topology.Instances.AddCircle` as the quotient `ℝ ⧸ zmultiples T`. Most results on it need the instance `Fact (0 < T)`. The measure `haarAddCircle` is the Haar measure with total mass $1$. The default measure `volume` on `AddCircle T` has mass $T$, and `volume_eq_smul_haarAddCircle` states `volume = ENNReal.ofReal T • haarAddCircle`. The lemma `integral_haarAddCircle` turns an integral for `haarAddCircle` into `T⁻¹ •` the `volume` integral.

<?decl AddCircle.haarAddCircle?>
<?decl AddCircle.volume_eq_smul_haarAddCircle?>
<?decl AddCircle.integral_haarAddCircle?>
:::

**Definition (Characters of the circle).** For $n \in \mathbb{Z}$, the function $e_n : \mathbb{R}/T\mathbb{Z} \to \mathbb{C}$ is $e_n(x) = e^{2\pi i n x/T}$. It is well defined because $e^{2\pi i n (x + kT)/T} = e^{2\pi i n x/T} e^{2\pi i nk} = e^{2\pi i n x/T}$ for $k \in \mathbb{Z}$. It is continuous, $|e_n(x)| = 1$, and $e_{m+n} = e_m e_n$. So $e_n$ is a continuous homomorphism from the circle to the unit circle of $\mathbb{C}$, a *character*.

::: mathlib
`AddCircle.fourier` · `Mathlib.Analysis.Fourier.AddCircle`

`fourier n : C(AddCircle T, ℂ)` is a bundled continuous map. The working formula is `fourier_coe_apply`: `fourier n ↑x = Complex.exp (2 * π * I * n * x / T)` for real `x`. The group law is `fourier_add`, and `fourier_norm` states that the sup norm of `fourier n` is $1$.

<?decl AddCircle.fourier?>
<?decl AddCircle.fourier_coe_apply?>
<?decl AddCircle.fourier_add?>
<?decl AddCircle.fourier_norm?>
:::

**Definition (Fourier coefficients).** Let $f : \mathbb{R}/T\mathbb{Z} \to E$ be integrable, with $E$ a complex Banach space. The $n$-th Fourier coefficient of $f$ is
$$\hat f(n) = \int e_{-n}(x)\, f(x)\,d\mu_T(x) = \frac{1}{T}\int_0^T e^{-2\pi i n x/T} f(x)\,dx.$$
For $f : \mathbb{R} \to E$ and an interval $[a, b]$ with $a < b$, the coefficients *on* $[a, b]$ are
$$c_n(f; a, b) = \frac{1}{b - a}\int_a^b e^{-2\pi i n x/(b-a)} f(x)\,dx.$$
They are the coefficients of the function of period $b - a$ that agrees with $f$ on $[a, b)$.

::: mathlib
`AddCircle.fourierCoeff` · `Mathlib.Analysis.Fourier.AddCircle`

`fourierCoeff f n` is `∫ t, fourier (-n) t • f t ∂haarAddCircle`. It takes any `f : AddCircle T → E` and gives `0` when the integrand is not integrable. The form with an interval is `fourierCoeff_eq_intervalIntegral`, valid for every starting point `a`. The coefficients only see `f` almost everywhere: `fourierCoeff_congr_ae`. The bare name `fourierCoeff` without the namespace is a deprecated alias in this edition.

<?decl AddCircle.fourierCoeff?>
<?decl AddCircle.fourierCoeff_eq_intervalIntegral?>
<?decl AddCircle.fourierCoeff_congr_ae?>
:::

::: mathlib
`AddCircle.fourierCoeffOn` · `Mathlib.Analysis.Fourier.AddCircle`

`fourierCoeffOn hab f n`, with `hab : a < b` and `f : ℝ → E`, is the coefficient of `f` on `[a, b]`. The lemma `fourierCoeff_liftIco_eq` identifies it with `fourierCoeff` of the periodic function `AddCircle.liftIco (b - a) a f`.

<?decl AddCircle.fourierCoeffOn?>
<?decl AddCircle.fourierCoeff_liftIco_eq?>
:::

### Theorems and proofs

**Theorem (Orthonormality of the characters).** For $m, n \in \mathbb{Z}$,
$$\int e_m \overline{e_n}\,d\mu_T = \begin{cases} 1 & m = n, \\ 0 & m \ne n. \end{cases}$$
So $(e_n)_{n \in \mathbb{Z}}$ is an orthonormal family in $L^2(\mu_T)$, and $\hat{e_m}(n)$ is $1$ for $n = m$ and $0$ otherwise.

*Proof.* Since $|e_n| = 1$, $\overline{e_n} = e_n^{-1} = e_{-n}$. So $e_m \overline{e_n} = e_{m-n}$. Put $k = m - n$. If $k = 0$, the integrand is $1$ and the integral is $\mu_T(\mathbb{R}/T\mathbb{Z}) = 1$. If $k \ne 0$, the function $x \mapsto \frac{T}{2\pi i k}e^{2\pi i k x/T}$ has derivative $e^{2\pi i k x/T}$. By the fundamental theorem of calculus (Volume 18, Chapter 8),
$$\frac{1}{T}\int_0^T e^{2\pi i k x/T}\,dx = \frac{1}{T}\cdot\frac{T}{2\pi i k}\left(e^{2\pi i k} - 1\right) = 0.$$
The last claim is the same computation: $\hat{e_m}(n) = \int e_{-n} e_m\,d\mu_T = \int e_{m-n}\,d\mu_T$. $\square$

::: mathlib
`AddCircle.orthonormal_fourier` · `Mathlib.Analysis.Fourier.AddCircle`

`orthonormal_fourier` states `Orthonormal ℂ (fourierLp 2)`, where `fourierLp 2 n` is `fourier n` seen as an element of `Lp ℂ 2 haarAddCircle`. The statement for coefficients is `fourierCoeff_fourier`: `fourierCoeff (fourier n) = Pi.single n 1`. The constant function has `fourierCoeff_const`: its coefficients are `Pi.single 0 c`.

<?decl AddCircle.orthonormal_fourier?>
<?decl AddCircle.fourierCoeff_fourier?>
<?decl AddCircle.fourierCoeff_const?>
:::

**Theorem (Coefficients of a derivative).** Let $a < b$, $L = b - a$, and let $f : \mathbb{R} \to \mathbb{C}$ have a derivative $f'(x)$ at every $x \in [a, b]$, with $f'$ integrable on $[a, b]$. Then for $n \ne 0$,
$$c_n(f; a, b) = \frac{1}{-2\pi i n}\Big(e^{-2\pi i n a/L}\big(f(b) - f(a)\big) - L\, c_n(f'; a, b)\Big).$$
In particular, if $f(a) = f(b)$, then $c_n(f'; a, b) = \frac{2\pi i n}{L}\, c_n(f; a, b)$.

*Proof.* Put $g(x) = e^{-2\pi i n x/L}$ and $G(x) = \frac{L}{-2\pi i n} g(x)$, so that $G' = g$. The product $G f$ has derivative $g f + G f'$ on $[a, b]$, and this derivative is integrable because $g$ and $G$ are bounded and continuous and $f$ is continuous. The fundamental theorem of calculus for an integrable derivative (Volume 18, Chapter 8) gives
$$\int_a^b g f\,dx = G(b) f(b) - G(a) f(a) - \int_a^b G f'\,dx.$$
Now $g(b) = g(a)e^{-2\pi i n} = g(a)$, so $G(b) = G(a)$, and the boundary term is $G(a)(f(b) - f(a))$. Divide by $L$:
$$c_n(f) = \frac{1}{L}\cdot\frac{L}{-2\pi i n}\Big(g(a)\big(f(b) - f(a)\big) - \int_a^b g f'\,dx\Big) = \frac{1}{-2\pi i n}\Big(g(a)\big(f(b) - f(a)\big) - L\,c_n(f')\Big).$$
If $f(a) = f(b)$, the first term vanishes, and solving for $c_n(f')$ gives the last formula. $\square$

For $T = 1$ and a smooth periodic function, the rule reads $\widehat{f'}(n) = 2\pi i n \hat f(n)$. Applied $k$ times it gives $|\hat f(n)| \le (2\pi |n|)^{-k}\sup|f^{(k)}|$ for $n \ne 0$. So smoothness of $f$ gives fast decay of $\hat f$.

::: mathlib
`AddCircle.fourierCoeffOn_of_hasDerivAt` · `Mathlib.Analysis.Fourier.AddCircle`

The hypotheses are `n ≠ 0`, `∀ x ∈ uIcc a b, HasDerivAt f (f' x) x` and `IntervalIntegrable f' volume a b`. The conclusion is literally the displayed formula, with `fourier (-n) ↑a` for $e^{-2\pi i n a/L}$. It uses `hasDerivAt_fourier`, the derivative $\frac{2\pi i n}{T}e_n(x)$ of $x \mapsto e_n(x)$.

<?decl AddCircle.fourierCoeffOn_of_hasDerivAt?>
<?decl AddCircle.hasDerivAt_fourier?>
:::

### Examples

**Example (The sawtooth).** Let $f(x) = x$ on $[0, 1]$, with period $1$. Then $c_0 = \int_0^1 x\,dx = \frac12$. For $n \ne 0$ apply the theorem with $a = 0$, $b = 1$, $f' = 1$. The coefficient $c_n(1)$ is $0$ by orthonormality, and $g(0) = 1$, so
$$c_n = \frac{1}{-2\pi i n}(1 - 0) = \frac{i}{2\pi n}.$$
The formal series is $\frac12 + \sum_{n \ne 0}\frac{i}{2\pi n}e^{2\pi i n x} = \frac12 - \sum_{n \ge 1}\frac{\sin 2\pi n x}{\pi n}$. The coefficients decay like $1/n$ and not faster, because the periodic function jumps at the integers. Section 2 uses these coefficients to compute $\sum 1/n^2$.

**Example (The square wave).** Let $f = 1$ on $[0, \frac12)$ and $f = -1$ on $[\frac12, 1)$, with period $1$. Then $\hat f(0) = 0$, and for $n \ne 0$,
$$\hat f(n) = \int_0^{1/2} e^{-2\pi i n x}\,dx - \int_{1/2}^1 e^{-2\pi i n x}\,dx = \frac{1 - (-1)^n}{2\pi i n} - \frac{(-1)^n - 1}{2\pi i n} = \frac{1 - (-1)^n}{\pi i n}.$$
So $\hat f(n) = \frac{2}{\pi i n}$ for odd $n$ and $0$ for even $n$. Pairing $n$ with $-n$ gives the series $\frac{4}{\pi}\sum_{n \text{ odd}, n > 0}\frac{\sin 2\pi n x}{n}$.

### The library around it

The file `Mathlib.Analysis.Fourier.AddCircle` holds everything of this chapter on one variable: the characters, the coefficients, the subalgebra they generate, the Hilbert basis and Parseval. The file `Mathlib.Analysis.Fourier.AddCircleMulti` does the same for the torus $(\mathbb{R}/\mathbb{Z})^d$.

Common errors of a learner:

- Forgetting the factor $1/T$. Mathlib averages with `haarAddCircle`, not with `volume`. A textbook that integrates over $[-\pi, \pi]$ without $\frac{1}{2\pi}$ has coefficients $2\pi$ times larger.
- Using the wrong sign. `fourierCoeff f n` integrates against `fourier (-n)`, the conjugate of `fourier n`.
- Expecting `fourierCoeff f n` to carry a proof of integrability. The value is $0$ for a non-integrable `f`, and lemmas take the integrability as a hypothesis.

### Exercises

1. (A) Compute the Fourier coefficients of $f(x) = \sin^3(2\pi x)$. Hint: write $\sin$ with exponentials and expand.
2. (A) Show that $\widehat{\bar f}(n) = \overline{\hat f(-n)}$, and deduce that $f$ is real valued only if $\hat f(-n) = \overline{\hat f(n)}$ for every $n$.
3. (B) Compute the coefficients of the triangle wave $f(x) = |x|$ on $[-\frac12, \frac12]$, with period $1$. Hint: $f$ is continuous and periodic, and $f'$ is the square wave away from the points $0$ and $\pm\frac12$. Integrate by parts on $[-\frac12, 0]$ and on $[0, \frac12]$ separately.
4. (B) Let $f$ be $C^2$ on $\mathbb{R}$ with period $1$. Show that $|\hat f(n)| \le \frac{1}{4\pi^2 n^2}\sup|f''|$ for $n \ne 0$, and deduce that $\sum_n |\hat f(n)| < \infty$.
5. (B) Show that $\hat f(n) \to 0$ as $|n| \to \infty$ for $f$ continuous and periodic. Hint: approximate $f$ uniformly by a $C^1$ periodic function $g$, and use $\|\hat f(n) - \hat g(n)\| \le \sup|f - g|$.
6. (C) Let $f$ be integrable on the circle with $\hat f(n) = 0$ for all $n$. Assume that $f$ is continuous. Show that $f = 0$, using the density theorem of Section 2. Hint: $\int f \bar p\,d\mu_T = 0$ for every trigonometric polynomial $p$.

### Notes and history

Daniel Bernoulli proposed sums of sines for the vibrating string in the 1750s. Joseph Fourier used such series for the heat equation in his *Théorie analytique de la chaleur* of 1822, and he gave the integral formula for the coefficients. Dirichlet proved in 1829 that the series of a piecewise monotone function converges at each point to the mean of the one sided limits.

### Reference

<?reference?>
