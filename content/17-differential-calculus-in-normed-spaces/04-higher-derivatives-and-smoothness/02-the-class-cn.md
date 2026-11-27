---
title: The class C^n
kind: theory
modules:
  - Mathlib.Analysis.Calculus.ContDiff.Defs
  - Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
explains:
  E3: [ContDiff, HasFTaylorSeriesUpTo, iteratedFDeriv]
  E2: [contDiff_succ_iff_fderiv, contDiff_zero, contDiff_one_iff_fderiv, contDiff_iff_continuous_differentiable, contDiff_infty_iff_fderiv, ContDiffAt, ContDiffOn, ftaylorSeries, iteratedFDeriv_succ_apply_left, iteratedFDeriv_two_apply, contDiff_iff_ftaylorSeries, ContDiff.of_le]
  E1: auto
families: []
requires: [V17.C01, V17.C02, V17.C03, V15.C04]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The class $C^n$

### Overview

Section 1 differentiated the derivative once. Repeat the step: the $k$-th derivative $D^k f(x)$ is a continuous $k$-multilinear map $E^k \to F$, and a map is of class $C^n$ if its derivatives up to order $n$ exist and are continuous.

There are two forms of the definition. The recursive form says that $f$ is $C^{n+1}$ if $f$ is differentiable and $Df$ is $C^n$. The second form asks for a family of maps $p_m : E \to L^m(E; F)$ that are the derivatives of each other. Mathlib uses it and calls the family a Taylor series up to order $n$. The main theorem shows that the two forms agree and that $p_m = D^m f$.

### Definitions

Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$ and let $E, F$ be normed spaces over $\mathbb{K}$. For $k \ge 0$ let $L^k(E; F)$ be the normed space of continuous $k$-multilinear maps $E^k \to F$. So $L^0(E; F) \cong F$ and $L^1(E; F) = L(E, F)$.

Volume 16 gives two isometric isomorphisms. The *left curry* $L^{k+1}(E; F) \cong L(E, L^k(E; F))$ sends $\varphi$ to $h \mapsto \varphi(h, \cdot, \dots, \cdot)$. The *right curry* $L^{k+1}(E; F) \cong L^k(E; L(E, F))$ sends $\varphi$ to $(h_1, \dots, h_k) \mapsto \varphi(h_1, \dots, h_k, \cdot)$.

**Definition (Iterated derivative).** Let $f : E \to F$. Put $D^0 f(x) = f(x) \in L^0(E; F)$. If $D^k f : E \to L^k(E; F)$ is differentiable at $x$, put
$$D^{k+1} f(x)(h_0, h_1, \dots, h_k) = \big(D(D^k f)(x)\, h_0\big)(h_1, \dots, h_k).$$

The first argument $h_0$ is the direction of the last derivative. For $k = 1$ this is $D^2 f$ of Section 1.

**Definition (Class $C^n$).** Let $n \in \mathbb{N}$. The map $f : E \to F$ is of *class $C^0$* if it is continuous. It is of *class $C^{n+1}$* if it is differentiable on $E$ and $Df : E \to L(E, F)$ is of class $C^n$. It is of *class $C^\infty$*, or *smooth*, if it is of class $C^n$ for every $n$.

**Definition (Taylor series up to order $n$).** Let $n \in \mathbb{N} \cup \{\infty\}$. A family of maps $p_m : E \to L^m(E; F)$, $m \in \mathbb{N}$, is a *Taylor series of $f$ up to order $n$* if

1. $p_0(x) = f(x)$ for every $x$;
2. for each $m < n$ and each $x$, the map $p_m$ is differentiable at $x$ and $D p_m(x)\,h = \big((h_1, \dots, h_m) \mapsto p_{m+1}(x)(h, h_1, \dots, h_m)\big)$;
3. for each $m \le n$, the map $p_m$ is continuous.

::: mathlib
`HasFTaylorSeriesUpTo` · `Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries`

The fields of `HasFTaylorSeriesUpTo n f p` are `zero_eq : ∀ x, (p x 0).curry0 = f x`, `fderiv : ∀ m : ℕ, m < n → ∀ x, HasFDerivAt (p · m) (p x m.succ).curryLeft x` and `cont : ∀ m : ℕ, m ≤ n → Continuous (p · m)`. Here `p : E → FormalMultilinearSeries 𝕜 E F`, so `p x m : E [×m]→L[𝕜] F`. Chapter 7 uses formal multilinear series for power series.

<?decl HasFTaylorSeriesUpTo?>
:::

::: mathlib
`iteratedFDeriv` · `Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries`

`iteratedFDeriv 𝕜 n f x : E [×n]→L[𝕜] F` is $D^n f(x)$, defined by the recursion above with `ContinuousMultilinearMap.uncurryLeft`. The unfolding lemmas are `iteratedFDeriv_succ_apply_left`, `iteratedFDeriv 𝕜 (n + 1) f x m = fderiv 𝕜 (iteratedFDeriv 𝕜 n f) x (m 0) (Fin.tail m)`, and `iteratedFDeriv_two_apply`, `iteratedFDeriv 𝕜 2 f z m = fderiv 𝕜 (fderiv 𝕜 f) z (m 0) (m 1)`. The family of all of them is `ftaylorSeries 𝕜 f x`.

<?decl iteratedFDeriv?>
<?decl ftaylorSeries?>
:::

### Theorems and proofs

**Theorem (Uniqueness of the Taylor series).** Let $p$ be a Taylor series of $f$ up to order $n$. Then for each $m \le n$ the iterated derivative $D^m f$ exists on $E$, and $p_m = D^m f$.

*Proof.* Induction on $m$. For $m = 0$, $p_0(x) = f(x) = D^0 f(x)$. Assume $p_m = D^m f$ with $m + 1 \le n$, so $m < n$. By condition 2, $D^m f = p_m$ is differentiable at each $x$, so $D^{m+1} f(x)$ is defined, and
$$D^{m+1} f(x)(h, h_1, \dots, h_m) = \big(D p_m(x)\,h\big)(h_1, \dots, h_m) = p_{m+1}(x)(h, h_1, \dots, h_m).$$
So $D^{m+1} f = p_{m+1}$. $\square$

The next lemma connects the two forms through the right curry.

**Lemma (Taylor series of the derivative).** Let $n \in \mathbb{N} \cup \{\infty\}$. The map $f$ has a Taylor series up to order $n + 1$ if and only if $f$ is differentiable on $E$ and $Df$ has a Taylor series up to order $n$. (For $n = \infty$ read $n + 1 = \infty$.)

*Proof.* Assume that $p$ is a Taylor series of $f$ up to $n + 1$. By condition 2 for $m = 0$, $f = p_0$ is differentiable, with $Df(x)h = p_1(x)(h)$. Define $q_m(x) \in L^m(E; L(E, F))$ by
$$q_m(x)(h_1, \dots, h_m)(k) = p_{m+1}(x)(h_1, \dots, h_m, k).$$
So $q_m = R \circ p_{m+1}$, where $R$ is the right curry, a continuous linear isometry. Then $q_0(x) = Df(x)$, which is condition 1 for $Df$. For $m \le n$, $m + 1 \le n + 1$, so $p_{m+1}$ is continuous and $q_m$ is continuous. For $m < n$, $p_{m+1}$ is differentiable, and by the chain rule (Chapter 2), $D q_m(x)\,h = R\big(D p_{m+1}(x)\,h\big)$.
$$D q_m(x)(h)(h_1, \dots, h_m)(k) = \big(D p_{m+1}(x)\,h\big)(h_1, \dots, h_m, k) = p_{m+2}(x)(h, h_1, \dots, h_m, k) = q_{m+1}(x)(h, h_1, \dots, h_m)(k).$$
This is condition 2 for $q$.

Conversely, let $f$ be differentiable and let $q$ be a Taylor series of $Df$ up to $n$. Put $p_0(x) = f(x)$ and $p_{m+1}(x)(h_1, \dots, h_{m+1}) = q_m(x)(h_1, \dots, h_m)(h_{m+1})$, so $p_{m+1} = R^{-1} \circ q_m$. The map $p_0 = f$ is continuous because it is differentiable, and $p_{m+1}$ is continuous for $m \le n$, that is, for $m + 1 \le n + 1$. For condition 2 at $m = 0$: $D p_0(x)\,h = Df(x)\,h = q_0(x)(h) = p_1(x)(h)$. For $1 \le m < n + 1$, the index $m - 1 < n$, and
$$D p_m(x)(h)(h_1, \dots, h_m) = D q_{m-1}(x)(h)(h_1, \dots, h_{m-1})(h_m) = q_m(x)(h, h_1, \dots, h_{m-1})(h_m) = p_{m+1}(x)(h, h_1, \dots, h_m).$$
So $p$ is a Taylor series of $f$ up to $n + 1$. $\square$

**Theorem (Two definitions of $C^n$).** Let $n \in \mathbb{N} \cup \{\infty\}$ and $f : E \to F$. These statements are equivalent:

1. $f$ is of class $C^n$;
2. $f$ has a Taylor series up to order $n$;
3. for each $m \le n$, $D^m f$ exists on $E$ and is continuous, and for each $m < n$, $D^m f$ is differentiable.

*Proof.* (1) $\iff$ (2) for $n \in \mathbb{N}$, by induction on $n$, for all target spaces at the same time. For $n = 0$, (2) says that $p_0 = f$ is continuous. For the step, $f$ is $C^{n+1}$ iff $f$ is differentiable and $Df$ is $C^n$, iff (hypothesis for the target $L(E, F)$) $Df$ has a Taylor series up to $n$, iff (lemma) $f$ has one up to $n + 1$.

(1) $\iff$ (2) for $n = \infty$. A Taylor series up to $\infty$ is one up to each $n$. Conversely, if $f$ has a Taylor series $p^{(n)}$ up to each $n$, then $p^{(n)}_m = D^m f$ for $m \le n$ by uniqueness, so $p_m = D^m f$ is a Taylor series up to $\infty$.

(2) $\iff$ (3). If (2) holds, uniqueness gives $p_m = D^m f$, and conditions 2 and 3 give (3). If (3) holds, $p_m = D^m f$ satisfies condition 2 by the definition of $D^{m+1} f$, and conditions 1 and 3 directly. $\square$

**Corollary.** If $f$ is $C^n$ and $m \le n$, then $f$ is $C^m$. A map is $C^{n+1}$ if and only if it is differentiable and $Df$ is $C^n$, also for $n = \infty$.

*Proof.* A Taylor series up to $n$ is one up to $m$. For $n = \infty$, the lemma with $n = \infty$ and the theorem give the second statement. $\square$

::: mathlib
`ContDiff` · `Mathlib.Analysis.Calculus.ContDiff.Defs`

`ContDiff 𝕜 n f` is the class $C^n$, with `n : WithTop ℕ∞`: the natural numbers, `∞` (the image of `⊤ : ℕ∞`) and `ω` (the top), with notation from `open scoped ContDiff`. For `n : ℕ∞` it is `∃ p, HasFTaylorSeriesUpTo n f p`. For `n = ω` each `p m` must also be analytic, the class of Chapter 7. The local forms are `ContDiffAt 𝕜 n f x` and `ContDiffOn 𝕜 n f s`.

<?decl ContDiff?>
<?decl ContDiffAt?>
<?decl ContDiffOn?>
:::

::: mathlib
`contDiff_succ_iff_fderiv` · `Mathlib.Analysis.Calculus.ContDiff.Defs`

`contDiff_succ_iff_fderiv` is the recursive form: `ContDiff 𝕜 (n + 1) f ↔ Differentiable 𝕜 f ∧ (n = ω → AnalyticOnNhd 𝕜 f univ) ∧ ContDiff 𝕜 n (fderiv 𝕜 f)`; the middle condition is empty unless `n = ω`. With it come `contDiff_zero` ($C^0$ is continuity), `contDiff_one_iff_fderiv`, `contDiff_infty_iff_fderiv`, and `ContDiff.of_le` for the corollary. Statement 3 is `contDiff_iff_continuous_differentiable` and statement 2 is `contDiff_iff_ftaylorSeries`.

<?decl contDiff_succ_iff_fderiv?>
<?decl contDiff_iff_continuous_differentiable?>
<?decl contDiff_iff_ftaylorSeries?>
:::

For $f : \mathbb{K} \to F$, induction with the one-variable case of Chapter 1 gives
$$D^m f(x)(h_1, \dots, h_m) = h_1 h_2 \cdots h_m\, f^{(m)}(x),$$
with $f^{(m)}$ as in Volume 15, Chapter 4. So $C^n$ here is $C^n$ there. In Mathlib this is `iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod`, with `contDiff_iff_iteratedDeriv`.

### Examples

**Example (Bounded linear and bilinear maps).** Let $A \in L(E, F)$. Then $DA(x) = A$ is constant, so $A$ is $C^\infty$ with $D^m A = 0$ for $m \ge 2$. Let $B$ be continuous bilinear on $E$ and $f(x) = B(x, x)$. By Chapter 2, $Df(x)h = B(x, h) + B(h, x)$, and $x \mapsto Df(x)$ is continuous linear. So $D^2 f(x)(k, h) = B(k, h) + B(h, k)$ is constant and $f$ is $C^\infty$. For $f(x) = \|x\|^2$ on a real Hilbert space, $D^2 f(x)(k, h) = 2\langle k, h\rangle$.

**Example (A third derivative).** Let $f(x, y) = x^2 y$ on $\mathbb{R}^2$. The only nonzero third partial derivatives are $\partial_x \partial_x \partial_y f = \partial_x \partial_y \partial_x f = \partial_y \partial_x \partial_x f = 2$. For $h, k, l \in \mathbb{R}^2$,
$$D^3 f(x, y)(h, k, l) = 2\,(h_1 k_1 l_2 + h_1 k_2 l_1 + h_2 k_1 l_1),$$
a constant symmetric trilinear map, and $D^4 f = 0$. On the diagonal, $D^3 f(x,y)(h, h, h) = 6 h_1^2 h_2 = 3!\, f(h)$.

**Counterexample ($C^1$ but not $C^2$).** Let $f(x) = x|x|$ on $\mathbb{R}$. Then $f'(x) = 2x$ for $x > 0$, $f'(x) = -2x$ for $x < 0$, and $f'(0) = \lim f(h)/h = \lim |h| = 0$. So $f' = 2|x|$ is continuous and $f$ is $C^1$. But $|x|$ is not differentiable at $0$, so $f$ is not $C^2$. In the same way $x^k |x|$ is $C^k$ and not $C^{k+1}$.

### The library around it

The order has the type `WithTop ℕ∞`, so a number `n : ℕ` is cast twice. To get `ContDiff 𝕜 2 f` from `ContDiff 𝕜 ∞ f` apply `ContDiff.of_le`; the side goal `2 ≤ ∞` is a cast inequality for `simp` or `norm_cast`.

Common errors of a learner:

- Writing `ContDiff ℝ ⊤ f` for smoothness. In `WithTop ℕ∞`, `⊤` is `ω`: this asks for an analytic map. Write `ContDiff ℝ ∞ f` with `open scoped ContDiff`.
- Mixing up the order of the arguments. In `iteratedFDeriv 𝕜 (n+1) f x m`, the vector `m 0` is the direction of the last derivative.

### Exercises

1. (A) Show that $f(x) = |x|^3$ is $C^2$ but not $C^3$ on $\mathbb{R}$. Compute $f'$ and $f''$.
2. (A) Let $f(x, y) = x^3 + x y^2$. Compute $D^3 f(x, y)(h, h, h)$ and check that it equals $3!\,f(h)$.
3. (B) Let $P(x) = A(x, \dots, x)$ for a continuous $m$-multilinear map $A$ on $E$. Show by induction that $D^m P(x)(h_1, \dots, h_m) = \sum_{\sigma \in S_m} A(h_{\sigma(1)}, \dots, h_{\sigma(m)})$. Hint: first compute $DP(x)h$ as a sum of $m$ terms.
4. (B) Let $U \subseteq \mathbb{R}^n$ be open and $f : U \to \mathbb{R}$. Show that $f$ is $C^1$ on $U$ if and only if all partial derivatives $\partial_j f$ exist and are continuous on $U$. Hint: Chapter 1, Section 2.
5. (B) Show that $f$ is $C^{n+1}$ if and only if $f$ is $C^n$ and $D^n f$ is $C^1$. Hint: use statement 3 of the theorem.

### Notes and history

The recursive definition of $C^n$ in Banach spaces, with the iterated derivatives identified with multilinear maps by currying, is the one of Dieudonné, *Foundations of Modern Analysis*, Chapter VIII. The form with a family $p_m$ has an advantage in a formal library: the family has one type for all orders, so no dependent type for each $D^k f$ is necessary.

### Reference

<?reference?>
