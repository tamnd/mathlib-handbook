---
title: The implicit function theorem and Lagrange multipliers
kind: theory
modules:
  - Mathlib.Analysis.Calculus.Implicit
  - Mathlib.Analysis.Calculus.ImplicitFunction.ProdDomain
  - Mathlib.Analysis.Calculus.ImplicitFunction.Bivariate
  - Mathlib.Analysis.Calculus.ImplicitContDiff
  - Mathlib.Analysis.Calculus.LagrangeMultipliers
explains:
  E3: [ImplicitFunctionData, HasStrictFDerivAt.implicitFunctionOfProdDomain, HasStrictFDerivAt.implicitFunction, IsLocalExtrOn.exists_multipliers_of_hasStrictFDerivAt]
  E2: [ImplicitFunctionData.implicitFunction, ImplicitFunctionData.hasStrictFDerivAt_implicitFunction, HasStrictFDerivAt.to_implicitFunction, HasStrictFDerivAt.map_implicitFunction_eq, HasStrictFDerivAt.eventually_apply_eq_iff_implicitFunctionOfProdDomain, HasStrictFDerivAt.hasStrictFDerivAt_implicitFunctionOfProdDomain, implicitFunctionOfBivariate, ContDiffAt.implicitFunction, ContDiffAt.contDiffAt_implicitFunction, IsLocalExtrOn.exists_multipliers_of_hasStrictFDerivAt_1d, IsLocalExtrOn.exists_linear_map_of_hasStrictFDerivAt, IsLocalExtrOn.range_ne_top_of_hasStrictFDerivAt]
  E1: auto
families: []
requires: [V17.C01, V17.C02, V17.C03, V17.C04]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The implicit function theorem and Lagrange multipliers

### Overview

The equation $x^2 + y^2 = 1$ does not define $y$ as a function of $x$ on the whole circle, but near most points it does: near $(a, b)$ with $b > 0$ the circle is the graph of $y = \sqrt{1 - x^2}$. The implicit function theorem says: if $f(x, y) = 0$ at $(a, b)$ and the partial derivative of $f$ in $y$ is invertible there, then near $(a, b)$ the solutions of $f(x, y) = 0$ form the graph of a function $y = \psi(x)$, and $D\psi(a)$ is computed from the partial derivatives. The same tools give the rule of Lagrange multipliers for constrained extrema.

### Definitions

Let $E_1$, $E_2$ and $F$ be Banach spaces, $u = (a, b) \in E_1 \times E_2$, and let $f : E_1 \times E_2 \to F$ be differentiable at $u$.

As in Chapter 2, the *partial derivatives* of $f$ at $u$ are $D_1 f(u) \in L(E_1, F)$ and $D_2 f(u) \in L(E_2, F)$, given by
$$D_1 f(u)h = Df(u)(h, 0), \qquad D_2 f(u)k = Df(u)(0, k).$$
By linearity, $Df(u)(h, k) = D_1 f(u)h + D_2 f(u)k$.

**Definition (Constrained extremum).** Let $M \subseteq E$ and $x_0 \in M$. A function $\varphi : E \to \mathbb{R}$ has a *local maximum on $M$* at $x_0$ if there is a neighbourhood $W$ of $x_0$ with $\varphi(x) \le \varphi(x_0)$ for all $x \in W \cap M$. A local minimum on $M$ is defined in the same way, and an extremum is either.

### Theorems and proofs

**Theorem (Implicit function theorem).** Let $f : E_1 \times E_2 \to F$ be strictly differentiable at $u = (a, b)$, and let $B = D_2 f(u)$ be invertible. Put $A = D_1 f(u)$. Then there are an open set $W \ni u$, an open set $U \ni a$ and a map $\psi : U \to E_2$ with $\psi(a) = b$, such that for $(x, y) \in W$
$$f(x, y) = f(u) \iff x \in U \text{ and } y = \psi(x).$$
The map $\psi$ is strictly differentiable at $a$, with
$$D\psi(a) = -B^{-1}A.$$
If $f$ is $C^k$ near $u$, with $k \ge 1$ and $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, then $\psi$ is $C^k$ near $a$.

*Proof.* Define $\Phi : E_1 \times E_2 \to E_1 \times F$ by $\Phi(x, y) = (x, f(x, y))$. Each component is strictly differentiable at $u$, so $\Phi$ is, with
$$D\Phi(u)(h, k) = (h,\ Ah + Bk).$$
This linear map is invertible. Its inverse is $(h, z) \mapsto (h, B^{-1}(z - Ah))$, because $Ah + B B^{-1}(z - Ah) = z$, and $B^{-1}(Ah + Bk - Ah) = k$.

The inverse function theorem gives open sets $W \ni u$ and $V \ni \Phi(u) = (a, f(u))$ such that $\Phi$ is a homeomorphism of $W$ onto $V$, with an inverse $G = (G_1, G_2)$ strictly differentiable at $\Phi(u)$. Since $\Phi$ keeps the first coordinate, $G_1(x, z) = x$. Put
$$U = \{x \in E_1 : (x, f(u)) \in V\}, \qquad \psi(x) = G_2(x, f(u)).$$
The set $U$ is open and contains $a$, and $\psi(a) = G_2(\Phi(u)) = b$.

Let $(x, y) \in W$. If $f(x, y) = f(u)$, then $\Phi(x, y) = (x, f(u))$. This point lies in $V$, so $x \in U$, and applying $G$ gives $(x, y) = (x, \psi(x))$. Conversely, if $x \in U$ and $y = \psi(x)$, then $(x, y) = G(x, f(u))$, so $\Phi(x, y) = (x, f(u))$ and $f(x, y) = f(u)$.

The map $\psi$ is the composition of $x \mapsto (x, f(u))$ with $G_2$. So it is strictly differentiable at $a$, and
$$D\psi(a)h = \text{second component of } D\Phi(u)^{-1}(h, 0) = B^{-1}(0 - Ah) = -B^{-1}Ah.$$
If $f$ is $C^k$, then $\Phi$ is $C^k$, and $G$ is $C^k$ near $\Phi(u)$ by the smooth inverse function theorem, so $\psi$ is $C^k$. $\square$

::: mathlib
`HasStrictFDerivAt.implicitFunctionOfProdDomain` · `Mathlib.Analysis.Calculus.ImplicitFunction.ProdDomain`

For `f : E₁ × E₂ → F` on complete spaces, `dfu : HasStrictFDerivAt f f'u u` and `if₂u : (f'u ∘L .inr 𝕜 E₁ E₂).IsInvertible`, it is the map `ψ : E₁ → E₂`. The partial derivative $D_2 f(u)$ is written `f'u ∘L .inr 𝕜 E₁ E₂`, the derivative composed with the inclusion $k \mapsto (0, k)$. The characterization is `HasStrictFDerivAt.eventually_apply_eq_iff_implicitFunctionOfProdDomain`: `∀ᶠ v in 𝓝 u, f v = f u ↔ ψ v.1 = v.2`. The derivative is `HasStrictFDerivAt.hasStrictFDerivAt_implicitFunctionOfProdDomain`, with the value `-(f'u ∘L .inr 𝕜 E₁ E₂).inverse ∘L (f'u ∘L .inl 𝕜 E₁ E₂)`, which is $-B^{-1}A$.

<?decl HasStrictFDerivAt.implicitFunctionOfProdDomain?>
:::

Mathlib builds the theorem from a more symmetric structure: two maps on one space whose derivatives are surjective with complementary kernels, here $f$ and the projection to $E_1$.

::: mathlib
`ImplicitFunctionData` · `Mathlib.Analysis.Calculus.Implicit`

A term `φ : ImplicitFunctionData 𝕜 E F G` holds a point `pt : E`, two maps `leftFun : E → F` and `rightFun : E → G`, their strict derivatives at `pt`, the proofs that both derivatives are surjective, and the proof that their kernels are complementary subspaces. The map `φ.prodFun = fun x => (leftFun x, rightFun x)` has an invertible strict derivative, and `ImplicitFunctionData.implicitFunction φ : F → G → E` is the curried inverse of the open partial homeomorphism. Its derivative is `ImplicitFunctionData.hasStrictFDerivAt_implicitFunction`. The construction `HasStrictFDerivAt.implicitFunctionDataOfProdDomain` takes `leftFun := f` and `rightFun := Prod.fst`, which is $\Phi$.

<?decl ImplicitFunctionData?>
:::

::: mathlib
`HasStrictFDerivAt.implicitFunction` · `Mathlib.Analysis.Calculus.Implicit`

This form has no product. For `f : E → F` with `F` finite-dimensional, `hf : HasStrictFDerivAt f f' a` and `hf' : f'.range = ⊤`, it gives `F → f'.ker → E`. It parametrizes the level set of `f` near `a` by a neighbourhood of `0` in the kernel. `HasStrictFDerivAt.map_implicitFunction_eq` says that `f (implicitFunction p.1 p.2) = p.1` near `(f a, 0)`, and `HasStrictFDerivAt.to_implicitFunction` gives the derivative `f'.ker.subtypeL` at `0`: the level set is tangent to the kernel.

<?decl HasStrictFDerivAt.implicitFunction?>
:::

For smooth maps, `ContDiffAt.implicitFunction` takes `cdf : ContDiffAt 𝕜 n f u`, `n ≠ 0` and the invertibility of `fderiv 𝕜 f u ∘L .inr 𝕜 E₁ E₂`, and `ContDiffAt.contDiffAt_implicitFunction` says that $\psi$ is $C^n$ at `u.1`. `implicitFunctionOfBivariate` is the form for a curried `f : E₁ → E₂ → F` with continuous partial derivatives.

The second topic is constrained extrema. Let $\varphi, f_1, \dots, f_m : E \to \mathbb{R}$ and
$$M = \{x \in E : f_i(x) = f_i(x_0) \text{ for } i = 1, \dots, m\}.$$

**Theorem (Lagrange multipliers).** Let $E$ be a real Banach space, and let $\varphi$ and $f_1, \dots, f_m$ be strictly differentiable at $x_0$. If $\varphi$ has a local extremum on $M$ at $x_0$, then there are real numbers $\Lambda_1, \dots, \Lambda_m, \Lambda_0$, not all zero, with
$$\sum_{i=1}^m \Lambda_i\, Df_i(x_0) + \Lambda_0\, D\varphi(x_0) = 0.$$

*Proof.* Let $\Psi = (f_1, \dots, f_m, \varphi) : E \to \mathbb{R}^{m+1}$ and $T = D\Psi(x_0)$. Suppose that $T$ is surjective. Choose $e_1, \dots, e_{m+1} \in E$ with $T e_j$ the $j$-th standard basis vector, and let $R : \mathbb{R}^{m+1} \to E$ be the linear map with $R(\varepsilon_j) = e_j$. Then $TR = I$. The map $h(z) = \Psi(x_0 + Rz)$ on $\mathbb{R}^{m+1}$ is strictly differentiable at $0$ with $Dh(0) = TR = I$. By the inverse function theorem, $h$ maps each small ball around $0$ onto a neighbourhood of $h(0) = \Psi(x_0)$.

Let $W$ be the neighbourhood of $x_0$ in the definition of the extremum, and say it is a maximum. Choose $\delta > 0$ with $x_0 + R(B(0, \delta)) \subseteq W$. For small $t > 0$, the point $\Psi(x_0) + t\,\varepsilon_{m+1}$ is $h(z)$ for some $z \in B(0, \delta)$. Then $x = x_0 + Rz$ lies in $W$, it satisfies $f_i(x) = f_i(x_0)$ for each $i$, so $x \in M$, and $\varphi(x) = \varphi(x_0) + t > \varphi(x_0)$. This contradicts the maximum. A minimum is the same with $-t$.

So the range of $T$ is a proper subspace of $\mathbb{R}^{m+1}$. A proper subspace lies in the kernel of a nonzero linear form, so there is $(\Lambda_1, \dots, \Lambda_m, \Lambda_0) \ne 0$ with $\sum_i \Lambda_i\, T_i v + \Lambda_0\, T_{m+1} v = 0$ for all $v \in E$. Here $T_i = Df_i(x_0)$ and $T_{m+1} = D\varphi(x_0)$. $\square$

**Corollary (The regular case).** If in addition $Df_1(x_0), \dots, Df_m(x_0)$ are linearly independent, then $\Lambda_0 \ne 0$, and $D\varphi(x_0) = \sum_i \mu_i Df_i(x_0)$ with $\mu_i = -\Lambda_i/\Lambda_0$.

*Proof.* If $\Lambda_0 = 0$, then $\sum_i \Lambda_i Df_i(x_0) = 0$ with $\Lambda \ne 0$, which contradicts the independence. $\square$

::: mathlib
`IsLocalExtrOn.exists_multipliers_of_hasStrictFDerivAt` · `Mathlib.Analysis.Calculus.LagrangeMultipliers`

For `hextr : IsLocalExtrOn φ {x | ∀ i, f i x = f i x₀} x₀`, with `f : ι → E → ℝ` for a `Fintype ι`, the strict derivatives `hf' : ∀ i, HasStrictFDerivAt (f i) (f' i) x₀` and `hφ' : HasStrictFDerivAt φ φ' x₀`, it gives `∃ Λ Λ₀, (Λ, Λ₀) ≠ 0 ∧ (∑ i, Λ i • f' i) + Λ₀ • φ' = 0`. The derivatives are in `StrongDual ℝ E`. The case of one constraint is `IsLocalExtrOn.exists_multipliers_of_hasStrictFDerivAt_1d`. The general form, `IsLocalExtrOn.exists_linear_map_of_hasStrictFDerivAt`, allows one constraint `f : E → F` with values in a complete space and gives a linear form `Λ : Module.Dual ℝ F`. The first step of the proof above is `IsLocalExtrOn.range_ne_top_of_hasStrictFDerivAt`.

<?decl IsLocalExtrOn.exists_multipliers_of_hasStrictFDerivAt?>
:::

### Examples

**Example (The circle).** Let $f(x, y) = x^2 + y^2$ and $(a, b)$ with $a^2 + b^2 = 1$. Then $A = D_1 f = 2a$ and $B = D_2 f = 2b$. If $b \ne 0$, the theorem gives $\psi$ near $a$ with $\psi'(a) = -2a/(2b) = -a/b$. For $b > 0$ the function is $\psi(x) = \sqrt{1 - x^2}$, and $\psi'(a) = -a/\sqrt{1 - a^2} = -a/b$, which agrees. At $(\pm 1, 0)$ the hypothesis fails, and so does the conclusion: near $x = 1$, there are two values of $y$ for $x < 1$ and none for $x > 1$.

**Example (The folium of Descartes).** Let $f(x, y) = x^3 + y^3 - 3xy$, so the curve is $f = 0$. Then $D_1 f = 3x^2 - 3y$ and $D_2 f = 3y^2 - 3x$. The point $(\frac32, \frac32)$ lies on the curve: $\frac{27}{8} + \frac{27}{8} = \frac{27}{4} = 3 \cdot \frac94$. There $D_1 f = D_2 f = \frac{27}{4} - \frac92 = \frac94$, so the curve is a graph $y = \psi(x)$ with $\psi'(\frac32) = -1$. At $(0, 0)$ both partial derivatives vanish, and the curve crosses itself there.

**Example (Extrema of $x + y$ on the circle).** Let $\varphi(x, y) = x + y$ and $f(x, y) = x^2 + y^2$, with the constraint $f = 1$. On the circle $Df = (2x, 2y) \ne 0$, so the corollary applies: at an extremum $(1, 1) = \mu(2x, 2y)$. So $x = y = 1/(2\mu)$, and $x^2 + y^2 = 1$ gives $x = y = \pm 1/\sqrt2$. By compactness, $\varphi$ has a maximum and a minimum on the circle, at these points: the maximum $\sqrt2$ at $(1/\sqrt2, 1/\sqrt2)$ and the minimum $-\sqrt2$ at $(-1/\sqrt2, -1/\sqrt2)$.

### The library around it

The implicit functions of Mathlib are total functions that are correct near the base point, as in Section 2. Their properties are stated with `∀ᶠ`.

Common errors of a learner:

- Writing the partial derivative as `fderiv 𝕜 (fun y => f (a, y)) b`. It is equal, but the theorems are stated with `f'u ∘L .inr 𝕜 E₁ E₂`, and a rewrite is needed.
- Forgetting $\Lambda_0$. Without independence of the $Df_i(x_0)$, the equation $D\varphi = \sum \mu_i Df_i$ can fail.
- Treating the multiplier rule as a sufficient condition. It only lists candidates. Compactness, or a second-order test, decides.

### Exercises

1. (A) Show that $x + y + xy^3 = 0$ defines $y = \psi(x)$ near $(0, 0)$, and compute $\psi'(0)$. Hint: $\psi'(0) = -1$.
2. (A) Find the extrema of $xy$ on the circle $x^2 + y^2 = 2$.
3. (B) Show that the sphere $x^2 + y^2 + z^2 = 1$ is a graph $z = \psi(x, y)$ near $(0, 0, 1)$, and compute $D\psi(0, 0)$ by the formula $-B^{-1}A$.
4. (B) Let $p_c(t) = t^n + c_{n-1}t^{n-1} + \dots + c_0$, and let $t_0$ be a simple real root of $p_{c^0}$. Show that for $c$ near $c^0$, $p_c$ has a root $t(c)$ near $t_0$ that depends smoothly on $c$, and that $\partial t/\partial c_0 = -1/p_{c^0}'(t_0)$ at $c^0$.
5. (B) Let $\varphi(x, y) = x$ and $f(x, y) = y^2 - x^3$. Show that $\varphi$ has a minimum on $\{f = 0\}$ at $(0, 0)$, that no $\mu$ satisfies $D\varphi = \mu Df$ there, and find $(\Lambda, \Lambda_0)$.
6. (C) Let $S$ be a symmetric real $n \times n$ matrix. Apply the multiplier rule to $\varphi(x) = \langle Sx, x\rangle$ on the unit sphere and show that $S$ has an eigenvector. Hint: $D\varphi(x)h = 2\langle Sx, h\rangle$.

### Notes and history

Lagrange introduced the multipliers in the *Mécanique analytique* (1788). The implicit function theorem in one real variable, with continuous partial derivatives, is often called Dini's theorem in Italian texts. The general theorem in Banach spaces, and its proof from the inverse function theorem through the map $\Phi$, are in Dieudonné, *Foundations of Modern Analysis* (1960), Chapter X.

### Reference

<?reference?>
