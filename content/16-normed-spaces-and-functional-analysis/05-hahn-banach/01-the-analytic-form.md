---
title: The analytic form
kind: theory
modules:
  - Mathlib.Analysis.Convex.Cone.Extension
  - Mathlib.Analysis.RCLike.Extend
  - Mathlib.Analysis.Normed.Module.HahnBanach
  - Mathlib.Analysis.LocallyConvex.HahnBanach
explains:
  E3: [exists_extension_of_le_sublinear, riesz_extension, StrongDual.extendRCLike, exists_extension_norm_eq]
  E2: [RieszExtension.step, RieszExtension.exists_top, StrongDual.extendRCLike_apply, StrongDual.re_extendRCLike_apply, Module.Dual.extendRCLike, Module.Dual.exists_extension_of_le_seminorm, Module.Dual.exists_continuous_extension_of_le_seminorm, StrongDual.exists_extension, ContinuousLinearMap.exist_extension_of_finiteDimensional_range]
  E1: auto
families: []
requires: [V04, V07, V13, V16.C01, V16.C02]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The analytic form

### Overview

Let $M$ be a subspace of a normed space $E$ and $f$ a bounded linear functional on $M$. The theorem of Hahn-Banach says that $f$ extends to a bounded functional on $E$ with the same norm. In finite dimension this is linear algebra with a little care for the norm, and for a Hilbert space it follows from the orthogonal projection of Chapter 7. For a general normed space the proof has two parts. The first is a one dimensional step: a functional dominated by a sublinear functional $p$ extends from $M$ to $M + \mathbb{R}x$ with the same domination. The second part is Zorn's lemma, which carries the step to all of $E$. This section proves the real theorem with a sublinear functional, then the normed form, then the complex form through the real part of a complex functional. It explains the route of Mathlib, which goes through the extension theorem of M. Riesz for convex cones.

### Definitions

**Definition (Sublinear functional).** Let $E$ be a real vector space. A function $p : E \to \mathbb{R}$ is *sublinear* if
1. $p(tx) = t\,p(x)$ for $t > 0$ and $x \in E$, and
2. $p(x + y) \le p(x) + p(y)$ for $x, y \in E$.

Each seminorm is sublinear, in particular $p(x) = C\|x\|$ on a normed space. A linear functional is sublinear. The function $p(x) = \max(x_1, x_2)$ on $\mathbb{R}^2$ is sublinear and not a seminorm, since $p(-x) \ne p(x)$ in general.

**Definition (Partial linear map).** A *partial linear map* from $E$ to $F$ is a pair $(D, f)$ of a subspace $D \subseteq E$, the domain, and a linear map $f : D \to F$. The partial maps are ordered by extension: $(D, f) \le (D', f')$ if $D \subseteq D'$ and $f'|_D = f$.

::: mathlib
`LinearPMap` · `Mathlib.LinearAlgebra.LinearPMap`

`E →ₗ.[R] F` is the type of partial linear maps, a structure with the fields `domain : Submodule R E` and `toFun : domain →ₗ[R] F`. It has the order of the definition, and the supremum of a directed family, which is the step of Zorn's lemma. The real form of the theorem of Hahn-Banach in Mathlib takes a partial map `f : E →ₗ.[ℝ] ℝ`, so that the subspace and the functional on it are one object.

<?decl LinearPMap?>
:::

### Theorems and proofs

**Lemma (One dimensional step).** Let $p$ be sublinear on a real vector space $E$, $M \subsetneq E$ a subspace, $f : M \to \mathbb{R}$ linear with $f \le p$ on $M$, and $x_0 \in E \setminus M$. Then $f$ extends to a linear $g$ on $M + \mathbb{R}x_0$ with $g \le p$.

*Proof.* Each vector of $M + \mathbb{R}x_0$ is $m + tx_0$ with unique $m \in M$ and $t \in \mathbb{R}$. An extension is $g(m + tx_0) = f(m) + tc$ for a number $c = g(x_0)$, and the task is to choose $c$. For $m, m' \in M$,
$$f(m) + f(m') = f(m + m') \le p(m + m') \le p(m - x_0) + p(m' + x_0).$$
So $f(m) - p(m - x_0) \le p(m' + x_0) - f(m')$ for all $m, m'$. Hence
$$a = \sup_{m \in M}\big(f(m) - p(m - x_0)\big) \le \inf_{m' \in M}\big(p(m' + x_0) - f(m')\big) = b,$$
and any $c \in [a, b]$ is a real number. Choose such a $c$. For $t > 0$, $c \le b$ applied to $m' = m/t$ gives $f(m/t) + c \le p(m/t + x_0)$, and multiplication by $t$ gives $g(m + tx_0) \le p(m + tx_0)$. For $t < 0$, write $t = -s$ with $s > 0$. Then $a \le c$ applied to $m/s$ gives $f(m/s) - c \le p(m/s - x_0)$, and multiplication by $s$ gives $g(m - sx_0) \le p(m - sx_0)$. For $t = 0$ the bound is the hypothesis. $\square$

**Theorem (Hahn-Banach, sublinear form).** Let $E$ be a real vector space, $p : E \to \mathbb{R}$ sublinear, $M$ a subspace and $f : M \to \mathbb{R}$ linear with $f(m) \le p(m)$ for $m \in M$. Then there is a linear $g : E \to \mathbb{R}$ with $g|_M = f$ and $g(x) \le p(x)$ for all $x \in E$.

*Proof.* Let $\mathcal{P}$ be the set of partial linear maps $(D, h)$ with $M \subseteq D$, $h|_M = f$ and $h \le p$ on $D$, ordered by extension. It contains $(M, f)$. Let $\mathcal{C}$ be a nonempty chain in $\mathcal{P}$. Then $D^* = \bigcup_{(D, h) \in \mathcal{C}}D$ is a subspace, since two vectors of $D^*$ lie in a common domain of the chain. The map $h^*(x) = h(x)$ for $x \in D$ is well defined and linear for the same reason, and $h^* \le p$. So $(D^*, h^*)$ is an upper bound of $\mathcal{C}$ in $\mathcal{P}$. By Zorn's lemma (Volume 4, Chapter 1) $\mathcal{P}$ has a maximal element $(D, g)$. If $D \ne E$, the one dimensional step extends $g$ to a strictly larger domain inside $\mathcal{P}$, which contradicts maximality. So $D = E$. $\square$

::: mathlib
`exists_extension_of_le_sublinear` · `Mathlib.Analysis.Convex.Cone.Extension`

`exists_extension_of_le_sublinear (f : E →ₗ.[ℝ] ℝ) (N : E → ℝ) (N_hom : ∀ c, 0 < c → ∀ x, N (c • x) = c * N x) (N_add : ∀ x y, N (x + y) ≤ N x + N y) (hf : ∀ x : f.domain, f x ≤ N x) : ∃ g : E →ₗ[ℝ] ℝ, (∀ x : f.domain, g x = f x) ∧ ∀ x, g x ≤ N x`. The two hypotheses on `N` are the definition of a sublinear functional, written out.

<?decl exists_extension_of_le_sublinear?>
:::

::: mathlib
`riesz_extension` · `Mathlib.Analysis.Convex.Cone.Extension`

Mathlib proves the sublinear form from the extension theorem of M. Riesz: if `s` is a convex cone in a real space `E`, `f` a partial linear functional that is nonnegative on `s ∩ f.domain`, and each `y` has an `x` in the domain with `x + y ∈ s`, then `f` extends to a linear `g` that is nonnegative on `s`. The sublinear form applies it on `E × ℝ` to the cone $\{(x, t) : p(x) \le t\}$ and to the functional $(x, t) \mapsto t - f(x)$. The one dimensional step is `RieszExtension.step`, and the step with Zorn's lemma is `RieszExtension.exists_top`.

<?decl riesz_extension?>
:::

**Corollary (Real normed form).** Let $E$ be a real normed space, $M$ a subspace and $f \in M^*$. Then there is $g \in E^*$ with $g|_M = f$ and $\|g\| = \|f\|$.

*Proof.* Apply the theorem with $p(x) = \|f\|\,\|x\|$, a sublinear functional with $f \le p$ on $M$. The extension $g$ satisfies $g(x) \le \|f\|\,\|x\|$ and $-g(x) = g(-x) \le \|f\|\,\|x\|$, so $|g(x)| \le \|f\|\,\|x\|$ and $\|g\| \le \|f\|$. Since $g$ extends $f$, $\|g\| \ge \|f\|$. $\square$

**Lemma (A complex functional and its real part).** Let $E$ be a complex vector space and $u : E \to \mathbb{R}$ a real linear functional. Then
$$f(x) = u(x) - i\,u(ix)$$
is complex linear with $\operatorname{Re}f = u$. Each complex linear functional $f$ arises in this way from $u = \operatorname{Re} f$. If $E$ is normed and $u$ is bounded, then $\|f\| = \|u\|$.

*Proof.* The map $f$ is real linear, and $f(ix) = u(ix) - i\,u(-x) = u(ix) + i\,u(x) = i\big(u(x) - i\,u(ix)\big) = if(x)$. So $f$ is complex linear, and $\operatorname{Re}f(x) = u(x)$. Conversely, for a complex linear $f$ with $u = \operatorname{Re}f$, $\operatorname{Im}f(x) = -\operatorname{Re}(if(x)) = -\operatorname{Re}f(ix) = -u(ix)$.

For the norms, $|u(x)| = |\operatorname{Re}f(x)| \le |f(x)|$, so $\|u\| \le \|f\|$. For the converse, let $x \in E$ and choose $\lambda \in \mathbb{C}$ with $|\lambda| = 1$ and $\lambda f(x) = |f(x)|$. Then $|f(x)| = f(\lambda x)$ is real, so $|f(x)| = u(\lambda x) \le \|u\|\,\|\lambda x\| = \|u\|\,\|x\|$. $\square$

::: mathlib
`StrongDual.extendRCLike` · `Mathlib.Analysis.RCLike.Extend`

`fr.extendRCLike : StrongDual 𝕜 F` for `fr : StrongDual ℝ F`, over any `RCLike` field `𝕜`, with `StrongDual.extendRCLike_apply : fr.extendRCLike x = ↑(fr x) - RCLike.I * ↑(fr (RCLike.I • x))`, the formula of the lemma, and `StrongDual.re_extendRCLike_apply` for the real part. The algebraic version without continuity is `Module.Dual.extendRCLike`. The equality of norms is proved inside the proof of the normed theorem, by the same rotation argument.

<?decl StrongDual.extendRCLike?>
:::

**Theorem (Hahn-Banach, normed form).** Let $E$ be a normed space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, $M$ a subspace and $f \in M^*$. Then there is $g \in E^*$ with $g|_M = f$ and $\|g\| = \|f\|$.

*Proof.* The real case is the corollary. Let $\mathbb{K} = \mathbb{C}$. Regard $E$ and $M$ as real spaces and put $u = \operatorname{Re}f$, a bounded real functional on $M$ with $\|u\| = \|f\|$ by the lemma. The real corollary gives a real functional $v$ on $E$ with $v|_M = u$ and $\|v\| = \|u\|$. Let $g(x) = v(x) - i\,v(ix)$. By the lemma $g$ is complex linear with $\|g\| = \|v\| = \|f\|$. For $m \in M$, $im \in M$, so $g(m) = u(m) - i\,u(im) = f(m)$, again by the lemma applied to $f$ on $M$. $\square$

::: mathlib
`exists_extension_norm_eq` · `Mathlib.Analysis.Normed.Module.HahnBanach`

`exists_extension_norm_eq (p : Subspace 𝕜 E) (f : StrongDual 𝕜 p) : ∃ g : StrongDual 𝕜 E, (∀ x : p, g x = f x) ∧ ‖g‖ = ‖f‖`, for a field with `[IsRCLikeNormedField 𝕜]`, a class that says that the normed field is $\mathbb{R}$ or $\mathbb{C}$ up to the choice of instances. The space `E` may be seminormed. The proof applies `Module.Dual.exists_continuous_extension_of_le_seminorm` of `Mathlib.Analysis.LocallyConvex.HahnBanach` to the seminorm `‖f‖₊ • normSeminorm 𝕜 E`, and that lemma does the work of the text: the real case by `exists_extension_of_le_sublinear`, and the complex case through the real part.

<?decl exists_extension_norm_eq?>
:::

### Examples

**Example (Extension in the plane).** Let $E = \mathbb{R}^2$ with $\|\cdot\|_\infty$, $M = \mathbb{R}(1, 1)$ and $f(t, t) = t$. Then $\|(t, t)\|_\infty = |t|$, so $\|f\| = 1$. The extensions of $f$ are $g_a(x, y) = ax + (1 - a)y$ for $a \in \mathbb{R}$, with $\|g_a\| = |a| + |1 - a|$, the norm of a functional for $\|\cdot\|_\infty$ being the $\ell^1$ norm of its coefficients. So the extensions of norm $1$ are exactly the $g_a$ with $a \in [0, 1]$: the extension of the theorem is not unique.

**Example (Uniqueness for the Euclidean norm).** For $E = \mathbb{R}^2$ with $\|\cdot\|_2$ and the same $f$, now $\|(t, t)\|_2 = \sqrt2|t|$, so $\|f\| = 1/\sqrt2$. The norm of $g_a$ is $\sqrt{a^2 + (1 - a)^2}$, which is minimal at $a = \frac12$ only, with value $1/\sqrt2$. So the extension of the same norm is unique, $g(x, y) = (x + y)/2$, the functional $\langle\cdot, (\frac12, \frac12)\rangle$. Chapter 7 shows that this uniqueness holds in each Hilbert space.

**Example (Banach limits).** On $\ell^\infty$ of real sequences let $p(x) = \limsup_n\frac1n(x_1 + \dots + x_n)$, a sublinear functional, and on the subspace $c$ of convergent sequences let $f(x) = \lim x_n$. Then $f = p$ on $c$. The theorem gives a linear $L$ on $\ell^\infty$ with $L(x) = \lim x_n$ for convergent $x$ and $L \le p$. Then $L(x) \le \limsup x_n$ and $-L(x) = L(-x) \le -\liminf x_n$, so $\liminf x_n \le L(x) \le \limsup x_n$, and $L$ is bounded with $\|L\| = 1$. For the shift $S(x)_n = x_{n+1}$, $p(Sx - x) = \limsup\frac{x_{n+1} - x_1}{n} = 0$ and also $p(x - Sx) = 0$, so $L(Sx) = L(x)$. For $x = (1, 0, 1, 0, \dots)$ this gives $L(x) = L(Sx)$ and $L(x) + L(Sx) = L(1, 1, \dots) = 1$, so $L(x) = \frac12$.

**Counterexample (Extension without the norm).** On $M = c_{00} \subseteq \ell^\infty$ the functional $s(x) = \sum_n x_n$ is linear and not bounded. By linear algebra it extends to a linear functional on $\ell^\infty$, but no extension is bounded, since its restriction to $c_{00}$ would be bounded. So the theorem needs the bound on $M$, and it extends a bound, not only a linear map.

### The library around it

The file `Mathlib.Analysis.Convex.Cone.Extension` has the extension theorem of M. Riesz and the sublinear form. The file `Mathlib.Analysis.Normed.Module.HahnBanach` has the normed form and the norming functionals of Section 2. The file `Mathlib.Analysis.LocallyConvex.HahnBanach` has the forms for seminorms and for locally convex spaces: `Module.Dual.exists_extension_of_le_seminorm` extends a functional dominated by a seminorm, and `StrongDual.exists_extension` extends a continuous functional on a subspace of a locally convex space, without a norm. The same file has `ContinuousLinearMap.exist_extension_of_finiteDimensional_range`: a bounded operator from a subspace into a finite dimensional space extends.

Common errors of a learner:

- Forgetting that the extension is not unique in general.
- Expecting a bounded extension of an operator into a general Banach space. For maps into $F \ne \mathbb{K}$ the theorem fails in general, but it holds for $F = \ell^\infty$ (Exercise 7).
- Using the real theorem for a complex space without the passage through the real part.

### Exercises

1. (A) Show that each seminorm is sublinear and that $p(x) = \max(x_1, x_2)$ is sublinear on $\mathbb{R}^2$.
2. (A) In the first example compute $\|g_a\|$ and check that the extensions of norm $1$ are the $g_a$ with $0 \le a \le 1$.
3. (A) Let $u(x, y) = x$ on $\mathbb{C}$ regarded as $\mathbb{R}^2$. Compute the complex functional $f(z) = u(z) - i\,u(iz)$.
4. (B) Show that the extension in the sublinear form is unique when $p$ is linear.
5. (B) Let $M$ be a closed subspace of a normed space $E$ and $x_0 \notin M$. Show that there is $g \in E^*$ with $g|_M = 0$, $\|g\| = 1$ and $g(x_0) = d(x_0, M)$. Hint: define $f$ on $M + \mathbb{K}x_0$.
6. (B) Show that a Banach limit $L$ is not multiplicative: find $x, y \in \ell^\infty$ with $L(xy) \ne L(x)L(y)$.
7. (C) Let $M$ be a subspace of a normed space $E$ and $T : M \to \ell^\infty$ bounded. Show that $T$ extends to $E$ with the same norm. Hint: extend each coordinate.
8. (C) Show that in the one dimensional step the extension with $g \le p$ is unique if and only if $a = b$. Give an example with $a < b$.

### Notes and history

Hans Hahn published the extension theorem for real normed spaces in 1927, and Banach published it, with the sublinear functional, in 1929. The complex form is due to Bohnenblust and Sobczyk, and independently to Soukhomlinov, in 1938. The extension theorem for convex cones is due to Marcel Riesz. The file `Mathlib.Analysis.Convex.Cone.Extension` has the authors Yury Kudryashov and Frédéric Dupuis, the file `Mathlib.Analysis.Normed.Module.HahnBanach` has the authors Yury Kudryashov and Heather Macbeth, and the file `Mathlib.Analysis.RCLike.Extend` has the author Ruben Van de Velde.

### Reference

<?reference?>
