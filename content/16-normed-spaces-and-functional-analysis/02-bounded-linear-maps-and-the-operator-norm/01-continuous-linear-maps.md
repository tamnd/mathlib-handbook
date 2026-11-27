---
title: Continuous linear maps
kind: theory
modules:
  - Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
  - Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
explains:
  E3: [LinearMap.mkContinuous, continuous_of_linear_of_bound, SemilinearMapClass.bound_of_continuous, IsBoundedLinearMap]
  E2: [LinearMap.mkContinuousOfExistsBound, IsBoundedLinearMap.toContinuousLinearMap, ContinuousLinearMap.isBoundedLinearMap, LinearMap.bound_of_ball_bound, LinearMap.bound_of_shell, AddMonoidHomClass.continuous_of_bound]
  E1: auto
families: []
requires: [V07, V13, V16.C01]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Continuous linear maps

### Overview

In linear algebra every linear map between finite dimensional spaces is given by a matrix, and it is automatically continuous. In infinite dimension this fails, and the maps that matter in analysis are the continuous ones. This section proves the basic criterion: a linear map between normed spaces is continuous if and only if it is *bounded*, that is, $\|Tx\| \le C\|x\|$ for a constant $C$. So continuity, a topological property, becomes one inequality. The section then shows how Mathlib bundles a continuous linear map as an object of the type `E →L[𝕜] F`, and how the constructor `LinearMap.mkContinuous` turns a linear map and a bound into such an object. The examples give one bounded and two unbounded maps, and the proof that each infinite dimensional normed space has a linear functional that is not continuous.

### Definitions

**Definition (Bounded linear map).** Let $E$ and $F$ be normed spaces over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$. A linear map $T : E \to F$ is *bounded* if there is a constant $C \ge 0$ with
$$\|Tx\| \le C\,\|x\| \quad \text{for all } x \in E.$$

The word "bounded" here does not mean that the image $T(E)$ is bounded, which happens only for $T = 0$. It means that $T$ maps bounded sets to bounded sets: if $\|x\| \le R$, then $\|Tx\| \le CR$. The two meanings are a frequent source of confusion, and the text uses "bounded" only in the sense of the definition.

::: mathlib
`IsBoundedLinearMap` · `Mathlib.Analysis.Normed.Operator.BoundedLinearMaps`

`IsBoundedLinearMap 𝕜 f` is a structure with two fields: `f` is linear, and `∃ M, 0 < M ∧ ∀ x, ‖f x‖ ≤ M * ‖x‖`. It is an unbundled predicate on a plain function `f : E → F`. It is used mainly in calculus (Volume 17), where a derivative is checked to be a bounded linear map. The conversion to the bundled form is `IsBoundedLinearMap.toContinuousLinearMap`, and the converse is `ContinuousLinearMap.isBoundedLinearMap`.

<?decl IsBoundedLinearMap?>
:::

**Definition (The type of continuous linear maps).** The set of continuous linear maps $E \to F$ is written $L(E, F)$. It is a vector space under pointwise operations, since sums and scalar multiples of continuous maps are continuous. For $F = \mathbb{K}$ it is the *dual space* $E^*$ of $E$, studied in Section 2 and in Chapter 5.

::: mathlib
`ContinuousLinearMap` · `Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic`

The type `E →L[𝕜] F` is a structure that extends the linear maps `E →ₗ[𝕜] F` with a field `cont` that says the map is continuous. It is defined for any topological modules, which is the subject of Volume 14. An element `f` coerces to a function, so `f x` makes sense, and to a linear map, written `(f : E →ₗ[𝕜] F)` or `f.toLinearMap`. The general form is the semilinear `E →SL[σ] F`, where `σ : 𝕜 →+* 𝕜₂` is a ring map and `f (c • x) = σ c • f x`. With `σ` the complex conjugation it covers the conjugate linear maps of Chapter 7, and `E →L[𝕜] F` is the special case `σ = RingHom.id 𝕜`.

<?decl ContinuousLinearMap?>
:::

### Theorems and proofs

**Theorem (Continuity and boundedness).** Let $T : E \to F$ be a linear map between normed spaces over $\mathbb{K}$. The following are equivalent.

1. $T$ is continuous.
2. $T$ is continuous at $0$.
3. $T$ is bounded on some ball $B(0, r)$ with $r > 0$: there is $M$ with $\|Tx\| \le M$ for $\|x\| < r$.
4. $T$ is bounded: $\|Tx\| \le C\|x\|$ for some $C \ge 0$ and all $x$.
5. $T$ is Lipschitz.

*Proof.* (1) ⇒ (2) is clear.

(2) ⇒ (3). Continuity at $0$ with $\varepsilon = 1$ gives $r > 0$ such that $\|x\| < r$ implies $\|Tx - T0\| = \|Tx\| < 1$. So $M = 1$ works.

(3) ⇒ (4). Let $x \in E$ and $0 < s < r$. If $\|x\| > 0$, the vector $y = \frac{s}{\|x\|}x$ has $\|y\| = s < r$. So $\|Ty\| \le M$, and by linearity $Ty = \frac{s}{\|x\|}Tx$, which gives $\|Tx\| \le \frac{M}{s}\|x\|$. If $\|x\| = 0$, then $\|tx\| = 0 < r$ for every $t \in \mathbb{R}$, so $|t|\,\|Tx\| = \|T(tx)\| \le M$ for all $t$. This forces $\|Tx\| = 0$, and the bound holds again. So (4) holds with $C = M/s$ for any $s < r$, and also with $C = M/r$ by letting $s \to r$.

(4) ⇒ (5). For $x, y \in E$, $\|Tx - Ty\| = \|T(x - y)\| \le C\|x - y\|$.

(5) ⇒ (1). A Lipschitz map is uniformly continuous, hence continuous. $\square$

Two points of the proof deserve attention. First, linearity turns local information at $0$ into a global bound, by scaling: this is the step (3) ⇒ (4). Second, the scaling uses real multiples of $x$. Over a general nontrivially normed field the norms of the scalars are not all real numbers, and the scaling uses the powers $c^n$ of a scalar with $|c| > 1$ to bring $x$ into a shell $r/|c| \le \|c^n x\| < r$. The constant is then $M|c|/r$ in place of $M/r$.

::: mathlib
`SemilinearMapClass.bound_of_continuous` · `Mathlib.Analysis.Normed.Operator.Basic`

The step (1) ⇒ (4): a continuous semilinear map gives `∃ C, 0 < C ∧ ∀ x, ‖f x‖ ≤ C * ‖x‖`. It needs the ring map `σ` to be isometric, `[RingHomIsometric σ₁₂]`, which holds for the identity and for the complex conjugation. The shell argument of the remark is `LinearMap.bound_of_shell`, and the step (3) ⇒ (4) is `LinearMap.bound_of_ball_bound`.

<?decl SemilinearMapClass.bound_of_continuous?>
:::

::: mathlib
`continuous_of_linear_of_bound` · `Mathlib.Analysis.Normed.Operator.ContinuousLinearMap`

The step (4) ⇒ (1) for an unbundled function: additivity, homogeneity and `∀ x, ‖f x‖ ≤ C * ‖x‖` give `Continuous f`. The same fact for any additive group map is `AddMonoidHomClass.continuous_of_bound` in `Mathlib.Analysis.Normed.Group.Uniform`. This direction needs no hypothesis on the scalar field, since it does not rescale.

<?decl continuous_of_linear_of_bound?>
:::

::: mathlib
`LinearMap.mkContinuous` · `Mathlib.Analysis.Normed.Operator.ContinuousLinearMap`

`f.mkContinuous C h : E →SL[σ] F` for a linear map `f` and a proof `h : ∀ x, ‖f x‖ ≤ C * ‖x‖`. This is the usual way to build a continuous linear map in Mathlib: define the linear map first, with its proofs of additivity and homogeneity, then prove the bound. The function of `f.mkContinuous C h` is `f` by definition (`LinearMap.mkContinuous_apply`), and its operator norm is at most `C` when `0 ≤ C` (`LinearMap.mkContinuous_norm_le`, Section 2). The variant `LinearMap.mkContinuousOfExistsBound` takes an existential bound.

<?decl LinearMap.mkContinuous?>
:::

**Theorem (Closed kernels).** Let $f : E \to \mathbb{K}$ be a linear functional. Then $f$ is continuous if and only if its kernel $\ker f$ is closed.

*Proof.* If $f$ is continuous, $\ker f = f^{-1}(\{0\})$ is the preimage of a closed set, so it is closed.

Conversely let $\ker f$ be closed. If $f = 0$, it is continuous. Otherwise choose $x_0$ with $f(x_0) = 1$. Then $x_0 \notin \ker f$, and since the complement of $\ker f$ is open, there is $r > 0$ with $B(x_0, r) \cap \ker f = \emptyset$. Claim: $|f(y)| < 1$ for all $y \in B(0, r)$. Suppose $\|y\| < r$ and $|f(y)| \ge 1$. Put $z = x_0 - y / f(y)$. Then $f(z) = 1 - 1 = 0$, so $z \in \ker f$, and $\|z - x_0\| = \|y\| / |f(y)| \le \|y\| < r$, so $z \in B(x_0, r)$. This contradicts the choice of $r$. So $f$ is bounded by $1$ on $B(0, r)$, and it is continuous by the last theorem. $\square$

The theorem is special to functionals. For a linear map into an infinite dimensional space a closed kernel does not imply continuity: Exercise 6 gives an injective, discontinuous map, whose kernel $\{0\}$ is closed.

::: mathlib
`LinearMap.continuous_iff_isClosed_ker` · `Mathlib.Topology.Algebra.Module.FiniteDimension`

`Continuous l ↔ IsClosed (l.ker : Set E)` for `l : E →ₗ[𝕜] 𝕜`, in any topological vector space over a nontrivially normed field. The easy direction for any continuous linear map is `ContinuousLinearMap.isClosed_ker`. Both live in the topological algebra of Volume 14.

<?decl LinearMap.continuous_iff_isClosed_ker?>
:::

### Examples

**Example (Integration is bounded).** Let $C[0,1]$ be the continuous real functions on $[0,1]$ with $\|f\|_\infty = \max_t |f(t)|$, and $I(f) = \int_0^1 f(t)\,dt$. Then $|I(f)| \le \int_0^1 |f| \le \|f\|_\infty$, so $I$ is bounded with $C = 1$. The constant $1$ is the best one, since $f = 1$ gives $I(f) = 1 = \|f\|_\infty$. In the same way $(Vf)(t) = \int_0^t f(s)\,ds$ is a bounded operator $C[0,1] \to C[0,1]$ with $\|Vf\|_\infty \le \|f\|_\infty$.

**Example (A multiplication operator).** Let $g \in C[0,1]$ and $(M_g f)(t) = g(t) f(t)$. Then $|g(t)f(t)| \le \|g\|_\infty \|f\|_\infty$, so $M_g$ is bounded with $C = \|g\|_\infty$. For $g(t) = t$ and $f = 1$, $\|M_g f\|_\infty = 1$, so the constant $1$ is sharp.

**Counterexample (Differentiation is not bounded).** Let $P$ be the space of real polynomials with the norm $\|p\|_\infty = \max_{[0,1]}|p|$, and $D(p) = p'$. For $p_n(t) = t^n$, $\|p_n\|_\infty = 1$ and $\|Dp_n\|_\infty = \|n t^{n-1}\|_\infty = n$. No constant $C$ has $n \le C$ for all $n$, so $D$ is not bounded and not continuous. Concretely $p_n / n \to 0$ in $P$, while $D(p_n/n) = t^{n-1}$ has norm $1$ and does not tend to $0$. Differentiation is continuous for other norms, for example as a map from $C^1[0,1]$ with $\|f\| = \|f\|_\infty + \|f'\|_\infty$ to $C[0,1]$.

**Counterexample (The sum of the terms).** On $c_{00}$ with $\|\cdot\|_\infty$ (Chapter 1, Section 3) let $s(x) = \sum_n x_n$, a finite sum for each $x$. For $x = (1, \dots, 1, 0, \dots)$ with $N$ ones, $\|x\|_\infty = 1$ and $s(x) = N$. So $s$ is an unbounded linear functional, and by the theorem on closed kernels, $\ker s$ is a hyperplane that is not closed. In fact $\ker s$ is dense in $c_{00}$ (Exercise 5).

**Example (Every infinite dimensional space has a discontinuous functional).** Let $E$ be an infinite dimensional normed space. By Zorn's lemma $E$ has an algebraic basis $(b_i)_{i \in J}$, a Hamel basis (Volume 7, Chapter 2). Replace $b_i$ by $b_i / \|b_i\|$, so each $\|b_i\| = 1$. Since $J$ is infinite, choose distinct indices $i_1, i_2, \dots$. A linear map is determined freely by its values on a basis, so there is a linear $f$ with $f(b_{i_n}) = n$ and $f(b_i) = 0$ for the other $i$. Then $|f(b_{i_n})| = n$ while $\|b_{i_n}\| = 1$, and $f$ is not bounded. The proof gives no formula for $f$, and the use of the axiom of choice cannot be removed.

### The library around it

The file `Mathlib.Analysis.Normed.Operator.ContinuousLinearMap` has the constructors from a bound: `LinearMap.mkContinuous`, `LinearMap.mkContinuousOfExistsBound` and `LinearMap.toContinuousLinearMap₁` for maps from the scalar field. The file `Mathlib.Analysis.Normed.Operator.BoundedLinearMaps` has the unbundled predicate `IsBoundedLinearMap` and its closure properties, and the bounded bilinear maps `IsBoundedBilinearMap`, with the bound $\|B(x, y)\| \le C\|x\|\,\|y\|$. Each bundled continuous linear map `f` has the lemmas `map_add`, `map_smul`, `map_sub`, `map_zero` and `map_sum` from the classes of Volume 7, and `f.continuous` and `f.uniformContinuous` from its field. The composition is `g.comp f`, written `g ∘L f`, the identity is `ContinuousLinearMap.id 𝕜 E`, and two maps are equal when they agree at each point, by the extensionality lemma `ContinuousLinearMap.ext`.

Common errors of a learner:

- Reading "bounded linear map" as "map with bounded image".
- Expecting each linear map of normed spaces to be continuous. Only the finite dimensional case of Chapter 3 gives this.
- Proving continuity at each point by hand, when continuity at $0$ or one bound suffices.
- Building a continuous linear map in Mathlib from a function with three separate proofs, in place of `mkContinuous`.

### Exercises

1. (A) Show that $T(x_1, x_2, \dots) = (x_2, x_3, \dots)$ is bounded on $\ell^p$ with $C = 1$.
2. (A) Show that $T(x)_n = x_n / n$ is bounded on $\ell^\infty$, and find the best constant.
3. (A) Show that $f \mapsto f(1/2)$ is a bounded functional on $C[0,1]$ with $\|\cdot\|_\infty$, and that it is not bounded on $C[0,1]$ with $\|f\|_1 = \int_0^1 |f|$.
4. (B) Let $T : E \to F$ be linear and $E$ a normed space. Show that $T$ is bounded if and only if $T$ maps the unit ball to a bounded set.
5. (B) Show that the kernel of $s$ in the last counterexample is dense in $c_{00}$. Hint: $x - s(x) \cdot \frac1N(e_1 + \dots + e_N)$ for large $N$.
6. (B) Find a linear injective map $T : c_{00} \to c_{00}$ that is not continuous. Hint: $T(x)_n = n x_n$.
7. (C) Let $E$ be a normed space and $f, g$ linear functionals with $\ker f \subseteq \ker g$. Show that $g = \lambda f$ for some scalar $\lambda$, and conclude that $g$ is continuous if $f$ is continuous and $g \neq 0$ is a multiple of it.
8. (C) Let $T : E \to F$ be linear and suppose that $T(x_n) \to 0$ whenever $x_n \to 0$. Show that $T$ is bounded. Hint: if not, find $x_n$ with $\|x_n\| = 1$ and $\|Tx_n\| \ge n^2$, and consider $x_n / n$.

### Notes and history

The equivalence of continuity and boundedness for linear operations is in Banach's thesis of 1920 and in the work of F. Riesz on linear functionals of the 1910s. The use of a Hamel basis to build a discontinuous functional goes back to the basis of $\mathbb{R}$ over $\mathbb{Q}$ that Hamel used in 1905 for a discontinuous solution of $f(x + y) = f(x) + f(y)$. The files `Mathlib.Analysis.Normed.Operator.ContinuousLinearMap` and `Mathlib.Analysis.Normed.Operator.Basic` have the authors Jan-David Salchow, Sébastien Gouëzel and Jean Lo.

### Reference

<?reference?>
