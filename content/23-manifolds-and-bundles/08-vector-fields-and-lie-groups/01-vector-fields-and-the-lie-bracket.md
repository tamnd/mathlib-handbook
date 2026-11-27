---
title: Vector fields and the Lie bracket
kind: theory
modules:
  - Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
  - Mathlib.Analysis.Calculus.VectorField
  - Mathlib.Geometry.Manifold.VectorField.Pullback
  - Mathlib.Geometry.Manifold.VectorField.LieBracket
  - Mathlib.Geometry.Manifold.DerivationBundle
  - Mathlib.Analysis.Calculus.DifferentialForm.Basic
  - Mathlib.Analysis.Calculus.DifferentialForm.VectorField
  - Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
  - Mathlib.Geometry.Manifold.VectorBundle.Tensoriality
  - Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
  - Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
  - Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric
  - Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
explains:
  E3: [VectorField.lieBracket, VectorField.mlieBracket, ContMDiffSection, extDeriv]
  E2: [VectorField.lieBracket_eq, VectorField.lieBracket_swap, VectorField.leibniz_identity_lieBracket, VectorField.lieBracket_smul_left, VectorField.fderiv_apply_lieBracket, VectorField.pullback, VectorField.pullback_lieBracket, VectorField.mpullback, VectorField.mpullback_mlieBracket, VectorField.leibniz_identity_mlieBracket, ContMDiffAt.mlieBracket_vectorField, extDeriv_extDeriv, extDeriv_apply_vectorField, PointDerivation, IsLocalFrameOn, TensorialAt, CovariantDerivative, CovariantDerivative.torsion, CovariantDerivative.IsMetricCompatible, CovariantDerivative.IsLeviCivitaConnection, CovariantDerivative.IsLeviCivitaConnection.uniqueness]
  E1: auto
families: []
requires: [V23.C03, V23.C04, V23.C05, V17.C04, V08.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Vector fields and the Lie bracket

### Overview

A vector field $V$ on an open set of a normed space $E$ is a map $V : E \to E$. It differentiates functions: $V f(x) = Df(x)\,V(x)$. The composite of two such operators is not of the same kind, since $V(Wf)$ contains second derivatives of $f$. The commutator $V(Wf) - W(Vf)$ has no second derivatives, by the symmetry of $D^2 f$, and it is again a vector field, the Lie bracket $[V, W]$. This section proves the identities of the bracket on a normed space, proves that it commutes with pullbacks by diffeomorphisms, and uses this to define it on a manifold. The same pattern gives the exterior derivative. The last part surveys the other operations on sections that Mathlib has.

Throughout, $\mathbb{K}$ is $\mathbb{R}$ or $\mathbb{C}$ and second derivatives are symmetric for $C^2$ maps (Volume 17, Chapter 4).

### Definitions

**Definition (Vector field).** A *vector field* on a manifold $M$ is a section $x \mapsto V(x) \in T_xM$ of the tangent bundle. It is $C^k$ if $x \mapsto (x, V(x))$ is a $C^k$ map $M \to TM$ (Chapter 5).

**Definition (Lie bracket on a normed space).** Let $V, W : E \to E$ be differentiable at $x$. Their *Lie bracket* at $x$ is
$$[V, W](x) = DW(x)\,V(x) - DV(x)\,W(x).$$

**Definition (Pullback).** Let $f : E \to F$ and $V : F \to F$. The *pullback* $f^*V$ is $f^*V(x) = Df(x)^{-1} V(f(x))$ when $Df(x)$ is invertible, and $0$ otherwise.

**Definition (Lie bracket on a manifold).** Let $V, W$ be vector fields on $M$ and $x_0 \in M$. Let $\tilde\varphi$ be the extended chart at $x_0$. Pull $V$ and $W$ back by $\tilde\varphi^{-1}$ to fields on $\operatorname{range} I \subseteq E$, take their bracket there at $\tilde\varphi(x_0)$, with derivatives within $\operatorname{range} I$, and pull the result back by $\tilde\varphi$ to $T_{x_0}M$. This is $[V, W](x_0)$.

**Definition (Exterior derivative).** Let $\omega : E \to \Lambda^n(E; F)$ be a field of continuous alternating $n$-linear maps (Volume 8, Chapter 1). Its *exterior derivative* is the $(n+1)$-form
$$d\omega(x)(v_0, \dots, v_n) = \sum_{i=0}^{n} (-1)^i\, D\omega(x)(v_i)(v_0, \dots, \widehat{v_i}, \dots, v_n).$$

::: mathlib
`VectorField.lieBracket` · `Mathlib.Analysis.Calculus.VectorField`

`VectorField.lieBracket 𝕜 V W x` is `fderiv 𝕜 W x (V x) - fderiv 𝕜 V x (W x)`, the lemma `lieBracket_eq`. The pullback `VectorField.pullback 𝕜 f V` has the junk value $0$ at points where the derivative is not invertible. The order of the two terms gives $[V, W] f = V(W f) - W(V f)$, the lemma `fderiv_apply_lieBracket`.

<?decl VectorField.lieBracket?>
<?decl VectorField.pullback?>
<?decl VectorField.fderiv_apply_lieBracket?>
:::

::: mathlib
`VectorField.mlieBracket` · `Mathlib.Geometry.Manifold.VectorField.LieBracket`

`VectorField.mlieBracket I V W x₀` follows the definition above: `mlieBracketWithin_def` writes it with the pullback `VectorField.mpullback` by `extChartAt I x₀` and its inverse, and the bracket `lieBracketWithin` on `range I`. The vector fields are dependent functions `(x : M) → TangentSpace I x`, and their smoothness is stated for `fun x ↦ (⟨x, V x⟩ : TangentBundle I M)`.

<?decl VectorField.mlieBracket?>
<?decl VectorField.mpullback?>
:::

### Theorems and proofs

Write $V'$ for $DV(x)$ and $V''$ for $D^2 V(x)$, a symmetric bilinear map when $V$ is $C^2$.

**Theorem (Antisymmetry and Leibniz rule).** $[V, W] = -[W, V]$. For a differentiable function $g : E \to \mathbb{K}$, $[gV, W] = -(Dg \cdot W)\,V + g\,[V, W]$.

*Proof.* The first identity is the definition read backwards. For the second, $D(gV)(x)w = (Dg(x)w)V(x) + g(x)V'w$. So $[gV, W] = W'(gV) - D(gV)W = g W'V - (Dg \cdot W)V - g V'W = g[V, W] - (Dg \cdot W)V$. $\square$

**Theorem (The bracket is a commutator).** Let $f : E \to F$ be $C^2$ at $x$, and let $V, W$ be differentiable at $x$. Then $Df \cdot [V, W] = V(Wf) - W(Vf)$, where $Vf = Df \cdot V$.

*Proof.* By the product rule, $D(Df \cdot W)(x)\,a = D^2f(x)(a, W(x)) + Df(x)\,W'a$. Put $a = V(x)$ and subtract the same formula with $V$ and $W$ exchanged. The terms $D^2f(x)(V, W)$ and $D^2f(x)(W, V)$ cancel by symmetry. What remains is $Df(x)(W'V - V'W) = Df(x)[V, W](x)$. $\square$

**Theorem (Jacobi identity).** Let $U, V, W$ be $C^2$ near $x$. Then
$$[U, [V, W]] = [[U, V], W] + [V, [U, W]].$$

*Proof.* By antisymmetry, the claim is the cyclic identity $[U, [V, W]] + [V, [W, U]] + [W, [U, V]] = 0$. By the product rule, $D[V, W]\,u = W''(u, V) + W'V'u - V''(u, W) - V'W'u$. So
$$[U, [V, W]] = W''(U, V) - V''(U, W) + W'V'U - V'W'U - U'W'V + U'V'W.$$
The cyclic substitution $U \to V \to W \to U$ gives the two other terms. The second derivatives cancel in pairs: $W''(U, V)$ from the first term and $-W''(V, U)$ from the second, by symmetry of $W''$, and in the same way for $U''$ and $V''$. The twelve products of first derivatives cancel in pairs too. For example, $W'V'U$ in the first term cancels $-W'V'U$ in the third, and $-U'W'V$ in the first cancels $U'W'V$ in the second. $\square$

**Theorem (Naturality).** Let $\varphi : E \to F$ be $C^2$ near $x$ with $D\varphi(x)$ invertible, and let $V, W : F \to F$ be differentiable at $\varphi(x)$. Then $\varphi^*[V, W](x) = [\varphi^*V, \varphi^*W](x)$.

*Proof.* The set where $D\varphi$ is invertible is open, so near $x$ the fields $V_1 = \varphi^*V$ and $W_1 = \varphi^*W$ satisfy $V \circ \varphi = D\varphi \cdot V_1$. Differentiate in the direction $a$:
$$V'(\varphi(x))\,D\varphi(x)\,a = D^2\varphi(x)(a, V_1(x)) + D\varphi(x)\,V_1'(x)\,a.$$
Put $a = W_1(x)$, do the same for $W$ with $a = V_1(x)$, and subtract. Since $D\varphi(x)W_1(x) = W(\varphi(x))$, the left sides give $W'V - V'W = [V, W]$ at $\varphi(x)$. On the right the second derivatives cancel by symmetry, and $D\varphi(x)(W_1'V_1 - V_1'W_1) = D\varphi(x)[V_1, W_1](x)$ remains. Apply $D\varphi(x)^{-1}$. $\square$

Naturality makes the bracket on a manifold independent of the chart. Two charts differ by a $C^2$ change of charts, and the bracket in one chart is the pullback of the bracket in the other. So the Jacobi identity and the Leibniz rule pass from $E$ to $M$, and $[V, W]$ is $C^{k}$ when $V$ and $W$ are $C^{k+1}$.

**Theorem ($d \circ d = 0$).** If $\omega$ is $C^2$, then $d(d\omega) = 0$.

*Proof.* Expand $d(d\omega)(x)(v_0, \dots, v_{n+1})$. Each term is $\pm D^2\omega(x)(v_i, v_j)$ applied to the list with $v_i$ and $v_j$ removed. Fix $i < j$. Removing $v_j$ first gives the sign $(-1)^j$, and then removing $v_i$, still at place $i$, gives $(-1)^i$. Removing $v_i$ first gives $(-1)^i$, and then $v_j$ is at place $j - 1$, which gives $(-1)^{j-1}$. The two terms have opposite signs and, by symmetry of $D^2\omega(x)$, the same value. So they cancel. $\square$

::: mathlib
`VectorField.leibniz_identity_mlieBracket` · `Mathlib.Geometry.Manifold.VectorField.LieBracket`

The Jacobi identity is stated as a Leibniz identity: `leibniz_identity_lieBracket` on a normed space and `leibniz_identity_mlieBracket` on a manifold, which needs `[CompleteSpace E]` and fields that are `ContMDiff` of order `minSmoothness 𝕜 2`. Here `minSmoothness 𝕜 n` is `n` for $\mathbb{R}$ and $\mathbb{C}$, and $\omega$ for other fields, where the symmetry of second derivatives needs analyticity. Naturality is `pullback_lieBracket` and `mpullback_mlieBracket`. `ContMDiffAt.mlieBracket_vectorField` gives a bracket of class $C^m$ from fields of class $C^n$ with `minSmoothness 𝕜 (m + 1) ≤ n`.

<?decl VectorField.leibniz_identity_mlieBracket?>
<?decl VectorField.leibniz_identity_lieBracket?>
<?decl VectorField.pullback_lieBracket?>
<?decl ContMDiffAt.mlieBracket_vectorField?>
:::

::: mathlib
`extDeriv` · `Mathlib.Analysis.Calculus.DifferentialForm.Basic`

`extDeriv` takes `ω : E → E [⋀^Fin n]→L[𝕜] F` to a field of `(n + 1)`-forms. `extDeriv_extDeriv` is $d \circ d = 0$ under `ContDiff 𝕜 r ω` and `minSmoothness 𝕜 2 ≤ r`. The file `DifferentialForm.VectorField` proves `extDeriv_apply_vectorField`, the formula of $d\omega$ on vector fields with brackets. The index of this edition has exterior derivatives only on normed spaces, not on manifolds.

<?decl extDeriv?>
<?decl extDeriv_extDeriv?>
<?decl extDeriv_apply_vectorField?>
:::

### Examples

**Example (A bracket in the plane).** On $\mathbb{R}^2$ let $V = \partial_x = (1, 0)$ and $W = x\,\partial_y = (0, x)$. Then $V' = 0$ and $W'(a, b) = (0, a)$. So $[V, W] = W'V - V'W = (0, 1) = \partial_y$. Constant fields have bracket $0$, but $\partial_x$ and $x\partial_y$ do not commute.

**Example (Rotations).** For $a \in \mathbb{R}^3$ let $V_a(p) = a \times p$, the infinitesimal rotation about $a$. It is linear, and by Exercise 2, $[V_a, V_b](p) = b \times (a \times p) - a \times (b \times p)$. The Jacobi identity of the cross product turns this into $p \times (a \times b) = -V_{a \times b}(p)$. For instance $L_x = V_{e_1}$ and $L_z = V_{e_3}$ give $L_x(p) = (0, -z, y)$, $L_z(p) = (-y, x, 0)$, and $[L_x, L_z](p) = (z, 0, -x) = V_{e_2}(p)$. So $a \mapsto -V_a$ is an isomorphism of Lie algebras from $(\mathbb{R}^3, \times)$ onto the rotation fields.

**Example (A $1$-form).** For $\omega = g\,dx$ on $\mathbb{R}^2$, $d\omega(v_0, v_1) = Dg(v_0)\,dx(v_1) - Dg(v_1)\,dx(v_0) = (\partial_y g)(dy \wedge dx)(v_0, v_1)$. So $d(g\,dx) = -\partial_y g\; dx \wedge dy$, the usual formula.

### The library around it

Smooth sections of a vector bundle form a module: `ContMDiffSection I F n V`, with notation `Cₛ^n⟮I; F, V⟯`, has instances of additive group and of module over $\mathbb{K}$. Point derivations `PointDerivation I x` are the derivations of the algebra of germs at $x$; the docstring warns that they agree with tangent vectors only for finite-dimensional $C^\infty$ real manifolds. A local frame `IsLocalFrameOn I F n s U` is a family of $C^n$ sections that is a basis at each point of $U$; `Bundle.Trivialization.localFrame` builds one from a trivialization. `TensorialAt` says that an operation on sections respects sums and products by germs of differentiable functions at a point, so that its value depends only on the value of the section there.

::: mathlib
`CovariantDerivative` · `Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic`

A covariant derivative is additive and satisfies $\nabla_X(g\sigma) = (Xg)\sigma + g\nabla_X\sigma$ on differentiable sections; the predicate is `IsCovariantDerivativeOn`, and the bundled object `CovariantDerivative`. The argument order is `cov σ x (X x)` for $\nabla_X\sigma(x)$. `CovariantDerivative.torsion` needs `[FiniteDimensional 𝕜 E]`. Over $\mathbb{R}$ with a Riemannian metric (`IsContMDiffRiemannianBundle`), `IsMetricCompatible` and `IsLeviCivitaConnection` (torsion free and metric) are defined, `leviCivitaConnection` constructs one, and `IsLeviCivitaConnection.uniqueness` proves uniqueness on differentiable fields.

<?decl CovariantDerivative?>
<?decl CovariantDerivative.torsion?>
<?decl CovariantDerivative.IsMetricCompatible?>
<?decl CovariantDerivative.IsLeviCivitaConnection?>
<?decl CovariantDerivative.IsLeviCivitaConnection.uniqueness?>
<?decl ContMDiffSection?>
<?decl PointDerivation?>
<?decl IsLocalFrameOn?>
<?decl TensorialAt?>
:::

Common errors of a learner:

- Expecting the bracket of non-differentiable fields to be meaningful. `lieBracket` is defined for all fields, with `fderiv` equal to $0$ at non-differentiable points.
- Forgetting the sign convention: Mathlib has $[V, W] = DW \cdot V - DV \cdot W$, which acts as $V \circ W - W \circ V$ on functions.
- Assuming that a pullback by a non-invertible map is meaningful. Its value is the junk $0$.

### Exercises

1. (A) Compute $[x\partial_x, y\partial_y]$ and $[x\partial_y, y\partial_x]$ on $\mathbb{R}^2$.
2. (A) Show that the bracket of two linear fields $V(x) = Ax$ and $W(x) = Bx$ is the linear field of $BA - AB$.
3. (B) Prove the Leibniz rule in the second argument: $[V, gW] = (Dg \cdot V)W + g[V, W]$.
4. (B) Let $\varphi(x) = 2x$ on $\mathbb{R}^n$. Compute $\varphi^*V$ for a field $V$ and check naturality for two linear fields.
5. (B) Show that $d(dg) = 0$ for a $C^2$ function $g$ on $\mathbb{R}^2$, written as a $0$-form. Hint: this is $\partial_x\partial_y g = \partial_y\partial_x g$.
6. (C) Prove the formula $d\omega(V, W) = V(\omega(W)) - W(\omega(V)) - \omega([V, W])$ for a $1$-form $\omega$ and vector fields $V, W$. Hint: write $\omega(W)(x) = \omega(x)(W(x))$ and use the product rule.
7. (C) Let $\nabla$ and $\nabla'$ be covariant derivatives on the same bundle. Show that $\nabla - \nabla'$ is tensorial in the section, and so is given by a field of linear maps.

### Notes and history

The bracket goes back to the work of Lie on transformation groups in the 1870s and 1880s, and the Jacobi identity is named after Jacobi. The exterior derivative is due to Cartan. The Mathlib definitions on normed spaces come first, and the definitions on manifolds are reduced to them through charts and pullbacks, as in this section.

### Reference

<?reference?>
