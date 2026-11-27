---
title: The Riesz representation theorem
kind: theory
modules:
  - Mathlib.Analysis.InnerProductSpace.Dual
  - Mathlib.Analysis.InnerProductSpace.LaxMilgram
  - Mathlib.Analysis.Normed.Operator.NormedSpace
explains:
  E3: [InnerProductSpace.toDualMap, InnerProductSpace.toDual, IsCoercive.continuousLinearEquivOfBilin]
  E2: [InnerProductSpace.toDualMap_apply_apply, InnerProductSpace.toDual_apply_apply, InnerProductSpace.toDual_symm_apply, InnerProductSpace.continuousLinearMapOfBilin, InnerProductSpace.continuousLinearMapOfBilin_apply, IsCoercive, IsCoercive.bounded_below, IsCoercive.ker_eq_bot, IsCoercive.isClosed_range, IsCoercive.range_eq_top, IsCoercive.continuousLinearEquivOfBilin_apply, IsCoercive.unique_continuousLinearEquivOfBilin]
  E1: auto
families: []
requires: [V07, V16.C01, V16.C02, V16.C04, V16.C06]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The Riesz representation theorem

### Overview

Each vector $y$ of an inner product space gives a bounded functional $\langle y, \cdot \rangle$ of norm $\|y\|$. The theorem of Riesz says that in a Hilbert space each bounded functional has this form for exactly one $y$. So a Hilbert space is its own dual, up to the complex conjugation that comes from the convention of the inner product. The proof uses the orthogonal projection of Section 1 onto the kernel of the functional. A consequence for bilinear forms is the theorem of Lax and Milgram, which gives the existence and uniqueness of weak solutions of elliptic equations.

### Definitions

**Definition (Riesz map).** For an inner product space $E$ over $\mathbb{K}$, the *Riesz map* $R : E \to E^*$ is $R(y) = \langle y, \cdot \rangle$.

By Chapter 6, Section 1, $R(y)$ is bounded with $\|R(y)\| = \|y\|$. The map $R$ is additive and $R(cy) = \bar{c}R(y)$, so it is conjugate linear over $\mathbb{C}$ and linear over $\mathbb{R}$.

::: mathlib
`InnerProductSpace.toDualMap` · `Mathlib.Analysis.InnerProductSpace.Dual`

`toDualMap 𝕜 E : E →ₗᵢ⋆[𝕜] StrongDual 𝕜 E` is the Riesz map as a conjugate linear isometry; the star in the arrow marks the conjugation. It exists for each inner product space, complete or not. The values are given by `toDualMap_apply_apply : toDualMap 𝕜 E x y = ⟪x, y⟫_𝕜`.

<?decl InnerProductSpace.toDualMap?>
:::

**Definition (coercive form).** A bounded bilinear form $B$ on a real normed space $E$ is *coercive* if there is $C > 0$ with $B(u, u) \ge C\|u\|^2$ for each $u$.

::: mathlib
`IsCoercive` · `Mathlib.Analysis.Normed.Operator.NormedSpace`

`IsCoercive B` for `B : E →L[ℝ] E →L[ℝ] ℝ` is `∃ C, 0 < C ∧ ∀ u, C * ‖u‖ * ‖u‖ ≤ B u u`. A bounded bilinear form is a bounded linear map into the bounded linear functionals, as in Chapter 2.

<?decl IsCoercive?>
:::

### Theorems and proofs

**Theorem (Riesz representation).** Let $E$ be a Hilbert space and $f \in E^*$. There is a unique $y \in E$ with $f(x) = \langle y, x \rangle$ for each $x$, and $\|y\| = \|f\|$. So $R$ is a conjugate linear isometry of $E$ onto $E^*$.

*Proof.* Uniqueness: if $\langle y, x \rangle = \langle y', x \rangle$ for each $x$, take $x = y - y'$. If $f = 0$, take $y = 0$. Otherwise $K = \ker f$ is a closed subspace different from $E$, so $K^\perp \ne \{0\}$ by Section 1. Pick $z \in K^\perp$ with $z \ne 0$. For each $x$, $f(z)x - f(x)z \in K$, since $f$ of it is $0$. So
$$0 = \langle z, f(z)x - f(x)z \rangle = f(z)\langle z, x \rangle - f(x)\|z\|^2.$$
Hence $f(x) = \langle y, x \rangle$ with $y = \overline{f(z)}\,z/\|z\|^2$, since $\langle y, x \rangle = f(z)\langle z, x \rangle/\|z\|^2$. The norm equality is the norm of $R(y)$. $\square$

::: mathlib
`InnerProductSpace.toDual` · `Mathlib.Analysis.InnerProductSpace.Dual`

`toDual 𝕜 E : E ≃ₗᵢ⋆[𝕜] StrongDual 𝕜 E` for a complete `E`. It is `LinearIsometryEquiv.ofSurjective (toDualMap 𝕜 E)`, and the proof of surjectivity is the proof of the text: a nonzero `z` in `(ker ℓ).orthogonal` and the vector `(conj (ℓ z) / ⟪z, z⟫) • z`. The two directions are `toDual_apply_apply : toDual 𝕜 E x y = ⟪x, y⟫_𝕜` and `toDual_symm_apply : ⟪(toDual 𝕜 E).symm y, x⟫_𝕜 = y x`.

<?decl InnerProductSpace.toDual?>
:::

**Corollary (sesquilinear forms).** Let $E$ be a Hilbert space and $B : E \times E \to \mathbb{K}$ conjugate linear in the first argument, linear in the second, with $|B(v, w)| \le M\|v\|\,\|w\|$. There is a unique bounded operator $A$ with $B(v, w) = \langle Av, w \rangle$, and $\|A\| \le M$.

*Proof.* For fixed $v$, $w \mapsto B(v, w)$ is in $E^*$ with norm at most $M\|v\|$. Let $Av$ be the vector that represents it. Uniqueness in the theorem gives linearity: $A(av + bv')$ and $aAv + bAv'$ both represent $\bar{a}B(v, \cdot) + \bar{b}B(v', \cdot)$, because $\langle aAv, w \rangle = \bar{a}\langle Av, w \rangle$. Also $\|Av\| = \|B(v, \cdot)\| \le M\|v\|$. $\square$

In Mathlib this is `InnerProductSpace.continuousLinearMapOfBilin B : E →L[𝕜] E` for `B : E →L⋆[𝕜] E →L[𝕜] 𝕜`, with `continuousLinearMapOfBilin_apply : ⟪continuousLinearMapOfBilin B v, w⟫_𝕜 = B v w`.

**Theorem (Lax-Milgram).** Let $E$ be a real Hilbert space and $B$ a bounded coercive bilinear form on $E$. For each $f \in E^*$ there is a unique $u \in E$ with $B(u, w) = f(w)$ for each $w$, and $\|u\| \le \|f\|/C$.

*Proof.* Let $A$ be the operator of the corollary, with $B(v, w) = \langle Av, w \rangle$. Coercivity and Cauchy-Schwarz give $C\|v\|^2 \le B(v, v) = \langle Av, v \rangle \le \|Av\|\,\|v\|$, so $\|Av\| \ge C\|v\|$. Then $A$ is injective, and its range is closed: if $Av_n \to y$, then $(v_n)$ is Cauchy, $v_n \to v$ and $Av = y$. If $z \perp \operatorname{range} A$, then $0 = \langle Az, z \rangle \ge C\|z\|^2$, so $z = 0$, and the range is dense by Section 1. So $A$ is a bijection with $\|A^{-1}y\| \le \|y\|/C$. Given $f$, let $y$ represent it and $u = A^{-1}y$. Then $B(u, w) = \langle y, w \rangle = f(w)$, and $\|u\| \le \|y\|/C = \|f\|/C$. If $u'$ is a second solution, $B(u - u', \cdot) = 0$, and $C\|u - u'\|^2 \le B(u - u', u - u') = 0$. $\square$

::: mathlib
`IsCoercive.continuousLinearEquivOfBilin` · `Mathlib.Analysis.InnerProductSpace.LaxMilgram`

`hB.continuousLinearEquivOfBilin : V ≃L[ℝ] V` for a coercive `B` on a real Hilbert space `V`. It is the operator $A$ of the proof as an isomorphism, with `continuousLinearEquivOfBilin_apply : ⟪hB.continuousLinearEquivOfBilin v, w⟫_ℝ = B v w` and uniqueness `unique_continuousLinearEquivOfBilin`. The steps of the proof are `IsCoercive.bounded_below`, `IsCoercive.ker_eq_bot`, `IsCoercive.isClosed_range` and `IsCoercive.range_eq_top`. The solution $u$ of the theorem is `hB.continuousLinearEquivOfBilin.symm ((toDual ℝ V).symm f)`.

<?decl IsCoercive.continuousLinearEquivOfBilin?>
:::

### Examples

**Example (Euclidean space).** On $\mathbb{R}^n$ each linear functional is $f(x) = \sum_k a_kx_k = \langle a, x \rangle$ with $a_k = f(e_k)$, and $\|f\| = \|a\|_2$ by Cauchy-Schwarz with equality at $x = a$. On $\mathbb{C}^n$, $f(x) = \sum_k a_kx_k = \langle \bar{a}, x \rangle$, and the conjugation shows up in the representing vector.

**Example (the functional $\sum x_n/n$ on $\ell^2$).** On $\ell^2$, $f(x) = \sum_n x_n/n$ is bounded, and it is represented by $y = (1/n)_n \in \ell^2$. So $\|f\| = \|y\|_2 = (\sum_n 1/n^2)^{1/2} = \pi/\sqrt6$.

**Counterexample (no representing vector without completeness).** On $c_{00}$ with the $\ell^2$ inner product, the same $f(x) = \sum_n x_n/n$ is bounded. If $f(x) = \langle y, x \rangle$ with $y \in c_{00}$, then $y_n = f(\delta_n) = 1/n$ for each $n$, which is not finitely supported. So the Riesz map of $c_{00}$ is not onto, and `toDual` needs `CompleteSpace E`.

### The library around it

The theorem identifies the dual of a Hilbert space with the space itself, so results on $E^*$ transfer to $E$. Section 3 uses it to define the adjoint. The duality of finite dimensional spaces needs no completeness, and `OrthonormalBasis.norm_dual` computes the norm of a functional from its values on an orthonormal basis.

Common errors:

- `toDual` is conjugate linear, `E ≃ₗᵢ⋆[𝕜] StrongDual 𝕜 E`, not a `LinearIsometryEquiv`. Over `ℝ` the star is the identity, but the type still carries it.
- The representing vector is `(toDual 𝕜 E).symm f`, and the lemma `toDual_symm_apply` puts it in the first, conjugate linear, argument.
- Lax-Milgram in Mathlib is real. A complex form needs its own argument.

### Exercises

1. (A) Find the vector that represents $f(x) = x_1 - 2x_2 + 3x_3$ on $\mathbb{R}^3$ and compute $\|f\|$.
2. (A) Find the vector of $\ell^2$ that represents $f(x) = x_1 + x_2/2 + x_3/4 + \dots$.
3. (A) Show that the Riesz map satisfies $R(cy) = \bar{c}R(y)$.
4. (B) Let $E$ be a Hilbert space. Show that each $f \in E^*$ attains its norm on the closed unit ball.
5. (B) Show that a Hilbert space is reflexive: the canonical map $E \to E^{**}$ of Chapter 5 is onto.
6. (C) Let $B(u, w) = \int_0^1 (u'w' + uw)$ on the space $H$ of the completion of $C^1[0, 1]$ for the norm $B(u, u)^{1/2}$. Show that for each $g \in C[0, 1]$ there is a unique $u \in H$ with $B(u, w) = \int_0^1 gw$ for each $w$.

### Notes and history

Frigyes Riesz and Maurice Fréchet proved the representation theorem for $L^2$ independently in 1907. Peter Lax and Arthur Milgram published their theorem in 1954. The file `Mathlib.Analysis.InnerProductSpace.Dual` has the author Frédéric Dupuis, and the file `Mathlib.Analysis.InnerProductSpace.LaxMilgram` has the author Daniel Roca González.

### Reference

<?reference?>
