---
title: Adjoints and the spectral theorem in finite dimension
kind: theory
modules:
  - Mathlib.Analysis.InnerProductSpace.Adjoint
  - Mathlib.Analysis.InnerProductSpace.Symmetric
  - Mathlib.Analysis.InnerProductSpace.Spectrum
  - Mathlib.Analysis.InnerProductSpace.Rayleigh
explains:
  E3: [ContinuousLinearMap.adjoint, ContinuousLinearMap.norm_adjoint_comp_self, LinearMap.IsSymmetric, LinearMap.IsSymmetric.eigenvectorBasis]
  E2: [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_left, ContinuousLinearMap.isSelfAdjoint_iff', ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric, LinearMap.adjoint, LinearMap.isSymmetric_iff_isSelfAdjoint, LinearMap.IsSymmetric.conj_eigenvalue_eq_self, LinearMap.IsSymmetric.orthogonalFamily_eigenspaces, LinearMap.IsSymmetric.direct_sum_isInternal, LinearMap.IsSymmetric.eigenvalues, LinearMap.IsSymmetric.apply_eigenvectorBasis, LinearMap.IsSymmetric.hasEigenvalue_iSup_of_finiteDimensional]
  E1: auto
families: []
requires: [V07, V13, V16.C01, V16.C02, V16.C03, V16.C06]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Adjoints and the spectral theorem in finite dimension

### Overview

The Riesz theorem of Section 2 turns each bounded operator $A : E \to F$ between Hilbert spaces into a second operator $A^* : F \to E$, the adjoint, with $\langle A^*y, x \rangle = \langle y, Ax \rangle$. The map $A \mapsto A^*$ is a conjugate linear isometry, and it satisfies the identity $\|A^*A\| = \|A\|^2$, which makes the bounded operators on a Hilbert space a C*-algebra. An operator with $A^* = A$ is self-adjoint, or symmetric. In finite dimension a symmetric operator has an orthonormal basis of eigenvectors with real eigenvalues. This is the spectral theorem, the end point of this volume.

### Definitions

**Definition (adjoint).** Let $E$ and $F$ be Hilbert spaces and $A : E \to F$ a bounded operator. The *adjoint* $A^* : F \to E$ is the operator with $\langle A^*y, x \rangle = \langle y, Ax \rangle$ for each $x \in E$ and $y \in F$.

The definition is correct by Section 2: the form $B(y, x) = \langle y, Ax \rangle$ is conjugate linear in $y$, linear in $x$ and bounded by $\|A\|\,\|y\|\,\|x\|$, so the corollary on sesquilinear forms gives a unique bounded $A^*$ with $\|A^*\| \le \|A\|$.

::: mathlib
`ContinuousLinearMap.adjoint` · `Mathlib.Analysis.InnerProductSpace.Adjoint`

`adjoint : (E →L[𝕜] F) ≃ₗᵢ⋆[𝕜] (F →L[𝕜] E)` for complete `E` and `F`, with the notation `A†` in the scope `InnerProductSpace`. It is built from `(toDual 𝕜 E).symm`. The defining equations are `adjoint_inner_left : ⟪adjoint A y, x⟫_𝕜 = ⟪y, A x⟫_𝕜` and `adjoint_inner_right : ⟪x, adjoint A y⟫_𝕜 = ⟪A x, y⟫_𝕜`. Since the map is a `LinearIsometryEquiv`, the equality $\|A^*\| = \|A\|$ is part of its type. For finite dimensional spaces, `LinearMap.adjoint` does the same for linear maps without a continuity condition.

<?decl ContinuousLinearMap.adjoint?>
:::

**Definition (symmetric operator).** A linear map $T : E \to E$ on an inner product space is *symmetric* if $\langle Tx, y \rangle = \langle x, Ty \rangle$ for each $x, y$. A bounded operator on a Hilbert space is *self-adjoint* if $T^* = T$.

::: mathlib
`LinearMap.IsSymmetric` · `Mathlib.Analysis.InnerProductSpace.Symmetric`

`T.IsSymmetric` for `T : E →ₗ[𝕜] E` is `∀ x y, ⟪T x, y⟫_𝕜 = ⟪x, T y⟫_𝕜`. It needs no completeness and no continuity. The general predicate `IsSelfAdjoint A`, for an element of a star monoid, is `star A = A`. For operators the two notions agree: `ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric` on a Hilbert space and `LinearMap.isSymmetric_iff_isSelfAdjoint` in finite dimension. Also `ContinuousLinearMap.isSelfAdjoint_iff'` says that `IsSelfAdjoint A ↔ adjoint A = A`.

<?decl LinearMap.IsSymmetric?>
:::

### Theorems and proofs

**Theorem (properties of the adjoint).** For bounded $A, A' : E \to F$, $B : F \to G$ and scalars $c$: $(A + A')^* = A^* + A'^*$, $(cA)^* = \bar{c}A^*$, $(BA)^* = A^*B^*$, $A^{**} = A$ and $\|A^*\| = \|A\|$.

*Proof.* Each equality follows from uniqueness in the definition. For example $\langle A^*B^*z, x \rangle = \langle B^*z, Ax \rangle = \langle z, BAx \rangle$, so $A^*B^* = (BA)^*$. Also $\langle Ay, x \rangle = \overline{\langle x, Ay \rangle} = \overline{\langle A^*x, y \rangle} = \langle y, A^*x \rangle$, so $A = A^{**}$. Then $\|A^*\| \le \|A\|$ and $\|A\| = \|A^{**}\| \le \|A^*\|$. $\square$

In Mathlib these are `map_add`, `map_smulₛₗ`, `ContinuousLinearMap.adjoint_comp` and `ContinuousLinearMap.adjoint_adjoint`.

**Theorem (C*-identity).** For a bounded operator $A : E \to F$ between Hilbert spaces, $\|A^*A\| = \|A\|^2$.

*Proof.* Chapter 2 and the previous theorem give $\|A^*A\| \le \|A^*\|\,\|A\| = \|A\|^2$. For the other direction, for each $x$,
$$\|Ax\|^2 = \langle Ax, Ax \rangle = \langle A^*Ax, x \rangle \le \|A^*Ax\|\,\|x\| \le \|A^*A\|\,\|x\|^2.$$
So $\|Ax\| \le \|A^*A\|^{1/2}\|x\|$ and $\|A\| \le \|A^*A\|^{1/2}$. $\square$

::: mathlib
`ContinuousLinearMap.norm_adjoint_comp_self` · `Mathlib.Analysis.InnerProductSpace.Adjoint`

`norm_adjoint_comp_self A : ‖adjoint A ∘L A‖ = ‖A‖ * ‖A‖`. The proof in Mathlib is the proof of the text, with `apply_norm_sq_eq_inner_adjoint_left : ‖A x‖ ^ 2 = re ⟪(adjoint A ∘L A) x, x⟫_𝕜` as the central equality. The file uses it for the instance `CStarRing (E →L[𝕜] E)`.

<?decl ContinuousLinearMap.norm_adjoint_comp_self?>
:::

**Lemma (eigenvalues of a symmetric map).** Let $T$ be symmetric. Each eigenvalue of $T$ is real, and eigenvectors for different eigenvalues are orthogonal.

*Proof.* If $Tx = \mu x$ with $x \ne 0$, then $\mu\|x\|^2 = \langle x, Tx \rangle = \langle Tx, x \rangle = \bar\mu\|x\|^2$, so $\mu = \bar\mu$. If also $Ty = \nu y$ with $\nu \ne \mu$, then $\mu\langle x, y \rangle = \langle Tx, y \rangle = \langle x, Ty \rangle = \nu\langle x, y \rangle$, since $\mu$ is real. So $\langle x, y \rangle = 0$. $\square$

These are `LinearMap.IsSymmetric.conj_eigenvalue_eq_self` and `LinearMap.IsSymmetric.orthogonalFamily_eigenspaces`.

**Theorem (spectral theorem in finite dimension).** Let $E$ be an inner product space of finite dimension $n$ over $\mathbb{R}$ or $\mathbb{C}$ and $T : E \to E$ symmetric. There is an orthonormal basis $v_1, \dots, v_n$ of $E$ and real numbers $\lambda_1, \dots, \lambda_n$ with $Tv_i = \lambda_iv_i$.

*Proof.* Induction on $n$, with nothing to prove for $n = 0$. Let $n \ge 1$. First $T$ has a unit eigenvector. The function $q(x) = \operatorname{Re}\langle Tx, x \rangle$ is continuous, and the unit sphere $S$ of $E$ is compact by Chapter 3, so $q$ has a maximum $\lambda$ at some $x_0 \in S$. Then $q(x) \le \lambda\|x\|^2$ for each $x$. Let $y \perp x_0$ and $t \in \mathbb{R}$. Symmetry gives $q(x_0 + ty) = \lambda + 2t\operatorname{Re}\langle Tx_0, y \rangle + t^2q(y)$ and $\|x_0 + ty\|^2 = 1 + t^2\|y\|^2$. So
$$2t\operatorname{Re}\langle Tx_0, y \rangle + t^2\bigl(q(y) - \lambda\|y\|^2\bigr) \le 0$$
for each real $t$. Divide by $t$ and let $t \to 0$ from both sides: $\operatorname{Re}\langle Tx_0, y \rangle = 0$. Over $\mathbb{C}$, replace $y$ by $iy$, which gives $\operatorname{Im}\langle Tx_0, y \rangle = 0$. So $Tx_0$ is orthogonal to $x_0^\perp$, and $Tx_0 \in (x_0^\perp)^\perp = \mathbb{K}x_0$ by Section 1. So $x_0$ is an eigenvector, and its eigenvalue is real by the lemma.

Now let $W = x_0^\perp$, of dimension $n - 1$. If $w \in W$, then $\langle Tw, x_0 \rangle = \langle w, Tx_0 \rangle = \mu\langle w, x_0 \rangle = 0$, so $T$ maps $W$ into $W$. The restriction of $T$ to $W$ is symmetric. By induction, $W$ has an orthonormal basis of eigenvectors with real eigenvalues. Add $x_0$ to get the basis of $E$. $\square$

::: mathlib
`LinearMap.IsSymmetric.eigenvectorBasis` · `Mathlib.Analysis.InnerProductSpace.Spectrum`

`hT.eigenvectorBasis hn : OrthonormalBasis (Fin n) 𝕜 E` for `hT : T.IsSymmetric` and `hn : finrank 𝕜 E = n`. The eigenvalues are `hT.eigenvalues hn : Fin n → ℝ`, and `apply_eigenvectorBasis` gives `T (v i) = (eigenvalues i : 𝕜) • v i`. Mathlib does not use induction. It proves `LinearMap.IsSymmetric.direct_sum_isInternal`: $E$ is the internal direct sum of the eigenspaces. Then it puts an orthonormal basis in each eigenspace. The existence of an eigenvalue comes from `LinearMap.IsSymmetric.hasEigenvalue_iSup_of_finiteDimensional` in the file on the Rayleigh quotient, which is the maximum argument of the text.

<?decl LinearMap.IsSymmetric.eigenvectorBasis?>
:::

### Examples

**Example (a $2 \times 2$ symmetric matrix).** On $\mathbb{R}^2$ let $T(x, y) = (2x + y, x + 2y)$. Then $T$ is symmetric, since its matrix is symmetric. The vectors $v_1 = (1, 1)/\sqrt2$ and $v_2 = (1, -1)/\sqrt2$ are orthonormal with $Tv_1 = 3v_1$ and $Tv_2 = v_2$. The maximum of $\langle Tx, x \rangle = 2x^2 + 2xy + 2y^2$ on the unit circle is $3$, at $v_1$, as in the proof.

**Example (adjoint of a matrix).** For $A : \mathbb{C}^n \to \mathbb{C}^m$ with matrix $(a_{ij})$, the adjoint has the conjugate transpose matrix $(\bar a_{ji})$, since $\langle y, Ax \rangle = \sum_{i,j} \bar y_ia_{ij}x_j = \langle (\bar a_{ji})y, x \rangle$.

**Example (the shift on $\ell^2$).** The right shift $S(x_1, x_2, \dots) = (0, x_1, x_2, \dots)$ has the adjoint $S^*(x_1, x_2, \dots) = (x_2, x_3, \dots)$, the left shift. Here $S^*S = 1$ but $SS^* \ne 1$. So $\|S^*S\| = 1 = \|S\|^2$.

**Counterexample (no spectral theorem without symmetry).** On $\mathbb{R}^2$ the rotation $T(x, y) = (-y, x)$ has no real eigenvalue. The map $T(x, y) = (y, 0)$ on $\mathbb{C}^2$ has only the eigenvalue $0$ and only one line of eigenvectors, so it has no basis of eigenvectors.

**Counterexample (no eigenvector in infinite dimension).** On $L^2[0, 1]$ the operator $(Tf)(t) = tf(t)$ is bounded and self-adjoint. If $tf(t) = \mu f(t)$ almost everywhere, then $f = 0$ almost everywhere outside the null set $\{\mu\}$. So $T$ has no eigenvector, and the finite dimensional theorem does not extend in this form.

### The library around it

The adjoint makes `E →L[𝕜] E` a star algebra, and with the C*-identity a `CStarRing`. Over $\mathbb{C}$ it is a C*-algebra, and the general theory of C*-algebras and the continuous functional calculus applies to it. For compact self-adjoint operators, the same file on the spectral theorem has `orthogonalComplement_iSup_eigenspaces_eq_bot`: the eigenspaces span a dense subspace. The index of this edition has no declaration for the spectral theorem of a general bounded self-adjoint operator as a multiplication operator.

Common errors:

- `adjoint` needs `CompleteSpace` on both spaces. For finite dimensional spaces, use `LinearMap.adjoint`.
- `eigenvectorBasis` needs the proof `hn` of the dimension, so its index type is `Fin n` with `n` fixed by you.
- `eigenvalues` takes real values. The cast to `𝕜` shows up in `apply_eigenvectorBasis`.

### Exercises

1. (A) Find the eigenvalues and an orthonormal basis of eigenvectors of $T(x, y) = (x + 2y, 2x + y)$ on $\mathbb{R}^2$.
2. (A) Show that the orthogonal projection $P$ of Section 1 is self-adjoint and that $P^2 = P$.
3. (A) Show that $\ker A^* = (\operatorname{range} A)^\perp$ for a bounded operator $A$ between Hilbert spaces.
4. (B) Show that a symmetric map $T$ with $\langle Tx, x \rangle = 0$ for each $x$ is $0$.
5. (B) Show that $\|T\| = \sup_{\|x\| = 1} |\langle Tx, x \rangle|$ for a symmetric $T$ in finite dimension, with the spectral theorem.
6. (B) Show that if $A$ is an isometry between Hilbert spaces, then $A^*A = 1$.
7. (C) Two symmetric maps $S, T$ on a finite dimensional space with $ST = TS$ have an orthonormal basis of common eigenvectors. Prove this.

### Notes and history

The spectral theorem for symmetric matrices goes back to the work of Cauchy on quadratic forms. The file `Mathlib.Analysis.InnerProductSpace.Adjoint` has the authors Frédéric Dupuis and Heather Macbeth, the file `Mathlib.Analysis.InnerProductSpace.Symmetric` has the authors Moritz Doll, Frédéric Dupuis and Heather Macbeth, the file `Mathlib.Analysis.InnerProductSpace.Spectrum` has the author Heather Macbeth, and the file `Mathlib.Analysis.InnerProductSpace.Rayleigh` has the authors Heather Macbeth and Frédéric Dupuis.

### Reference

<?reference?>
