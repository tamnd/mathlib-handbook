---
title: Orientations, area forms and the norm determinant
kind: api
modules:
  - Mathlib.Analysis.InnerProductSpace.Orientation
  - Mathlib.Analysis.InnerProductSpace.TwoDim
  - Mathlib.Analysis.InnerProductSpace.NormDet
  - Mathlib.Analysis.InnerProductSpace.Affine
explains:
  E2: [Orientation.volumeForm, Orientation.abs_volumeForm_apply_le, OrthonormalBasis.adjustToOrientation, Orientation.areaForm, Orientation.rightAngleRotation, Orientation.kahler_apply_apply, Orientation.inner_sq_add_areaForm_sq, LinearMap.normDet, LinearMap.normDet_sq, dist_sq_of_inner_eq_zero]
  E1: auto
families: []
requires: [V07, V08, V13, V16.C01, V16.C02, V16.C03]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Orientations, area forms and the norm determinant

### Overview

A finite dimensional real vector space has two orientations, and Volume 7 defines them with bases and determinants. An inner product picks out more structure: among the alternating $n$-forms that are positive on an orientation, exactly one has the value $1$ on each positive orthonormal basis. This form is the volume form. This section collects the modules that use it.

The first module defines the volume form of an oriented inner product space of dimension $n$. The second module specializes to dimension $2$, where the volume form is an area form $\omega$ and the orientation gives a rotation $J$ by a right angle. The two together turn an oriented Euclidean plane into a copy of $\mathbb{C}$. The third module measures how a linear map between spaces of different dimensions changes volume, with the norm determinant $\sqrt{\det(f^* f)}$. The last, small module states the theorem of Pythagoras for points of a Euclidean affine space.

### The library around it

#### Orthonormal bases and orientations

Let $E$ be a real inner product space of finite dimension, and let $\iota$ be a finite index type. An orientation `o : Orientation ℝ E ι` is a ray of nonzero alternating forms, and each basis $b$ has an orientation, `Module.Basis.orientation`. The module `Mathlib.Analysis.InnerProductSpace.Orientation` first compares orthonormal bases.

| Lean name | Statement |
|---|---|
| `OrthonormalBasis.det_to_matrix_orthonormalBasis_of_same_orientation` | for two orthonormal bases with the same orientation, $\det_e(f) = 1$ |
| `OrthonormalBasis.det_to_matrix_orthonormalBasis_of_opposite_orientation` | for opposite orientations, $\det_e(f) = -1$ |
| `OrthonormalBasis.same_orientation_iff_det_eq_det` | $\det_e = \det_f$ as forms if and only if $e$ and $f$ have the same orientation |
| `OrthonormalBasis.det_eq_neg_det_of_opposite_orientation` | $\det_e = -\det_f$ for opposite orientations |

The proof of the first two lines is short. The change of basis matrix between two orthonormal bases is orthogonal, so its determinant is $\pm 1$. Two bases have the same orientation exactly when this determinant is positive.

The definition `OrthonormalBasis.adjustToOrientation e x` changes an orthonormal basis $e$ so that it has the orientation $x$. If $e$ already has orientation $x$, it does nothing. If not, it replaces one vector $e_i$ by $-e_i$. The lemmas `OrthonormalBasis.orientation_adjustToOrientation` and `OrthonormalBasis.adjustToOrientation_apply_eq_or_eq_neg` record these two facts. With it, `Orientation.finOrthonormalBasis` gives a positive orthonormal basis indexed by `Fin n` for each orientation, and `Orientation.finOrthonormalBasis_orientation` checks its orientation.

#### The volume form

Fix $n$ with the instance `Fact (Module.finrank ℝ E = n)`. The volume form `o.volumeForm : E [⋀^Fin n]→ₗ[ℝ] ℝ` of an orientation $o$ is the determinant $\det_b$ for one positive orthonormal basis $b$. The value does not depend on the choice of $b$, by the table above. So for every orthonormal basis $b$, the volume form is $\det_b$ when $b$ is positive and $-\det_b$ when it is negative. The library states the two cases as two lemmas, and a third lemma gives $|\omega(v)| = |\det_b(v)|$ for every orthonormal basis $b$.

| Lean name | Statement |
|---|---|
| `Orientation.volumeForm_neg_orientation` | $\omega_{-o} = -\omega_o$ |
| `Orientation.abs_volumeForm_apply_of_orthonormal` | $|\omega(v)| = 1$ for an orthonormal basis $v$ |
| `Orientation.abs_volumeForm_apply_of_pairwise_orthogonal` | $|\omega(v)| = \prod_i \lVert v_i \rVert$ for pairwise orthogonal $v_i$ |
| `Orientation.abs_volumeForm_apply_le` | $|\omega(v)| \le \prod_i \lVert v_i \rVert$ |
| `Orientation.volumeForm_apply_le` | $\omega(v) \le \prod_i \lVert v_i \rVert$ |
| `Orientation.volumeForm_map` | a linear isometric equivalence $\varphi$ moves the volume form: $\omega_{\varphi o}(x) = \omega_o(\varphi^{-1} x)$ |
| `Orientation.volumeForm_comp_linearIsometryEquiv` | an isometry with positive determinant keeps the volume form |

The bound `Orientation.abs_volumeForm_apply_le` is the inequality of Hadamard. Here is the proof. If the $v_i$ are linearly dependent, then $\omega(v) = 0$. If not, apply the Gram-Schmidt process: $w_1 = v_1$, and $w_k$ is $v_k$ minus its projection on the span of $v_1, \dots, v_{k-1}$. The form $\omega$ is alternating, so adding to $v_k$ a combination of the other vectors does not change $\omega(v)$. Thus $\omega(v) = \omega(w)$. The $w_k$ are pairwise orthogonal, so $|\omega(w)| = \prod_k \lVert w_k \rVert$, and $\lVert w_k \rVert \le \lVert v_k \rVert$ because $w_k$ is an orthogonal projection of $v_k$.

In dimension $0$, the volume form is the constant $\pm 1$, by `Orientation.volumeForm_zero_pos` and `Orientation.volumeForm_zero_neg`.

#### The oriented plane

The module `Mathlib.Analysis.InnerProductSpace.TwoDim` works in an oriented real inner product space $E$ of dimension $2$, with the instance `Fact (Module.finrank ℝ E = 2)`. It defines three objects.

1. The area form `o.areaForm : E →ₗ[ℝ] E →ₗ[ℝ] ℝ`, written $\omega$. It is the volume form as a bilinear map, `Orientation.areaForm_to_volumeForm`. The number $\omega(x, y)$ is the signed area of the parallelogram on $x$ and $y$. The form is antisymmetric (`Orientation.areaForm_swap`) and $\omega(x, x) = 0$ (`Orientation.areaForm_apply_self`). The bundled continuous form is `Orientation.areaForm'`.
2. The rotation `o.rightAngleRotation : E ≃ₗᵢ[ℝ] E`, written $J$. It is defined by $\langle J x, y \rangle = \omega(x, y)$, the lemma `Orientation.inner_rightAngleRotation_left`. It is an isometry with $J^2 = -1$ (`Orientation.rightAngleRotation_rightAngleRotation`), and $J x \perp x$ (`Orientation.inner_rightAngleRotation_self`). For $x \ne 0$, the pair $(x, J x)$ is a basis, `Orientation.basisRightAngleRotation`.
3. The Kähler form `o.kahler : E →ₗ[ℝ] E →ₗ[ℝ] ℂ`. It joins the inner product and the area form into one complex number: `Orientation.kahler_apply_apply` says
$$\kappa(x, y) = \langle x, y \rangle + \omega(x, y)\, i.$$

The main identity is `Orientation.inner_sq_add_areaForm_sq`:
$$\langle a, b \rangle^2 + \omega(a, b)^2 = \lVert a \rVert^2 \lVert b \rVert^2.$$
For the proof, take $a \ne 0$ and the orthogonal basis $(a, J a)$. Write $b = s a + t J a$. Then $\langle a, b \rangle = s \lVert a \rVert^2$ and $\omega(a, b) = \langle J a, b \rangle = t \lVert a \rVert^2$, so the left side is $(s^2 + t^2) \lVert a \rVert^4 = \lVert b \rVert^2 \lVert a \rVert^2$. In terms of $\kappa$, the identity says $\lvert \kappa(a, b) \rvert = \lVert a \rVert \lVert b \rVert$, the lemma `Orientation.norm_kahler`. So $\kappa(a, b) = 0$ only when $a = 0$ or $b = 0$, `Orientation.kahler_eq_zero_iff`. Other consequences are `Orientation.abs_areaForm_le`, the bound $|\omega(x, y)| \le \lVert x \rVert \lVert y \rVert$, and `Orientation.nonneg_inner_and_areaForm_eq_zero_iff_sameRay`, which says that $x$ and $y$ point in the same direction exactly when $\langle x, y \rangle \ge 0$ and $\omega(x, y) = 0$.

On $\mathbb{C}$ with its standard orientation `Complex.orientation`, the three objects are explicit: `Complex.areaForm` gives $\omega(w, z) = \mathrm{Im}(\bar w z)$, `Complex.rightAngleRotation` gives $J z = i z$, and `Complex.kahler` gives $\kappa(w, z) = \bar w z$. Each oriented plane is isometric to $\mathbb{C}$ with this orientation, and the lemmas `Orientation.areaForm_map_complex`, `Orientation.rightAngleRotation_map_complex` and `Orientation.kahler_map_complex` move the formulas along such an isometry. The lemmas whose names end in comp_rightAngleRotation and comp_linearIsometryEquiv say that $J$ and all isometries with positive determinant keep $\omega$, $J$ and $\kappa$. Volume 22 uses these objects for oriented angles in the plane.

#### The norm determinant

Let $f : U \to V$ be a linear map between inner product spaces over $\mathbb{K}$, with $U$ finite dimensional. The space $V$ can be of infinite dimension. The module `Mathlib.Analysis.InnerProductSpace.NormDet` defines the number `LinearMap.normDet f`, the factor by which $f$ multiplies $m$-dimensional volume, where $m = \dim U$. The definition takes an orthonormal basis of $U$ and an orthonormal basis of the range of $f$, and takes the absolute value of the determinant of the matrix of $f$ in these bases. If the range has dimension less than $m$, the value is $0$.

| Lean name | Statement |
|---|---|
| `LinearMap.normDet_sq` | $\mathrm{normDet}(f)^2 = \det(f^* f)$ |
| `LinearMap.normDet_sq_eq_det_gram` | $\mathrm{normDet}(f)^2 = \det G(f b_1, \dots, f b_m)$ for an orthonormal basis $b$ of $U$ |
| `LinearMap.normDet_eq_norm_det` | for $U = V$, $\mathrm{normDet}(f) = \lvert \det f \rvert$ |
| `LinearMap.normDet_eq_zero_iff_ker_ne_bot` | $\mathrm{normDet}(f) = 0$ if and only if $f$ is not injective |
| `LinearMap.normDet_comp_of_finrank_eq` | $\mathrm{normDet}(g f) = \mathrm{normDet}(g)\, \mathrm{normDet}(f)$ when $\dim U = \dim V$ |
| `LinearMap.normDet_smul` | $\mathrm{normDet}(c f) = \lvert c \rvert^m \mathrm{normDet}(f)$ |
| `LinearIsometry.normDet_eq_one` | an isometry has norm determinant $1$ |
| `LinearMap.normDet_eq_prod_singularValues` | $\mathrm{normDet}(f)$ is the product of the first $m$ singular values of $f$ |

The proof of `LinearMap.normDet_sq` is a short computation. Let $A$ be the matrix of $f$ from an orthonormal basis of $U$ to an orthonormal basis of the range. Then $A$ is square, the matrix of $f^* f$ is $A^* A$, and $\det(A^* A) = \lvert \det A \rvert^2$. The Gram form follows, because the entries of $A^* A$ are the inner products $\langle f b_i, f b_j \rangle$. The singular values come from Chapter 7.

The volume meaning is a theorem on Hausdorff measure. For a real linear map $f : U \to V$ and a set $s \subseteq U$, `LinearMap.euclideanHausdorffMeasure_image_eq_normDet_mul_volume` says that the $m$-dimensional Hausdorff measure of $f(s)$ is $\mathrm{normDet}(f)$ times the volume of $s$. The Hausdorff measure is the subject of Volume 18.

#### Pythagoras in affine spaces

The module `Mathlib.Analysis.InnerProductSpace.Affine` has nine lemmas for a metric affine space $P$ over a real inner product space $V$. The lemma `dist_sq_of_inner_eq_zero` is the theorem of Pythagoras for points: if $\langle p - a, b - a \rangle = 0$, then $d(p, b)^2 = d(p, a)^2 + d(a, b)^2$. The proof expands $\lVert (p - a) - (b - a) \rVert^2$. The lemmas `dist_sq_lineMap_of_inner_eq_zero` and `dist_sq_lineMap_lineMap_of_inner_eq_zero` give the same formula for points of a line through $a$, and the lemmas such as `inner_vsub_vsub_left_eq_dist_sq_left_iff` turn an equation for an inner product into a condition of orthogonality.

#### Common errors

1. The volume form needs the instance `Fact (Module.finrank ℝ E = n)` and an orientation indexed by `Fin n`. An orientation indexed by another type of size $n$ does not give a volume form directly.
2. The rotation $J$ depends on the orientation. For the opposite orientation, $J$ changes sign: `Orientation.rightAngleRotation_neg_orientation`. A lemma that holds for $o$ can fail for $-o$.
3. `LinearMap.normDet` is never negative, even for $U = V$. For an endomorphism of a real space, it is $\lvert \det f \rvert$ (`LinearMap.normDet_eq_abs_det`), not $\det f$.

### Exercises

1. (A) Prove that $\omega(x, J x) = \lVert x \rVert^2$ from `Orientation.inner_rightAngleRotation_left`.
2. (A) Compute `Complex.orientation.areaForm 1 Complex.I` with `Complex.areaForm`.
3. (B) Prove that $J$ commutes with every isometry of $E$ with positive determinant, and anticommutes with each reflection.
4. (B) Let $f : \mathbb{R} \to \mathbb{R}^2$ be $t \mapsto (t, t)$. Compute $\mathrm{normDet}(f)$ with `LinearMap.normDet_sq_eq_det_gram`, and interpret it as a length factor.
5. (B) Prove the equality case of the inequality of Hadamard: for linearly independent $v_i$, $|\omega(v)| = \prod_i \lVert v_i \rVert$ if and only if the $v_i$ are pairwise orthogonal.
6. (C) Prove that $\mathrm{normDet}(g f) \le \lVert g \rVert^m \mathrm{normDet}(f)$ for $f : U \to V$ and $g : V \to W$, with $m = \dim U$.

### Reference

<?reference?>
