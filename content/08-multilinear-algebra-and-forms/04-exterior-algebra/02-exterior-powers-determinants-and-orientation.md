---
title: Exterior powers, determinants and orientation
kind: theory
modules:
  - Mathlib.LinearAlgebra.ExteriorPower.Basic
  - Mathlib.LinearAlgebra.ExteriorPower.Basis
  - Mathlib.LinearAlgebra.ExteriorPower.Pairing
  - Mathlib.LinearAlgebra.ExteriorPower.WedgePairing
  - Mathlib.LinearAlgebra.ExteriorPower.HodgeStar
  - Mathlib.LinearAlgebra.ExteriorPower.Orientation
  - Mathlib.LinearAlgebra.Orientation
  - Mathlib.LinearAlgebra.CrossProduct
  - Mathlib.LinearAlgebra.ExteriorPower.BaseChange
  - Mathlib.LinearAlgebra.ExteriorPower.BilinForm
explains:
  E3: [exteriorPower.alternatingMapLinearEquiv, Module.Basis.exteriorPower, exteriorPower.map, Orientation]
  E2: [exteriorPower.ιMulti, exteriorPower.ιMulti_span, exteriorPower.map_comp, Module.Basis.orientation, Module.Basis.orientation_eq_iff_det_pos, Orientation.map_eq_iff_det_pos, crossProduct, triple_product_eq_det]
  E1: auto
families: []
requires: [V08.C01, V07.C04, V05.C07]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Exterior powers, determinants and orientation

### Overview

This section studies the graded pieces $\Lambda^k(M)$ of the exterior algebra of Section 1 of this chapter as modules. Each is the universal target of alternating $k$-linear maps. For a free module of rank $n$, the top power $\Lambda^n(M)$ is free of rank $1$, and a linear map $f : M \to M$ acts on it as multiplication by the scalar $\det f$. Over an ordered field the sign of $\det f$ gives the notion of an orientation.

The section uses the determinant of Volume 7, Chapter 4. The ring $R$ is commutative.

### Definitions

**Definition (Exterior power as a module).** The $k$-th exterior power $\Lambda^k(M)$ is the submodule of $\Lambda(M)$ spanned by the products $x_1 \wedge \dots \wedge x_k$ (Section 1). The alternating map $\iota_k : M^k \to \Lambda^k(M)$ sends $(x_1, \dots, x_k)$ to $x_1 \wedge \dots \wedge x_k$.

::: mathlib
`exteriorPower.ιMulti` · `Mathlib.LinearAlgebra.ExteriorPower.Basic`

The alternating map `ιMulti R n : M [⋀^Fin n]→ₗ[R] ⋀[R]^n M`. Its image spans, by `exteriorPower.ιMulti_span`.

<?decl exteriorPower.ιMulti?>
:::

**Definition (Exterior power of a linear map).** For a linear map $f : M \to N$, the map $\Lambda^k f : \Lambda^k(M) \to \Lambda^k(N)$ is the restriction of the algebra homomorphism $\Lambda(f)$ of Section 1. It sends $x_1 \wedge \dots \wedge x_k$ to $f(x_1) \wedge \dots \wedge f(x_k)$.

::: mathlib
`exteriorPower.map` · `Mathlib.LinearAlgebra.ExteriorPower.Basic`

The linear map `map n f : ⋀[R]^n M →ₗ[R] ⋀[R]^n N`.

<?decl exteriorPower.map?>
:::

**Definition (Orientation).** Let $R$ be an ordered field and $M$ a vector space of dimension $n \ge 1$. Two nonzero alternating $n$-forms $\omega, \omega' : M^n \to R$ are equivalent when $\omega' = c\, \omega$ for some $c > 0$. An orientation of $M$ is an equivalence class. A basis $e$ gives the orientation of the form $\det_e$, where $\det_e(v_1, \dots, v_n)$ is the determinant of the matrix of the coordinates of the $v_j$ in $e$.

::: mathlib
`Orientation` · `Mathlib.LinearAlgebra.Orientation`

The type `Orientation R M ι`, defined as `Module.Ray R (M [⋀^ι]→ₗ[R] R)`, the rays of nonzero alternating maps with index type `ι`.

<?decl Orientation?>
:::

::: mathlib
`Module.Basis.orientation` · `Mathlib.LinearAlgebra.Orientation`

The orientation `e.orientation` of a basis `e : Basis ι R M`, the ray of `e.det`.

<?decl Module.Basis.orientation?>
:::

<?decl Module.Basis.det?>

### Theorems and proofs

**Theorem (Universal property of the exterior power).** For each alternating map $\varphi : M^k \to N$ there is a unique linear map $\bar\varphi : \Lambda^k(M) \to N$ with $\bar\varphi(x_1 \wedge \dots \wedge x_k) = \varphi(x_1, \dots, x_k)$.

*Proof.* By the proof of the grading theorem of Section 1, $\Lambda^k(M) \cong M^{\otimes k} / J_k$, where $J_k = J \cap M^{\otimes k}$ is spanned by the pure tensors $a_1 \otimes \dots \otimes a_k$ with $a_i = a_{i+1}$ for some $i$. The map $\varphi$ is multilinear, so it gives a linear map $\psi : M^{\otimes k} \to N$ (Chapter 3, Section 1). The map $\psi$ vanishes on each generator of $J_k$, since $\varphi$ is zero when two arguments are equal. So $\psi$ factors through $\Lambda^k(M)$. Uniqueness holds since the products $x_1 \wedge \dots \wedge x_k$ span. $\square$

::: mathlib
`exteriorPower.alternatingMapLinearEquiv` · `Mathlib.LinearAlgebra.ExteriorPower.Basic`

The linear equivalence `(M [⋀^Fin n]→ₗ[R] N) ≃ₗ[R] (⋀[R]^n M →ₗ[R] N)`.

<?decl exteriorPower.alternatingMapLinearEquiv?>
:::

**Theorem (Functoriality).** $\Lambda^k(g \circ f) = \Lambda^k g \circ \Lambda^k f$ and $\Lambda^k(\mathrm{id}) = \mathrm{id}$.

*Proof.* Both sides send $x_1 \wedge \dots \wedge x_k$ to $g f x_1 \wedge \dots \wedge g f x_k$, and the products span. $\square$

::: mathlib
`exteriorPower.map_comp` · `Mathlib.LinearAlgebra.ExteriorPower.Basic`

The statement `map n (g ∘ₗ f) = map n g ∘ₗ map n f`.

<?decl exteriorPower.map_comp?>
:::

**Theorem (Basis of an exterior power).** Let $(e_i)_{i \in I}$ be a basis of $M$, with $I$ totally ordered. Then the $e_S$ with $|S| = k$ form a basis of $\Lambda^k(M)$. If $M$ is free of rank $n$, then $\Lambda^k(M)$ is free of rank $\binom{n}{k}$. The coordinate of $v_1 \wedge \dots \wedge v_k$ at $e_S$ is the $k \times k$ minor, with the rows in $S$, of the $n \times k$ matrix of the coordinates of the $v_j$.

*Proof.* The first two statements are the theorem on bases of Section 1. For the coordinates, write $v_j = \sum_i a_{ij} e_i$ and expand by multilinearity: $v_1 \wedge \dots \wedge v_k = \sum_{i_1, \dots, i_k} a_{i_1 1} \cdots a_{i_k k}\, e_{i_1} \wedge \dots \wedge e_{i_k}$. A term with two equal indices is zero. The other terms with $\{i_1, \dots, i_k\} = S = \{s_1 < \dots < s_k\}$ have $i_j = s_{\sigma(j)}$ for a unique permutation $\sigma$ of $\{1, \dots, k\}$. Sorting the factors gives $e_{i_1} \wedge \dots \wedge e_{i_k} = \operatorname{sgn} \sigma \cdot e_S$, since each transposition of neighbours changes the sign and $\operatorname{sgn}$ is multiplicative. So the coefficient of $e_S$ is $\sum_\sigma \operatorname{sgn} \sigma \prod_j a_{s_{\sigma(j)} j}$. This is the formula of Leibniz (Volume 7, Chapter 4) for the minor. $\square$

::: mathlib
`Module.Basis.exteriorPower` · `Mathlib.LinearAlgebra.ExteriorPower.Basis`

The basis `b.exteriorPower n : Basis (Set.powersetCard I n) R (⋀[R]^n M)` from a basis `b` indexed by a linearly ordered type `I`. The index set is the subsets of `I` of size `n`.

<?decl Module.Basis.exteriorPower?>
:::

**Theorem (The top power and the determinant).** Let $M$ be free with basis $e_1, \dots, e_n$, and let $f : M \to M$ be linear. Then $\Lambda^n(M)$ is free with the basis $e_1 \wedge \dots \wedge e_n$, and
$$f(v_1) \wedge \dots \wedge f(v_n) = \det f \cdot v_1 \wedge \dots \wedge v_n$$
for all $v_1, \dots, v_n \in M$. So $\Lambda^n f$ is multiplication by $\det f$.

*Proof.* The first statement is the case $k = n$ of the theorem on bases. A linear map of the free module $R \cdot (e_1 \wedge \dots \wedge e_n)$ to itself is multiplication by a scalar $c$, so $\Lambda^n f = c \cdot \mathrm{id}$. To find $c$, apply it to $e_1 \wedge \dots \wedge e_n$. Let $A$ be the matrix of $f$ in the basis $e$. By the theorem on bases with $k = n$ and $S = \{1, \dots, n\}$, the coefficient of $f(e_1) \wedge \dots \wedge f(e_n)$ at $e_1 \wedge \dots \wedge e_n$ is the minor of all rows of $A$, which is $\det A$. So $c = \det A = \det f$. $\square$

**Corollary (Multiplicativity).** $\det(g f) = \det g \det f$, and $\det f$ does not depend on the basis.

*Proof.* By functoriality, $\Lambda^n(g f) = \Lambda^n g \circ \Lambda^n f$, which is multiplication by $\det g \det f$. The scalar $c$ in the proof above is defined without a basis, since $\Lambda^n f$ is. $\square$

The index of this edition has no declaration that states that `exteriorPower.map` on the top power is multiplication by `LinearMap.det`.

<?decl LinearMap.det?>

**Theorem (Orientation of a basis).** Let $R$ be an ordered field, and let $e, e'$ be bases of $M$ of size $n$. Let $P$ be the matrix of the coordinates of the $e'_j$ in $e$. Then $e$ and $e'$ give the same orientation exactly when $\det P > 0$. A linear automorphism $f$ preserves each orientation exactly when $\det f > 0$.

*Proof.* By the universal property and $\operatorname{rank} \Lambda^n(M) = 1$, the alternating $n$-forms are a vector space of dimension $1$, so $\det_{e'} = c \det_e$. Evaluate at $e'$: $1 = \det_{e'}(e') = c \det_e(e') = c \det P$. So $c = (\det P)^{-1}$, and $c > 0$ exactly when $\det P > 0$. For the second statement, the form $\omega \circ f$ is $\omega(f v_1, \dots, f v_n)$, which equals $\det f \cdot \omega$ by the theorem on the top power. So $\omega \circ f$ is equivalent to $\omega$ exactly when $\det f > 0$. $\square$

There are exactly two orientations, since $c$ is either positive or negative.

::: mathlib
`Module.Basis.orientation_eq_iff_det_pos` · `Mathlib.LinearAlgebra.Orientation`

The statement `e₁.orientation = e₂.orientation ↔ 0 < e₁.det e₂`.

<?decl Module.Basis.orientation_eq_iff_det_pos?>
:::

::: mathlib
`Orientation.map_eq_iff_det_pos` · `Mathlib.LinearAlgebra.Orientation`

For a linear equivalence `f` of a finite dimensional space over an ordered field, `Orientation.map ι f x = x ↔ 0 < LinearMap.det f`, when `Fintype.card ι = finrank R M`.

<?decl Orientation.map_eq_iff_det_pos?>
:::

**Definition (Cross product).** For $u, v \in R^3$, $u \times v = (u_2 v_3 - u_3 v_2,\ u_3 v_1 - u_1 v_3,\ u_1 v_2 - u_2 v_1)$. It encodes $u \wedge v \in \Lambda^2(R^3)$ as a vector.

**Proposition (Triple product).** $u \cdot (v \times w) = \det [u, v, w]$, the determinant of the matrix with the rows $u, v, w$.

*Proof.* Expand: $u \cdot (v \times w) = u_1(v_2 w_3 - v_3 w_2) - u_2(v_1 w_3 - v_3 w_1) + u_3(v_1 w_2 - v_2 w_1)$. This is the expansion of $\det [u, v, w]$ along the first row. $\square$

::: mathlib
`crossProduct` · `Mathlib.LinearAlgebra.CrossProduct`

The bilinear map `crossProduct : (Fin 3 → R) →ₗ[R] (Fin 3 → R) →ₗ[R] Fin 3 → R`, with the notation `u ⨯₃ v` in the scope `Matrix`.

<?decl crossProduct?>
:::

::: mathlib
`triple_product_eq_det` · `Mathlib.LinearAlgebra.CrossProduct`

The statement `u ⬝ᵥ (v ⨯₃ w) = Matrix.det ![u, v, w]`.

<?decl triple_product_eq_det?>
:::

### Examples

**Example (A determinant by wedges).** Let $f$ on $\mathbb{Q}^3$ have $f(e_1) = e_1 + 2 e_2$, $f(e_2) = e_2 - e_3$ and $f(e_3) = e_1$. Section 1 computed $(e_1 + 2 e_2) \wedge (e_2 - e_3) \wedge e_1 = -2 e_{123}$. So $\det f = -2$, and $f$ reverses the orientation of $\mathbb{Q}^3$.

**Example (The second exterior power of a matrix).** Let $f$ on $\mathbb{Q}^3$ have the matrix $A$ with the columns $(1, 0, 2)$, $(0, 1, 1)$ and $(3, 1, 0)$. Then $f(e_1) \wedge f(e_2) = (e_1 + 2 e_3) \wedge (e_2 + e_3) = e_{12} + e_{13} - 2 e_{23}$. The coefficients are the minors of the first two columns of $A$: rows $\{1,2\}$ give $1$, rows $\{1, 3\}$ give $1 \cdot 1 - 0 \cdot 2 = 1$, and rows $\{2,3\}$ give $0 \cdot 1 - 1 \cdot 2 = -2$.

**Counterexample (Independence needs a domain).** Over a field, $v_1 \wedge \dots \wedge v_k \neq 0$ exactly when the $v_i$ are independent (Exercise 3). Over $\mathbb{Z}/6$ with $M = R$, the vector $v = 2$ has $v \neq 0$ but $3 v = 0$, so $v$ is not independent.

### The library around it

The folder `Mathlib.LinearAlgebra.ExteriorPower` also has the pairing $\Lambda^k \times \Lambda^{n-k} \to \Lambda^n$ in `WedgePairing`, the Hodge star `exteriorPower.hodgeStar`, and `exteriorPower.volOrientation`, the orientation of an isomorphism $\Lambda^n(M) \cong R$.

The exterior powers commute with base change as well: `exteriorPower.baseChangeEquiv R M S i` is an $S$-linear isomorphism $S \otimes_R \Lambda^i_R(M) \cong \Lambda^i_S(S \otimes_R M)$, with $s \otimes (m_1 \wedge \dots \wedge m_i) \mapsto s \cdot (1 \otimes m_1) \wedge \dots \wedge (1 \otimes m_i)$ (`exteriorPower.baseChangeEquiv_tmul_ιMulti`). The file `Mathlib.LinearAlgebra.ExteriorPower.BilinForm` extends a bilinear form $B$ on $M$ to each exterior power. The form `LinearMap.BilinForm.exteriorPower B n` takes the Gram determinant $\det\big(B(v_j, w_i)\big)_{i, j}$ at the pair $(v_1 \wedge \dots \wedge v_n, \; w_1 \wedge \dots \wedge w_n)$ (`LinearMap.BilinForm.bilinForm_ιMulti_ιMulti`). For a finite free module, `LinearMap.BilinForm.bijective_exteriorPower` says that the extended form is perfect when $B$ is perfect, that is, when $B : M \to M^*$ is bijective.

### Exercises

1. (A) Compute $\det f$ for $f(e_1) = 2 e_1 + e_2$, $f(e_2) = e_1 + e_2$ on $\mathbb{Q}^2$ with wedges. Hint: compute $f(e_1) \wedge f(e_2)$.
2. (A) Show that $\Lambda^k(M) = 0$ for $k > n$ when $M$ is free of rank $n$. Hint: there is no subset of size $k$.
3. (B) Over a field, show that $v_1 \wedge \dots \wedge v_k \neq 0$ exactly when the $v_i$ are independent. Hint: extend an independent family to a basis.
4. (B) Show that a linear map $f$ of a free module of rank $n$ is invertible exactly when $\det f$ is a unit. Hint: use the adjugate, and multiplicativity.
5. (B) Show that $u \times (v \times w) = (u \cdot w) v - (u \cdot v) w$ in $R^3$. Hint: both sides are linear in each vector, so check on basis vectors.
6. (B) Show that the matrix of $\Lambda^k f$ in the basis $(e_S)$ has the entry $\det A_{S, T}$ at $(S, T)$, the minor of $A$ with rows $S$ and columns $T$. Deduce the Cauchy-Binet formula for $\det(AB)_{S,T}$. Hint: use functoriality.
7. (C) Show that $\operatorname{tr} f$ is the coefficient of $t$ in $\det(\mathrm{id} + t f)$, and that $\det(\mathrm{id} + t f) = \sum_k t^k \operatorname{tr}(\Lambda^k f)$. Hint: expand $(e_1 + t f e_1) \wedge \dots \wedge (e_n + t f e_n)$.

### Notes and history

Grassmann introduced the exterior product in his Ausdehnungslehre of 1844. In Mathlib the orientation is a ray of alternating maps and needs no exterior power.

### Reference

<?reference?>
