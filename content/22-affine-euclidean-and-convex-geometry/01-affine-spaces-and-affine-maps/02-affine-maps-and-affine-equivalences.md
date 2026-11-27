---
title: Affine maps and affine equivalences
kind: theory
modules:
  - Mathlib.LinearAlgebra.AffineSpace.AffineMap
  - Mathlib.LinearAlgebra.AffineSpace.AffineEquiv
  - Mathlib.LinearAlgebra.AffineSpace.Slope
  - Mathlib.LinearAlgebra.AffineSpace.Ordered
  - Mathlib.LinearAlgebra.AffineSpace.Homogenization
explains:
  E3: [AffineMap, AffineMap.mk', AffineMap.lineMap, AffineMap.homothety, AffineEquiv, AffineEquiv.ofBijective, AffineEquiv.linearHom, slope, map_le_lineMap_iff_slope_le_slope, Homogenization, Homogenization.lift]
  E2: [AffineMap.map_vadd, AffineMap.ext_linear, AffineMap.const, AffineMap.linear_injective_iff, AffineMap.lineMap_apply, AffineMap.decomp, AffineMap.linearHom, AffineEquiv.symm, AffineEquiv.trans, AffineEquiv.constVAdd, AffineMap.slope_comp, lineMap_le_map_iff_slope_le_slope, Homogenization.ofPoint, Homogenization.weight]
  E1: auto
families: []
requires: [V05.C06, V07]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Affine maps and affine equivalences

### Overview

An affine map between affine spaces is a map that is linear after a choice of origin in each space. Each affine map has a linear part, and it is determined by its linear part and the image of one point. This section also studies the affine group. It ends with slopes and with the homogenization of an affine space.

Throughout, $k$ is a ring, $P_1$ and $P_2$ are affine spaces over $k$-modules $V_1$ and $V_2$.

### Definitions

**Definition (affine map).** An *affine map* $f : P_1 \to P_2$ is a map together with a $k$-linear map $L : V_1 \to V_2$ such that $f(v +_v p) = L(v) +_v f(p)$ for all $v \in V_1$ and $p \in P_1$. The map $L$ is the *linear part* of $f$.

::: mathlib
`AffineMap` · `Mathlib.LinearAlgebra.AffineSpace.AffineMap`

`structure AffineMap (k P1 P2)` has the fields `toFun`, `linear : V1 →ₗ[k] V2` and `map_vadd' : ∀ p v, toFun (v +ᵥ p) = linear v +ᵥ toFun p`. The notation is `P1 →ᵃ[k] P2`. The ring is part of the type. See also `AffineMap.map_vadd`.

<?decl AffineMap?>
:::

**Definition (line map and homothety).** For $p_0, p_1 \in P$ the *line map* is $\ell_{p_0 p_1} : k \to P$, $\ell_{p_0 p_1}(c) = c(p_1 -_v p_0) +_v p_0$. For $c_0 \in P$ and $r \in k$, with $k$ commutative, the *homothety* with center $c_0$ and ratio $r$ is $h_{c_0, r}(p) = r(p -_v c_0) +_v c_0$.

The line map is affine with linear part $c \mapsto c(p_1 -_v p_0)$, and $\ell(0) = p_0$, $\ell(1) = p_1$. The homothety is affine with linear part $r \cdot \mathrm{id}$.

::: mathlib
`AffineMap.lineMap` · `Mathlib.LinearAlgebra.AffineSpace.AffineMap`

`AffineMap.lineMap p₀ p₁ : k →ᵃ[k] P1`, with `AffineMap.lineMap_apply : lineMap p₀ p₁ c = c • (p₁ -ᵥ p₀) +ᵥ p₀`. The homothety is `AffineMap.homothety c r`.

<?decl AffineMap.lineMap?>
:::

**Definition (affine equivalence).** An *affine equivalence* $P_1 \to P_2$ is a bijection $f$ with a linear equivalence $L : V_1 \to V_2$ such that $f(v +_v p) = L(v) +_v f(p)$.

::: mathlib
`AffineEquiv` · `Mathlib.LinearAlgebra.AffineSpace.AffineEquiv`

`AffineEquiv k P₁ P₂` extends `P₁ ≃ P₂` with `linear : V₁ ≃ₗ[k] V₂` and `map_vadd'`. The notation is `P₁ ≃ᵃ[k] P₂`. See `AffineEquiv.symm` and `AffineEquiv.trans`. Translations are `AffineEquiv.constVAdd`.

<?decl AffineEquiv?>
:::

**Definition (slope).** Let $k$ be a field and $f : k \to P$. For $a, b \in k$ the *slope* of $f$ on $[a, b]$ is $\operatorname{slope}(f, a, b) = (b - a)^{-1}(f(b) -_v f(a)) \in V$.

::: mathlib
`slope` · `Mathlib.LinearAlgebra.AffineSpace.Slope`

`slope f a b = (b - a)⁻¹ • (f b -ᵥ f a)`. For `a = b` the value is `0`, since `0⁻¹ = 0` in Mathlib. For an affine map `g`, `AffineMap.slope_comp` gives the slope of `g ∘ f` as the image of the slope of `f` under the linear part.

<?decl slope?>
:::

### Theorems and proofs

**Theorem (construction from a base point).** Let $f : P_1 \to P_2$ be a map, $L : V_1 \to V_2$ linear and $p \in P_1$, with $f(q) = L(q -_v p) +_v f(p)$ for all $q$. Then $f$ is affine with linear part $L$. The linear part of an affine map is unique, and two affine maps with the same linear part and the same value at one point are equal.

*Proof.* For $v \in V_1$ and $q \in P_1$, rule (4) of Section 1 gives $(v +_v q) -_v p = v + (q -_v p)$. So $f(v +_v q) = (L v + L(q -_v p)) +_v f(p) = L v +_v f(q)$. The linear part is unique, since $L v = f(v +_v p) -_v f(p)$. If $f$ and $g$ have the linear part $L$ and $f(p) = g(p)$, then $f(q) = L(q -_v p) +_v f(p) = g(q)$. $\square$

::: mathlib
`AffineMap.mk'` · `Mathlib.LinearAlgebra.AffineSpace.AffineMap`

`AffineMap.mk' f f' p h` builds an affine map from `h : ∀ p', f p' = f' (p' -ᵥ p) +ᵥ f p`. Extensionality is `AffineMap.ext_linear`. Constant maps are `AffineMap.const k P1 q`.

<?decl AffineMap.mk'?>
:::

For modules, the theorem with $p = 0$ gives $f = L + f(0)$. This is `AffineMap.decomp`.

**Theorem (injective, surjective, bijective).** An affine map $f$ is injective, surjective or bijective if and only if its linear part $L$ is.

*Proof.* Fix $p \in P_1$. By the construction theorem, $f = \tau \circ L \circ \sigma$ with $\sigma(q) = q -_v p$ and $\tau(w) = w +_v f(p)$. The maps $\sigma : P_1 \to V_1$ and $\tau : V_2 \to P_2$ are bijections by Section 1. A composite with bijections on both sides is injective, surjective or bijective exactly when the middle map is. $\square$

In Lean these are `AffineMap.linear_injective_iff` and its two variants.

**Theorem (inverse of a bijective affine map).** Let $f : P_1 \to P_2$ be a bijective affine map with linear part $L$. Then $f^{-1}$ is affine with linear part $L^{-1}$, so $f$ is an affine equivalence.

*Proof.* By the previous theorem, $L$ is a bijective linear map, so $L^{-1}$ is linear. For $w \in V_2$ and $q \in P_2$, put $p = f^{-1}(q)$. Then $f(L^{-1}(w) +_v p) = L L^{-1}(w) +_v f(p) = w +_v q$. Apply $f^{-1}$: $f^{-1}(w +_v q) = L^{-1}(w) +_v f^{-1}(q)$. $\square$

::: mathlib
`AffineEquiv.ofBijective` · `Mathlib.LinearAlgebra.AffineSpace.AffineEquiv`

`AffineEquiv.ofBijective : Function.Bijective φ → P₁ ≃ᵃ[k] P₂` for `φ : P₁ →ᵃ[k] P₂`.

<?decl AffineEquiv.ofBijective?>
:::

**Theorem (the affine group).** The affine automorphisms of $P$ form a group under composition. The map $f \mapsto L$ that sends an automorphism to its linear part is a surjective group homomorphism onto $GL(V)$, and its kernel is the group of translations, which is isomorphic to $V$.

*Proof.* The linear part of $f \circ g$ is $L_f L_g$, since $f(g(v +_v p)) = f(L_g v +_v g p) = L_f L_g v +_v f g p$. So the map is a homomorphism. For surjectivity, fix $o \in P$ and $A \in GL(V)$. The map $p \mapsto A(p -_v o) +_v o$ is affine with linear part $A$, by the construction theorem, and it is bijective by the theorem on bijectivity. If $L = \mathrm{id}$, put $v = f(o) -_v o$. For each $p$, $f(p) = (p -_v o) +_v f(o)$ and $v +_v p = (v + (p -_v o)) +_v o$. Both are $((f(o) -_v o) + (p -_v o)) +_v o$. So $f$ is the translation by $v$. Conversely, translations have linear part $\mathrm{id}$, and $v \mapsto (p \mapsto v +_v p)$ is an injective homomorphism from $V$. $\square$

::: mathlib
`AffineEquiv.linearHom` · `Mathlib.LinearAlgebra.AffineSpace.AffineEquiv`

`AffineEquiv.linearHom` is `AffineEquiv.linear` on automorphisms as a `MonoidHom` from `P ≃ᵃ[k] P` to `V ≃ₗ[k] V`. In `AffineEquiv.group`, `e * e' = e'.trans e`. For endomorphisms it is `AffineMap.linearHom`.

<?decl AffineEquiv.linearHom?>
:::

**Theorem (chord and slopes).** Let $k$ be an ordered field, $E$ an ordered $k$-module, $f : k \to E$, $a < b$, $0 < r < 1$ and $c = \ell_{ab}(r)$. Then $f(c) \le \ell_{f a, f b}(r)$ if and only if $\operatorname{slope}(f, a, c) \le \operatorname{slope}(f, c, b)$.

*Proof.* Here $c - a = r(b - a) > 0$ and $b - c = (1 - r)(b - a) > 0$. Multiply the slope inequality by the positive scalar $r(1 - r)(b - a)$. The result is $(1 - r)(f c - f a) \le r(f b - f c)$, which is $f(c) \le (1 - r)f(a) + r f(b) = \ell_{f a, f b}(r)$. $\square$

::: mathlib
`map_le_lineMap_iff_slope_le_slope` · `Mathlib.LinearAlgebra.AffineSpace.Ordered`

The statement needs instances such as `PosSMulReflectLE k E`. The reverse form is `lineMap_le_map_iff_slope_le_slope`. Chapter 6 uses these lemmas for convex functions.

<?decl map_le_lineMap_iff_slope_le_slope?>
:::

### Examples

**Example (an explicit affine equivalence).** Let $f : \mathbb{R}^2 \to \mathbb{R}^2$, $f(x, y) = (2x + y + 1, x - 3)$. By `AffineMap.decomp`, $L(x, y) = (2x + y, x)$ and $f(0) = (1, -3)$. The determinant of $L$ is $-1$, so $f$ is bijective and $f^{-1}$ is affine with linear part $L^{-1}(u, v) = (v, u - 2v)$. Solving $u = 2x + y + 1$, $v = x - 3$ gives $f^{-1}(u, v) = (v + 3, u - 2v - 7)$.

**Counterexample (the ring matters).** Complex conjugation $\kappa : \mathbb{C} \to \mathbb{C}$ is $\mathbb{R}$-linear, so it is an $\mathbb{R}$-affine map. It is not $\mathbb{C}$-affine. If it were, `AffineMap.decomp` would give $\kappa(z) = a z + \kappa(0) = a z$ with $a \in \mathbb{C}$. From $\kappa(1) = 1$, $a = 1$, but $\kappa(i) = -i \neq i$.

### The library around it

The file `Mathlib.LinearAlgebra.AffineSpace.Homogenization` embeds $P$, by `Homogenization.ofPoint`, into a module, the *homogenization*, as the hyperplane where the linear form `Homogenization.weight` is $1$. An affine map into a module extends uniquely to a linear map. The docstring says that the homogenization is isomorphic to `V × R`, but not canonically unless `P = V`.

::: mathlib
`Homogenization.lift` · `Mathlib.LinearAlgebra.AffineSpace.Homogenization`

`Homogenization.lift : (P →ᵃ[R] W) ≃+ (Homogenization R P →ₗ[R] W)` for a module `W` over `R`.

<?decl Homogenization.lift?>
:::

### Exercises

1. (A) Find the linear part and the value at $0$ of $f(x, y, z) = (x - z + 2, 3y, x + y + z - 1)$. Is $f$ bijective?
2. (A) Show that an affine map $f : k \to k$ has the form $f(x) = ax + b$, and that $\operatorname{slope}(f, s, t) = a$ for $s \neq t$.
3. (B) Show that an affine map $f : \mathbb{R}^2 \to \mathbb{R}^2$ that fixes $(0,0)$, $(1,0)$ and $(0,1)$ is the identity.
4. (B) In $\mathbb{R}^n$, let $rs \neq 1$. Show that $h_{a, r} \circ h_{b, s}$ is a homothety with ratio $rs$, and find its center.
5. (B) Let $f : \mathbb{R} \to \mathbb{R}$, $a < b$, and suppose $\operatorname{slope}(f, a, c) \le \operatorname{slope}(f, c, b)$ for each $c \in (a, b)$. Show that the graph of $f$ on $[a, b]$ lies below the chord.
6. (C) Show that the conjugation of a translation by an affine automorphism $g$ is a translation: $g \circ t_v \circ g^{-1} = t_{L_g v}$. Deduce that the affine group is a semidirect product of $V$ and $GL(V)$.

### Notes and history

The file on affine maps has the author Joseph Myers. Yury Kudryashov wrote the files on affine equivalences, slopes and ordered line maps. The file on homogenization has the author Attila Gáspár and dates from 2026.

### Reference

<?reference?>
