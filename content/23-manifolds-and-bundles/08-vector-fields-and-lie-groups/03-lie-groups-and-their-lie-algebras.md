---
title: Lie groups and their Lie algebras
kind: theory
modules:
  - Mathlib.Geometry.Manifold.Algebra.Monoid
  - Mathlib.Geometry.Manifold.Algebra.LieGroup
  - Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
  - Mathlib.Geometry.Manifold.Algebra.SMul
  - Mathlib.Geometry.Manifold.Algebra.Structures
  - Mathlib.Geometry.Manifold.Algebra.LeftInvariantDerivation
  - Mathlib.Geometry.Manifold.GroupLieAlgebra
explains:
  E3: [LieGroup, GroupLieAlgebra, mulInvariantVectorField, LeftInvariantDerivation]
  E2: [ContMDiffMul, LieAddGroup, LieGroup.contMDiff_inv, contMDiff_mul_left, topologicalGroup_of_lieGroup, Prod.instLieGroup, smoothLeftMul, ContMDiffMonoidMorphism, ContMDiffSMul, Diffeomorph.smul, ContMDiffRing, ContMDiffMap.commRing, GroupLieAlgebra.bracket_def, instLieAlgebraGroupLieAlgebra, mulInvariantVectorField_eq_mpullback, contMDiff_mulInvariantVectorField, mulInvariantVector_mlieBracket, LeftInvariantDerivation.left_invariant, LeftInvariantDerivation.commutator_apply, LeftInvariantDerivation.instLieAlgebra]
  E1: auto
families: []
requires: [V23.C03, V23.C04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Lie groups and their Lie algebras

### Overview

A Lie group is a group with a manifold structure for which multiplication and inversion are smooth. Left translation by a group element is then a diffeomorphism, and it moves the identity to that element. So a tangent vector at the identity spreads to a vector field on the whole group, invariant under left translations. The bracket of two such fields is again invariant, and its value at the identity defines a bracket on the tangent space $T_1G$. This makes $T_1G$ a Lie algebra, the Lie algebra of $G$. This section defines Lie groups, proves these facts with the bracket of Section 1, computes the Lie algebra in examples, and describes the second construction that Mathlib has, by left invariant derivations.

### Definitions

**Definition (Lie group).** Let $G$ be a group and a $C^n$ manifold modelled on $(E, H, I)$ over $\mathbb{K}$. It is a *$C^n$ Lie group* if the multiplication $G \times G \to G$ and the inversion $G \to G$ are $C^n$, with the product manifold structure on $G \times G$ (Chapter 2).

**Definition (Left translation).** For $g \in G$, the *left translation* is $L_g(h) = gh$.

**Definition (Invariant vector field).** For $v \in T_1G$, the *left invariant vector field* of $v$ is $X_v(g) = d(L_g)_1\, v \in T_gG$. A vector field $X$ is *left invariant* if $L_h^*X = X$ for all $h$, where $L_h^*$ is the pullback of Section 1.

**Definition (Lie algebra of a Lie group).** The *Lie algebra* of $G$ is $T_1G$ with the bracket $[v, w] = [X_v, X_w](1)$.

**Definition (Left invariant derivation).** Let $C^\infty(G)$ be the algebra of smooth functions $G \to \mathbb{K}$. A derivation $D$ of $C^\infty(G)$ is *left invariant* if $D(f \circ L_g) = (Df) \circ L_g$ for all $f$ and $g$.

::: mathlib
`LieGroup` · `Mathlib.Geometry.Manifold.Algebra.LieGroup`

`LieGroup I n G` is a class that extends `ContMDiffMul I n G` and adds `ContMDiff I I n fun a ↦ a⁻¹` (`LieGroup.contMDiff_inv`). `ContMDiffMul I n G` extends `IsManifold I n G` and asks that `fun p : G × G ↦ p.1 * p.2` is `C^n`. The additive versions are `ContMDiffAdd` and `LieAddGroup`. `topologicalGroup_of_lieGroup` proves that a Lie group is a topological group, but it is not an instance; the library note "Design choices about smooth algebraic structures" in `Algebra.Monoid` explains why. Conversely, every topological group is a `LieGroup I 0 G`, and products are Lie groups (`Prod.instLieGroup`).

<?decl LieGroup?>
<?decl ContMDiffMul?>
<?decl LieGroup.contMDiff_inv?>
<?decl topologicalGroup_of_lieGroup?>
<?decl Prod.instLieGroup?>
:::

::: mathlib
`GroupLieAlgebra` · `Mathlib.Geometry.Manifold.GroupLieAlgebra`

`GroupLieAlgebra I G` is an abbreviation for the tangent space of `G` at `1`. The name avoids the class `LieAlgebra`. `mulInvariantVectorField v g` is the image of `v` under the derivative of left multiplication by `g`. The bracket is defined by `GroupLieAlgebra.bracket_def`, `⁅v, w⁆ = mlieBracket I (mulInvariantVectorField v) (mulInvariantVectorField w) 1`, and `instLieAlgebraGroupLieAlgebra` is the instance of Lie algebra. The standing hypothesis is `LieGroup I (minSmoothness 𝕜 3) G`, which is $C^3$ over $\mathbb{R}$ or $\mathbb{C}$.

<?decl GroupLieAlgebra?>
<?decl mulInvariantVectorField?>
<?decl GroupLieAlgebra.bracket_def?>
<?decl instLieAlgebraGroupLieAlgebra?>
:::

### Theorems and proofs

**Lemma (Translations).** In a $C^n$ Lie group with $n \ge 1$, each $L_g$ is a $C^n$ diffeomorphism with inverse $L_{g^{-1}}$, and $L_g \circ L_h = L_{gh}$.

*Proof.* The map $L_g$ is the composite of $h \mapsto (g, h)$, which is $C^\infty$, and the multiplication, which is $C^n$. The identities $L_g L_h = L_{gh}$ and $L_g L_{g^{-1}} = L_1 = \mathrm{id}$ are associativity and the group axioms. So $L_g$ is a bijection with the $C^n$ inverse $L_{g^{-1}}$. $\square$

**Theorem (Invariant fields).** For $v \in T_1G$ the field $X_v$ is left invariant, and $X_v(g) = (L_{g^{-1}}^* X)(g)$ for every field $X$ with $X(1) = v$. If $X$ is left invariant, then $X = X_{X(1)}$. So $v \mapsto X_v$ is a linear bijection from $T_1G$ onto the left invariant fields.

*Proof.* By the chain rule and the lemma, $d(L_h)_g\, d(L_g)_1 = d(L_{hg})_1$, and $d(L_h)_g$ is invertible. Then
$$(L_h^* X_v)(g) = d(L_h)_g^{-1}\,X_v(hg) = d(L_h)_g^{-1}\,d(L_{hg})_1 v = d(L_g)_1 v = X_v(g).$$
For the second claim, $(L_{g^{-1}}^* X)(g) = d(L_{g^{-1}})_g^{-1} X(g^{-1}g) = d(L_g)_1\,v$, since $d(L_{g^{-1}})_g^{-1} = d(L_g)_1$ by the chain rule applied to $L_g \circ L_{g^{-1}} = \mathrm{id}$. If $X$ is left invariant, take $h = g^{-1}$ in $L_h^*X = X$: then $X(g) = (L_{g^{-1}}^*X)(g) = X_{X(1)}(g)$. Linearity of $v \mapsto X_v$ is linearity of $d(L_g)_1$. $\square$

**Lemma (Smoothness of invariant fields).** If $G$ is a $C^{k+1}$ Lie group, then $X_v$ is a $C^k$ vector field.

*Proof.* Let $m : G \times G \to G$ be the multiplication. Then $L_g = m(g, \cdot)$, so $X_v(g) = dm_{(g, 1)}(0, v)$. The differential of a $C^{k+1}$ map is a $C^k$ map of tangent bundles $T(G \times G) \to TG$ (Chapter 4), and $g \mapsto ((g, 1), (0, v))$ is a $C^\infty$ section of $T(G \times G)$ along $g \mapsto (g, 1)$. The composite $g \mapsto X_v(g)$ is $C^k$. $\square$

**Theorem (The Lie algebra).** Let $G$ be a $C^3$ Lie group over $\mathbb{R}$ or $\mathbb{C}$, modelled on a Banach space. Then $[X_v, X_w] = X_{[v, w]}$, and $T_1G$ with the bracket $[v, w]$ is a Lie algebra.

*Proof.* By the lemma, $X_v$ and $X_w$ are $C^2$. Each $L_h$ is a $C^3$ diffeomorphism, so naturality of the bracket (Section 1) gives $L_h^*[X_v, X_w] = [L_h^*X_v, L_h^*X_w] = [X_v, X_w]$. So $[X_v, X_w]$ is left invariant, and by the theorem on invariant fields it equals $X_u$ with $u = [X_v, X_w](1) = [v, w]$.

The bracket on $T_1G$ is bilinear because $v \mapsto X_v$ is linear and the bracket of fields is bilinear. It is antisymmetric because the bracket of fields is. For the Jacobi identity, apply the Jacobi identity of Section 1 to the $C^2$ fields $X_u, X_v, X_w$ and evaluate at $1$:
$$[u, [v, w]] = [X_u, X_{[v, w]}](1) = [X_u, [X_v, X_w]](1) = [[X_u, X_v], X_w](1) + [X_v, [X_u, X_w]](1),$$
and the right side is $[[u, v], w] + [v, [u, w]]$ by the same substitution. $\square$

The order $3$ comes from this proof. The Jacobi identity of fields needs $C^2$ fields, and the fields $X_v$ lose one derivative from the group.

**Theorem (Left invariant derivations).** The left invariant derivations of $C^\infty(G)$ form a Lie algebra under the commutator $[D_1, D_2] = D_1 D_2 - D_2 D_1$.

*Proof.* The commutator is a derivation:
$$D_1D_2(fg) = D_1(f\,D_2g + g\,D_2f) = D_1f\,D_2g + f\,D_1D_2g + D_1g\,D_2f + g\,D_1D_2f.$$
Subtract the same formula with $D_1$ and $D_2$ exchanged. The mixed terms $D_1f\,D_2g + D_1g\,D_2f$ are symmetric and cancel, which leaves $f\,[D_1, D_2]g + g\,[D_1, D_2]f$. If $D_1$ and $D_2$ commute with $f \mapsto f \circ L_g$, so does each composite, hence the commutator. The Jacobi identity holds for commutators in any associative algebra of operators, by expanding the twelve terms. $\square$

For a finite-dimensional real $C^\infty$ Lie group, a left invariant derivation $D$ is determined by the point derivation $f \mapsto (Df)(1)$, and this identifies the two Lie algebras. The index of this edition has no declaration for this identification; the Mathlib file lists it as a TODO.

### Examples

**Example (Vector spaces).** Let $G = (E, +)$. Then $L_g(h) = g + h$ has differential the identity, and $X_v$ is the constant field $v$. Constant fields have zero derivative, so $[v, w] = 0$. The Lie algebra is abelian. The same holds for the circle, whose Lie algebra has dimension $1$, where every antisymmetric bracket is $0$.

**Example (Units of a Banach algebra).** Let $A$ be a complete normed algebra and $G = A^\times$, an open subset of $A$ with the chart $\mathrm{id}$. Then $L_g(h) = gh$ is the restriction of a continuous linear map, so $d(L_g)_1 v = gv$ and $X_v(g) = gv$. Its derivative is $DX_v(g)\,h = hv$. The bracket of Section 1 gives
$$[v, w] = DX_w(1)\,X_v(1) - DX_v(1)\,X_w(1) = vw - wv.$$
For $A = M_n(\mathbb{R})$ this is the Lie algebra $\mathfrak{gl}_n(\mathbb{R})$ with the commutator of matrices.

**Example (The affine group of the line).** Let $G = \{(a, b) : a > 0\} \subseteq \mathbb{R}^2$ with $(a, b)(c, d) = (ac, ad + b)$, the maps $x \mapsto ax + b$ under composition. The unit is $(1, 0)$. The translation $L_{(a, b)}(c, d) = (ac, ad + b)$ has differential $(h, k) \mapsto (ah, ak)$. So $X_1(a, b) = (a, 0)$ and $X_2(a, b) = (0, a)$ for the basis vectors $e_1, e_2$. Then $DX_2 \cdot X_1 = (0, a)$ and $DX_1 \cdot X_2 = (0, 0)$, so $[X_1, X_2] = (0, a) = X_2$ and $[e_1, e_2] = e_2$. This is the unique nonabelian Lie algebra of dimension $2$, up to isomorphism.

### The library around it

The file `Algebra.Monoid` defines `ContMDiffMul`, proves `contMDiff_mul_left`, defines left multiplication as the smooth map `smoothLeftMul` with the notation `𝑳`, and defines morphisms `ContMDiffMonoidMorphism`. The file `Algebra.SMul` treats smooth actions: `ContMDiffSMul I I' n G M` says that $G \times M \to M$ is $C^n$, and `Diffeomorph.smul` turns an element of $G$ into a diffeomorphism of $M$. The file `Algebra.Structures` defines smooth rings, `ContMDiffRing`, and the file `Algebra.SmoothFunctions` proves that smooth maps to such a ring form a ring, `ContMDiffMap.commRing`, and an algebra. The groups of units of complete normed algebras and the circle are Lie groups, by instances in the files `Instances.UnitsOfNormedAlgebra` and `Instances.Sphere` of Chapter 2.

::: mathlib
`LeftInvariantDerivation` · `Mathlib.Geometry.Manifold.Algebra.LeftInvariantDerivation`

`LeftInvariantDerivation I G` needs `[ContMDiffMul I ⊤ G]`. It is a structure of derivations of the algebra of `C^∞` functions `G → 𝕜` that are invariant under left translations. `LeftInvariantDerivation.left_invariant` writes the invariance with the differential `𝒅ₕ` of left multiplication and the evaluation `evalAt`. `commutator_apply` says `⁅X, Y⁆ f = X (Y f) - Y (X f)`, and `LeftInvariantDerivation.instLieAlgebra` is the instance. The docstring of `GroupLieAlgebra` explains that the point of view of the tangent space is more general: derivations agree with tangent vectors only for finite-dimensional $C^\infty$ real manifolds.

<?decl LeftInvariantDerivation?>
<?decl LeftInvariantDerivation.left_invariant?>
<?decl LeftInvariantDerivation.commutator_apply?>
<?decl LeftInvariantDerivation.instLieAlgebra?>
:::

::: mathlib
`mulInvariantVector_mlieBracket` · `Mathlib.Geometry.Manifold.GroupLieAlgebra`

This is the identity $X_{[v, w]} = [X_v, X_w]$ of the theorem above. It needs `[CompleteSpace E]`. The supporting lemmas are `mulInvariantVectorField_eq_mpullback`, the formula with the pullback by $x \mapsto g^{-1}x$, and `contMDiff_mulInvariantVectorField`, the smoothness of order `minSmoothness 𝕜 2`.

<?decl mulInvariantVector_mlieBracket?>
<?decl mulInvariantVectorField_eq_mpullback?>
<?decl contMDiff_mulInvariantVectorField?>
:::

Common errors of a learner:

- Expecting a Lie group to be a topological group by instance search. Use `topologicalGroup_of_lieGroup` explicitly.
- Looking for `LieAlgebra G`. The Lie algebra is the type `GroupLieAlgebra I G`, with an instance `LieAlgebra 𝕜 (GroupLieAlgebra I G)`.
- Assuming that the two Lie algebras of Mathlib are identified. The index of this edition has no declaration for it.

### Exercises

1. (A) Show that the right translations $R_g(h) = hg$ are diffeomorphisms of a Lie group.
2. (A) Compute the left invariant fields and the bracket of the torus $\mathbb{R}^2/\mathbb{Z}^2$.
3. (B) Show that the differential of the inversion at $1$ is $v \mapsto -v$. Hint: differentiate $m(g, g^{-1}) = 1$ at $g = 1$.
4. (B) Compute the Lie algebra of the group of upper triangular $2 \times 2$ real matrices with positive diagonal, and compare it with the affine group.
5. (B) Let $\varphi : G \to G'$ be a smooth group morphism. Show that $d\varphi_1$ maps $X_v$ to $X_{d\varphi_1 v}$ in the sense that $d\varphi_g X_v(g) = X_{d\varphi_1 v}(\varphi(g))$, and deduce that $d\varphi_1$ is a morphism of Lie algebras.
6. (C) Prove the Jacobi identity for commutators of operators by expanding the twelve terms.
7. (C) Let $G$ be the group of units of a Banach algebra $A$. Show that the right invariant fields are $Y_v(g) = vg$ and that their bracket at $1$ is $wv - vw$. Hint: use the formula of Section 1 as in the example.

### Notes and history

Lie introduced continuous transformation groups and their infinitesimal transformations in the 1870s. The abstract notion of a Lie algebra came later. In Mathlib, the Lie algebra of a group is the tangent space at the identity with the bracket of invariant vector fields; the docstring of the file prefers it to the derivation point of view because it works in all smoothness classes and over all fields.

### Reference

<?reference?>
