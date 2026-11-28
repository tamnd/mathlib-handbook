---
title: Simplicial objects and augmentations
kind: theory
modules:
  - Mathlib.AlgebraicTopology.CechNerve
  - Mathlib.AlgebraicTopology.ExtraDegeneracy
  - Mathlib.AlgebraicTopology.Reedy.Basic
  - Mathlib.AlgebraicTopology.Reedy.SimplexCategory
  - Mathlib.AlgebraicTopology.SimplicialCategory.Basic
  - Mathlib.AlgebraicTopology.SimplicialCategory.SimplicialObject
  - Mathlib.AlgebraicTopology.SimplicialObject.Basic
  - Mathlib.AlgebraicTopology.SimplicialObject.ChainHomotopy
  - Mathlib.AlgebraicTopology.SimplicialObject.Coskeletal
  - Mathlib.AlgebraicTopology.SimplicialObject.DeltaZeroIter
  - Mathlib.AlgebraicTopology.SimplicialObject.Homotopy
  - Mathlib.AlgebraicTopology.SimplicialObject.II
  - Mathlib.AlgebraicTopology.SimplicialObject.Op
  - Mathlib.AlgebraicTopology.SimplicialObject.Split
explains:
  E3: [CategoryTheory.SimplicialObject, CategoryTheory.SimplicialObject.δ, CategoryTheory.SimplicialObject.σ, CategoryTheory.SimplicialObject.Augmented, CategoryTheory.Arrow.augmentedCechNerve, CategoryTheory.SimplicialObject.Augmented.ExtraDegeneracy, CategoryTheory.SimplicialObject.Homotopy, CategoryTheory.Arrow.AugmentedCechNerve.extraDegeneracy]
  E2: [CategoryTheory.CosimplicialObject, CategoryTheory.CosimplicialObject.Augmented, CategoryTheory.simplicialCosimplicialEquiv, CategoryTheory.SimplicialObject.δ_comp_δ, CategoryTheory.SimplicialObject.δ_comp_σ_self, CategoryTheory.SimplicialObject.δ_comp_σ_succ, CategoryTheory.SimplicialObject.δ_comp_σ_of_le, CategoryTheory.SimplicialObject.δ_comp_σ_of_gt, CategoryTheory.SimplicialObject.σ_comp_σ, CategoryTheory.SimplicialObject.δ_naturality, CategoryTheory.SimplicialObject.whiskering, CategoryTheory.SimplicialObject.Truncated, CategoryTheory.SimplicialObject.truncation, CategoryTheory.SimplicialObject.Truncated.sk, CategoryTheory.SimplicialObject.Truncated.cosk, CategoryTheory.SimplicialObject.skAdj, CategoryTheory.SimplicialObject.coskAdj, CategoryTheory.SimplicialObject.Augmented.drop, CategoryTheory.SimplicialObject.Augmented.point, CategoryTheory.SimplicialObject.Augmented.toArrow, CategoryTheory.SimplicialObject.augment, CategoryTheory.Arrow.cechNerve, CategoryTheory.SimplicialObject.cechNerveEquiv, CategoryTheory.SimplicialObject.cechNerveAdjunction, CategoryTheory.Arrow.cechConerve, CategoryTheory.cechNerveTerminalFrom, CategoryTheory.SimplicialObject.Augmented.ExtraDegeneracy.homotopyEquiv, CategoryTheory.SimplicialObject.Augmented.ExtraDegeneracy.map, CategoryTheory.SimplicialObject.Augmented.ExtraDegeneracy.homotopy, CategoryTheory.SimplicialObject.Augmented.ExtraDegeneracy.section_, SSet.Augmented.StandardSimplex.extraDegeneracy, CategoryTheory.SimplicialObject.Homotopy.refl, CategoryTheory.SimplicialObject.Homotopy.toChainHomotopy, CategoryTheory.SimplicialObject.Splitting, CategoryTheory.SimplicialObject.Splitting.N, CategoryTheory.SimplicialObject.Splitting.IndexSet, CategoryTheory.SimplicialObject.Splitting.isColimit', CategoryTheory.SimplicialObject.Splitting.ofIso, CategoryTheory.SimplicialObject.Split, CategoryTheory.SimplicialObject.IsCoskeletal, CategoryTheory.SimplicialObject.isoCoskOfIsCoskeletal, HomotopicalAlgebra.ReedyStructure, HomotopicalAlgebra.ReedyStructure.deg, HomotopicalAlgebra.ReedyStructure.op, SimplexCategory.reedyStructure, CategoryTheory.SimplicialCategory, CategoryTheory.SimplicialCategory.sHom, CategoryTheory.SimplicialCategory.sHomComp, CategoryTheory.SimplicialObject.instSimplicialCategory, SimplexCategory.II, SimplicialObject.opFunctor, SimplicialObject.opEquivalence, CategoryTheory.SimplicialObject.δ₀Iter]
  E1: auto
families: []
requires: [V24.C01, V24.C02, V24.C04, V24.C05, V24.C08, V26.C02, V26.C03]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Simplicial objects and augmentations

### Overview

A simplicial object in a category $C$ is a functor $\Delta^{\mathrm{op}} \to C$. It has objects $X_n$, faces $d_i$ and degeneracies $s_j$ that satisfy the simplicial identities read backwards.

This section defines simplicial and cosimplicial objects and their augmentations. It builds the Čech nerve of a morphism and proves that an extra degeneracy makes the alternating face complex of an augmented object contractible. It proves that the Čech nerve of a split epimorphism has an extra degeneracy. It then reads simplicial homotopies, splittings, coskeleta, the Reedy structure on $\Delta$ and simplicial categories.

### Definitions

Fix a category $C$.

**Definition (Simplicial object).** A *simplicial object* in $C$ is a functor $X : \Delta^{\mathrm{op}} \to C$. Write $X_n = X([n])$, $d_i = X(\delta_i) : X_{n+1} \to X_n$ for $0 \leq i \leq n + 1$ and $s_j = X(\sigma_j) : X_n \to X_{n+1}$ for $0 \leq j \leq n$. A morphism of simplicial objects is a natural transformation. A *cosimplicial object* is a functor $\Delta \to C$, with *cofaces* $d^i = X(\delta_i)$ and *codegeneracies* $s^j = X(\sigma_j)$.

Since $X$ reverses arrows, the identities of Section 1 become, for $X$:

1. $d_i d_j = d_{j-1} d_i$ for $i < j$;
2. $d_i s_j = s_{j-1} d_i$ for $i < j$;
3. $d_j s_j = \mathrm{id} = d_{j+1} s_j$;
4. $d_i s_j = s_j d_{i-1}$ for $i > j + 1$;
5. $s_i s_j = s_{j+1} s_i$ for $i \leq j$.

::: mathlib
`CategoryTheory.SimplicialObject` · `Mathlib.AlgebraicTopology.SimplicialObject.Basic`

`SimplicialObject C` is the abbreviation `SimplexCategoryᵒᵖ ⥤ C`, and `X _⦋n⦌` is the object $X_n$. `X.δ i : X _⦋n + 1⦌ ⟶ X _⦋n⦌` is `X.map (SimplexCategory.δ i).op`, and `X.σ i : X _⦋n⦌ ⟶ X _⦋n + 1⦌` is `X.map (SimplexCategory.σ i).op`. The identities are `δ_comp_δ`, `δ_comp_σ_of_le`, `δ_comp_σ_self`, `δ_comp_σ_succ`, `δ_comp_σ_of_gt` and `σ_comp_σ`; for example `δ_comp_σ_self` is `X.σ i ≫ X.δ i.castSucc = 𝟙 _`. `δ_naturality` says that a morphism commutes with the faces. `whiskering` composes with a functor $C \to D$. `CosimplicialObject C` is `SimplexCategory ⥤ C`, with `X ^⦋n⦌` for $X^n$, and `simplicialCosimplicialEquiv` identifies `(SimplicialObject C)ᵒᵖ` with `CosimplicialObject Cᵒᵖ`.

<?decl CategoryTheory.SimplicialObject?>
:::

**Definition (Augmented simplicial object).** An *augmented simplicial object* is a simplicial object $X$ with an object $X_{-1}$ and a morphism $\varepsilon : X_0 \to X_{-1}$ with $\varepsilon d_0 = \varepsilon d_1$ on $X_1$. Equivalently, it is a natural transformation from $X$ to the constant simplicial object at $X_{-1}$.

The two forms agree. A natural transformation $X \to \mathrm{const}\, X_{-1}$ has components $\varepsilon_n : X_n \to X_{-1}$, and naturality for the map $[0] \to [n]$ at $0$ gives $\varepsilon_n = \varepsilon_0 v_n$, where $v_n : X_n \to X_0$ is the induced map. So $\varepsilon_0$ determines all components. Naturality at $\delta_0, \delta_1 : [0] \to [1]$ gives $\varepsilon_0 d_0 = \varepsilon_1 = \varepsilon_0 d_1$. Conversely, if $\varepsilon d_0 = \varepsilon d_1$, then $\varepsilon v_n$ does not depend on the choice of vertex, since any two vertices of $[n]$ are joined by an edge, and the family $\varepsilon v_n$ is natural.

::: mathlib
`CategoryTheory.SimplicialObject.Augmented` · `Mathlib.AlgebraicTopology.SimplicialObject.Basic`

`Augmented C` is the comma category `Comma (𝟭 (SimplicialObject C)) (const C)`. For `X : Augmented C`, `X.left` is the simplicial object, `X.right` is $X_{-1}$, and `X.hom : X.left ⟶ (const C).obj X.right` is the augmentation. `Augmented.drop` and `Augmented.point` are the two projections, `Augmented.toArrow` sends `X` to the arrow $\varepsilon : X_0 \to X_{-1}$, and `augment X X₀ f w` builds an augmented object from `f : X _⦋0⦌ ⟶ X₀` and the condition `w` on the two faces.

<?decl CategoryTheory.SimplicialObject.Augmented?>
:::

**Definition (Čech nerve).** Let $f : Y \to Z$ be a morphism in a category with finite wide pullbacks over $Z$. The *Čech nerve* of $f$ is the simplicial object with $$\check C(f)_n = Y \times_Z Y \times_Z \cdots \times_Z Y \qquad (n + 1 \text{ factors}).$$ A morphism $\theta : [m] \to [n]$ of $\Delta$ acts by $\check C(f)_n \to \check C(f)_m$, $(y_0, \dots, y_n) \mapsto (y_{\theta(0)}, \dots, y_{\theta(m)})$ in terms of generalized elements. So $d_i$ forgets the factor $y_i$ and $s_j$ repeats the factor $y_j$. The map $f$ gives an augmentation $\varepsilon = f : \check C(f)_0 = Y \to Z$.

**Definition (Extra degeneracy).** An *extra degeneracy* of an augmented simplicial object $\varepsilon : X \to X_{-1}$ is a morphism $e' : X_{-1} \to X_0$ and morphisms $e_n : X_n \to X_{n+1}$ for $n \geq 0$ with $$\varepsilon e' = \mathrm{id}, \quad d_1 e_0 = e' \varepsilon, \quad d_0 e_n = \mathrm{id}, \quad d_{i+1} e_{n+1} = e_n d_i, \quad s_{j+1} e_n = e_{n+1} s_j.$$ The maps $e_n$ act as one more degeneracy $s_{-1}$ that inserts a new vertex in front. Mathlib writes $s'$ and $s$ for $e'$ and $e$.

**Definition (Simplicial homotopy).** Let $f, g : X \to Y$ be morphisms of simplicial objects. A *simplicial homotopy* from $f$ to $g$ is a family $h_j : X_n \to Y_{n+1}$ for $0 \leq j \leq n$ with $d_0 h_0 = g$, $d_{n+1} h_n = f$, and the rules $d_i h_j = h_{j-1} d_i$ for $i < j$, $d_{j+1} h_{j+1} = d_{j+1} h_j$, $d_i h_j = h_j d_{i-1}$ for $i > j + 1$, $s_i h_j = h_{j+1} s_i$ for $i \leq j$ and $s_i h_j = h_j s_{i-1}$ for $i > j$.

**Definition (Splitting).** A *splitting* of a simplicial object $X$ in a category with coproducts is a family of objects $N_n$ and morphisms $\iota_n : N_n \to X_n$ such that for each $n$ the map $$\coprod_{p : [n] \twoheadrightarrow [k]} N_k \longrightarrow X_n,$$ which is $X(p)\, \iota_k$ on the summand of the surjection $p$, is an isomorphism.

**Definition (Coskeletal).** Let $\mathrm{tr}_n$ be the restriction from simplicial objects to functors on $\Delta_{\leq n}^{\mathrm{op}}$. When its right adjoint $\mathrm{cosk}_n$ exists, $X$ is *$n$-coskeletal* if the unit $X \to \mathrm{cosk}_n \mathrm{tr}_n X$ is an isomorphism.

### Theorems and proofs

**Theorem (Extra degeneracy and contractibility).** Let $C$ be preadditive and let $\varepsilon : X \to X_{-1}$ be an augmented simplicial object with an extra degeneracy $(e', e_n)$. Let $K$ be the augmented complex $$\cdots \to X_2 \xrightarrow{\partial} X_1 \xrightarrow{\partial} X_0 \xrightarrow{\varepsilon} X_{-1} \to 0, \qquad \partial = \sum_{i=0}^{n+1} (-1)^i d_i : X_{n+1} \to X_n.$$ Then $K$ is contractible: the maps $e'$ and $e_n$ form a chain homotopy from the identity of $K$ to $0$.

*Proof.* Put $h_{-1} = e'$ and $h_n = e_n$. The claim is $\partial h + h \partial = \mathrm{id}$ in each degree, with $\varepsilon$ in the part of $\partial$ on $X_0$.

In degree $-1$: $\varepsilon e' = \mathrm{id}$.

In degree $0$: $\partial e_0 = d_0 e_0 - d_1 e_0 = \mathrm{id} - e' \varepsilon$, so $\partial h_0 + h_{-1} \varepsilon = \mathrm{id}$.

In degree $n \geq 1$: $$\partial e_n = d_0 e_n + \sum_{i=0}^{n} (-1)^{i+1} d_{i+1} e_n = \mathrm{id} - \sum_{i=0}^{n} (-1)^i e_{n-1} d_i = \mathrm{id} - e_{n-1} \partial,$$ by the rules $d_0 e_n = \mathrm{id}$ and $d_{i+1} e_n = e_{n-1} d_i$. So $\partial h_n + h_{n-1} \partial = \mathrm{id}$. $\square$

The proof uses only the face rules of the extra degeneracy. The rule with the degeneracies of $X$ is what makes the maps $e_n$ into a simplicial homotopy, and not only a chain homotopy.

**Theorem (Čech nerve of a split epimorphism).** Let $f : Y \to Z$ have a section $t : Z \to Y$, $f t = \mathrm{id}_Z$. Then the augmented Čech nerve of $f$ has an extra degeneracy, given by $e' = t$ and $$e_n(y_0, \dots, y_n) = (t f y_0, y_0, \dots, y_n).$$

*Proof.* The map $e_n$ is well defined: all the factors $t f y_0, y_0, \dots, y_n$ have the same image $f y_0$ in $Z$, since $f t f = f$. Now check the rules on generalized elements. First $\varepsilon e' = f t = \mathrm{id}$. Next $d_1 e_0(y_0) = t f y_0 = e' \varepsilon(y_0)$. The face $d_0$ forgets the first factor, so $d_0 e_n = \mathrm{id}$. For $0 \leq i \leq n + 1$, $d_{i+1} e_{n+1}$ forgets $y_i$ from $(t f y_0, y_0, \dots, y_{n+1})$, and $e_n d_i$ forgets $y_i$ first and then puts $t f$ of the new first factor in front. When $i \geq 1$ the first factor is still $y_0$. When $i = 0$ the new first factor is $y_1$, and $t f y_1 = t f y_0$ since $f y_1 = f y_0$. So the two sides agree. The rule $s_{j+1} e_n = e_{n+1} s_j$ holds in the same way: both sides repeat $y_j$ and put $t f y_0$ in front. $\square$

By the previous theorem, in a preadditive category with these pullbacks the augmented complex of the Čech nerve of a split epimorphism is contractible. This is the base of descent theory: after pullback along a cover, the cover splits.

**Proposition (The Reedy structure on Δ).** Give $[n]$ the degree $n$. Each surjection of $\Delta$ that is not an identity lowers the degree, each injection that is not an identity raises it, and each morphism factors uniquely as a surjection followed by an injection.

*Proof.* A surjection $[n] \to [m]$ has $m \leq n$. If $m = n$ it is a monotone bijection, so it is the identity by Section 1. The same argument applies to injections, with $n \leq m$. The unique factorization is the epi-mono factorization theorem of Section 1. $\square$

**Proposition (Coskeleta and adjunctions).** If $C$ has finite limits, then $\mathrm{tr}_n$ has a right adjoint $\mathrm{cosk}_n$ given by right Kan extension, and if $C$ has finite colimits it has a left adjoint $\mathrm{sk}_n$ given by left Kan extension.

*Proof.* The functor $\mathrm{tr}_n$ is precomposition with the inclusion $i : \Delta_{\leq n}^{\mathrm{op}} \to \Delta^{\mathrm{op}}$. For a functor $Y$ on $\Delta_{\leq n}^{\mathrm{op}}$, the pointwise right Kan extension along $i$ at $[m]$ is the limit of $Y$ over the opposite of the slice category $\Delta_{\leq n} / [m]$, whose objects are the maps $[k] \to [m]$ with $k \leq n$. This category has finitely many objects and finitely many morphisms, so the limit exists. A functor with a pointwise right Kan extension at every object gives a right adjoint to precomposition. The left adjoint is dual, with the colimit over $([m] / \Delta_{\leq n})$ in $\Delta^{\mathrm{op}}$. $\square$

### Examples

**Example (The standard simplex as an augmented simplicial set).** Let $X = \Delta[n]$, with $X_m$ the set of monotone maps $[m] \to [n]$, augmented to a point. An extra degeneracy is given by $e'(\ast) = 0$, the vertex $0$, and $e_m(a) = (0, a(0), \dots, a(m))$, which puts the vertex $0$ in front. Then $d_0 e_m(a) = a$, $d_1 e_0(a) = 0 = e' \varepsilon(a)$, and $d_{i+1} e_{m+1}(a)$ and $e_m d_i(a)$ both forget $a(i)$ and put $0$ in front. By the theorem the augmented chain complex $\mathbb{Z}[X] \to \mathbb{Z}$ is contractible, so $\Delta[n]$ has the homology of a point.

**Example (Čech nerve of a surjection of sets).** Let $f : Y \to Z$ be a surjection of sets and choose $t$ with $f t = \mathrm{id}$. Then $\check C(f)_n$ is the set of $(n+1)$-tuples in one fibre of $f$, and $e_n$ puts $t(f y_0)$ in front. Take $Z$ a point and $Y = \{a, b\}$. Then $\check C(f)_n = Y^{n+1}$, the simplicial set $E\{a, b\}$, and $t(\ast) = a$ gives $e_n(y) = (a, y_0, \dots, y_n)$. The complex $\mathbb{Z}[Y^{n+1}]$ with the alternating sum of the faces is then contractible to $\mathbb{Z}$.

**Example (The constant homotopy).** For $f : X \to Y$ put $h_j = s_j f : X_n \to Y_{n+1}$. Then $d_0 h_0 = d_0 s_0 f = f$ and $d_{n+1} h_n = d_{n+1} s_n f = f$ by identity (3), and the other rules are the identities (2), (4) and (5). So $h$ is a simplicial homotopy from $f$ to $f$.

**Counterexample (A simplicial object that is not 0-coskeletal).** For a simplicial set $X$, $(\mathrm{cosk}_0 \mathrm{tr}_0 X)_1 = X_0 \times X_0$, and the unit sends a $1$-simplex to its pair of vertices $(d_1 x, d_0 x)$. For $X = \Delta[1] / \partial\Delta[1]$, the circle with one vertex and one nondegenerate edge, $X_0$ is a point and $X_1$ has two elements. So the unit is not injective in degree $1$, and $X$ is not $0$-coskeletal. The simplicial set $E\{a, b\}$ of the previous example is $0$-coskeletal: its unit is the identity of $Y^{n+1}$ in each degree.

```lean
open CategoryTheory Simplicial in
example {C : Type*} [Category C] (X : SimplicialObject C) (n : ℕ) (i : Fin (n + 1)) :
    X.σ i ≫ X.δ i.castSucc = 𝟙 _ :=
  X.δ_comp_σ_self
```

### The library around it

::: mathlib
`CategoryTheory.Arrow.augmentedCechNerve` · `Mathlib.AlgebraicTopology.CechNerve`

For `f : Arrow C` with the needed wide pullbacks, `f.cechNerve` is the Čech nerve, with `f.cechNerve _⦋n⦌` the wide pullback of `n + 1` copies of `f.hom`, and `f.augmentedCechNerve` adds `f.right` as $X_{-1}$. `SimplicialObject.cechNerveAdjunction` says that `augmentedCechNerve` is right adjoint to `Augmented.toArrow`, through the bijection `cechNerveEquiv`: a map from an augmented object $X$ to $\check C(f)$ is the same as a map from the arrow $X_0 \to X_{-1}$ to $f$. `cechConerve` is the dual construction, and `cechNerveTerminalFrom` is the Čech nerve of $X \to \ast$ built from finite products.

<?decl CategoryTheory.Arrow.augmentedCechNerve?>
:::

::: mathlib
`CategoryTheory.SimplicialObject.Augmented.ExtraDegeneracy` · `Mathlib.AlgebraicTopology.ExtraDegeneracy`

The fields are `s'`, `s n`, `s'_comp_ε`, `s₀_comp_δ₁`, `s_comp_δ₀`, `s_comp_δ` and `s_comp_σ`, written with `≫`; for example `s_comp_δ₀` is `s n ≫ X.left.δ 0 = 𝟙 _`. `ExtraDegeneracy.map` transports an extra degeneracy along a functor, `section_` is the induced map from the constant object, and `ExtraDegeneracy.homotopy` is a `SimplicialObject.Homotopy` from `X.hom ≫ section_` to the identity. `homotopyEquiv` is the first theorem: in a preadditive category with a zero object, the augmentation from the alternating face map complex of `X.left` to `X.right` in degree $0$ is a homotopy equivalence. `Arrow.AugmentedCechNerve.extraDegeneracy` is the second theorem, for an arrow with a `SplitEpi`, and `SSet.Augmented.StandardSimplex.extraDegeneracy` is the first example.

<?decl CategoryTheory.SimplicialObject.Augmented.ExtraDegeneracy?>
:::

::: mathlib
`CategoryTheory.SimplicialObject.Homotopy` · `Mathlib.AlgebraicTopology.SimplicialObject.Homotopy`

`Homotopy f g` has the field `h i : X _⦋n⦌ ⟶ Y _⦋n + 1⦌` for `i : Fin (n + 1)`, with `h_zero_comp_δ_zero : h 0 ≫ Y.δ 0 = g.app _` and `h_last_comp_δ_last : h (Fin.last n) ≫ Y.δ (Fin.last (n + 1)) = f.app _`, and five more fields for the other rules. `Homotopy.refl` is the constant homotopy of the example. In the module `ChainHomotopy`, `Homotopy.toChainHomotopy` sends a simplicial homotopy to a chain homotopy between the maps of alternating face map complexes, with components $-\sum_i (-1)^i h_i$.

<?decl CategoryTheory.SimplicialObject.Homotopy?>
:::

`SimplicialObject.Splitting` has the fields `N`, `ι` and `isColimit'`, where `Splitting.IndexSet Δ` is the set of surjections out of `Δ`; `Splitting.ofIso` transports a splitting, and `SimplicialObject.Split C` is the category of simplicial objects with a chosen splitting, which Chapter 5 uses for the Dold-Kan correspondence. `SimplicialObject.Truncated C n` is the category of truncated objects, `truncation n` is $\mathrm{tr}_n$, and `skAdj` and `coskAdj` are the two adjunctions of the proposition, with `Truncated.sk` and `Truncated.cosk`. `IsCoskeletal X n` asks that `X` is a right Kan extension of its truncation, and `isoCoskOfIsCoskeletal` gives `X ≅ (cosk n).obj X`.

`HomotopicalAlgebra.ReedyStructure W₁ W₂ α` has the degree `deg`, the two strict inequalities and unique factorization, and `ReedyStructure.op` is the opposite structure. `SimplexCategory.reedyStructure` is the proposition, with `W₁` the epimorphisms and `W₂` the monomorphisms. The module header lists the Reedy model structure on diagram categories as work to do; the index of this edition has no declaration for it.

`SimplicialCategory C` is a category enriched over `SSet` whose enriched hom has the ordinary hom as its set of $0$-simplices; `sHom K L` is the simplicial set of maps and `sHomComp` the composition. The instance `SimplicialObject.instSimplicialCategory` makes `SimplicialObject D` a simplicial category, and so simplicial sets form one. `SimplicialObject.opFunctor` and `opEquivalence` are the involution induced by `SimplexCategory.rev`, `δ₀Iter` iterates $d_0$, and `SimplexCategory.II` is the cosimplicial object of Gabriel and Zisman in $\Delta^{\mathrm{op}}$, which exchanges faces and degeneracies.

Common errors of a learner:

- `X.δ i ≫ X.δ j` means $d_j d_i$. The identities for `X` have the arrows in the opposite order to those of `SimplexCategory`, since `X` is contravariant.
- `X _⦋n⦌` is notation for `X.obj (op ⦋n⦌)`; a goal can show either form.
- The point of an augmented object is `X.right` and the simplicial object is `X.left`, since `Augmented C` is a comma category.
- The constant homotopy needs the degeneracies. A family $h_j$ with only the face rules is a chain homotopy, not a simplicial one.

### Exercises

1. (A) Write out the simplicial identities that involve only $X_0$, $X_1$ and $X_2$. *Hint:* in degree $0$ only identity (3) appears.
2. (A) For the Čech nerve of $Y \to \ast$ in sets, describe $\check C_n$, $d_i$ and $s_j$. *Hint:* $\check C_n = Y^{n+1}$.
3. (B) Show that if $X$ has an extra degeneracy, then $\varepsilon : X_0 \to X_{-1}$ is a split epimorphism and $X_{-1}$ is the coequalizer of $d_0, d_1 : X_1 \to X_0$. *Hint:* $e'$ and $e_0$ make $\varepsilon$ a split coequalizer of $d_0$ and $d_1$.
4. (B) Let $\varepsilon : X \to X_{-1}$ be an augmented simplicial set with an extra degeneracy. Show that each fibre of $\varepsilon_0 : X_0 \to X_{-1}$ has one connected component, for the relation given by edges. *Hint:* join $x$ to $e' \varepsilon x$ by the edge $e_0 x$.
5. (B) Show that each simplicial set has a splitting with $N_n$ the set of nondegenerate $n$-simplices *Hint:* use the Eilenberg-Zilber lemma of Section 3.
6. (C) Let $H : X \times \Delta[1] \to Y$ restrict to $f$ on $X \times \{0\}$ and to $g$ on $X \times \{1\}$. Show that $h_j(x) = H(s_j x, \tau_j)$, with $\tau_j : [n+1] \to [1]$ equal to $0$ exactly on $\{0, \dots, j\}$, is a simplicial homotopy from $f$ to $g$. *Hint:* $\tau_0 \delta_0$ is the constant map at $1$ and $\tau_n \delta_{n+1}$ is the constant map at $0$.

### Notes and history

Simplicial objects come from the semi-simplicial complexes of Eilenberg and Zilber (1950). Kan (1955 and 1958) developed the combinatorial homotopy theory of simplicial sets, with simplicial homotopies. Gabriel and Zisman (1967) give the construction `SimplexCategory.II`, and Mathlib cites them. Mathlib cites Riehl and Verity for Reedy structures.

The Mathlib Authors of `SimplicialObject.Basic` are Johan Commelin, Kim Morrison and Adam Topaz. `CechNerve` is by Adam Topaz. `ExtraDegeneracy`, `SimplicialObject.II`, `SimplicialObject.Op`, `SimplicialObject.DeltaZeroIter`, `SimplicialObject.Split` and the two `SimplicialCategory` files are by Joël Riou. `SimplicialObject.Homotopy` and `SimplicialObject.ChainHomotopy` are by Fabian Odermatt. `SimplicialObject.Coskeletal` is by Mario Carneiro, Emily Riehl and Joël Riou. `Reedy.Basic` is by Joël Riou, Nima Rasekh and Aras Ergus, and `Reedy.SimplexCategory` by Joël Riou and Julian Kuelshammer.

### Reference

<?reference?>
