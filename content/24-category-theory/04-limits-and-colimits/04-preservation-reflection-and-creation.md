---
title: Preservation, reflection and creation
kind: theory
modules:
  - Mathlib.CategoryTheory.Limits.Preserves.Basic
  - Mathlib.CategoryTheory.Limits.Preserves.Limits
  - Mathlib.CategoryTheory.Limits.Creates
  - Mathlib.CategoryTheory.Limits.Yoneda
  - Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
explains:
  E3: [CategoryTheory.Limits.PreservesLimit, CategoryTheory.Limits.ReflectsLimit, CategoryTheory.CreatesLimit, CategoryTheory.coyonedaJointlyReflectsLimits, CategoryTheory.Limits.combinedIsLimit]
  E2: [CategoryTheory.Functor.mapCone, CategoryTheory.Limits.PreservesLimit.preserves, CategoryTheory.Limits.PreservesLimitsOfShape, CategoryTheory.Limits.PreservesLimitsOfSize, CategoryTheory.Limits.PreservesLimits, CategoryTheory.Limits.isLimitOfPreserves, CategoryTheory.Limits.ReflectsLimits, CategoryTheory.Limits.isLimitOfReflects, CategoryTheory.Limits.reflectsLimit_of_reflectsIsomorphisms, CategoryTheory.Limits.PreservesColimit, CategoryTheory.Limits.PreservesColimits, CategoryTheory.Limits.ReflectsColimit, CategoryTheory.preservesLimitIso, CategoryTheory.CreatesLimitsOfShape, CategoryTheory.CreatesLimits, CategoryTheory.LiftableCone, CategoryTheory.LiftsToLimit, CategoryTheory.hasLimit_of_created, CategoryTheory.preservesLimit_of_createsLimit_and_hasLimit, CategoryTheory.createsLimitOfReflectsIso, CategoryTheory.coyoneda_preservesLimit, CategoryTheory.yoneda_preservesLimits, CategoryTheory.Limits.Cone.isLimitCoyonedaEquiv, CategoryTheory.Limits.combineCones, CategoryTheory.Limits.functorCategoryHasLimitsOfShape, CategoryTheory.Limits.limitObjIsoLimitCompEvaluation, CategoryTheory.Limits.evaluationJointlyReflectsLimits, CategoryTheory.Limits.evaluation_preservesLimit]
  E1: auto
families: []
requires: [V24.C01, V24.C02, V24.C03, V05, V13]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Preservation, reflection and creation

### Overview

A functor $G : C \to D$ sends a cone over a diagram $K$ to a cone over $G \circ K$. This section asks when the image of a limit is a limit, and when a cone whose image is a limit is itself a limit. These are preservation and reflection. A third property, creation, explains why limits of groups, rings and modules are computed on the underlying sets. The main theorems: the functors $\mathrm{Hom}(X, -)$ preserve limits and jointly detect them, limits in a functor category are computed pointwise, and a functor that reflects isomorphisms and preserves a limit also reflects it. Chapter 5 adds the main source of examples: a right adjoint preserves all limits.

### Definitions

Fix a diagram $K : J \to C$ and a functor $G : C \to D$. For a cone $c = (X, \pi)$ over $K$, the *image cone* $G(c)$ is $(G(X), (G(\pi_j))_j)$. It is a cone over $G \circ K$, since $G(K(u)) \circ G(\pi_j) = G(K(u) \circ \pi_j) = G(\pi_k)$.

**Definition (Preservation).** $G$ *preserves limits of $K$* if $G(c)$ is a limit cone for every limit cone $c$ over $K$.

**Definition (Reflection).** $G$ *reflects limits of $K$* if a cone $c$ over $K$ is a limit cone whenever $G(c)$ is a limit cone.

**Definition (Creation).** $G$ *creates limits of $K$* if it reflects limits of $K$ and, for each limit cone $d$ over $G \circ K$, there is a cone $c$ over $K$ with $G(c) \cong d$ as cones.

A functor *reflects isomorphisms* if $G(f)$ is an isomorphism only when $f$ is one. The forgetful functor from groups to sets has this property: a bijective homomorphism has a homomorphic inverse.

::: mathlib
`CategoryTheory.Limits.PreservesLimit` · `Mathlib.CategoryTheory.Limits.Preserves.Basic`

The image cone is `G.mapCone c`. `PreservesLimit K G` is a class in `Prop` with one field, `preserves {c} (hc : IsLimit c) : Nonempty (IsLimit (G.mapCone c))`. Since `IsLimit` is data, the field gives only `Nonempty`; the function `isLimitOfPreserves G hc` chooses the term. The classes `PreservesLimitsOfShape J G`, `PreservesLimitsOfSize G` and `PreservesLimits G` quantify over diagrams, and the colimit forms are `PreservesColimit` and `PreservesColimits`. For the chosen limits, `preservesLimitIso G K : G.obj (limit K) ≅ limit (K ⋙ G)`.

<?decl CategoryTheory.Limits.PreservesLimit?>
:::

::: mathlib
`CategoryTheory.Limits.ReflectsLimit` · `Mathlib.CategoryTheory.Limits.Preserves.Basic`

`ReflectsLimit K G` has the field `reflects`, which sends `IsLimit (G.mapCone c)` to `Nonempty (IsLimit c)`; `isLimitOfReflects` chooses the term. `ReflectsLimits` and `ReflectsColimit` are the other forms.

<?decl CategoryTheory.Limits.ReflectsLimit?>
:::

::: mathlib
`CategoryTheory.CreatesLimit` · `Mathlib.CategoryTheory.Limits.Creates`

`CreatesLimit K G` extends `ReflectsLimit K G` with `lifts : ∀ c, IsLimit c → LiftableCone K G c`. A `LiftableCone K G c` holds a cone `liftedCone : Cone K` and an isomorphism `validLift : G.mapCone liftedCone ≅ c`. The lift is asked only up to isomorphism, not equality, so the notion is stable under isomorphism of categories. These declarations are in the namespace `CategoryTheory`, not `CategoryTheory.Limits`.

<?decl CategoryTheory.CreatesLimit?>
:::

### Theorems and proofs

**Theorem (Hom functors preserve limits).** For each object $X$ of $C$, the functor $\mathrm{Hom}(X, -) : C \to \mathbf{Set}$ preserves all limits. Conversely, a cone $c$ over $K$ is a limit if $\mathrm{Hom}(X, c)$ is a limit cone in $\mathbf{Set}$ for every $X$.

*Proof.* Let $c = (L, \pi)$ be a cone over $K$. By the theorem on limits in sets (Section 2), the limit of $\mathrm{Hom}(X, K(-))$ is the set of compatible families $(f_j)$ with $f_j : X \to K(j)$ and $K(u) \circ f_j = f_k$. These are the cones over $K$ with apex $X$. The image cone $\mathrm{Hom}(X, c)$ has apex $\mathrm{Hom}(X, L)$ and projections $f \mapsto \pi_j \circ f$. The induced map to the limit in sets is the map $\Phi_X : f \mapsto (\pi_j \circ f)_j$ of Section 1. A cone in $\mathbf{Set}$ is a limit if and only if its map to the explicit limit cone is a bijection, by the uniqueness of limits. So $\mathrm{Hom}(X, c)$ is a limit if and only if $\Phi_X$ is bijective. By the theorem that limits represent cones (Section 1), $c$ is a limit if and only if $\Phi_X$ is bijective for all $X$. Both statements follow. $\square$

So a limit is a cone that every $\mathrm{Hom}(X, -)$ sees as a limit. In the language of Chapter 3, the covariant Yoneda functor detects limits, and the Yoneda embedding $C \to [C^{\mathrm{op}}, \mathbf{Set}]$ preserves them.

**Theorem (Limits in functor categories).** Let $F : J \to [A, C]$, where $[A, C]$ is the category of functors $A \to C$ (Chapter 2). Suppose that for each object $a$ of $A$, the diagram $F_a = F(-)(a) : J \to C$ has a limit cone $(L(a), \pi^a)$. Then there is a unique way to make $L$ a functor $A \to C$ such that the maps $\pi_j : L \Rightarrow F(j)$, with components $\pi^a_j$, are natural. With this structure, $(L, \pi)$ is a limit cone over $F$.

*Proof.* *The functor.* Let $\phi : a \to b$ in $A$. The maps $F(j)(\phi) \circ \pi^a_j : L(a) \to F(j)(b)$ form a cone over $F_b$: for $u : j \to k$, naturality of $F(u)$ gives $F(u)_b \circ F(j)(\phi) \circ \pi^a_j = F(k)(\phi) \circ F(u)_a \circ \pi^a_j = F(k)(\phi) \circ \pi^a_k$. Let $L(\phi) : L(a) \to L(b)$ be the unique map with $\pi^b_j \circ L(\phi) = F(j)(\phi) \circ \pi^a_j$. This equation says that $\pi_j$ is natural, and it determines $L(\phi)$, which proves the uniqueness. Both $L(1_a)$ and $1_{L(a)}$ satisfy the equation for $\phi = 1_a$, and both $L(\psi \circ \phi)$ and $L(\psi) \circ L(\phi)$ satisfy it for $\psi \circ \phi$. Maps into a limit are determined by their components, so $L$ is a functor.

*The cone.* For $u : j \to k$, $F(u) \circ \pi_j = \pi_k$ holds at each $a$, since $\pi^a$ is a cone.

*The universal property.* Let $(M, \sigma)$ be a cone over $F$, with $\sigma_j : M \Rightarrow F(j)$. For each $a$, $(M(a), (\sigma_{j,a})_j)$ is a cone over $F_a$, so there is a unique $\theta_a : M(a) \to L(a)$ with $\pi^a_j \circ \theta_a = \sigma_{j,a}$. For $\phi : a \to b$, compose with $\pi^b_j$:
$$\pi^b_j \circ L(\phi) \circ \theta_a = F(j)(\phi) \circ \sigma_{j,a} = \sigma_{j,b} \circ M(\phi) = \pi^b_j \circ \theta_b \circ M(\phi).$$
So $L(\phi) \circ \theta_a = \theta_b \circ M(\phi)$, and $\theta$ is natural. It satisfies $\pi_j \circ \theta = \sigma_j$, and it is unique because each component $\theta_a$ is. $\square$

In particular, if $C$ is complete, then $[A, C]$ is complete, and the evaluation functors $[A, C] \to C$ preserve limits. Presheaf categories $[A^{\mathrm{op}}, \mathbf{Set}]$ are complete and cocomplete, by the dual statement.

**Theorem (Creation gives limits).** Suppose $G$ creates limits of $K$ and $G \circ K$ has a limit. Then $K$ has a limit, and $G$ preserves limits of $K$.

*Proof.* Let $d$ be a limit cone over $G \circ K$. By creation, there is a cone $c$ over $K$ with $G(c) \cong d$. A cone isomorphic to a limit cone is a limit cone (Section 1, Exercise 3), so $G(c)$ is a limit, and by reflection $c$ is a limit. Now let $c'$ be any limit cone over $K$. By uniqueness of limits, $c' \cong c$ as cones, so $G(c') \cong G(c)$, and $G(c')$ is a limit. $\square$

**Theorem (Conservative functors reflect limits).** Suppose $K$ has a limit cone $\ell$, $G$ preserves limits of $K$, and $G$ reflects isomorphisms. Then $G$ reflects limits of $K$.

*Proof.* Let $c = (X, \sigma)$ be a cone over $K$ with $G(c)$ a limit. Let $u : X \to \ell$ be the unique map of cones $c \to \ell$. Then $G(u)$ is a map of cones $G(c) \to G(\ell)$. Both are limit cones, since $G$ preserves $\ell$, so by the uniqueness theorem of Section 1, $G(u)$ is an isomorphism. Hence $u$ is an isomorphism, and its inverse is a map of cones. So $c \cong \ell$ in the category of cones, and $c$ is a limit. $\square$

::: mathlib
`CategoryTheory.coyonedaJointlyReflectsLimits` · `Mathlib.CategoryTheory.Limits.Yoneda`

The first theorem is the instance `coyoneda_preservesLimit F X : PreservesLimit F (coyoneda.obj X)` and the definition `coyonedaJointlyReflectsLimits F c hc : IsLimit c`, from `IsLimit ((coyoneda.obj X).mapCone c)` for all `X`. `yoneda_preservesLimits` is the statement for the Yoneda embedding. The third and fourth theorems are `hasLimit_of_created`, `preservesLimit_of_createsLimit_and_hasLimit` and `reflectsLimit_of_reflectsIsomorphisms`. The constructor `createsLimitOfReflectsIso` builds `CreatesLimit` for a functor that reflects isomorphisms from lifts of limit cones alone.

<?decl CategoryTheory.coyonedaJointlyReflectsLimits?>
:::

::: mathlib
`CategoryTheory.Limits.combinedIsLimit` · `Mathlib.CategoryTheory.Limits.FunctorCategory.Basic`

For `F : J ⥤ K ⥤ C` and a limit cone of `F.flip.obj k` for each `k`, `combineCones F c` is the cone of the theorem, and `combinedIsLimit F c` proves it is a limit. The proof uses `evaluationJointlyReflectsLimits`. From it come the instance `functorCategoryHasLimitsOfShape`, the instance `evaluation_preservesLimit`, and `limitObjIsoLimitCompEvaluation : (limit F).obj k ≅ limit (F ⋙ (evaluation K C).obj k)`.

<?decl CategoryTheory.Limits.combinedIsLimit?>
:::

### Examples

**Example (Groups).** The forgetful functor $U : \mathbf{Grp} \to \mathbf{Set}$ creates limits. Let $K : J \to \mathbf{Grp}$ and let $L \subseteq \prod_j U K(j)$ be the set of compatible families. It is a subgroup of the direct product, since each $K(u)$ is a homomorphism. With this group structure, the projections are homomorphisms. For a cone of groups $(H, \sigma)$, the unique map of sets $h \mapsto (\sigma_j(h))$ is a homomorphism, since its components are. So $L$ is a limit in groups, and its image is the limit of sets. By the theorem on conservative functors, $U$ also reflects limits. Hence limits in groups are computed on the underlying sets, as in Section 2.

**Counterexample (Groups and colimits).** $U$ does not preserve colimits. The initial group is the trivial group, but $U$ sends it to a one-point set, not to the initial set $\emptyset$. The coproduct $\mathbb{Z}/2 * \mathbb{Z}/2$ (Section 3) is infinite, but the coproduct of the underlying sets has $4$ elements.

**Counterexample (Spaces).** The forgetful functor $U : \mathbf{Top} \to \mathbf{Set}$ preserves all limits and all colimits (Chapter 5 proves this from its two adjoints), but it reflects neither. Let $P$ be the set $\mathbb{R}^2$ with the discrete topology and the two projections to $\mathbb{R}$, which are continuous. Its image in $\mathbf{Set}$ is a product. It is not a product in $\mathbf{Top}$: the factorization of the cone $\mathbb{R}^2$ with the product topology (Volume 13, Chapter 1) would be the identity map from $\mathbb{R}^2$ to $P$, and this map is not continuous. Here $U$ does not reflect isomorphisms: the identity from discrete to usual $\mathbb{R}^2$ is a continuous bijection without continuous inverse.

::: mathlib
`GrpCat.forget_createsLimitsOfSize` · `Mathlib.Algebra.Category.Grp.Limits`

The example on groups is the instance `GrpCat.forget_createsLimitsOfSize`, and `GrpCat.forget_preservesLimitsOfSize` follows. For spaces, `TopCat.forget_preservesLimitsOfSize` and `TopCat.forget_preservesColimitsOfSize` are instances. The forgetful functor of a concrete category is `forget C`.

<?decl GrpCat.forget_createsLimitsOfSize?>
<?decl TopCat.forget_preservesLimitsOfSize?>
:::

### The library around it

`Cone.isLimitCoyonedaEquiv` packs both halves of the first theorem into one equivalence: `IsLimit c` against limits after each `coyoneda.obj X`. The files on preservation of special shapes, such as `Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products`, give comparison isomorphisms for products, equalizers and pullbacks. A useful pattern: to prove that a concrete forgetful functor creates limits, give the lifted cone and use `createsLimitOfReflectsIso`.

Common errors of a learner:

- `PreservesLimit K G` is a `Prop` and holds `Nonempty (IsLimit _)`. To get a term, use `isLimitOfPreserves`.
- Reading "creates" as strict creation, with equality of cones. Mathlib asks only for an isomorphism of cones.
- Expecting that preservation implies reflection. The example of spaces shows that it does not.

### Exercises

1. (A) Show that a composite of functors that preserve limits of the relevant shapes preserves them, and the same for reflection.
2. (A) Show that the inclusion of abelian groups into groups preserves products but not coproducts. Hint: compare $\mathbb{Z} \times \mathbb{Z}$ with $\mathbb{Z} * \mathbb{Z}$.
3. (A) Show that a fully faithful functor reflects all limits.
4. (B) Show that a functor that preserves pullbacks preserves monomorphisms. Hint: Section 2, Exercise 4.
5. (B) Prove the dual of the theorem on functor categories, and deduce that colimits in $[A^{\mathrm{op}}, \mathbf{Set}]$ are computed pointwise.
6. (B) Show that the forgetful functor from rings to sets creates limits, and that it does not preserve the initial object.
7. (C) Let $G$ reflect isomorphisms, let $C$ have equalizers and let $G$ preserve them. Show that $G$ is faithful.

### Notes and history

The words "preserve", "reflect" and "create" are in Mac Lane's book (1971), where creation is the strict notion. The weaker notion of Mathlib, with an isomorphism of cones, is invariant under equivalence of categories. Pointwise limits in functor categories are part of the basic theory of presheaves and sheaves.

### Reference

<?reference?>
