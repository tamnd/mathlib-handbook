---
title: Cones and limits
kind: theory
modules:
  - Mathlib.CategoryTheory.Limits.Cones
  - Mathlib.CategoryTheory.Limits.IsLimit
  - Mathlib.CategoryTheory.Limits.HasLimits
  - Mathlib.CategoryTheory.Limits.Shapes.Terminal
  - Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
explains:
  E3: [CategoryTheory.Limits.Cone, CategoryTheory.Limits.IsLimit, CategoryTheory.Limits.HasLimit, CategoryTheory.Limits.limit, CategoryTheory.Limits.IsTerminal]
  E2: [CategoryTheory.Limits.Cone.w, CategoryTheory.Limits.ConeMorphism, CategoryTheory.Limits.Cone.category, CategoryTheory.Functor.cones, CategoryTheory.Limits.IsLimit.lift, CategoryTheory.Limits.IsLimit.fac, CategoryTheory.Limits.IsLimit.uniq, CategoryTheory.Limits.IsLimit.hom_ext, CategoryTheory.Limits.IsLimit.ofExistsUnique, CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso, CategoryTheory.Limits.IsLimit.uniqueUpToIso, CategoryTheory.Limits.IsLimit.homIso, CategoryTheory.Limits.HasLimitsOfShape, CategoryTheory.Limits.HasLimitsOfSize, CategoryTheory.Limits.HasLimits, CategoryTheory.Limits.limit.π, CategoryTheory.Limits.limit.lift, CategoryTheory.Limits.limit.lift_π, CategoryTheory.Limits.limit.hom_ext, CategoryTheory.Limits.limit.isLimit, CategoryTheory.Limits.IsTerminal.from, CategoryTheory.Limits.IsTerminal.hom_ext, CategoryTheory.Limits.IsTerminal.uniqueUpToIso, CategoryTheory.Limits.HasTerminal, CategoryTheory.Limits.terminal, CategoryTheory.Limits.coneOfDiagramInitial, CategoryTheory.Limits.limitOfDiagramInitial]
  E1: auto
families: []
requires: [V24.C01, V24.C02, V24.C03, V04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Cones and limits

### Overview

The direct product of groups, the intersection of subgroups, the kernel of a homomorphism and the infimum of a family in a poset are each "the best object with maps to a given diagram". This section gives the one definition that covers all of them: the limit of a diagram.

A limit of a diagram $F : J \to C$ is a cone through which every other cone factors in exactly one way. In the language of Chapter 3, a limit represents the functor of cones. The section proves that a limit is unique up to a unique isomorphism and that a terminal object is the limit of the empty diagram.

### Definitions

Throughout, $C$ is a category and $J$ is a small category. Mathlib writes composition in diagram order: `f ≫ g` is the textbook $g \circ f$, "first $f$, then $g$". This text uses $g \circ f$ in mathematics and `f ≫ g` in code.

**Definition (Diagram).** A *diagram of shape $J$* in $C$ is a functor $F : J \to C$. For a set $I$ seen as a discrete category, it is a family $(F(i))_{i \in I}$.

**Definition (Cone).** A *cone* over $F$ is an object $X$ of $C$, the *apex*, with a morphism $\pi_j : X \to F(j)$ for each object $j$ of $J$, such that $F(u) \circ \pi_j = \pi_k$ for each morphism $u : j \to k$ of $J$.

A cone with apex $X$ is the same as a natural transformation $\pi : \Delta X \Rightarrow F$ from the constant functor $\Delta X$: the naturality square for $u$ is the condition above.

**Definition (Category of cones).** A *morphism of cones* $(X, \pi) \to (Y, \sigma)$ is a morphism $f : X \to Y$ of $C$ with $\sigma_j \circ f = \pi_j$ for all $j$. Composition and identities are those of $C$. This gives the category $\mathrm{Cone}(F)$.

**Definition (Limit).** A cone $(L, \pi)$ over $F$ is a *limit cone* if for each cone $(X, \sigma)$ there is exactly one morphism $u : X \to L$ with $\pi_j \circ u = \sigma_j$ for all $j$. Equivalently, $(L, \pi)$ is a terminal object of $\mathrm{Cone}(F)$. The category $C$ *has limits of shape $J$* if every diagram of shape $J$ has a limit cone, and $C$ is *complete* if it has limits of every small shape.

**Definition (Terminal object).** An object $T$ of $C$ is *terminal* if for each object $X$ there is exactly one morphism $X \to T$.

::: mathlib
`CategoryTheory.Limits.Cone` · `Mathlib.CategoryTheory.Limits.Cones`

A structure with two fields: the apex `pt : C` and `π : (Functor.const J).obj pt ⟶ F`, a natural transformation from the constant functor. The component at `j` is `c.π.app j`. The cone condition is the lemma `Cone.w`: `c.π.app j ≫ F.map f = c.π.app j'` for `f : j ⟶ j'`. A morphism of cones is a `ConeMorphism`, and the instance `Cone.category` makes `Cone F` a category. The functor `F.cones` sends `X` to the cones with apex `X`.

<?decl CategoryTheory.Limits.Cone?>
:::

::: mathlib
`CategoryTheory.Limits.IsLimit` · `Mathlib.CategoryTheory.Limits.IsLimit`

`IsLimit t` is a structure, not a proposition. It holds the data `lift : ∀ s : Cone F, s.pt ⟶ t.pt` and two properties: `fac` says `lift s ≫ t.π.app j = s.π.app j`, and `uniq` says that any `m` with this property equals `lift s`. The data lets a proof compute with `lift s`. Two terms of `IsLimit t` are equal (`IsLimit.subsingleton`). The constructor `IsLimit.ofExistsUnique` builds the structure from the textbook statement "for each cone there is a unique factorization".

<?decl CategoryTheory.Limits.IsLimit?>
:::

::: mathlib
`CategoryTheory.Limits.HasLimit` · `Mathlib.CategoryTheory.Limits.HasLimits`

`HasLimit F` is a class in `Prop`: some limit cone exists. Under this class, `limit F : C` is an apex chosen by the axiom of choice, `limit.π F j : limit F ⟶ F.obj j` are its projections, `limit.lift F c` is the factorization of a cone `c`, and `limit.isLimit F` is the proof that the chosen cone is a limit. `HasLimitsOfShape J C` asks for all limits of one shape, and `HasLimitsOfSize` and `HasLimits` ask for all small shapes; this is "complete".

<?decl CategoryTheory.Limits.HasLimit?>
<?decl CategoryTheory.Limits.limit?>
:::

### Theorems and proofs

**Proposition (Terminal objects are unique).** Let $T$ and $T'$ be terminal objects of $C$. There is exactly one morphism $T \to T'$, and it is an isomorphism.

*Proof.* Since $T'$ is terminal, there is exactly one morphism $a : T \to T'$. Since $T$ is terminal, there is exactly one morphism $b : T' \to T$. The composite $b \circ a$ is a morphism $T \to T$. The identity $1_T$ is also a morphism $T \to T$, and there is only one such morphism, so $b \circ a = 1_T$. In the same way $a \circ b = 1_{T'}$. So $a$ is an isomorphism with inverse $b$. $\square$

**Theorem (Uniqueness of limits).** Let $(L, \pi)$ and $(L', \pi')$ be limit cones over $F$. There is exactly one morphism $\theta : L' \to L$ with $\pi_j \circ \theta = \pi'_j$ for all $j$, and $\theta$ is an isomorphism.

*Proof.* A morphism of cones $(L', \pi') \to (L, \pi)$ is exactly a morphism $\theta$ of $C$ with $\pi_j \circ \theta = \pi'_j$. Both cones are terminal in $\mathrm{Cone}(F)$, so by the proposition there is exactly one such $\theta$, with an inverse $\theta'$ in $\mathrm{Cone}(F)$. Composition in $\mathrm{Cone}(F)$ is composition in $C$, so $\theta$ and $\theta'$ are inverse in $C$. $\square$

**Proposition (Maps into a limit).** Let $(L, \pi)$ be a limit cone over $F$ and let $f, g : X \to L$. If $\pi_j \circ f = \pi_j \circ g$ for all $j$, then $f = g$.

*Proof.* The morphisms $\sigma_j = \pi_j \circ f$ form a cone over $F$ with apex $X$: for $u : j \to k$, $F(u) \circ \sigma_j = (F(u) \circ \pi_j) \circ f = \pi_k \circ f = \sigma_k$. Both $f$ and $g$ satisfy $\pi_j \circ u = \sigma_j$ for all $j$. By the uniqueness in the definition of a limit, $f = g$. $\square$

In Mathlib this is `IsLimit.hom_ext` and, for the chosen limit, `limit.hom_ext`.

**Theorem (Limits represent cones).** Let $\mathrm{Cone}(X, F)$ be the set of cones over $F$ with apex $X$. For a morphism $h : X' \to X$, the map $\sigma \mapsto (\sigma_j \circ h)_j$ sends $\mathrm{Cone}(X, F)$ to $\mathrm{Cone}(X', F)$, and this makes $X \mapsto \mathrm{Cone}(X, F)$ a functor $C^{\mathrm{op}} \to \mathbf{Set}$. A cone $(L, \pi)$ is a limit if and only if the maps
$$\Phi_X : \mathrm{Hom}(X, L) \to \mathrm{Cone}(X, F), \qquad f \mapsto (\pi_j \circ f)_j,$$
are bijective for all $X$. The maps $\Phi_X$ are natural in $X$, so a limit cone is a representation of the functor of cones.

*Proof.* The family $(\pi_j \circ f)_j$ is a cone by the computation in the previous proof. For $h : X' \to X$, $\Phi_{X'}(f \circ h) = (\pi_j \circ f \circ h)_j$, which is the image of $\Phi_X(f)$ under the map of cones induced by $h$. So $\Phi$ is natural. Surjectivity of $\Phi_X$ says that each cone with apex $X$ factors through $L$, and injectivity says that the factorization is unique. Together they are the definition of a limit. $\square$

By the Yoneda lemma of Chapter 3, a representing object is unique up to a unique isomorphism compatible with the representations. This gives a second proof of the uniqueness theorem.

**Proposition (Limit over a shape with an initial object).** Suppose $J$ has an initial object $i_0$, and write $!_j : i_0 \to j$ for the unique morphism. Then $F(i_0)$, with the projections $\pi_j = F(!_j)$, is a limit cone over $F$.

*Proof.* First, it is a cone. For $u : j \to k$, $u \circ !_j$ is a morphism $i_0 \to k$, so it equals $!_k$. Hence $F(u) \circ F(!_j) = F(u \circ !_j) = F(!_k)$. Now let $(X, \sigma)$ be a cone. Put $f = \sigma_{i_0}$. Then $\pi_j \circ f = F(!_j) \circ \sigma_{i_0} = \sigma_j$ by the cone condition for $!_j$. If $g : X \to F(i_0)$ also satisfies $\pi_j \circ g = \sigma_j$ for all $j$, take $j = i_0$. Since $!_{i_0} = 1_{i_0}$, $\pi_{i_0} = 1_{F(i_0)}$, and $g = \sigma_{i_0} = f$. $\square$

**Corollary (Terminal objects as limits).** Let $\emptyset$ be the empty category and $F : \emptyset \to C$ the unique functor. A cone over $F$ is just an object $X$, and a morphism of cones is any morphism of $C$. So a limit of $F$ is a terminal object of $C$, and $C$ has a terminal object if and only if it has limits of shape $\emptyset$.

*Proof.* A cone and a morphism of cones over $F$ have no conditions, so $\mathrm{Cone}(F)$ is isomorphic to $C$. $\square$

::: mathlib
`CategoryTheory.Limits.IsTerminal` · `Mathlib.CategoryTheory.Limits.Shapes.IsTerminal`

Mathlib follows the corollary. `IsTerminal X` is `IsLimit (asEmptyCone X)`. The unique map is `IsTerminal.from t Y : Y ⟶ X`, uniqueness is `IsTerminal.hom_ext`, and `IsTerminal.uniqueUpToIso` is the isomorphism of the proposition. The class `HasTerminal C` and the chosen object `terminal C` are in `Mathlib.CategoryTheory.Limits.Shapes.Terminal`. The proposition on shapes with an initial object is `limitOfDiagramInitial`, with the cone `coneOfDiagramInitial`.

<?decl CategoryTheory.Limits.IsTerminal?>
:::

### Examples

**Example (Infima in a poset).** Let $(P, \le)$ be a poset, seen as a category with one morphism $x \to y$ when $x \le y$ (Chapter 1). A diagram $F : J \to P$ picks elements $F(j)$. A cone with apex $x$ is an element with $x \le F(j)$ for all $j$; the cone conditions hold automatically, since all parallel morphisms in $P$ are equal. A morphism of cones $x \to y$ exists when $x \le y$. So a limit is a greatest lower bound of $\{F(j)\}$, that is, an infimum (Volume 4, Chapter 1). A terminal object is a greatest element. A complete lattice (Volume 4, Chapter 4) is a complete category.

**Example (Terminal objects in the concrete categories).** In $\mathbf{Set}$, a one-point set $\{*\}$ is terminal: the only map $X \to \{*\}$ is constant. In groups, the trivial group is terminal. In rings with identity, the zero ring $\{0\}$ is terminal, because a ring homomorphism $R \to \{0\}$ must send $1$ to $0 = 1$, and the constant map does this. In topological spaces, the one-point space is terminal.

**Counterexample (Fields have no terminal object).** In the category of fields and ring homomorphisms, a homomorphism of fields is injective and preserves the characteristic. Suppose $T$ is a terminal field. Then there are homomorphisms $\mathbb{Q} \to T$ and $\mathbb{F}_2 \to T$. Then $\operatorname{char} T$ is both $0$ and $2$, which is impossible. So the empty diagram has no limit in fields.

### The library around it

In `Mathlib.CategoryTheory.Limits.IsLimit`, `IsLimit.conePointUniqueUpToIso` is the isomorphism of the apexes of two limit cones, and `IsLimit.uniqueUpToIso` the isomorphism in the category of cones. `IsLimit.homIso` is the bijection $\Phi$ of the representation theorem. For the chosen limit, `limit.lift_π` says `limit.lift F c ≫ limit.π F j = c.π.app j`.

Common errors of a learner:

- `IsLimit c` is data, so `have h : IsLimit c := ...` loses the definition of `lift`. Use `let` or a named definition when the proof must compute with the lifted map.
- `limit F` is a choice. A proof must not depend on what it is; it uses `limit.lift`, `limit.π` and `limit.hom_ext`. To compare it with an explicit construction, use `limit.isoLimitCone` or `IsLimit.conePointUniqueUpToIso`.
- In `Cone.w` the order is diagram order: `c.π.app j ≫ F.map f` is $F(f) \circ \pi_j$.

### Exercises

1. (A) Show that an object $T$ is terminal in $C$ if and only if it is initial in $C^{\mathrm{op}}$.
2. (A) Let $J$ have a terminal object $t$. Show by an example in $\mathbf{Set}$ that the limit of $F : J \to C$ need not be $F(t)$. Hint: use the shape $\bullet \to \bullet \leftarrow \bullet$.
3. (B) Let $(L, \pi)$ be a limit cone over $F$ and let $\phi : L' \to L$ be an isomorphism. Show that $(L', (\pi_j \circ \phi)_j)$ is a limit cone.
4. (B) Let $F, G : J \to C$ have limit cones $(L, \pi)$ and $(M, \rho)$, and let $\alpha : F \Rightarrow G$. Show that there is a unique $\lim \alpha : L \to M$ with $\rho_j \circ \lim \alpha = \alpha_j \circ \pi_j$, and that this makes $\lim$ a functor on the diagrams that have limits.
5. (B) Show that $f : X \to Y$ is a monomorphism if and only if the square with sides $1_X$, $1_X$, $f$, $f$ makes $X$ a limit of the diagram $X \xrightarrow{f} Y \xleftarrow{f} X$.
6. (C) Let $C$ be a small category with products of all families indexed by sets (Section 2). Show that $C$ is a preorder. Hint: if $f \neq g : X \to Y$, let $M$ be the set of all morphisms of $C$ and compare the size of $\mathrm{Hom}(X, Y^M)$ with that of $M$.

### Notes and history

Inverse and direct limits of sequences of groups and spaces were used in algebraic topology before categories existed. The definition by a universal cone over a functor is the one of Mac Lane's *Categories for the Working Mathematician* (1971). Exercise 6 is a theorem of Freyd: a small category with all small limits is a preorder. So completeness is of interest only for large categories, and Mathlib separates the universe of the shape from the universes of the category.

### Reference

<?reference?>
