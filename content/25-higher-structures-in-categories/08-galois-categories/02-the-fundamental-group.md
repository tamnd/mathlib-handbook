---
title: The fundamental group of a Galois category
kind: theory
modules:
  - Mathlib.CategoryTheory.Galois.Prorepresentability
  - Mathlib.CategoryTheory.Galois.Action
  - Mathlib.CategoryTheory.Galois.Topology
  - Mathlib.CategoryTheory.Galois.Full
  - Mathlib.CategoryTheory.Galois.EssSurj
  - Mathlib.CategoryTheory.Galois.Equivalence
  - Mathlib.CategoryTheory.Galois.IsFundamentalgroup
  - Mathlib.CategoryTheory.Galois.ContAction
  - Mathlib.CategoryTheory.Galois.FullSubcategory
explains:
  E3: [CategoryTheory.PreGaloisCategory.PointedGaloisObject, CategoryTheory.PreGaloisCategory.PointedGaloisObject.isColimit, CategoryTheory.PreGaloisCategory.autMulEquivAutGalois, CategoryTheory.PreGaloisCategory.FiberFunctor.isPretransitive_of_isConnected, CategoryTheory.PreGaloisCategory.autEmbedding, CategoryTheory.PreGaloisCategory.functorToAction, CategoryTheory.PreGaloisCategory.functorToAction_full, CategoryTheory.PreGaloisCategory.exists_lift_of_continuous, CategoryTheory.PreGaloisCategory.functorToContAction, CategoryTheory.PreGaloisCategory.IsFundamentalGroup, CategoryTheory.ObjectProperty.IsGaloisSubcategory]
  E2: [CategoryTheory.PreGaloisCategory.PointedGaloisObject.cocone, CategoryTheory.PreGaloisCategory.PointedGaloisObject.incl, CategoryTheory.PreGaloisCategory.autGaloisSystem, CategoryTheory.PreGaloisCategory.AutGalois, CategoryTheory.PreGaloisCategory.AutGalois.π, CategoryTheory.PreGaloisCategory.AutGalois.π_surjective, CategoryTheory.PreGaloisCategory.endMulEquivAutGalois, CategoryTheory.PreGaloisCategory.FibreFunctor.end_isUnit, CategoryTheory.PreGaloisCategory.FiberFunctor.isPretransitive_of_isGalois, CategoryTheory.PreGaloisCategory.autEmbedding_injective, CategoryTheory.PreGaloisCategory.autEmbedding_range_isClosed, CategoryTheory.PreGaloisCategory.autEmbedding_isClosedEmbedding, CategoryTheory.PreGaloisCategory.continuousSMul_aut_fiber, CategoryTheory.PreGaloisCategory.exists_set_ker_evaluation_subset_of_isOpen, CategoryTheory.PreGaloisCategory.nhds_one_has_basis_stabilizers, CategoryTheory.PreGaloisCategory.exists_lift_of_mono_of_isConnected, CategoryTheory.PreGaloisCategory.exists_lift_of_mono, CategoryTheory.PreGaloisCategory.has_decomp_quotients, CategoryTheory.PreGaloisCategory.fiberIsoQuotientStabilizer, CategoryTheory.PreGaloisCategory.exists_lift_of_quotient_openSubgroup, CategoryTheory.PreGaloisCategory.instIsEquivalenceContActionFintypeCatFunObjFiniteAutFunctorFunctorToContAction, CategoryTheory.PreGaloisCategory.IsNaturalSMul, CategoryTheory.PreGaloisCategory.toAut, CategoryTheory.PreGaloisCategory.toAut_injective_of_non_trivial, CategoryTheory.PreGaloisCategory.toAut_surjective_of_isPretransitive, CategoryTheory.PreGaloisCategory.toAut_bijective, CategoryTheory.PreGaloisCategory.toAut_isHomeomorph, CategoryTheory.PreGaloisCategory.toAutMulEquiv, CategoryTheory.PreGaloisCategory.toAutHomeo, CategoryTheory.PreGaloisCategory.instIsFundamentalGroupAutFunctorFintypeCat, CategoryTheory.GaloisCategory.instFullSubcategoryOfIsGaloisSubcategory, Action.trivialOnSet, Action.trivialOnSet_le_isContinuous, Action.isContinuous_eq_iSup, Action.exists_openSubgroup_of_isContinuous_of_finite, Action.instIsGaloisSubcategoryFintypeCatIsContinuousFunObjFinite]
  E1: auto
families: []
requires: [V05, V13, V14, V24.C02, V24.C03, V24.C04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The fundamental group of a Galois category

### Overview

Let $C$ be a Galois category with a fiber functor $F$. The fundamental group of $C$ at $F$ is the group $\mathrm{Aut}(F)$ of the natural automorphisms of $F$. An element $\sigma$ of $\mathrm{Aut}(F)$ is a family of bijections $\sigma_X : F(X) \to F(X)$, one for each object $X$, such that $F(f) \circ \sigma_X = \sigma_Y \circ F(f)$ for each $f : X \to Y$. So $\mathrm{Aut}(F)$ acts on each fiber, and each $F(f)$ is equivariant.

This section proves the main theorem of Grothendieck. The group $\mathrm{Aut}(F)$ has a natural topology, and with it $\mathrm{Aut}(F)$ is a profinite group. The functor $X \mapsto F(X)$, with the action of $\mathrm{Aut}(F)$, is an equivalence from $C$ to the category of the finite sets with a continuous action of $\mathrm{Aut}(F)$. The last part gives a criterion for a given topological group to be the fundamental group, because in practice a group such as an absolute Galois group is known first.

The proofs use Section 1 at each step: the theorem on evaluation at one point, the Galois representatives and the transitivity of $\mathrm{Aut}(A)$ on $F(A)$ for a Galois object $A$. Compact spaces are in Volume 13, and topological groups are in Volume 14. In the text $g \circ f$ is the textbook composite, and Mathlib writes `f ≫ g`.

### Definitions

**Definition (Pointed Galois object).** A pointed Galois object is a pair $(A, a)$ with $A$ Galois and $a \in F(A)$. A morphism $(A, a) \to (B, b)$ is a morphism $f : A \to B$ with $F(f)(a) = b$.

By the theorem on evaluation, there is at most one morphism $(A, a) \to (B, b)$. So the category of pointed Galois objects is a preorder.

**Definition (The induced functor).** The functor $H$ from $C$ to the finite $\mathrm{Aut}(F)$-sets sends $X$ to $F(X)$ with the action $\sigma \cdot x = \sigma_X(x)$, and $f$ to $F(f)$.

**Definition (The topology).** Give each finite group $\mathrm{Aut}(F(X))$ of permutations the discrete topology, and give the product $\prod_X \mathrm{Aut}(F(X))$ the product topology. The map $\sigma \mapsto (\sigma_X)_X$ from $\mathrm{Aut}(F)$ to this product is an injective group homomorphism. The topology of $\mathrm{Aut}(F)$ is the topology induced by this map.

So a basic open neighborhood of $1$ in $\mathrm{Aut}(F)$ is the set of the $\sigma$ that act as the identity on $F(X_1), \dots, F(X_n)$ for a finite list of objects.

**Definition (Continuous action).** Let $G$ be a topological group and let $S$ be a finite set with an action of $G$. The action is continuous if the map $G \times S \to S$ is continuous for the discrete topology on $S$. This is true if and only if the stabilizer of each point is open, and if and only if there is an open subgroup of $G$ that acts as the identity on $S$.

**Definition (Profinite group).** A profinite group is a topological group that is compact, Hausdorff and totally disconnected.

::: mathlib
`CategoryTheory.PreGaloisCategory.PointedGaloisObject` · `Mathlib.CategoryTheory.Galois.Prorepresentability`

A structure with the fields `obj`, `pt : F.obj obj` and `isGalois : IsGalois obj`. A morphism is a structure `Hom` with the fields `val` and `comp : F.map val A.pt = B.pt`. The functor `PointedGaloisObject.incl F` forgets the point.

<?decl CategoryTheory.PreGaloisCategory.PointedGaloisObject?>
:::

### Theorems and proofs

In this part $C$ is a Galois category and $F$ is a fiber functor. The first theorem says that $F$ is a filtered colimit of representable functors. A functor of this form is called pro-representable.

**Theorem (Pro-representability).** The category of pointed Galois objects is cofiltered. For each $X$, the maps $\mathrm{Hom}(A, X) \to F(X)$, $f \mapsto F(f)(a)$, make $F(X)$ the colimit of the sets $\mathrm{Hom}(A, X)$ over the opposite category of pointed Galois objects.

*Proof.* The category is not empty, because the terminal object with its point is a pointed Galois object. Let $(A, a)$ and $(B, b)$ be pointed Galois objects. By the corollary to the Galois representative in Section 1, there are a Galois object $Z$, a point $z$ and $f : Z \to A \times B$ with $F(f)(z) = (a, b)$. The composites of $f$ with the two projections are morphisms $(Z, z) \to (A, a)$ and $(Z, z) \to (B, b)$. Two parallel morphisms are equal, because the category is a preorder. So the category is cofiltered.

The maps $f \mapsto F(f)(a)$ are compatible: if $g : (A, a) \to (B, b)$ and $f : B \to X$, then $F(f \circ g)(a) = F(f)(b)$. A colimit of sets over a filtered category has the description of Volume 24, Chapter 4. For surjectivity, let $x \in F(X)$. The corollary to the Galois representative gives $A$, $a$ and $f : A \to X$ with $F(f)(a) = x$. For injectivity, let $u : A \to X$ and $v : B \to X$ with $F(u)(a) = F(v)(b)$. Take $(Z, z)$ with morphisms $f : (Z, z) \to (A, a)$ and $g : (Z, z) \to (B, b)$. Then $F(u \circ f)(z) = F(u)(a) = F(v)(b) = F(v \circ g)(z)$. By the theorem on evaluation, $u \circ f = v \circ g$. So $u$ and $v$ have the same class in the colimit. $\square$

The Yoneda lemma now computes the endomorphisms of $F$. A natural transformation from a colimit of functors $\mathrm{Hom}(A, -)$ to $F$ is a compatible family of elements of the sets $F(A)$. For a pointed Galois object $(A, a)$, the corollary on torsors in Section 1 identifies $F(A)$ with $\mathrm{Aut}(A)$ by $\varphi \mapsto F(\varphi)(a)$.

**Theorem (The group as a limit).** The monoid of the endomorphisms of $F$ is isomorphic to the opposite of the limit of the finite groups $\mathrm{Aut}(A)$ over the pointed Galois objects $(A, a)$. Each endomorphism of $F$ is an automorphism. The projection from the limit to each $\mathrm{Aut}(A)$ is surjective.

*Proof (outline).* For a morphism $f : (A, a) \to (B, b)$ and $\varphi \in \mathrm{Aut}(A)$, the last example of Section 1 gives the unique $\psi \in \mathrm{Aut}(B)$ with $\psi \circ f = f \circ \varphi$. This defines the transition maps of the system $(A, a) \mapsto \mathrm{Aut}(A)$, and they are surjective because $A$ and $B$ are Galois. By the theorem on pro-representability and the Yoneda lemma, an endomorphism $t$ of $F$ is determined by the elements $t_A(a)$, and these elements are a compatible family. Under the identification of $F(A)$ with $\mathrm{Aut}(A)$, this gives a bijection from the endomorphisms of $F$ to the limit. A computation shows that it reverses the order of composition. The limit is a group, so each endomorphism of $F$ is invertible.

For the last statement, the limit of a system of nonempty finite sets over a cofiltered category, with surjective transition maps, projects onto each member of the system. This is a compactness argument, and Mathlib proves it for the system of sections of a functor to finite types. $\square$

**Theorem (Transitivity).** For each connected object $X$, the group $\mathrm{Aut}(F)$ acts transitively on $F(X)$.

*Proof.* Suppose first that $X$ is Galois, and let $x, y \in F(X)$. By Section 1, there is $\varphi \in \mathrm{Aut}(X)$ with $F(\varphi)(x) = y$. By the surjectivity of the projection to $\mathrm{Aut}(X)$ at $(X, x)$, there is an element of the limit with the component $\varphi$ there. The corresponding $\sigma \in \mathrm{Aut}(F)$ satisfies $\sigma_X(x) = F(\varphi)(x) = y$.

Now let $X$ be connected. By Section 1, there is $f : A \to X$ with $A$ Galois, and $F(f)$ is surjective because $X$ is connected and $F(A)$ is not empty. Let $x, y \in F(X)$, and choose $a, b \in F(A)$ with $F(f)(a) = x$ and $F(f)(b) = y$. Take $\sigma$ with $\sigma_A(a) = b$. By naturality, $\sigma_X(x) = \sigma_X(F(f)(a)) = F(f)(\sigma_A(a)) = y$. $\square$

So $H$ preserves connected objects: if $X$ is connected, then $H(X)$ is a transitive $\mathrm{Aut}(F)$-set, which is a connected object in the Galois category of finite $\mathrm{Aut}(F)$-sets.

**Theorem (Topology).** The group $\mathrm{Aut}(F)$ is a profinite group, and its action on each fiber is continuous. The stabilizers of the points $a$ of the pointed Galois objects $(A, a)$ are a basis of open neighborhoods of $1$.

*Proof.* The product $P = \prod_X \mathrm{Aut}(F(X))$ is a product of finite discrete groups. By the theorem of Tychonoff, $P$ is compact, and a product of discrete spaces is Hausdorff and totally disconnected. The image of $\mathrm{Aut}(F)$ is the set of the families $(\tau_X)$ with $F(f) \circ \tau_X = \tau_Y \circ F(f)$ for each $f : X \to Y$, because such a family is a natural automorphism of $F$. Each of these conditions involves two coordinates, and it is closed because the coordinates are discrete. So the image is closed in $P$, and it is compact, Hausdorff and totally disconnected. Multiplication and inversion are continuous in $P$, so $\mathrm{Aut}(F)$ is a topological group. The action on $F(X)$ factors through the continuous projection to $\mathrm{Aut}(F(X))$, so it is continuous.

The stabilizer of $a$ is open, because it is the inverse image of an open set under the projection to the discrete group $\mathrm{Aut}(F(A))$. Let $V$ be an open neighborhood of $1$. Then $V$ contains the set of the $\sigma$ that act as the identity on $F(X_1), \dots, F(X_n)$. Mathlib reduces to the case where the $X_i$ are connected, by the decomposition into connected components. Let $Y = X_1 \times \dots \times X_n$, and let $(A, a)$ be a Galois representative of $Y$. Each point of $F(X_i)$ is $F(g)(a)$ for some $g : A \to X_i$, because $F(Y) \to F(X_i)$ is surjective. If $\sigma_A(a) = a$, then $\sigma_{X_i}(F(g)(a)) = F(g)(\sigma_A(a)) = F(g)(a)$. So the stabilizer of $a$ is in $V$. $\square$

The next two theorems say that $H$ is an equivalence onto the continuous finite $\mathrm{Aut}(F)$-sets. The faithfulness of $H$ follows from the faithfulness of $F$.

**Lemma (Lift of subobjects).** Let $Y \subseteq F(X)$ be a subset that is stable under $\mathrm{Aut}(F)$. Then there is a monomorphism $i : Z \to X$ such that $F(i)$ is a bijection from $F(Z)$ to $Y$.

*Proof.* Suppose first that $Y$ is one orbit, and choose $y \in Y$. By the corollary on components in Section 1, there are a connected $Z$, a monomorphism $i : Z \to X$ and $z \in F(Z)$ with $F(i)(z) = y$. The image of $F(i)$ is stable under $\mathrm{Aut}(F)$ by naturality, and it is one orbit by the theorem on transitivity. Two orbits that contain $y$ are equal, so the image of $F(i)$ is $Y$. In general, $Y$ is a finite disjoint union of orbits $Y_1, \dots, Y_m$. Take $i_j : Z_j \to X$ for each $Y_j$, and let $i : \coprod_j Z_j \to X$ be the induced morphism. The functor $F$ preserves the coproduct, so $F(i)$ is a bijection onto $Y$. Then $F(i)$ is injective, and $i$ is a monomorphism because $F$ reflects monomorphisms. $\square$

**Theorem (Fullness).** For objects $X$ and $Y$, each equivariant map $g : F(X) \to F(Y)$ is $F(f)$ for a morphism $f : X \to Y$.

*Proof.* Let $\Gamma = \{(x, g(x)) : x \in F(X)\}$ be the graph of $g$. It is a subset of $F(X) \times F(Y) = F(X \times Y)$, and it is stable under $\mathrm{Aut}(F)$ because $g$ is equivariant. By the lemma, there is a monomorphism $i : Z \to X \times Y$ with $F(i)$ a bijection onto $\Gamma$. Let $p_1$ and $p_2$ be the projections, and put $\psi = p_1 \circ i : Z \to X$. The map $F(\psi)$ is the composite of the bijection $F(Z) \to \Gamma$ and the first projection $\Gamma \to F(X)$, which is bijective. By (G6), $\psi$ is an isomorphism. Put $f = p_2 \circ i \circ \psi^{-1}$. For $x \in F(X)$, the point $F(i)(F(\psi^{-1})(x))$ is in $\Gamma$ and has first coordinate $x$, so it is $(x, g(x))$. Thus $F(f)(x) = g(x)$. $\square$

**Theorem (Essential image).** A finite $\mathrm{Aut}(F)$-set $S$ is isomorphic to $H(X)$ for some $X$ if and only if the action on $S$ is continuous.

*Proof (outline).* The action on each $H(X)$ is continuous by the theorem on topology. Conversely, let the action on $S$ be continuous. Then $S$ is a finite disjoint union of orbits, and each orbit is isomorphic to $\mathrm{Aut}(F)/U$, where $U$ is the stabilizer of a point. The subgroup $U$ is open. Because $H$ preserves finite coproducts, it is enough to find $X$ with $H(X) \cong \mathrm{Aut}(F)/U$.

By the theorem on topology, $U$ contains the stabilizer $N$ of a point $a$ of a pointed Galois object $(A, a)$. Section 1 shows that $N$ is a normal subgroup. By transitivity, $H(A) \cong \mathrm{Aut}(F)/N$. The finite group $U/N$ acts on $\mathrm{Aut}(F)/N$ by right multiplication, and by the theorem on fullness these maps come from automorphisms of $A$. Let $X$ be the quotient of $A$ by this finite group, which exists by (G2). The functor $F$ preserves this quotient by (G5). So $H(X)$ is the quotient of $\mathrm{Aut}(F)/N$ by $U/N$, which is $\mathrm{Aut}(F)/U$. $\square$

**Theorem (Main theorem).** The functor $H$ is an equivalence from $C$ to the category of the finite sets with a continuous action of the profinite group $\mathrm{Aut}(F)$.

*Proof.* The functor $H$ takes values in the continuous actions by the theorem on topology. It is faithful because $F$ is faithful, it is full by the theorem on fullness, and it is essentially surjective by the theorem on the essential image. A fully faithful and essentially surjective functor is an equivalence (Volume 24, Chapter 2). $\square$

The last theorem characterizes $\mathrm{Aut}(F)$ by its action. Let $G$ be a compact topological group with an action on each fiber $F(X)$. Call $G$ a fundamental group of $F$ if the action is natural in $X$, it is transitive on $F(X)$ for each Galois $X$, it is continuous on each $F(X)$, and only $1$ acts as the identity on all fibers.

**Theorem (Universal property).** If $G$ is a fundamental group of $F$, then the map $G \to \mathrm{Aut}(F)$ that sends $g$ to the family of its actions on the fibers is an isomorphism of groups and a homeomorphism. The group $\mathrm{Aut}(F)$ is a fundamental group of $F$.

*Proof (outline).* The map is a group homomorphism by naturality. It is continuous, because each coordinate $g \mapsto (x \mapsto g \cdot x)$ is continuous for the discrete topology on $\mathrm{Aut}(F(X))$. It is injective by the last condition. For surjectivity, let $t \in \mathrm{Aut}(F)$. For each pointed Galois object $(A, a)$, transitivity gives $g_A \in G$ with $g_A \cdot a = t_A(a)$. The elements $g$ with $g \cdot a = t_A(a)$ are the coset $g_A \cdot \mathrm{Stab}_G(a)$. Each of them agrees with $t$ on all of $F(A)$, because each point of $F(A)$ is $F(\varphi)(a)$ for some $\varphi \in \mathrm{Aut}(A)$. The stabilizer is open, so it is closed, and the coset is closed. These closed sets have the finite intersection property, because a finite family of pointed Galois objects receives morphisms from one pointed Galois object. By compactness, their intersection contains an element $g$, and $g$ agrees with $t$ on all Galois objects. By Section 1, $g$ maps to $t$. So the map is a continuous bijection from a compact space to a Hausdorff space, and it is a homeomorphism. The four conditions for $\mathrm{Aut}(F)$ itself are the theorems above. $\square$

### Examples

**Example (Finite groups).** Let $G$ be a finite group, and let $F$ be the forgetful functor on the finite $G$-sets. Give $G$ the discrete topology. Then $G$ is a fundamental group of $F$. The action on each fiber is natural and continuous. A Galois $G$-set is connected, so $G$ acts on it transitively. The set $G$ with the action by left multiplication is a finite $G$-set, and only $1$ acts on it as the identity. By the universal property, $G \cong \mathrm{Aut}(F)$. The index of this edition has no declaration for this example, so it is an application of the theorem.

**Example (Profinite groups).** Let $G$ be a topological group. The finite sets with a continuous action of $G$ form a Galois category. Mathlib proves this with a criterion for full subcategories. A property $P$ of the objects of a Galois category gives a Galois category if $P$ is closed under the terminal object, pullbacks, finite coproducts, quotients by finite groups and subobjects, and if the inclusion preserves epimorphisms. The continuous actions on finite sets are the union, over the open subgroups $U$, of the actions that are trivial on $U$, and each of these classes is closed under the constructions. When $G$ is profinite, the open normal subgroups have intersection $\{1\}$, and $G$ is a fundamental group of the forgetful functor. The index has no declaration for this last statement.

**Example (Fields).** For a field $K$ with separable closure $K^s$, the category of Section 1, Example (Field extensions), has the fundamental group $\mathrm{Gal}(K^s/K)$ with the Krull topology. The main theorem then gives the equivalence of the finite étale $K$-algebras with the continuous finite $\mathrm{Gal}(K^s/K)$-sets. Infinite Galois theory with the Krull topology is in `Mathlib.FieldTheory.Galois.Infinite`, but the index of this edition has no declaration that connects it to Galois categories.

**Example (The pointed Galois objects of finite $G$-sets).** For $G$ finite, a pointed Galois object is $(G/N, N)$ with $N$ normal, up to isomorphism. A morphism $(G/N, N) \to (G/M, M)$ exists if and only if $N \subseteq M$. The limit of the groups $\mathrm{Aut}(G/N) \cong G/N$ is $G$ itself, because $\{1\}$ is a normal subgroup and $G/\{1\} = G$ is the smallest member.

### The library around it

::: mathlib
`CategoryTheory.PreGaloisCategory.PointedGaloisObject.isColimit` · `Mathlib.CategoryTheory.Galois.Prorepresentability`

The theorem on pro-representability. The cocone `PointedGaloisObject.cocone F` on `(incl F).op ⋙ coyoneda` has the point `F ⋙ FintypeCat.incl`, and this definition shows that it is a colimit cocone. The category of pointed Galois objects has an instance of `IsCofilteredOrEmpty`.

<?decl CategoryTheory.PreGaloisCategory.PointedGaloisObject.isColimit?>
:::

::: mathlib
`CategoryTheory.PreGaloisCategory.autMulEquivAutGalois` · `Mathlib.CategoryTheory.Galois.Prorepresentability`

The isomorphism `Aut F ≃* (AutGalois F)ᵐᵒᵖ`. Here `AutGalois F` is the limit of `autGaloisSystem F`, and `AutGalois.π F A` is its projection to `Aut A.obj`. The projections are surjective by `AutGalois.π_surjective`.

<?decl CategoryTheory.PreGaloisCategory.autMulEquivAutGalois?>
:::

::: mathlib
`CategoryTheory.PreGaloisCategory.FiberFunctor.isPretransitive_of_isConnected` · `Mathlib.CategoryTheory.Galois.Prorepresentability`

The theorem on transitivity, as an instance of `MulAction.IsPretransitive (Aut F) (F.obj X)` for `[IsConnected X]`. It is true for a fiber functor to `FintypeCat.{w}` in any universe `w`. The proof moves to the universe of the morphisms of `C` with `FintypeCat.uSwitch`.

<?decl CategoryTheory.PreGaloisCategory.FiberFunctor.isPretransitive_of_isConnected?>
:::

::: mathlib
`CategoryTheory.PreGaloisCategory.autEmbedding` · `Mathlib.CategoryTheory.Galois.Topology`

The homomorphism `Aut F →* ∀ X, Aut (F.obj X)`. The topology on `Aut F` is the induced topology. The file proves `autEmbedding_isClosedEmbedding` and gives the instances `CompactSpace`, `T2Space`, `TotallyDisconnectedSpace` and `IsTopologicalGroup` for `Aut F`.

<?decl CategoryTheory.PreGaloisCategory.autEmbedding?>
:::

::: mathlib
`CategoryTheory.PreGaloisCategory.functorToAction` · `Mathlib.CategoryTheory.Galois.Action`

The functor $H$, of type `C ⥤ Action FintypeCat (Aut F)`. Its composite with `forget₂ _ FintypeCat` is `F` by `rfl`. The file gives instances for faithfulness, finite coproducts, finite products and `PreservesIsConnected`.

<?decl CategoryTheory.PreGaloisCategory.functorToAction?>
:::

::: mathlib
`CategoryTheory.PreGaloisCategory.functorToAction_full` · `Mathlib.CategoryTheory.Galois.Full`

The theorem on fullness, as an instance of `Functor.Full`. The lemma on the lift of subobjects is `exists_lift_of_mono`, for a monomorphism `Y ⟶ (functorToAction F).obj X` of `Aut F`-sets.

<?decl CategoryTheory.PreGaloisCategory.functorToAction_full?>
:::

::: mathlib
`CategoryTheory.PreGaloisCategory.exists_lift_of_continuous` · `Mathlib.CategoryTheory.Galois.EssSurj`

The theorem on the essential image. For a finite `Aut F`-set `X` with a continuous action, it gives `A : C` with an isomorphism of `Aut F`-sets from `(functorToAction F).obj A` to `X`. The case of one orbit is `exists_lift_of_quotient_openSubgroup`.

<?decl CategoryTheory.PreGaloisCategory.exists_lift_of_continuous?>
:::

::: mathlib
`CategoryTheory.PreGaloisCategory.functorToContAction` · `Mathlib.CategoryTheory.Galois.Equivalence`

The functor `C ⥤ ContAction FintypeCat (Aut F)`. The file gives the instances `Faithful`, `Full`, `EssSurj` and `IsEquivalence`, and the last one is the main theorem. The category `ContAction` is in `Mathlib.CategoryTheory.Action.Continuous`.

<?decl CategoryTheory.PreGaloisCategory.functorToContAction?>
:::

::: mathlib
`CategoryTheory.PreGaloisCategory.IsFundamentalGroup` · `Mathlib.CategoryTheory.Galois.IsFundamentalgroup`

The class of fundamental groups of `F`. It extends `IsNaturalSMul F G`, and its fields are `transitive_of_isGalois`, `continuous_smul` and `non_trivial'`. It needs `[IsTopologicalGroup G]` and `[CompactSpace G]`. The map is `toAut F G`, and `toAutMulEquiv F G` and `toAutHomeo F G` give the isomorphism and the homeomorphism.

<?decl CategoryTheory.PreGaloisCategory.IsFundamentalGroup?>
:::

::: mathlib
`CategoryTheory.ObjectProperty.IsGaloisSubcategory` · `Mathlib.CategoryTheory.Galois.FullSubcategory`

The criterion for full subcategories in the example on profinite groups. An instance makes `P.FullSubcategory` a Galois category when `C` is one. The file `Galois.ContAction` applies it to `Action.isContinuous FintypeCat G` with `Action.isContinuous_eq_iSup`.

<?decl CategoryTheory.ObjectProperty.IsGaloisSubcategory?>
:::

The theorem on the group as a limit also gives `FibreFunctor.end_isUnit`, which says that each endomorphism of `F` is a unit. The basis of neighborhoods is `nhds_one_has_basis_stabilizers`, and the continuity of the action is `continuousSMul_aut_fiber`. The universal property is `toAut_bijective` with `toAut_isHomeomorph`, and the instance for `Aut F` itself is `instIsFundamentalGroupAutFunctorFintypeCat`.

Common errors of a learner:

- The theorems on pro-representability and the group as a limit need `F : C ⥤ FintypeCat.{u₂}`, where `u₂` is the universe of the morphisms of `C`. Later theorems remove this condition with `FintypeCat.uSwitch`.
- The group `Aut F` acts on `F.obj X` by `σ.asIso.hom.app X`. The lemma `mulAction_def` unfolds the action, and `mulAction_naturality` moves it past `F.map f`.
- The isomorphism `autMulEquivAutGalois` goes to the opposite group. The composition of natural transformations and the composition of automorphisms in `C` are in opposite orders.
- A statement about a known group, such as an absolute Galois group, uses `IsFundamentalGroup F G` and not `Aut F` itself. This is the design of the file `Galois.IsFundamentalgroup`.

### Exercises

1. (A) Show that a morphism of pointed Galois objects $(A, a) \to (A, a')$ is an automorphism of $A$, and that each $\varphi \in \mathrm{Aut}(A)$ is such a morphism for one $a'$.
2. (A) Show that the stabilizer of a point of $F(X)$ is an open subgroup of $\mathrm{Aut}(F)$ for each object $X$.
3. (A) Use the main theorem to show that $X$ is connected if and only if $\mathrm{Aut}(F)$ acts transitively on $F(X)$ and $F(X)$ is not empty.
4. (B) Let $X$ be connected and $x \in F(X)$, with stabilizer $U$. Show that $\mathrm{Hom}(X, Y) \to F(Y)^U$, $f \mapsto F(f)(x)$, is a bijection onto the points fixed by $U$. *Hint:* use the theorem on fullness for $H(X) \cong \mathrm{Aut}(F)/U$.
5. (B) Show that two fiber functors $F$ and $F'$ on the same Galois category give isomorphic profinite groups $\mathrm{Aut}(F)$ and $\mathrm{Aut}(F')$. *Hint:* the two equivalences give an equivalence of the continuous finite sets of the two groups, and a profinite group is the fundamental group of the forgetful functor.
6. (B) Let $G = \mathbb{Z}$ with the discrete topology. Describe the finite $G$-sets, and show that $\mathrm{Aut}$ of the forgetful functor is the profinite completion $\widehat{\mathbb{Z}}$ and not $\mathbb{Z}$. Which hypothesis of the universal property fails for $\mathbb{Z}$?
7. (C) Prove that the limit of a cofiltered system of nonempty finite sets is not empty, by the use of the theorem of Tychonoff and the finite intersection property.

### Notes and history

The main theorem is due to Grothendieck, SGA 1, Exposé V, Theorem 4.1. Grothendieck defined the étale fundamental group of a connected scheme as the fundamental group of the Galois category of its finite étale coverings, with the fiber functor at a geometric point. The proof in Mathlib follows the notes of Lenstra, *Galois theory for schemes*, and the Stacks Project, Tags 0BMQ and 0BN4. The design of `IsFundamentalGroup` lets a later file identify the fundamental group with a known group without a transport along `Aut F`.

The Mathlib Authors line of `Galois.Prorepresentability`, `Galois.Action`, `Galois.Topology`, `Galois.Full`, `Galois.EssSurj`, `Galois.Equivalence` and `Galois.IsFundamentalgroup` names Christian Merten. The files `Galois.ContAction` and `Galois.FullSubcategory` are by Joël Riou.

### Reference

<?reference?>
