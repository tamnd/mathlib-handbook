---
title: Adjunctions
kind: theory
modules:
  - Mathlib.CategoryTheory.Adjunction.Basic
  - Mathlib.CategoryTheory.Category.GaloisConnection
explains:
  E3: [CategoryTheory.Adjunction, CategoryTheory.Adjunction.homEquiv, CategoryTheory.Adjunction.unit, CategoryTheory.Adjunction.counit, CategoryTheory.Adjunction.mkOfUnitCounit]
  E2: [CategoryTheory.Adjunction.mkOfHomEquiv, CategoryTheory.Adjunction.CoreHomEquiv, CategoryTheory.Adjunction.CoreUnitCounit, CategoryTheory.Adjunction.left_triangle_components, CategoryTheory.Adjunction.right_triangle_components, CategoryTheory.Adjunction.left_triangle, CategoryTheory.Adjunction.right_triangle, CategoryTheory.Adjunction.homEquiv_unit, CategoryTheory.Adjunction.homEquiv_counit, CategoryTheory.Adjunction.homEquiv_naturality_left, CategoryTheory.Adjunction.homEquiv_naturality_right, CategoryTheory.Adjunction.unit_naturality, CategoryTheory.Adjunction.counit_naturality, CategoryTheory.Functor.IsLeftAdjoint, CategoryTheory.Functor.IsRightAdjoint, CategoryTheory.Functor.leftAdjoint, CategoryTheory.Functor.rightAdjoint, CategoryTheory.Adjunction.ofIsRightAdjoint, CategoryTheory.Adjunction.ofIsLeftAdjoint, CategoryTheory.Adjunction.id, CategoryTheory.Equivalence.toAdjunction, GaloisConnection.adjunction]
  E1: auto
families: []
requires: [V24.C01, V24.C02, V24.C03, V24.C04, V04, V05, V13]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Adjunctions

### Overview

The free group on a set $S$ has a property that determines it: a homomorphism from it to a group $H$ is the same as a function from $S$ to the underlying set of $H$. The product topology, the tensor product, the abelianization and the image of a subset under a function have properties of the same form. An adjunction between functors $F : C \to D$ and $G : D \to C$ is a bijection $\mathrm{Hom}_D(F X, Y) \cong \mathrm{Hom}_C(X, G Y)$, natural in both variables. This section gives the definition, its second form by a unit and a counit, and the proof that the two forms are equivalent. The examples compute the unit and the counit for free groups, Galois connections, currying and topological spaces.

### Definitions

Throughout, $C$ and $D$ are categories. Mathlib writes composition in diagram order: `f ≫ g` is the textbook $g \circ f$. This text uses $g \circ f$ in mathematics and `f ≫ g` in code.

**Definition (Adjunction).** An *adjunction* $F \dashv G$ between functors $F : C \to D$ and $G : D \to C$ is a family of bijections
$$\varphi_{X, Y} : \mathrm{Hom}_D(F X, Y) \to \mathrm{Hom}_C(X, G Y)$$
for objects $X$ of $C$ and $Y$ of $D$, natural in $X$ and $Y$. Explicitly, for $h : X' \to X$, $f : F X \to Y$ and $k : Y \to Y'$,
$$\varphi_{X', Y'}(k \circ f \circ F(h)) = G(k) \circ \varphi_{X, Y}(f) \circ h.$$
$F$ is the *left adjoint* and $G$ the *right adjoint*. The image $\varphi(f)$ is the *transpose* of $f$.

The naturality condition is the statement that $\varphi$ is a natural isomorphism between the two functors $C^{\mathrm{op}} \times D \to \mathbf{Set}$ given by $(X, Y) \mapsto \mathrm{Hom}(F X, Y)$ and $(X, Y) \mapsto \mathrm{Hom}(X, G Y)$. It is enough to check it with $k = 1$ and with $h = 1$ separately.

**Definition (Unit and counit).** A *unit-counit adjunction* between $F$ and $G$ is a pair of natural transformations $\eta : 1_C \Rightarrow G F$ and $\varepsilon : F G \Rightarrow 1_D$ that satisfy the *triangle identities*
$$\varepsilon_{F X} \circ F(\eta_X) = 1_{F X}, \qquad G(\varepsilon_Y) \circ \eta_{G Y} = 1_{G Y}$$
for all $X$ in $C$ and $Y$ in $D$.

::: mathlib
`CategoryTheory.Adjunction` · `Mathlib.CategoryTheory.Adjunction.Basic`

`Adjunction F G`, with notation `F ⊣ G`, is a structure with four fields: `unit : 𝟭 C ⟶ F ⋙ G`, `counit : G ⋙ F ⟶ 𝟭 D`, and the triangle identities `left_triangle_components X : F.map (unit.app X) ≫ counit.app (F.obj X) = 𝟙 _` and `right_triangle_components Y : unit.app (G.obj Y) ≫ G.map (counit.app Y) = 𝟙 _`. The bijection is a definition built from them, `adj.homEquiv X Y : (F.obj X ⟶ Y) ≃ (X ⟶ G.obj Y)`, with `homEquiv_unit` and `homEquiv_counit` as the formulas of the theorem below. Mathlib stores the unit and the counit because they are the data that proofs use most. The forms of the triangle identities as equations of natural transformations are `left_triangle` and `right_triangle`.

<?decl CategoryTheory.Adjunction?>
<?decl CategoryTheory.Adjunction.homEquiv?>
:::

### Theorems and proofs

**Theorem (Two forms of an adjunction).** Let $F : C \to D$ and $G : D \to C$.

1. Given an adjunction $\varphi$, put $\eta_X = \varphi(1_{F X})$ and $\varepsilon_Y = \varphi^{-1}(1_{G Y})$. Then $\eta$ and $\varepsilon$ are natural, they satisfy the triangle identities, and
$$\varphi(f) = G(f) \circ \eta_X, \qquad \varphi^{-1}(g) = \varepsilon_Y \circ F(g).$$
2. Conversely, given $\eta$ and $\varepsilon$ that satisfy the triangle identities, the formulas above define an adjunction.

The two constructions are inverse to each other.

*Proof.* (1) *The formulas.* Naturality in $Y$ with $h = 1$ and $f = 1_{F X}$ gives $\varphi(k) = \varphi(k \circ 1_{F X}) = G(k) \circ \varphi(1_{F X}) = G(k) \circ \eta_X$ for each $k : F X \to Y$. Naturality of $\varphi$ in $X$ gives naturality of $\varphi^{-1}$ in $X$: $\varphi^{-1}(g \circ h) = \varphi^{-1}(g) \circ F(h)$. Apply this with $g = 1_{G Y}$ to get $\varphi^{-1}(h) = \varepsilon_Y \circ F(h)$ for each $h : X \to G Y$.

*Naturality of $\eta$.* Let $h : X \to X'$. By the formula, $G F(h) \circ \eta_X = \varphi(F(h))$. By naturality in $X$, $\eta_{X'} \circ h = \varphi(1_{F X'}) \circ h = \varphi(1_{F X'} \circ F(h)) = \varphi(F(h))$. So $G F(h) \circ \eta_X = \eta_{X'} \circ h$. The proof for $\varepsilon$ is dual: for $k : Y \to Y'$, both $k \circ \varepsilon_Y$ and $\varepsilon_{Y'} \circ F G(k)$ equal $\varphi^{-1}(G(k))$.

*The triangles.* $\varepsilon_{F X} \circ F(\eta_X) = \varphi^{-1}(\eta_X) = \varphi^{-1}(\varphi(1_{F X})) = 1_{F X}$, and $G(\varepsilon_Y) \circ \eta_{G Y} = \varphi(\varepsilon_Y) = \varphi(\varphi^{-1}(1_{G Y})) = 1_{G Y}$.

(2) Put $\varphi(f) = G(f) \circ \eta_X$ and $\psi(g) = \varepsilon_Y \circ F(g)$. For $f : F X \to Y$,
$$\psi(\varphi(f)) = \varepsilon_Y \circ F G(f) \circ F(\eta_X) = f \circ \varepsilon_{F X} \circ F(\eta_X) = f,$$
by naturality of $\varepsilon$ and the first triangle. For $g : X \to G Y$,
$$\varphi(\psi(g)) = G(\varepsilon_Y) \circ G F(g) \circ \eta_X = G(\varepsilon_Y) \circ \eta_{G Y} \circ g = g,$$
by naturality of $\eta$ and the second triangle. So $\varphi$ is a bijection with inverse $\psi$. For naturality, let $h : X' \to X$ and $k : Y \to Y'$. Then
$$\varphi(k \circ f \circ F(h)) = G(k) \circ G(f) \circ G F(h) \circ \eta_{X'} = G(k) \circ G(f) \circ \eta_X \circ h = G(k) \circ \varphi(f) \circ h.$$

*Inverse constructions.* Start from $\varphi$. The adjunction built in (2) from $\eta, \varepsilon$ is $f \mapsto G(f) \circ \eta_X$, which is $\varphi$ by the formula in (1). Start from $\eta, \varepsilon$. The unit of the adjunction of (2) is $\varphi(1_{F X}) = G(1_{F X}) \circ \eta_X = \eta_X$, and the counit is $\psi(1_{G Y}) = \varepsilon_Y$. $\square$

So the transpose of $f : F X \to Y$ is "first $\eta_X$, then $G(f)$", and the transpose of $g : X \to G Y$ is "first $F(g)$, then $\varepsilon_Y$".

**Proposition (Adjoint equivalences).** If $(F, G, \eta, \varepsilon)$ is an equivalence of categories in which $\eta$ and $\varepsilon$ satisfy the triangle identities, then $F \dashv G$. The identity functor is adjoint to itself, with $\eta$ and $\varepsilon$ the identities.

*Proof.* The data are a unit and a counit that satisfy the triangle identities, so part (2) of the theorem applies. For the identity functor, both triangles read $1 \circ 1 = 1$. $\square$

Every equivalence can be improved to one in which the triangles hold, so every equivalence gives adjunctions in both directions. Mathlib's `Equivalence` stores a triangle identity as the field `functor_unitIso_comp`.

::: mathlib
`CategoryTheory.Adjunction.mkOfUnitCounit` · `Mathlib.CategoryTheory.Adjunction.Basic`

Part (2) of the theorem is `Adjunction.mkOfUnitCounit`, which takes a `CoreUnitCounit F G`: a unit, a counit and the two triangle identities. Part (1), the direction from bijections, is `Adjunction.mkOfHomEquiv`, which takes a `CoreHomEquiv F G`: the bijections `homEquiv X Y` and the two halves of naturality, in the form `homEquiv_naturality_left_symm` and `homEquiv_naturality_right`. For an existing adjunction the two halves are the lemmas `homEquiv_naturality_left` and `homEquiv_naturality_right`. The proposition is `Equivalence.toAdjunction` and `Adjunction.id`.

<?decl CategoryTheory.Adjunction.mkOfUnitCounit?>
<?decl CategoryTheory.Adjunction.mkOfHomEquiv?>
:::

### Examples

**Example (Free groups).** Let $U : \mathbf{Grp} \to \mathbf{Set}$ be the forgetful functor and $F(S)$ the free group on $S$, with generators $e_s$ for $s \in S$. The universal property of the free group says that each function $S \to U(H)$ extends to exactly one homomorphism $F(S) \to H$. So restriction to the generators is a bijection $\mathrm{Hom}(F S, H) \to \mathrm{Hom}(S, U H)$, and it is natural, so $F \dashv U$. The unit $\eta_S : S \to U F(S)$ sends $s$ to the word $e_s$. The counit $\varepsilon_H : F(U H) \to H$ evaluates a word in the elements of $H$. For $H = \mathbb{Z}/3$, the free group $F(U H)$ has three generators $e_0, e_1, e_2$, and
$$\varepsilon_H(e_1 e_2 e_1^{-1}) = 1 + 2 - 1 = 2.$$
The second triangle says that $h \mapsto e_h \mapsto h$ is the identity of $U(H)$. The first says that the word $e_{e_s}$ in $F(U F(S))$ evaluates to $e_s$.

**Example (Galois connections).** Let $P$ and $Q$ be posets, seen as categories (Chapter 1). Monotone maps $l : P \to Q$ and $u : Q \to P$ are adjoint, $l \dashv u$, exactly when $l(x) \le y \iff x \le u(y)$ for all $x, y$. Hom sets have at most one element, so the bijection is this equivalence and naturality holds automatically. This is a Galois connection (Volume 4, Chapter 6). The unit says $x \le u(l(x))$ and the counit $l(u(y)) \le y$. For a function $f : A \to B$, the image and preimage maps on subsets give $f(S) \subseteq T \iff S \subseteq f^{-1}(T)$, so image is left adjoint to preimage.

**Example (Currying).** In $\mathbf{Set}$, fix a set $A$. A function $f : X \times A \to Y$ corresponds to the function $\tilde f : X \to Y^A$, $\tilde f(x)(a) = f(x, a)$. This bijection is natural, so $(- \times A) \dashv (-)^A$. The unit $X \to (X \times A)^A$ sends $x$ to $a \mapsto (x, a)$, and the counit $Y^A \times A \to Y$ is evaluation, $(g, a) \mapsto g(a)$.

**Example (Topological spaces).** Let $U : \mathbf{Top} \to \mathbf{Set}$ be the forgetful functor, $D(S)$ the set $S$ with the discrete topology, and $I(S)$ the set $S$ with the indiscrete topology. Every function from a discrete space is continuous, and every function to an indiscrete space is continuous. So $\mathrm{Hom}(D S, X) = \mathrm{Hom}(S, U X)$ and $\mathrm{Hom}(U X, S) = \mathrm{Hom}(X, I S)$, and $D \dashv U \dashv I$. Both units and counits are identity maps of sets.

**Counterexample (Fields).** The forgetful functor $U$ from fields to sets has no left adjoint. Suppose $F \dashv U$. Then for every field $K$, $\mathrm{Hom}(F(\emptyset), K) \cong \mathrm{Hom}(\emptyset, U K)$, a one-point set. So $F(\emptyset)$ is an initial field and has homomorphisms to $\mathbb{Q}$ and to $\mathbb{F}_2$. Its characteristic would be both $0$ and $2$.

::: mathlib
`GrpCat.adj` · `Mathlib.Algebra.Category.Grp.Adjunctions`

The free group adjunction is `GrpCat.adj : GrpCat.free ⊣ forget GrpCat`, built with `Adjunction.mkOfHomEquiv` from `FreeGroup.lift`. The adjunctions of spaces are `TopCat.adj₁ : TopCat.discrete ⊣ forget TopCat` and `TopCat.adj₂ : forget TopCat ⊣ TopCat.trivial`. A Galois connection gives `GaloisConnection.adjunction` between the functors of the two monotone maps.

<?decl GrpCat.adj?>
<?decl TopCat.adj₁?>
<?decl TopCat.adj₂?>
<?decl GaloisConnection.adjunction?>
:::

### The library around it

`Functor.IsLeftAdjoint F` and `Functor.IsRightAdjoint G` are classes in `Prop` that say an adjoint exists. Under them, `F.rightAdjoint` and `G.leftAdjoint` choose one, and `Adjunction.ofIsLeftAdjoint` and `Adjunction.ofIsRightAdjoint` give the adjunction. The lemmas `unit_naturality` and `counit_naturality` are the naturality squares in a form that `simp` can use.

Common errors of a learner:

- Swapping the sides. In `F ⊣ G` the left adjoint `F` is the one whose maps go *out of* `F.obj X`.
- Expecting `adj.homEquiv X Y f` to simplify to something other than `adj.unit.app X ≫ G.map f`. That is its definition.
- Proving naturality of a bijection by hand when `Adjunction.mkOfHomEquiv` needs only the two halves.

### Exercises

1. (A) Show that the abelian group $\mathbb{Z}^{(S)}$ of finitely supported functions $S \to \mathbb{Z}$ gives a left adjoint to the forgetful functor from abelian groups to sets. Compute the counit on the element $2 e_1 - e_3$ of $\mathbb{Z}^{(U \mathbb{Z})}$.
2. (A) Show that the diagonal $\Delta : C \to C \times C$ has a right adjoint if and only if $C$ has binary products.
3. (A) Show that the inclusion of $\mathbb{Z}$ into $\mathbb{R}$, as posets, has a left adjoint and a right adjoint, and identify them.
4. (B) Let $F \dashv G$. Show that $F$ sends initial objects to initial objects and that $G$ sends terminal objects to terminal objects.
5. (B) Show that the forgetful functor from rings to sets has a left adjoint, the polynomial ring. Describe the unit and the counit.
6. (B) Let $F \dashv G$ with unit $\eta$. Show that $G$ is faithful if and only if each $\varepsilon_Y$ is an epimorphism.
7. (C) Show that $G : D \to C$ has a left adjoint if and only if the functor $\mathrm{Hom}_C(X, G(-)) : D \to \mathbf{Set}$ is representable for every object $X$ of $C$. Hint: choose representing objects $F X$, and use the Yoneda lemma (Chapter 3) to make $X \mapsto F X$ a functor.

### Notes and history

Kan introduced adjoint functors in 1958. Galois connections between posets are older, and they are the special case where all Hom sets have at most one element. Mac Lane's book (1971) has the slogan "adjoint functors arise everywhere".

### Reference

<?reference?>
