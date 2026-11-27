---
title: Natural transformations
kind: theory
modules:
  - Mathlib.CategoryTheory.NatTrans
  - Mathlib.CategoryTheory.Functor.Category
  - Mathlib.CategoryTheory.NatIso
  - Mathlib.CategoryTheory.Whiskering
  - Mathlib.CategoryTheory.Functor.Const
explains:
  E3: [CategoryTheory.NatTrans, CategoryTheory.Functor.category, CategoryTheory.NatIso.isIso_of_isIso_app, CategoryTheory.NatTrans.hcomp, CategoryTheory.Functor.whiskerLeft]
  E2: [CategoryTheory.NatTrans.app, CategoryTheory.NatTrans.naturality, CategoryTheory.NatTrans.ext, CategoryTheory.NatTrans.id, CategoryTheory.NatTrans.vcomp, CategoryTheory.NatTrans.comp_app, CategoryTheory.NatTrans.id_app, CategoryTheory.NatTrans.hcomp_app, CategoryTheory.NatTrans.exchange, CategoryTheory.NatIso.ofComponents, CategoryTheory.Iso.app, CategoryTheory.NatIso.isIso_app_of_isIso, CategoryTheory.Functor.whiskerRight, CategoryTheory.Functor.NatTrans.hcomp_eq_whiskerLeft_comp_whiskerRight, CategoryTheory.Functor.const]
  E1: auto
families: []
requires: [V24.C01, V05.C05, V06.C01, V07.C04, V07.C06, V08.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Natural transformations

### Overview

A vector space $V$ maps to its double dual $V^{**}$ by $v \mapsto (\lambda \mapsto \lambda(v))$. This map needs no choice: it is defined in the same way for each $V$, and it commutes with all linear maps. A finite-dimensional space is also isomorphic to its dual $V^*$, but each such isomorphism depends on a basis. Natural transformations make this difference precise. Eilenberg and Mac Lane defined categories and functors for this purpose.

A natural transformation from a functor $F$ to a functor $G$ is a family of morphisms $F(X) \to G(X)$, one for each object $X$, that commutes with the images of all morphisms. The natural transformations between two functors $C \to D$ are the morphisms of a new category, the functor category. This section defines them, proves that a natural transformation is an isomorphism exactly when each component is one, and studies whiskering and horizontal composition.

Mathlib writes `α.app X` for the component of `α` at `X`, and composes in diagram order: `α ≫ β` is the textbook $\beta \circ \alpha$, as `f ≫ g` is $g \circ f$.

### Definitions

**Definition (Natural transformation).** Let $F, G : C \to D$ be functors. A *natural transformation* $\alpha : F \Rightarrow G$ is a family of morphisms $\alpha_X : F(X) \to G(X)$, one for each object $X$ of $C$, such that for each $f : X \to Y$,
$$G(f) \circ \alpha_X = \alpha_Y \circ F(f).$$
This equation is the *naturality square*. The $\alpha_X$ are the *components* of $\alpha$.

::: mathlib
`CategoryTheory.NatTrans` · `Mathlib.CategoryTheory.NatTrans`

`NatTrans F G` is a structure with the field `app : ∀ X, F.obj X ⟶ G.obj X` and the field `naturality : F.map f ≫ α.app Y = α.app X ≫ G.map f`. The naturality law has the default proof `by cat_disch`. The lemma `NatTrans.ext` says that two natural transformations are equal when their components are equal. `NatTrans.id F` has the components `𝟙 (F.obj X)`, and `NatTrans.vcomp α β` composes componentwise.

<?decl CategoryTheory.NatTrans?>
:::

**Definition (Vertical composition and the functor category).** Let $\alpha : F \Rightarrow G$ and $\beta : G \Rightarrow H$. Their *vertical composite* $\beta \circ \alpha$ has the components $\beta_X \circ \alpha_X$. The *functor category* $[C, D]$ has the functors $C \to D$ as objects and the natural transformations as morphisms, with vertical composition and the identity transformations $1_F$.

The vertical composite is natural: for $f : X \to Y$,
$$H(f) \circ \beta_X \circ \alpha_X = \beta_Y \circ G(f) \circ \alpha_X = \beta_Y \circ \alpha_Y \circ F(f).$$
The axioms of a category hold in each component, so $[C, D]$ is a category. A *natural isomorphism* is an isomorphism in $[C, D]$.

::: mathlib
`CategoryTheory.Functor.category` · `Mathlib.CategoryTheory.Functor.Category`

The instance that makes `C ⥤ D` a category, with `F ⟶ G` equal to `NatTrans F G`. The simp lemmas `NatTrans.comp_app : (α ≫ β).app X = α.app X ≫ β.app X` and `NatTrans.id_app` compute the components. If `C` has objects in `Type u₁` and `D` has morphisms in `Type v₂`, then `C ⥤ D` has morphisms in `Type (max u₁ v₂)`.

<?decl CategoryTheory.Functor.category?>
:::

**Definition (Whiskering and horizontal composition).** Let $F, G : C \to D$ with $\alpha : F \Rightarrow G$, and $H, K : D \to E$ with $\beta : H \Rightarrow K$. The *whiskering* $H\alpha : H \circ F \Rightarrow H \circ G$ has the components $H(\alpha_X)$. For $L : B \to C$, the whiskering $\alpha L : F \circ L \Rightarrow G \circ L$ has the components $\alpha_{L(X)}$. The *horizontal composite* $\beta * \alpha : H \circ F \Rightarrow K \circ G$ has the components
$$(\beta * \alpha)_X = K(\alpha_X) \circ \beta_{F(X)}.$$

### Theorems and proofs

**Theorem (Componentwise isomorphisms).** A natural transformation $\alpha : F \Rightarrow G$ is a natural isomorphism if and only if each component $\alpha_X$ is an isomorphism.

*Proof.* If $\beta$ is an inverse of $\alpha$ in $[C, D]$, then $\beta_X \circ \alpha_X = 1_{F(X)}$ and $\alpha_X \circ \beta_X = 1_{G(X)}$, since composition and identities are componentwise. Conversely, let each $\alpha_X$ have an inverse $\beta_X$. It suffices to show that $\beta$ is natural. Let $f : X \to Y$. Naturality of $\alpha$ gives $G(f) \circ \alpha_X = \alpha_Y \circ F(f)$. Compose with $\beta_Y$ on the left and with $\beta_X$ on the right:
$$\beta_Y \circ G(f) \circ \alpha_X \circ \beta_X = \beta_Y \circ \alpha_Y \circ F(f) \circ \beta_X.$$
This is $\beta_Y \circ G(f) = F(f) \circ \beta_X$, the naturality of $\beta$. Then $\beta$ is an inverse of $\alpha$ in each component, so in $[C, D]$. $\square$

::: mathlib
`CategoryTheory.NatIso.isIso_of_isIso_app` · `Mathlib.CategoryTheory.NatIso`

If `IsIso (α.app X)` for each `X`, then `IsIso α`. The converse is `NatIso.isIso_app_of_isIso`, and `Iso.app` gives the component of an isomorphism of functors. To build `F ≅ G` from components, use `NatIso.ofComponents`: it takes `F.obj X ≅ G.obj X` for each `X` and the naturality of the forward maps only, as in the proof above.

<?decl CategoryTheory.NatIso.isIso_of_isIso_app?>
:::

**Proposition (Two forms of the horizontal composite).** In the notation above, for each $X$,
$$K(\alpha_X) \circ \beta_{F(X)} = \beta_{G(X)} \circ H(\alpha_X).$$
So $\beta * \alpha = (\beta G) \circ (H\alpha) = (K\alpha) \circ (\beta F)$, and $\beta * \alpha$ is natural.

*Proof.* The equation is the naturality square of $\beta$ at the morphism $\alpha_X : F(X) \to G(X)$ of $D$. The whiskerings are natural: $H\alpha$ is the image of the naturality square of $\alpha$ under $H$, and $\beta G$ is the naturality of $\beta$ at the morphisms $G(f)$. A vertical composite of natural transformations is natural, so $\beta * \alpha$ is natural. $\square$

**Theorem (Interchange law).** Let $\alpha : F \Rightarrow G$, $\alpha' : G \Rightarrow G'$ between functors $C \to D$, and $\beta : H \Rightarrow K$, $\beta' : K \Rightarrow K'$ between functors $D \to E$. Then
$$(\beta' \circ \beta) * (\alpha' \circ \alpha) = (\beta' * \alpha') \circ (\beta * \alpha).$$

*Proof.* Compute the component at $X$. The left side is $K'(\alpha'_X \circ \alpha_X) \circ \beta'_{F(X)} \circ \beta_{F(X)}$. The right side is $K'(\alpha'_X) \circ \beta'_{G(X)} \circ K(\alpha_X) \circ \beta_{F(X)}$. Naturality of $\beta'$ at $\alpha_X$ gives $\beta'_{G(X)} \circ K(\alpha_X) = K'(\alpha_X) \circ \beta'_{F(X)}$. So the right side is $K'(\alpha'_X) \circ K'(\alpha_X) \circ \beta'_{F(X)} \circ \beta_{F(X)}$, which equals the left side by functoriality of $K'$. $\square$

::: mathlib
`CategoryTheory.NatTrans.hcomp` · `Mathlib.CategoryTheory.Functor.Category`

For `α : F ⟶ G` and `β : H ⟶ I`, the horizontal composite `α ◫ β : F ⋙ H ⟶ G ⋙ I`. The order of the arguments is the diagram order. The lemma `NatTrans.hcomp_app` gives the component `β.app (F.obj X) ≫ I.map (α.app X)`, and `NatTrans.exchange` is the interchange law. The lemma `Functor.NatTrans.hcomp_eq_whiskerLeft_comp_whiskerRight` expresses `α ◫ β` with whiskerings.

<?decl CategoryTheory.NatTrans.hcomp?>
:::

::: mathlib
`CategoryTheory.Functor.whiskerLeft` · `Mathlib.CategoryTheory.Whiskering`

`Functor.whiskerLeft L α : L ⋙ F ⟶ L ⋙ G` for `α : F ⟶ G`, with the components `α.app (L.obj X)`. This is the textbook $\alpha L$. `Functor.whiskerRight α H : F ⋙ H ⟶ G ⋙ H` has the components `H.map (α.app X)`, the textbook $H\alpha$. The words "left" and "right" refer to the side of the functor in the diagram order.

<?decl CategoryTheory.Functor.whiskerLeft?>
:::

### Examples

**Example (The double dual).** Let $k$ be a field and $\mathbf{Vect}_k$ the category of $k$-vector spaces. The double dual $V \mapsto V^{**}$ is a covariant functor, the composite of two contravariant ones (Section 1). Define $\mathrm{ev}_V : V \to V^{**}$ by $\mathrm{ev}_V(v)(\lambda) = \lambda(v)$. For a linear map $f : V \to W$, the map $f^{**}$ sends $\Phi$ to $\Phi \circ f^*$. So, for $\mu \in W^*$,
$$f^{**}(\mathrm{ev}_V(v))(\mu) = \mathrm{ev}_V(v)(\mu \circ f) = \mu(f(v)) = \mathrm{ev}_W(f(v))(\mu).$$
So $f^{**} \circ \mathrm{ev}_V = \mathrm{ev}_W \circ f$, and $\mathrm{ev}$ is a natural transformation from the identity functor to the double dual. On finite-dimensional spaces each $\mathrm{ev}_V$ is an isomorphism (Volume 7, Chapter 6), so $\mathrm{ev}$ is a natural isomorphism by the theorem above.

::: mathlib
`Module.Dual.eval` · `Mathlib.LinearAlgebra.Dual.Defs`

The linear map `V →ₗ[R] Dual R (Dual R V)` with `eval R V v f = f v`. `Module.evalEquiv` is the linear equivalence in finite dimension. Mathlib states each map for one module. The index of this edition has no declaration for the double dual as a natural isomorphism of functors on `ModuleCat`.

<?decl Module.Dual.eval?>
:::

**Example (The determinant).** Fix $n \ge 1$. On commutative rings, $R \mapsto \mathrm{GL}_n(R)$ and $R \mapsto R^\times$ are functors to groups. A ring homomorphism $f$ acts on a matrix entrywise. The determinant $\det_R : \mathrm{GL}_n(R) \to R^\times$ is a homomorphism of groups (Volume 7, Chapter 4). It is natural: the determinant is a polynomial in the entries with integer coefficients, and $f$ commutes with sums and products, so $f(\det A) = \det f(A)$.

**Example (The abelianization).** For each group $G$, the quotient map $q_G : G \to G/[G, G]$ is a homomorphism. Let $U$ be the functor from abelian groups to groups that forgets commutativity, and $G \mapsto G^{\mathrm{ab}}$ the abelianization functor. Then $q$ is a natural transformation from the identity functor on groups to $U \circ (\cdot)^{\mathrm{ab}}$. For $f : G \to H$, the map $f^{\mathrm{ab}}$ is defined by $f^{\mathrm{ab}} \circ q_G = q_H \circ f$, which is the naturality square (Volume 5, Chapter 5). Chapter 5 shows that this is the unit of an adjunction.

**Counterexample (A space and its dual).** Let $\mathcal{V}$ be the category of finite-dimensional real vector spaces with linear isomorphisms. Define $D(V) = V^*$ and $D(f) = (f^{-1})^* = (f^*)^{-1}$, a covariant functor on $\mathcal{V}$. Each $V$ is isomorphic to $D(V)$. But there is no natural isomorphism $\varphi$ from the identity to $D$. Take $V = \mathbb{R}$ and $f = 2$. Naturality gives $\varphi(2v) = \varphi(v) \circ f^{-1}$, so $2\varphi(v)(w) = \varphi(v)(w/2) = \tfrac{1}{2}\varphi(v)(w)$ for all $v, w$. Then $\varphi = 0$, and $\varphi$ is not an isomorphism.

**Example (Constant functors).** For a category $J$ and an object $X$ of $C$, the *constant functor* $\Delta X : J \to C$ sends each object to $X$ and each morphism to $1_X$. A natural transformation $\Delta X \Rightarrow F$ is a family $\pi_j : X \to F(j)$ with $F(u) \circ \pi_j = \pi_{j'}$ for each $u : j \to j'$. This is a cone over $F$, the first notion of Chapter 4. In Mathlib, `Functor.const J : C ⥤ (J ⥤ C)` is this construction.

### The library around it

The files `Mathlib.CategoryTheory.NatTrans` and `Mathlib.CategoryTheory.Functor.Category` define natural transformations and the functor category. The file `Mathlib.CategoryTheory.Whiskering` has the whiskering functors `Functor.whiskeringLeft` and `Functor.whiskeringRight`, and `Mathlib.CategoryTheory.NatIso` has the natural isomorphisms. The unitors and the associator of functor composition, `Functor.leftUnitor` and `Functor.associator`, are natural isomorphisms whose components are identities.

Common errors of a learner:

- The component of `α` at `X` is `α.app X`, and the composite of `α` and `β` in `C ⥤ D` is `α ≫ β`, the textbook $\beta \circ \alpha$.
- In `α ◫ β` the first argument is the transformation of the first functor in diagram order. Read the type before the use.
- To prove that two natural transformations are equal, use `NatTrans.ext` and compare components. To build an isomorphism of functors, use `NatIso.ofComponents`.

### Exercises

1. (A) Show that a natural isomorphism $\alpha$ has a unique inverse, and that its components are $\alpha_X^{-1}$.
2. (A) Let $P$ and $Q$ be preorders and $\varphi, \psi : P \to Q$ monotone maps. Show that there is a natural transformation $\varphi \Rightarrow \psi$ exactly when $\varphi(a) \le \psi(a)$ for all $a$, and that it is unique.
3. (A) Let $G$ be a group and $\varphi, \psi : G \to H$ homomorphisms, seen as functors $BG \to BH$. Show that a natural transformation $\varphi \Rightarrow \psi$ is an element $h \in H$ with $\psi(g) = h \varphi(g) h^{-1}$ for all $g$.
4. (B) Show that $V \mapsto V \otimes_k W$ is a functor on $\mathbf{Vect}_k$ for fixed $W$, and that the swap maps $V \otimes W \to W \otimes V$ are natural in both variables (Volume 8, Chapter 2).
5. (B) Show that the map $X \to \mathcal{P}(X)$, $x \mapsto \{x\}$, is a natural transformation from the identity functor on sets to the covariant power set functor. Show that $A \mapsto X \setminus A$ is a natural isomorphism from the contravariant power set functor to itself.
6. (B) Prove that the whiskerings satisfy $H(\alpha' \circ \alpha) = H\alpha' \circ H\alpha$ and $(\beta' \circ \beta) F = \beta' F \circ \beta F$, and deduce the interchange law from them.
7. (C) Let $\mathcal{V}$ be as in the counterexample, and allow any field with at least $4$ elements. Show again that no natural isomorphism from the identity to $D$ exists. Hint: use a scalar $c$ with $c^2 \ne 1$.

### Notes and history

Eilenberg and Mac Lane introduced natural transformations in "General theory of natural equivalences" (1945). Mac Lane later wrote that categories were defined in order to define functors, and functors in order to define natural transformations. The double dual was a motivating example in that paper. Mac Lane, *Categories for the Working Mathematician* (1971), Chapter 2, and Riehl, *Category Theory in Context* (2016), Chapter 1, treat functor categories and the interchange law.

### Reference

<?reference?>
