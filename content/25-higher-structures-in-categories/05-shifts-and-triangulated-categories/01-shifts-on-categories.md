---
title: Shifts on categories
kind: theory
modules:
  - Mathlib.CategoryTheory.Shift.Basic
  - Mathlib.CategoryTheory.Shift.CommShift
  - Mathlib.CategoryTheory.Shift.ShiftedHom
explains:
  E3: [CategoryTheory.HasShift, CategoryTheory.shiftFunctor, CategoryTheory.shiftFunctorAdd, CategoryTheory.shiftFunctorZero, CategoryTheory.shiftEquiv, CategoryTheory.shiftFunctorComm, CategoryTheory.Functor.CommShift, CategoryTheory.ShiftedHom, CategoryTheory.ShiftedHom.comp]
  E2: [CategoryTheory.ShiftMkCore, CategoryTheory.hasShiftMk, CategoryTheory.shiftFunctorAdd', CategoryTheory.shiftFunctorAdd'_assoc, CategoryTheory.shiftFunctorCompIsoId, CategoryTheory.shiftComm, CategoryTheory.shift_zero_eq_zero, CategoryTheory.Functor.FullyFaithful.hasShift, CategoryTheory.Functor.CommShift.commShiftIso, CategoryTheory.Functor.CommShift.isoZero, CategoryTheory.Functor.CommShift.isoAdd, CategoryTheory.Functor.CommShift.id, CategoryTheory.Functor.CommShift.comp, CategoryTheory.NatTrans.CommShift, CategoryTheory.ShiftedHom.mk₀, CategoryTheory.ShiftedHom.comp_assoc, CategoryTheory.ShiftedHom.mk₀_comp, CategoryTheory.ShiftedHom.map, CategoryTheory.ShiftedHom.map_comp]
  E1: auto
families: []
requires: [V05, V24.C02, V24.C07, V24.C08]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Shifts on categories

### Overview

A complex of modules can be moved by one degree. The new complex has the same terms and the same differentials, with new indices and a sign. The derived category, the homotopy category and the stable categories of topology all have such an operation, and in each case it is an autoequivalence $X \mapsto X[1]$. A triangulated category is a category with a shift and a class of triangles. This section treats the shift alone. The main point is that the shifts by $a$ and $b$ are not equal to the shift by $a + b$. They are only isomorphic, and the isomorphisms must satisfy coherence conditions. Mathlib makes the shift a monoidal functor from the monoid of indices to the category of endofunctors, which packs these conditions in one notion.

In the text $g \circ f$ is the textbook composite, and Mathlib writes `f ≫ g`. The shift of an object $X$ by $a$ is $X[a]$, and Mathlib writes `X⟦a⟧`. The shift of a morphism $f$ is $f[a]$, written `f⟦a⟧'`.

### Definitions

**Definition (Shift).** Let $A$ be an additive monoid. A *shift* on a category $C$ by $A$ is the data of:

1. a functor $T_a : C \to C$ for each $a \in A$, written $X \mapsto X[a]$;
2. a natural isomorphism $\varepsilon : T_0 \cong 1_C$;
3. natural isomorphisms $\mu_{a,b} : T_{a+b} \cong T_b \circ T_a$, so that $\mu_{a,b}(X) : X[a+b] \to X[a][b]$.

The data satisfy three coherence conditions. For all $a, b, c$ and $X$, the two isomorphisms $X[a+b+c] \to X[a][b][c]$ given by $\mu_{a,b}(X)[c] \circ \mu_{a+b,c}(X)$ and $\mu_{b,c}(X[a]) \circ \mu_{a,b+c}(X)$ are equal. For all $a$ and $X$, $\mu_{0,a}(X) = T_a(\varepsilon(X)^{-1})$ and $\mu_{a,0}(X) = \varepsilon(X[a])^{-1}$, after the identifications $0 + a = a$ and $a + 0 = a$.

These are the conditions for a monoidal functor from the discrete monoidal category of $A$ to the monoidal category of endofunctors of $C$, from Volume 24, Chapter 7.

**Definition (Functor that commutes with shifts).** Let $C$ and $D$ have shifts by $A$. A functor $F : C \to D$ *commutes with the shifts* if it has natural isomorphisms $\varphi_a : F(X[a]) \cong F(X)[a]$ such that $\varphi_0(X) = \varepsilon(FX)^{-1} \circ F(\varepsilon(X))$ and $\varphi_{a+b}(X) = \mu_{a,b}(FX)^{-1} \circ \varphi_a(X)[b] \circ \varphi_b(X[a]) \circ F(\mu_{a,b}(X))$. The isomorphisms $\varphi_a$ are data, and not a property of $F$.

A natural transformation $\tau : F \to G$ between two such functors *commutes with the shifts* if $\tau(X)[a] \circ \varphi^F_a(X) = \varphi^G_a(X) \circ \tau(X[a])$ for all $a$ and $X$.

**Definition (Shifted morphisms).** Let $C$ have a shift by $A$. A *shifted morphism of degree* $a$ from $X$ to $Y$ is a morphism $X \to Y[a]$. For $f : X \to Y[a]$ and $g : Y \to Z[b]$ with $b + a = c$, the composite of degree $c$ is
$$g \cdot f = \mu_{b,a}(Z)^{-1} \circ g[a] \circ f : X \to Y[a] \to Z[b][a] \to Z[c].$$

::: mathlib
`CategoryTheory.HasShift` · `Mathlib.CategoryTheory.Shift.Basic`

The class `HasShift C A` holds a monoidal functor `Discrete A ⥤ C ⥤ C`. A user does not work with it directly. The API is `shiftFunctor C a`, `shiftFunctorZero C A : shiftFunctor C 0 ≅ 𝟭 C` and `shiftFunctorAdd C a b : shiftFunctor C (a + b) ≅ shiftFunctor C a ⋙ shiftFunctor C b`. The variant `shiftFunctorAdd' C a b c h` takes a proof `h : a + b = c`, which avoids rewriting with equalities of indices. To construct a shift, fill in a `ShiftMkCore` and apply `hasShiftMk`.

<?decl CategoryTheory.HasShift?>
:::

### Theorems and proofs

**Theorem (Shifts by a group are equivalences).** Let $A$ be an additive group with a shift on $C$. For $i, j \in A$ with $i + j = 0$, the functors $T_i$ and $T_j$ are inverse equivalences. In particular, each $T_a$ is an equivalence with inverse $T_{-a}$.

*Proof.* Define $\eta : T_j \circ T_i \cong 1_C$ as the composite $X[i][j] \to X[i+j] = X[0] \to X$ of $\mu_{i,j}(X)^{-1}$ and $\varepsilon(X)$. In a group, $i + j = 0$ gives $j = -i$, so $j + i = 0$ as well, and the same formula gives $\eta' : T_i \circ T_j \cong 1_C$. Two natural isomorphisms $T_j T_i \cong 1$ and $T_i T_j \cong 1$ make $T_i$ an equivalence with inverse $T_j$, by Volume 24, Chapter 2. Mathlib proves in addition that these two isomorphisms satisfy the triangle identities, so that they form an adjoint equivalence. This step uses the coherence conditions. ∎

**Theorem (Shifts commute).** Let $A$ be commutative. For $i, j \in A$ there is a natural isomorphism $\sigma_{i,j} : X[i][j] \cong X[j][i]$, defined as $\mu_{j,i}(X) \circ \mu_{i,j}(X)^{-1}$ through $X[i+j] = X[j+i]$. It satisfies $\sigma_{j,i} = \sigma_{i,j}^{-1}$ and $\sigma_{i,i} = 1$.

*Proof.* The composite of natural isomorphisms is a natural isomorphism. For the inverse, $\sigma_{j,i} \circ \sigma_{i,j} = \mu_{i,j} \circ \mu_{j,i}^{-1} \circ \mu_{j,i} \circ \mu_{i,j}^{-1} = 1$. For $i = j$, the two factors are inverse to each other. ∎

The theorem forces only $\sigma_{i,i} = 1$. For $i \neq j$, the isomorphism $\sigma_{i,j}$ is part of the structure, and a proof must not replace it by an identity, even when $X[i][j]$ and $X[j][i]$ are the same object.

**Theorem (Composition of shifted morphisms).** The composite of shifted morphisms is associative: for $f : X \to Y[a_1]$, $g : Y \to Z[a_2]$ and $h : Z \to W[a_3]$, $(h \cdot g) \cdot f = h \cdot (g \cdot f)$ in degree $a_3 + a_2 + a_1$. A morphism $u : X \to Y$ gives a shifted morphism of degree $0$, $\varepsilon(Y)^{-1} \circ u$, and these morphisms compose as in $C$. The morphism of degree $0$ given by $1_Y$ is a unit for the composite.

*Proof.* Write $a_{12} = a_2 + a_1$ and $a_{23} = a_3 + a_2$. By definition,
$$(h \cdot g) \cdot f = \mu_{a_{23}, a_1}^{-1} \circ (\mu_{a_3,a_2}^{-1} \circ h[a_2] \circ g)[a_1] \circ f,$$
$$h \cdot (g \cdot f) = \mu_{a_3, a_{12}}^{-1} \circ h[a_{12}] \circ \mu_{a_2,a_1}^{-1} \circ g[a_1] \circ f.$$
Both begin with $g[a_1] \circ f : X \to Z[a_2][a_1]$. By naturality of $\mu_{a_2,a_1}$, $h[a_{12}] \circ \mu_{a_2,a_1}^{-1}(Z) = \mu_{a_2,a_1}^{-1}(W[a_3]) \circ h[a_2][a_1]$. It remains to show that the two isomorphisms $W[a_3][a_2][a_1] \to W[a_3 + a_2 + a_1]$ given by $\mu_{a_3,a_{12}}^{-1} \circ \mu_{a_2,a_1}^{-1}$ and $\mu_{a_{23},a_1}^{-1} \circ \mu_{a_3,a_2}^{-1}[a_1]$ are equal. This is the inverse of the associativity condition with $(a, b, c) = (a_3, a_2, a_1)$.

For the degree $0$ part, the composite of $\varepsilon^{-1} \circ v$ and $\varepsilon^{-1} \circ u$ is $\mu_{0,0}^{-1} \circ (\varepsilon^{-1} \circ v)[0] \circ \varepsilon^{-1} \circ u$. By naturality of $\varepsilon$, this is $\mu_{0,0}^{-1} \circ \varepsilon(Z[0])^{-1} \circ \varepsilon(Z)^{-1} \circ v \circ u$. The unit condition $\mu_{0,0} = \varepsilon(Z[0])^{-1}$ reduces it to $\varepsilon(Z)^{-1} \circ v \circ u$. The unit law follows from the unit conditions in the same way. ∎

When $C$ is preadditive and each $T_a$ is additive, the composite is bilinear. Thus the groups $\mathrm{Hom}(X, Y[a])$ form an $A$-graded ring for $X = Y$. In the derived category of Volume 26, these groups are the groups $\mathrm{Ext}^a(X, Y)$, and the composite is the Yoneda product.

**Theorem (Functors that commute with shifts).** The identity functor commutes with the shifts, with $\varphi_a = 1$. If $F : C \to D$ and $G : D \to E$ commute with the shifts, then $G \circ F$ commutes with the shifts, with $\varphi^{GF}_a = \varphi^G_a(FX) \circ G(\varphi^F_a(X))$. Such a functor sends a shifted morphism $f : X \to Y[a]$ to $\varphi^F_a(Y) \circ F(f) : FX \to FY[a]$, and this map respects the composite of shifted morphisms.

*Proof.* For the identity, the two conditions read $\varepsilon \circ \varepsilon^{-1} = 1$ and $\mu \circ \mu^{-1} = 1$. For $G \circ F$, the zero condition is
$$\varphi^G_0(FX) \circ G(\varphi^F_0(X)) = \varepsilon(GFX)^{-1} \circ G(\varepsilon(FX)) \circ G(\varepsilon(FX))^{-1} \circ GF(\varepsilon(X)),$$
which is $\varepsilon^{-1} \circ GF(\varepsilon)$, as required. The addition condition is a longer computation of the same kind. It uses the naturality of $\varphi^G_b$ to move $G(\varphi^F_a)[b]$ past $\varphi^G_b$. For the last claim, the composite $g \cdot f$ maps to $\varphi_c \circ F(\mu^{-1}) \circ F(g[a]) \circ F(f)$. The condition on $\varphi_{b+a}$ replaces $\varphi_c \circ F(\mu^{-1})$ by $\mu^{-1} \circ \varphi_b[a] \circ \varphi_a$, and the naturality of $\varphi_a$ moves $\varphi_a$ to the right of $F(g)[a]$. The result is the composite of the images of $g$ and $f$. ∎

**Theorem (Transport along a fully faithful functor).** Let $F : C \to D$ be fully faithful and let $D$ have a shift by $A$. Let $S_a : C \to C$ be functors with natural isomorphisms $\psi_a : F \circ S_a \cong T_a \circ F$. Then $C$ has a shift with $T_a = S_a$, for which $F$ commutes with the shifts through $\psi_a$.

*Proof.* A fully faithful functor gives a bijection on morphisms, so a natural isomorphism between functors of the form $F \circ P$ and $F \circ Q$ comes from a unique natural isomorphism $P \cong Q$. Define $\varepsilon_C$ as the preimage of $\varepsilon_D(FX) \circ \psi_0(X)$, and $\mu_{a,b}$ on $C$ as the preimage of $\psi_b(S_a X)^{-1} \circ \psi_a(X)^{-1}[b] \circ \mu_{a,b}(FX) \circ \psi_{a+b}(X)$. The coherence conditions are equalities of morphisms in $C$. Since $F$ is faithful, it is sufficient to check them after $F$. After $F$, the factors $\psi$ cancel in pairs, and the conditions become the coherence conditions in $D$. By the construction, $\psi_a$ satisfies the two conditions of a functor that commutes with the shifts. ∎

### Examples

**Example (Cochain complexes).** Let $C$ be a preadditive category. For a cochain complex $K$ and $n \in \mathbb{Z}$, the complex $K[n]$ has $K[n]^p = K^{p+n}$ and the differential $(-1)^n d_K$. The square of this differential is $d_K^2 = 0$. A morphism $\varphi : K \to L$ gives $\varphi[n]$ with components $\varphi^{p+n}$, and it commutes with the new differentials because the sign is the same on both sides. The isomorphism $\mu_{m,n} : K[m+n] \to K[m][n]$ is the identity of $K^{p+m+n}$ in each degree. It is a morphism of complexes because $(-1)^{m+n} = (-1)^m (-1)^n$. The coherence conditions hold because all the maps are identities in each degree. The sign is not necessary for a shift. It is the convention that makes the mapping cone triangles of the homotopy category distinguished in Section 2.

**Example (Graded objects).** Let $\beta$ be an additive group, $s \in \beta$ and $C$ a category. A $\beta$-graded object is a family $(X_b)_{b \in \beta}$ of objects of $C$. The formula $(X[n])_b = X_{b + n s}$ for $n \in \mathbb{Z}$ gives a shift by $\mathbb{Z}$. Here each $\mu_{m,n}$ is the identity after the equality $b + (m+n)s = (b + ms) + ns$.

**Example (Graded abelian groups).** Let $C$ be the category of $\mathbb{Z}$-graded abelian groups with the shift of the previous example and $s = 1$. A shifted morphism of degree $a$ from $X$ to $Y$ is a family of homomorphisms $X_b \to Y_{b+a}$. The composite of degrees $a$ and $b$ has degree $a + b$, and it is the composite of the families. This is the usual category of graded groups with maps of all degrees.

### The library around it

::: mathlib
`CategoryTheory.ShiftedHom.comp` · `Mathlib.CategoryTheory.Shift.ShiftedHom`

`ShiftedHom X Y m` is the type `X ⟶ Y⟦m⟧`. For `f : ShiftedHom X Y a`, `g : ShiftedHom Y Z b` and `h : b + a = c`, `f.comp g h` is `f ≫ g⟦a⟧' ≫ (shiftFunctorAdd' C b a c h).inv.app _`. Note the order of the indices: the degree of the second map comes first in `b + a = c`. The map `mk₀` gives a shifted morphism of degree zero, and `ShiftedHom.map` applies a functor that commutes with the shifts.

<?decl CategoryTheory.ShiftedHom.comp?>
:::

::: mathlib
`CategoryTheory.Functor.CommShift` · `Mathlib.CategoryTheory.Shift.CommShift`

The class `F.CommShift A` holds the isomorphisms `F.commShiftIso a : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a`, with the conditions `commShiftIso_zero` and `commShiftIso_add`. `NatTrans.CommShift τ A` is the condition on natural transformations. The source notes that this notion is the one in the thesis of Verdier.

<?decl CategoryTheory.Functor.CommShift?>
:::

The shift on cochain complexes is `CochainComplex.shiftFunctor` in `Mathlib.Algebra.Homology.HomotopyCategory.Shift`, and it belongs to Volume 26. The shift on graded objects is `GradedObject.hasShift`.

Common errors of a learner:

- `shiftFunctorAdd C a b` goes from the shift by `a + b` to the shift by `a` followed by the shift by `b`. In the text this is $X[a+b] \to X[a][b]$, and the functor $T_b \circ T_a$.
- Equalities of indices such as `a + 0 = a` are not definitional. Use `shiftFunctorAdd'` and `shiftFunctorZero'`, which take the equality as an argument, and avoid `eqToHom` in statements.
- `F.CommShift A` is data. Two instances on the same functor can give different isomorphisms, and lemmas then fail to apply.

### Exercises

1. (A) Show that the constant family $T_a = 1_C$, with $\varepsilon$ and $\mu_{a,b}$ the identities, is a shift on $C$ by any additive monoid.
2. (A) Let $C$ have a shift by $\mathbb{Z}$. Show that $X[n][-n] \cong X$ naturally in $X$, and write the isomorphism in terms of $\mu$ and $\varepsilon$.
3. (B) Let $C$ be preadditive and let $T_a$ be additive for all $a$. Show that the composite of shifted morphisms is bilinear.
4. (B) Show that the shift by $1$ on cochain complexes without the sign, $K[1]^p = K^{p+1}$ with the differential $d_K$, is also a shift by $\mathbb{Z}$, and that the identity in each degree is an isomorphism of complexes between $K[1]$ with and without the sign only when $2 d_K = 0$.
5. (B) Let $F$ commute with the shifts and let $u : X \to Y$. Show that $\varphi_a(Y) \circ F(u[a]) = F(u)[a] \circ \varphi_a(X)$.
6. (C) On cochain complexes, replace each $\mu_{m,n}$ by $(-1)^{mn} \mu_{m,n}$. Show that the new data is again a shift by $\mathbb{Z}$, and that the isomorphisms $\sigma_{i,j}$ do not change. *Hint:* compare the signs $(-1)^{ab + (a+b)c}$ and $(-1)^{bc + a(b+c)}$.

### Notes and history

Shift functors on categories of complexes are as old as homological algebra. The axiomatic shift of a triangulated category is in the thesis of Verdier, published in 1996 as *Des catégories dérivées des catégories abéliennes*, and in the work of Puppe on stable homotopy theory. The source of `CommShift` states that its definition is the one of Verdier, given there with a fibred category in place of a monoidal functor.

The Mathlib Authors of `Shift.Basic` are Kim Morrison, Johan Commelin, Andrew Yang and Joël Riou. The files `Shift.CommShift` and `Shift.ShiftedHom` are by Joël Riou.

### Reference

<?reference?>
