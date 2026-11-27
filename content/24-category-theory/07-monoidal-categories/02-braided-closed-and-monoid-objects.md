---
title: Braided and closed categories and monoid objects
kind: theory
modules:
  - Mathlib.CategoryTheory.Monoidal.Braided.Basic
  - Mathlib.CategoryTheory.Monoidal.Functor
  - Mathlib.CategoryTheory.Monoidal.Closed.Basic
  - Mathlib.CategoryTheory.Monoidal.Closed.Types
  - Mathlib.CategoryTheory.Monoidal.Mon
  - Mathlib.CategoryTheory.Monoidal.Internal.Types.Basic
  - Mathlib.CategoryTheory.Monad.EquivMon
explains:
  E3: [CategoryTheory.BraidedCategory, CategoryTheory.SymmetricCategory, CategoryTheory.Functor.LaxMonoidal, CategoryTheory.MonoidalClosed, CategoryTheory.MonObj, CategoryTheory.Mon, CategoryTheory.Monad.monadMonEquiv]
  E2: [CategoryTheory.BraidedCategory.braiding, CategoryTheory.BraidedCategory.hexagon_forward, CategoryTheory.BraidedCategory.hexagon_reverse, CategoryTheory.BraidedCategory.yang_baxter, CategoryTheory.SymmetricCategory.symmetry, CategoryTheory.Functor.Braided, CategoryTheory.Functor.OplaxMonoidal, CategoryTheory.Functor.Monoidal, CategoryTheory.Functor.Monoidal.μIso, CategoryTheory.ihom, CategoryTheory.ihom.adjunction, CategoryTheory.ihom.ev, CategoryTheory.MonoidalClosed.curry, CategoryTheory.MonoidalClosed.uncurry, CategoryTheory.Types.tensorProductAdjunction, CategoryTheory.Mon.forget, CategoryTheory.IsMonHom, CategoryTheory.Functor.mapMon, CategoryTheory.MonObj.mul_assoc, monTypeEquivalenceMon]
  E1: auto
families: []
requires: [V07, V08, V24.C02, V24.C05, V24.C06]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Braided and closed categories and monoid objects

### Overview

A *braiding* on a monoidal category is a natural isomorphism $X \otimes Y \cong Y \otimes X$ subject to two hexagon axioms; a braiding that is its own inverse is a *symmetry*. A monoidal category is *closed* when each $A \otimes -$ has a right adjoint, an internal hom. The axioms of a monoid make sense in any monoidal category, and *monoid objects* unify three notions: monoids in sets, rings in abelian groups with the tensor product, and monads in endofunctors (Chapter 6). As in Section 1, Mathlib's `f ≫ g` is the textbook $g \circ f$.

### Definitions

**Definition (Braided category).** A *braiding* on a monoidal category $C$ is a natural isomorphism $\beta_{X,Y} : X \otimes Y \to Y \otimes X$ such that the two hexagons commute:
$$\alpha_{Y,Z,X} \circ \beta_{X, Y \otimes Z} \circ \alpha_{X,Y,Z} = (Y \triangleleft \beta_{X,Z}) \circ \alpha_{Y,X,Z} \circ (\beta_{X,Y} \triangleright Z),$$
$$\alpha^{-1}_{Z,X,Y} \circ \beta_{X \otimes Y, Z} \circ \alpha^{-1}_{X,Y,Z} = (\beta_{X,Z} \triangleright Y) \circ \alpha^{-1}_{X,Z,Y} \circ (X \triangleleft \beta_{Y,Z}).$$
The braiding is *symmetric* if $\beta_{Y,X} \circ \beta_{X,Y} = \mathrm{id}_{X \otimes Y}$ for all $X, Y$.

The first hexagon says that moving $X$ past $Y \otimes Z$ at once equals moving it past $Y$, then past $Z$.

::: mathlib
`CategoryTheory.BraidedCategory` · `Mathlib.CategoryTheory.Monoidal.Braided.Basic`

The class over a monoidal category. The braiding `braiding X Y : X ⊗ Y ≅ Y ⊗ X` has notation `β_ X Y`, and the fields `hexagon_forward` and `hexagon_reverse` are the two hexagons written with `≫`. `SymmetricCategory` adds the field `symmetry`.

<?decl CategoryTheory.BraidedCategory?>
:::

**Definition (Monoidal functors).** Let $C$ and $D$ be monoidal categories. A *lax monoidal functor* is a functor $F : C \to D$ with a morphism $\varepsilon : I \to F(I)$ and a natural transformation $\mu_{X,Y} : F(X) \otimes F(Y) \to F(X \otimes Y)$ such that
$$F(\alpha_{X,Y,Z}) \circ \mu_{X \otimes Y, Z} \circ (\mu_{X,Y} \triangleright F Z) = \mu_{X, Y \otimes Z} \circ (F X \triangleleft \mu_{Y,Z}) \circ \alpha_{FX,FY,FZ},$$
$$F(\lambda_X) \circ \mu_{I,X} \circ (\varepsilon \triangleright F X) = \lambda_{FX}, \qquad F(\rho_X) \circ \mu_{X,I} \circ (F X \triangleleft \varepsilon) = \rho_{FX}.$$
*Oplax* functors have the maps reversed; a *strong* monoidal functor is a lax one with $\varepsilon$ and $\mu$ invertible. Between braided categories, a lax monoidal functor is *braided* if $F(\beta_{X,Y}) \circ \mu_{X,Y} = \mu_{Y,X} \circ \beta_{FX,FY}$.

::: mathlib
`CategoryTheory.Functor.LaxMonoidal` · `Mathlib.CategoryTheory.Monoidal.Functor`

A class on a functor `F`, with data `ε F` and `μ F X Y`. `Functor.OplaxMonoidal` is the dual, `Functor.Monoidal` holds both, mutually inverse, with `Functor.Monoidal.μIso` the isomorphism $\mu$, and `Functor.Braided` is the braided version.

<?decl CategoryTheory.Functor.LaxMonoidal?>
:::

**Definition (Closed monoidal category).** An object $A$ of a monoidal category is *closed* if the functor $A \otimes - : C \to C$ has a right adjoint $[A, -]$, the *internal hom*. The category is *closed* if every object is. The counit is the *evaluation* $A \otimes [A, B] \to B$, and the hom bijection is *currying*.

::: mathlib
`CategoryTheory.MonoidalClosed` · `Mathlib.CategoryTheory.Monoidal.Closed.Basic`

Every object has an instance of `Closed`. The internal hom is `ihom A : C ⥤ C`, with `ihom.adjunction A : tensorLeft A ⊣ ihom A`, counit `ihom.ev`, and the bijection given by `MonoidalClosed.curry` and `MonoidalClosed.uncurry`.

<?decl CategoryTheory.MonoidalClosed?>
:::

**Definition (Monoid object).** A *monoid object* in a monoidal category $C$ is an object $M$ with a *unit* $\eta : I \to M$ and a *multiplication* $m : M \otimes M \to M$ such that
$$m \circ (\eta \triangleright M) = \lambda_M, \qquad m \circ (M \triangleleft \eta) = \rho_M, \qquad m \circ (m \triangleright M) = m \circ (M \triangleleft m) \circ \alpha_{M,M,M}.$$
A *morphism* is an $f : M \to N$ with $f \circ \eta_M = \eta_N$ and $f \circ m_M = m_N \circ (f \otimes f)$. This gives a category $\mathrm{Mon}(C)$.

::: mathlib
`CategoryTheory.MonObj` · `Mathlib.CategoryTheory.Monoidal.Mon`

A class on `X` with `one : 𝟙_ C ⟶ X`, `mul : X ⊗ X ⟶ X` and the laws `one_mul`, `mul_one`, `mul_assoc`. The bundled category is `Mon C`, with morphisms satisfying `IsMonHom` and forgetful functor `Mon.forget C`.

<?decl CategoryTheory.MonObj?>
:::

### Theorems and proofs

**Theorem (Symmetry gives the second hexagon).** Let $\beta$ be a natural isomorphism $X \otimes Y \to Y \otimes X$ that satisfies the first hexagon and $\beta_{Y,X} \circ \beta_{X,Y} = \mathrm{id}$. Then $\beta$ satisfies the second hexagon, so it is a symmetric braiding.

*Proof.* Write the first hexagon for the objects $Z, X, Y$:
$$\alpha_{X,Y,Z} \circ \beta_{Z, X \otimes Y} \circ \alpha_{Z,X,Y} = (X \triangleleft \beta_{Z,Y}) \circ \alpha_{X,Z,Y} \circ (\beta_{Z,X} \triangleright Y).$$
All the maps are isomorphisms. Invert both sides; the inverse of a composite is the composite of the inverses in the reverse order, and whiskering preserves inverses:
$$\alpha^{-1}_{Z,X,Y} \circ \beta_{Z, X \otimes Y}^{-1} \circ \alpha^{-1}_{X,Y,Z} = (\beta_{Z,X}^{-1} \triangleright Y) \circ \alpha^{-1}_{X,Z,Y} \circ (X \triangleleft \beta_{Z,Y}^{-1}).$$
By the symmetry, $\beta_{Z,W}^{-1} = \beta_{W,Z}$ for all $W$. Substituting $\beta_{X \otimes Y, Z}$, $\beta_{X,Z}$ and $\beta_{Y,Z}$ gives exactly the second hexagon. $\square$

The same argument shows that $\beta'_{X,Y} = \beta_{Y,X}^{-1}$ is a braiding whenever $\beta$ is. A braided category also satisfies the Yang-Baxter equation, `BraidedCategory.yang_baxter`, the braid relation $s_1 s_2 s_1 = s_2 s_1 s_2$ that explains the name.

**Theorem (Lax monoidal functors preserve monoids).** Let $F : C \to D$ be lax monoidal and $(M, \eta, m)$ a monoid object in $C$. Then $F(M)$ with unit $F(\eta) \circ \varepsilon$ and multiplication $F(m) \circ \mu_{M,M}$ is a monoid object in $D$, and $F$ sends morphisms of monoids to morphisms of monoids. This gives a functor $\mathrm{Mon}(C) \to \mathrm{Mon}(D)$.

*Proof.* Left unit. Using $(F(\eta) \circ \varepsilon) \triangleright F M = (F(\eta) \triangleright FM) \circ (\varepsilon \triangleright FM)$ and the naturality of $\mu$ in the first variable, $\mu_{M,M} \circ (F(\eta) \triangleright FM) = F(\eta \triangleright M) \circ \mu_{I,M}$. Hence
$$F(m) \circ \mu_{M,M} \circ ((F(\eta) \circ \varepsilon) \triangleright FM) = F(m \circ (\eta \triangleright M)) \circ \mu_{I,M} \circ (\varepsilon \triangleright FM) = F(\lambda_M) \circ \mu_{I,M} \circ (\varepsilon \triangleright FM) = \lambda_{FM},$$
by the left unit law of $M$ and the left unitality of $F$. The right unit is the mirror image.

Associativity. By naturality of $\mu$, $\mu_{M,M} \circ (F(m) \triangleright FM) = F(m \triangleright M) \circ \mu_{M \otimes M, M}$. So
$$F(m) \circ \mu_{M,M} \circ ((F(m) \circ \mu_{M,M}) \triangleright FM) = F(m \circ (m \triangleright M)) \circ \mu_{M \otimes M, M} \circ (\mu_{M,M} \triangleright FM).$$
By associativity in $M$, $m \circ (m \triangleright M) = m \circ (M \triangleleft m) \circ \alpha$, and the associativity axiom of $F$ turns $F(\alpha) \circ \mu_{M \otimes M,M} \circ (\mu_{M,M} \triangleright FM)$ into $\mu_{M, M \otimes M} \circ (FM \triangleleft \mu_{M,M}) \circ \alpha$. Then naturality in the second variable gives $F(M \triangleleft m) \circ \mu_{M, M \otimes M} = \mu_{M,M} \circ (FM \triangleleft F(m))$, and the whole is
$$F(m) \circ \mu_{M,M} \circ (FM \triangleleft (F(m) \circ \mu_{M,M})) \circ \alpha_{FM,FM,FM},$$
which is the associativity law for $F(M)$. For a morphism $f : M \to N$ of monoids, $F(f) \circ F(m_M) \circ \mu_{M,M} = F(m_N) \circ F(f \otimes f) \circ \mu_{M,M} = F(m_N) \circ \mu_{N,N} \circ (Ff \otimes Ff)$ by naturality, and the unit is similar. $\square$

::: mathlib
`CategoryTheory.Functor.mapMon` · `Mathlib.CategoryTheory.Monoidal.Mon`

For a lax monoidal functor `F`, the functor `F.mapMon : Mon C ⥤ Mon D` of the theorem.

<?decl CategoryTheory.Functor.mapMon?>
:::

**Theorem (Monads are monoids of endofunctors).** For every category $C$, the category of monads on $C$ is equivalent to the category of monoid objects in the monoidal category of endofunctors of Section 1.

*Proof.* The unit is the identity functor, and Mathlib's convention gives $(F \otimes G)(X) = G(F(X))$, so $T \otimes T = T \circ T$. For a natural transformation $\theta : F \Rightarrow F'$, the whiskerings have components $(\theta \triangleright T)_X = T(\theta_X)$ and $(T \triangleleft \theta)_X = \theta_{TX}$, and the associator and unitors have identity components. Take a monoid object with unit $\eta : \mathrm{id} \Rightarrow T$ and multiplication $\mu : T T \Rightarrow T$. Evaluated at $X$, the three monoid laws read
$$\mu_X \circ T(\eta_X) = \mathrm{id}_{TX}, \qquad \mu_X \circ \eta_{TX} = \mathrm{id}_{TX}, \qquad \mu_X \circ T(\mu_X) = \mu_X \circ \mu_{TX},$$
which are the laws of a monad from Chapter 6, and conversely. A morphism of monoids $\phi : T \Rightarrow T'$ satisfies $\phi \circ \eta = \eta'$ and $\phi \circ \mu = \mu' \circ (\phi \otimes \phi)$, where $(\phi \otimes \phi)_X = T'(\phi_X) \circ \phi_{TX}$; these define a morphism of monads. Both translations are the identity on underlying data, so they give an isomorphism of categories. $\square$

::: mathlib
`CategoryTheory.Monad.monadMonEquiv` · `Mathlib.CategoryTheory.Monad.EquivMon`

The equivalence `Monad C ≌ Mon (C ⥤ C)`.

<?decl CategoryTheory.Monad.monadMonEquiv?>
:::

### Examples

**Example (Swap).** In types, $\beta_{X,Y}(x, y) = (y, x)$ is natural, satisfies the first hexagon (both sides send $(x, y, z)$ to $(y, z, x)$) and squares to the identity. By the first theorem it is a symmetric braiding. For a commutative ring $R$, the map $x \otimes y \mapsto y \otimes x$ on $R$-modules (Volume 8) is a symmetric braiding in the same way, checked on pure tensors.

::: mathlib
`ModuleCat.MonoidalCategory.symmetricCategory` · `Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric`

The symmetry on `ModuleCat R`. The closed structure is `ModuleCat.instMonoidalClosed`, with currying `ModuleCat.monoidalClosedHomEquiv`.
:::

**Example (Functions and linear maps).** In types, $A \times -$ is left adjoint to $B \mapsto B^A$, the type of functions. The bijection sends $f : A \times Y \to B$ to $\hat f(y)(a) = f(a, y)$, its inverse sends $g$ to $(a, y) \mapsto g(y)(a)$, and both directions are natural in $Y$ and $B$ by direct evaluation; Chapter 5 turns a natural hom bijection into an adjunction, with evaluation as counit. For $R$-modules, $\mathrm{Hom}_R(M, -)$ is the internal hom by the currying of Volume 8.

::: mathlib
`CategoryTheory.Types.tensorProductAdjunction` · `Mathlib.CategoryTheory.Monoidal.Closed.Types`

The adjunction `tensorLeft X ⊣ coyoneda.obj (op X)`; the right adjoint sends `Y` to `X → Y`.

<?decl CategoryTheory.Types.tensorProductAdjunction?>
:::

**Example (Monoids and rings).** A monoid object in types is a type $M$ with an element $e$ and a map $m : M \times M \to M$. On elements, the laws say $m(e, x) = x$, $m(x, e) = x$ and $m(m(x, y), z) = m(x, m(y, z))$, so $M$ is a monoid, and morphisms of monoid objects are monoid homomorphisms. For $R$-modules with the tensor product, a multiplication $M \otimes_R M \to M$ is an $R$-bilinear map, and the laws make $M$ an associative unital $R$-algebra. For $R = \mathbb{Z}$, monoid objects in abelian groups are rings.

::: mathlib
`monTypeEquivalenceMon` · `Mathlib.CategoryTheory.Monoidal.Internal.Types.Basic`

The equivalence `Mon (Type u) ≌ MonCat` of the example.

<?decl monTypeEquivalenceMon?>
:::

::: mathlib
`ModuleCat.monModuleEquivalenceAlgebra` · `Mathlib.CategoryTheory.Monoidal.Internal.Module`

The equivalence `Mon (ModuleCat R) ≌ AlgCat R` for a commutative ring `R`.
:::

**Counterexample (The cartesian product of abelian groups).** In abelian groups with the direct sum $A \oplus B$ as a cartesian monoidal product, every object has exactly one monoid structure, so monoid objects there are not rings. Indeed the unit $0 \to A$ is zero, and for an additive $m : A \oplus A \to A$ the unit laws give $m(a, 0) = a$ and $m(0, b) = b$, so $m(a, b) = m(a, 0) + m(0, b) = a + b$. 

::: mathlib
`AddCommGrpCat.cartesianMonoidalCategory` · `Mathlib.Algebra.Category.Grp.CartesianMonoidal`

The cartesian monoidal structure on additive commutative groups.
:::

### The library around it

Monoidal functors are classes on a functor, so one functor can be used with or without its monoidal structure; `Functor.LaxMonoidal.comp` composes them. Cartesian monoidal categories have their own class `CartesianMonoidalCategory`, with types as an instance (Section 1). The file `Mathlib.CategoryTheory.Monoidal.Mon` develops monoid objects: the category `Mon C`, its forgetful functor, the functor `Functor.mapMon` and, for braided $C$, the monoidal structure `Mon.monMonoidal` on `Mon C`, which is the tensor product of Exercise 7. Commutative monoid objects, comonoid objects and Hopf objects have their own files next to it.

### Exercises

1. (A) Check both hexagons for the swap on types by evaluating each side on an element $(x, y, z)$, and check that the swap is natural.
2. (A) Show that the forgetful functor from $R$-modules to sets is lax monoidal for the tensor product on modules and the product on sets, with $\mu(x, y) = x \otimes y$ and $\varepsilon$ picking $1 \in R$. Show that it is not strong.
3. (B) Prove that in a braided category $\beta_{I,X} = \rho_X^{-1} \circ \lambda_X$. Hint: apply the first hexagon to $(I, I, X)$, use naturality of $\lambda$ and the faithfulness of $I \otimes -$ from Section 1.
4. (B) Show that in a closed monoidal category, $A \otimes -$ preserves all colimits that exist.
5. (B) Let $q : \mathbb{R} \to Y$ be the quotient map that collapses the subset $\mathbb{Z}$ to one point (not the quotient by the group $\mathbb{Z}$). Taking as given that $\mathrm{id}_{\mathbb{Q}} \times q$ is not a quotient map (Munkres, *Topology*, Section 22), show with Exercise 4 that topological spaces with the product are not closed.
6. (B) Prove the Eckmann-Hilton argument: if $M$ is a monoid object in the category of monoids with the cartesian product, its two multiplications agree and are commutative.
7. (C) Let $C$ be braided and $M, N$ monoid objects. Show that $M \otimes N$ is a monoid object with multiplication $(m_M \otimes m_N) \circ (M \triangleleft \beta_{N,M} \triangleright N)$, up to associators.

### Notes and history

Braided monoidal categories are due to Joyal and Street (preprint 1986, published 1993). Symmetric ones go back to Mac Lane (1963), and closed categories to Eilenberg and Kelly (1966). Mac Lane's 1971 book states that a monad is a monoid in the category of endofunctors.

### Reference

<?reference?>
