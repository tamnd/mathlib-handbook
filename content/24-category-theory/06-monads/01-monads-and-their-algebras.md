---
title: Monads and their algebras
kind: theory
modules:
  - Mathlib.CategoryTheory.Monad.Basic
  - Mathlib.CategoryTheory.Monad.Algebra
  - Mathlib.CategoryTheory.Monad.Adjunction
  - Mathlib.CategoryTheory.Monad.Types
explains:
  E3: [CategoryTheory.Monad, CategoryTheory.Monad.Algebra, CategoryTheory.Adjunction.toMonad, CategoryTheory.Monad.adj, CategoryTheory.Monad.comparison, CategoryTheory.ofTypeMonad]
  E2: [CategoryTheory.Monad.assoc, CategoryTheory.Monad.left_unit, CategoryTheory.Monad.right_unit, CategoryTheory.Monad.Algebra.unit, CategoryTheory.Monad.Algebra.assoc, CategoryTheory.Monad.Algebra.Hom, CategoryTheory.Monad.free, CategoryTheory.Monad.forget, CategoryTheory.Monad.left_comparison, CategoryTheory.Monad.comparisonForget, CategoryTheory.MonadHom, CategoryTheory.Monad.forget_reflects_iso, CategoryTheory.Monad.algebraFunctorOfMonadHom, CategoryTheory.Comonad, CategoryTheory.Adjunction.toComonad]
  E1: auto
families: []
requires: [V04.C04, V05, V24.C02, V24.C05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Monads and their algebras

### Overview

An adjunction $F \dashv G$ with $F : C \to D$ gives an endofunctor $T = G \circ F$ of $C$. For the free group adjunction of Chapter 5, $T$ sends a set $X$ to the set of reduced words on $X$. It has a unit $X \to TX$ and a multiplication $TTX \to TX$ that evaluates a word of words. These maps satisfy the laws of a monoid, and a *monad* is an endofunctor with such a structure. An *algebra* for $T$ is an object with an action of $T$; for the free group monad the algebras are the groups. This section builds the monad of an adjunction, the free algebras and the comparison functor. Section 2 asks when the comparison functor is an equivalence.

Mathlib writes `f ≫ g` for "first $f$, then $g$", which is $g \circ f$ in the textbook order.

### Definitions

**Definition (Monad).** A *monad* on a category $C$ is a triple $(T, \eta, \mu)$ of a functor $T : C \to C$ and natural transformations $\eta : \mathrm{id}_C \Rightarrow T$ (the *unit*) and $\mu : T \circ T \Rightarrow T$ (the *multiplication*) such that for each object $X$
$$\mu_X \circ T\mu_X = \mu_X \circ \mu_{TX}, \qquad \mu_X \circ \eta_{TX} = \mathrm{id}_{TX} = \mu_X \circ T\eta_X.$$
A *morphism of monads* $\theta : (T, \eta, \mu) \to (T', \eta', \mu')$ is a natural transformation $\theta : T \Rightarrow T'$ with $\theta \circ \eta = \eta'$ and $\theta_X \circ \mu_X = \mu'_X \circ T'\theta_X \circ \theta_{TX}$.

Chapter 7 shows that a monad is a monoid object in the monoidal category of endofunctors.

::: mathlib
`CategoryTheory.Monad` · `Mathlib.CategoryTheory.Monad.Basic`

`Monad C` extends `C ⥤ C`, so `T.obj X` and `T.map f` work directly, with the fields `η : 𝟭 C ⟶ T` and `μ : T ⋙ T ⟶ T`. The `simp` lemmas `Monad.assoc`, `Monad.left_unit` and `Monad.right_unit` are the laws; for instance `Monad.left_unit` reads `T.η.app (T.obj X) ≫ T.μ.app X = 𝟙 _`. Morphisms of monads are `MonadHom T T'`, with the fields `app_η` and `app_μ`. The dual notion is `Comonad`.

<?decl CategoryTheory.Monad?>
:::

**Definition (Algebra).** Let $T$ be a monad on $C$. A *$T$-algebra*, or Eilenberg-Moore algebra, is a pair $(A, a)$ of an object $A$ of $C$ and a morphism $a : TA \to A$, the *structure map*, such that
$$a \circ \eta_A = \mathrm{id}_A, \qquad a \circ Ta = a \circ \mu_A.$$
A *morphism of algebras* $f : (A, a) \to (B, b)$ is a map $f : A \to B$ with $f \circ a = b \circ Tf$. They form the *Eilenberg-Moore category* $C^T$, with the forgetful functor $G^T(A, a) = A$.

::: mathlib
`CategoryTheory.Monad.Algebra` · `Mathlib.CategoryTheory.Monad.Algebra`

`T.Algebra` is a structure with the fields `A : C`, `a : T.obj A ⟶ A`, `unit : T.η.app A ≫ a = 𝟙 A` and `assoc : T.μ.app A ≫ a = T.map a ≫ a`. A morphism `Monad.Algebra.Hom A B` has a field `f` and the law `h : T.map f ≫ B.a = A.a ≫ f`. The functors `T.forget` and `T.free` and the adjunction `T.adj : T.free ⊣ T.forget` come from the proposition on free algebras. Equality of morphisms is checked on `f` with `Monad.Algebra.Hom.ext`.

<?decl CategoryTheory.Monad.Algebra?>
:::

### Theorems and proofs

**Proposition (The monad of an adjunction).** Let $F \dashv G$ be an adjunction with unit $\eta : \mathrm{id}_C \Rightarrow GF$ and counit $\varepsilon : FG \Rightarrow \mathrm{id}_D$. Then $T = GF$ with the unit $\eta$ and the multiplication $\mu_X = G\varepsilon_{FX}$ is a monad on $C$.

*Proof.* The map $\mu = G\varepsilon F$ is natural as a whiskering. The naturality of $\varepsilon$ at the morphism $\varepsilon_{FX} : FGFX \to FX$ gives $\varepsilon_{FX} \circ FG\varepsilon_{FX} = \varepsilon_{FX} \circ \varepsilon_{FGFX}$. Apply $G$. The left side becomes $G\varepsilon_{FX} \circ GFG\varepsilon_{FX} = \mu_X \circ T\mu_X$. The right side becomes $G\varepsilon_{FX} \circ G\varepsilon_{FGFX} = \mu_X \circ \mu_{TX}$. For the unit laws, the triangle identities of Chapter 5 say $G\varepsilon_Y \circ \eta_{GY} = \mathrm{id}_{GY}$ and $\varepsilon_{FX} \circ F\eta_X = \mathrm{id}_{FX}$. The first with $Y = FX$ gives $\mu_X \circ \eta_{TX} = \mathrm{id}$. The second, after $G$, gives $\mu_X \circ T\eta_X = G(\varepsilon_{FX} \circ F\eta_X) = \mathrm{id}$. $\square$

::: mathlib
`CategoryTheory.Adjunction.toMonad` · `Mathlib.CategoryTheory.Monad.Adjunction`

For `h : L ⊣ R` with `L : C ⥤ D`, the monad `h.toMonad` has underlying functor `L ⋙ R`, unit `h.unit` and multiplication the whiskering of `h.counit`. Dually, `h.toComonad` is the comonad $FG$ on `D`.

<?decl CategoryTheory.Adjunction.toMonad?>
:::

**Proposition (Free algebras).** Let $T$ be a monad on $C$. For each $X$, the pair $F^T X = (TX, \mu_X)$ is a $T$-algebra, and $F^T f = Tf$ makes $F^T$ a functor $C \to C^T$. Then $F^T \dashv G^T$, with unit $\eta$ and counit $\varepsilon_{(A,a)} = a$. The monad of this adjunction is $T$.

*Proof.* The algebra laws for $(TX, \mu_X)$ are a unit law and associativity of $T$. For $f : X \to Y$, the naturality of $\mu$ gives $Tf \circ \mu_X = \mu_Y \circ TTf$, so $Tf$ is a morphism of algebras.

Now fix $X$ in $C$ and an algebra $(A, a)$. For $g : X \to A$ put $\bar g = a \circ Tg : TX \to A$. It is a morphism of algebras:
$$\bar g \circ \mu_X = a \circ Tg \circ \mu_X = a \circ \mu_A \circ TTg = a \circ Ta \circ TTg = a \circ T\bar g,$$
by the naturality of $\mu$ and the algebra law. In the other direction, send a morphism of algebras $f : (TX, \mu_X) \to (A, a)$ to $f \circ \eta_X$. First, $\bar g \circ \eta_X = a \circ Tg \circ \eta_X = a \circ \eta_A \circ g = g$ by the naturality of $\eta$ and the unit law of the algebra. Second, $\overline{f \circ \eta_X} = a \circ Tf \circ T\eta_X = f \circ \mu_X \circ T\eta_X = f$, because $f$ is a morphism of algebras and $\mu_X \circ T\eta_X = \mathrm{id}$.

The bijection is natural: $\overline{g \circ h} = \bar g \circ Th$, and $k \circ \bar g = b \circ Tk \circ Tg = \overline{k \circ g}$ for a morphism of algebras $k : (A, a) \to (B, b)$. So $F^T \dashv G^T$. The unit is the image of $\mathrm{id}_{TX}$, which is $\eta_X$, and the counit is $\overline{\mathrm{id}_A} = a$. Finally $G^T F^T = T$, and the new multiplication is $G^T \varepsilon_{F^T X} = \mu_X$. $\square$

**Proposition (Comparison functor).** Let $F \dashv G$ be an adjunction with monad $T = GF$. Then $K B = (GB, G\varepsilon_B)$ and $K f = Gf$ define a functor $K : D \to C^T$ with $G^T \circ K = G$ and $K \circ F = F^T$.

*Proof.* The unit law $G\varepsilon_B \circ \eta_{GB} = \mathrm{id}$ is a triangle identity. The naturality of $\varepsilon$ at $\varepsilon_B$ gives $\varepsilon_B \circ FG\varepsilon_B = \varepsilon_B \circ \varepsilon_{FGB}$. After $G$, the left side is $G\varepsilon_B \circ T(G\varepsilon_B)$, and the right side is $G\varepsilon_B \circ \mu_{GB}$. For $f : B \to B'$, the naturality of $\varepsilon$ gives $Gf \circ G\varepsilon_B = G\varepsilon_{B'} \circ GFGf$, so $Gf$ is a morphism of algebras. Finally $KFX = (GFX, G\varepsilon_{FX}) = (TX, \mu_X)$ and $KFf = GFf = Tf$. $\square$

**Lemma (The forgetful functor reflects isomorphisms).** If a morphism of algebras $f : (A, a) \to (B, b)$ is an isomorphism in $C$, then it is an isomorphism in $C^T$.

*Proof.* It is enough to show that $f^{-1}$ is a morphism of algebras. Since $f \circ a = b \circ Tf$, it follows that $a = f^{-1} \circ b \circ Tf$, so $a \circ Tf^{-1} = f^{-1} \circ b$. $\square$

::: mathlib
`CategoryTheory.Monad.comparison` · `Mathlib.CategoryTheory.Monad.Adjunction`

For `h : L ⊣ R`, `Monad.comparison h : D ⥤ h.toMonad.Algebra` is the functor $K$. The isomorphism `Monad.comparisonForget h` says that `comparison h ⋙ forget` is `R`, and `Monad.left_comparison h` says that `L ⋙ comparison h = h.toMonad.free`. The instance `Monad.forget_reflects_iso` is the lemma above. A morphism of monads `T₂ ⟶ T₁` gives `Monad.algebraFunctorOfMonadHom : T₁.Algebra ⥤ T₂.Algebra`.

<?decl CategoryTheory.Monad.comparison?>
:::

### Examples

**Example (The list monad).** Let $TX$ be the set of finite lists in $X$, with $\eta_X(x) = [x]$ and $\mu_X$ the concatenation. It is the free monoid monad. Let $(A, a)$ be an algebra. Put $m \cdot n = a([m, n])$ and $e = a([\,])$. Apply associativity of the algebra to $[[m, n], [p]] \in TTA$: the map $\mu_A$ gives $[m, n, p]$, and $Ta$ gives $[m \cdot n, p]$. So $a([m, n, p]) = (m \cdot n) \cdot p$. The list $[[m], [n, p]]$ gives $a([m, n, p]) = m \cdot (n \cdot p)$, because $a([m]) = m$ by the unit law. The list $[[\,], [m]]$ gives $e \cdot m = a([m]) = m$, and $[[m], [\,]]$ gives $m \cdot e = m$. So $A$ is a monoid. The list $[[x_1, \ldots, x_{k-1}], [x_k]]$ shows by induction that $a([x_1, \ldots, x_k]) = x_1 \cdots x_k$, so $a$ is determined by the monoid. Conversely the product in a monoid satisfies both laws, and the morphisms of algebras are the monoid homomorphisms. So $\mathbf{Set}^T$ is isomorphic to the category of monoids.

**Example (The power set monad).** Let $TX = \mathcal{P}(X)$, with $\eta_X(x) = \{x\}$, $\mu_X$ the union of a set of subsets and $Tf$ the direct image. Let $(A, a)$ be an algebra. The associativity law applied to a set $\{S_i\}$ of subsets of $A$ reads
$$a\Big(\bigcup_i S_i\Big) = a(\{a(S_i)\}), \qquad (\ast)$$
and the unit law reads $a(\{x\}) = x$. Define $x \le y$ when $a(\{x, y\}) = y$. It is reflexive by the unit law and antisymmetric since $\{x, y\} = \{y, x\}$. A case of $(\ast)$ is $a(\{x\} \cup S) = a(\{x, a(S)\})$. For transitivity, let $x \le y \le z$. Then
$$a(\{x, z\}) = a(\{x, a(\{y, z\})\}) = a(\{x, y, z\}) = a(\{a(\{x, y\}), z\}) = a(\{y, z\}) = z.$$
For $s \in S$, $a(\{s, a(S)\}) = a(\{s\} \cup S) = a(S)$, so $a(S)$ is an upper bound of $S$. If $u$ is an upper bound, $S \cup \{u\}$ is the union of $\{u\}$ and the sets $\{s, u\}$, so $(\ast)$ gives $a(S \cup \{u\}) = a(\{u\}) = u$. Also $a(S \cup \{u\}) = a(\{a(S), u\})$, so $a(S) \le u$. So $a(S) = \sup S$, and $A$ is a complete lattice (Volume 4, Chapter 4). Conversely $a = \sup$ satisfies both laws, and the morphisms of algebras are the maps that preserve all joins.

**Example (The free group monad).** For the free group adjunction $F \dashv G$, an element of $TTX$ is a reduced word in symbols $\langle w \rangle$, one for each reduced word $w$ over $X$, and $\mu_X = G\varepsilon_{FX}$ evaluates it in $FX$. For $X = \{x\}$ and the word $\langle x^3 \rangle \langle x^{-1} \rangle^{-1}$, the value is $x^3 (x^{-1})^{-1} = x^4$. Section 2 proves that the comparison functor for this adjunction is an equivalence.

### The library around it

Lean's class `Monad m` gives `pure : α → m α` and `bind : m α → (α → m β) → m β`, and `LawfulMonad` holds the laws. Here `pure` is $\eta$, `Functor.map` is $T$ on maps, `bind x f` is $\mu(Tf(x))$, and $\mu$ is `bind x id`.

::: mathlib
`CategoryTheory.ofTypeMonad` · `Mathlib.CategoryTheory.Monad.Types`

`ofTypeMonad m` needs `[Monad m]` and `[LawfulMonad m]` and gives a `Monad (Type u)` in the sense of category theory. Its unit is `pure` and its multiplication is `joinM`. The instances `Set.monad` with `Set.instLawfulMonad`, and `List.instMonad` with `List.instLawfulMonad`, give the power set monad and the list monad of the examples.

<?decl CategoryTheory.ofTypeMonad?>
:::

The free group monad is `GrpCat.adj.toMonad`, and the free monoid monad is `MonCat.adj.toMonad`. A common error is to read `≫` in the order of $\circ$: `T.μ.app A ≫ a = T.map a ≫ a` is $a \circ \mu_A = a \circ Ta$.

### Exercises

1. (A) Let $M$ be a monoid. Show that $TX = M \times X$ with $\eta_X(x) = (1, x)$ and $\mu_X(m, (n, x)) = (mn, x)$ is a monad on $\mathbf{Set}$, and that its algebras are the sets with a left action of $M$.
2. (A) Show that the maybe monad $TX = X \sqcup \{\ast\}$ is a monad on $\mathbf{Set}$, and that its algebras are the pointed sets. Hint: the structure map sends $\ast$ to the base point.
3. (A) Prove that $a : (TA, \mu_A) \to (A, a)$ is a morphism of algebras for every algebra $(A, a)$.
4. (B) Let $P$ be a preorder seen as a category. Show that a monad on $P$ is a closure operator: a monotone map $c$ with $x \le c(x)$ and $c(c(x)) = c(x)$. Show that the algebras are the closed elements, and compare with Volume 4, Chapter 6.
5. (C) Let $R$ be a commutative ring and $TX$ the set of finitely supported functions $X \to R$. Make $T$ a monad on $\mathbf{Set}$ and show that its algebras are the $R$-modules. Hint: $a$ of a function $c$ is $\sum_x c(x) x$.

### Notes and history

Monads appeared first in homological algebra, as the "standard constructions" that Godement used for resolutions of sheaves in his book on sheaf theory of 1958. Eilenberg and Moore, in "Adjoint functors and triples" (1965), proved that every monad comes from an adjunction and built the category of algebras. Kleisli gave the other construction in the same year. Mac Lane's *Categories for the Working Mathematician* (1971) made the name "monad" standard.

### Reference

<?reference?>
