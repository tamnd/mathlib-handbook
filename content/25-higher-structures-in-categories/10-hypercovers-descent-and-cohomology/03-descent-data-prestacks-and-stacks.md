---
title: Descent data, prestacks and stacks
kind: api
modules:
  - Mathlib.CategoryTheory.Sites.Descent.DescentData
  - Mathlib.CategoryTheory.Sites.Descent.DescentDataPrime
  - Mathlib.CategoryTheory.Sites.Descent.DescentDataAsCoalgebra
  - Mathlib.CategoryTheory.Sites.Descent.IsPrestack
  - Mathlib.CategoryTheory.Sites.Descent.IsStack
  - Mathlib.CategoryTheory.Sites.Descent.Precoverage
explains:
  E2: [CategoryTheory.Pseudofunctor.DescentData, CategoryTheory.Pseudofunctor.toDescentData, CategoryTheory.Pseudofunctor.IsPrestack, CategoryTheory.Pseudofunctor.IsStack, CategoryTheory.Pseudofunctor.isPrestackFor_iff_isSheafFor, CategoryTheory.Pseudofunctor.isEquivalence_toDescentData, CategoryTheory.Pseudofunctor.DescentData'.descentDataEquivalence, CategoryTheory.Pseudofunctor.DescentDataAsCoalgebra.coalgebraEquivalence, CategoryTheory.Pseudofunctor.IsStack.of_precoverage]
  E1: auto
families: []
requires: [V24.C05, V24.C06, V25.C06]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Descent data, prestacks and stacks

### Overview

A sheaf glues sections: compatible sections on the members of a cover come from a unique section on the base. Descent asks the same question one level up, for objects of categories. Let each object $X$ of $C$ carry a category $F(X)$, for example the quasi-coherent modules on a scheme or the vector bundles on a space, and let each morphism $g : Y \to X$ give a pullback functor $g^* : F(X) \to F(Y)$. Given a cover $(f_i : X_i \to S)$ and objects $M_i$ of $F(X_i)$ with isomorphisms between their pullbacks to the overlaps, when is there an object $M$ of $F(S)$ with $f_i^* M \cong M_i$? The isomorphisms on the overlaps must satisfy a cocycle condition on the triple overlaps. These data are the *descent data*, and a *stack* is an $F$ for which the descent data are effective.

The pullbacks compose only up to isomorphism: $(g h)^*$ is isomorphic to $h^* g^*$, not equal. So the library takes $F$ to be a pseudofunctor `LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat`. This section describes the category of descent data, its two other forms (with chosen pullbacks, and as coalgebras over a comonad), the presheaves of morphisms that define a prestack, and the stack condition. The sheaf condition of Chapter 6 is the case of a presheaf of sets, viewed as a pseudofunctor with discrete fibres.

### The library around it

#### Descent data

Let $F$ be a pseudofunctor from `LocallyDiscrete Cᵒᵖ` to `Cat`, and let $f_i : X_i \to S$ be a family of morphisms. For $g : Y \to X$ write $g^*$ for the functor `(F.map g.op.toLoc).toFunctor`. An object of `Pseudofunctor.DescentData F f` has two fields:

1. `obj i`, an object $M_i$ of $F(X_i)$ for each $i$;
2. `hom q f₁ f₂`, a morphism $f_1^* M_{i_1} \to f_2^* M_{i_2}$ for each object $Y$, each $q : Y \to S$ and each pair $f_1 : Y \to X_{i_1}$, $f_2 : Y \to X_{i_2}$ over $q$.

The morphisms are natural in $Y$ (the field `Pseudofunctor.DescentData.pullHom_hom`), they are the identity when $f_1 = f_2$ (`Pseudofunctor.DescentData.hom_self`), and they compose: the morphism for $(f_1, f_3)$ is the composite of the morphisms for $(f_1, f_2)$ and $(f_2, f_3)$ (`Pseudofunctor.DescentData.hom_comp`). The last two conditions are the cocycle condition. They imply that each `hom` is an isomorphism, and `Pseudofunctor.DescentData.iso` gives the isomorphism. This form needs no fibre products: the overlaps are described by all pairs of morphisms from a test object $Y$.

A morphism of descent data, `Pseudofunctor.DescentData.Hom`, is a family of morphisms $M_i \to N_i$ that commutes with the `hom` fields. These form the category `Pseudofunctor.DescentData.instCategory`, and `Pseudofunctor.DescentData.isoMk` builds isomorphisms. Each object $M$ of $F(S)$ gives descent data $(f_i^* M)$ with the canonical isomorphisms. This is the functor
$$\texttt{Pseudofunctor.toDescentData}\ F\ f : F(S) \to \mathrm{Desc}_F(f).$$
Descent is the question whether this functor is fully faithful (descent of morphisms) or an equivalence (effective descent).

The category of descent data depends on the family only through the sieve that it generates. Given a second family $f'_j : X'_j \to S'$ with an isomorphism $S' \cong S$ and maps $X'_j \to X_{\alpha(j)}$ over it, `Pseudofunctor.DescentData.pullFunctor` is the restriction functor $\mathrm{Desc}_F(f) \to \mathrm{Desc}_F(f')$. Up to isomorphism it does not depend on the choices (`Pseudofunctor.DescentData.pullFunctorIso`), it respects identities and composition (`Pseudofunctor.DescentData.pullFunctorIdIso`, `Pseudofunctor.DescentData.pullFunctorCompIso`), and `Pseudofunctor.DescentData.pullFunctorEquivalence` is an equivalence when the two families generate the same sieve. The lemma `Pseudofunctor.DescentData.isEquivalence_toDescentData_iff_of_sieve_eq` deduces that effective descent depends only on the sieve.

#### Descent data with chosen pullbacks

When the fibre products exist, the descent data take the classical form. Choose pullbacks $X_{ij} = X_i \times_S X_j$ and threefold fibre products $X_{ijk}$, as `ChosenPullback` and `ChosenPullback₃` data. An object of `Pseudofunctor.DescentData'` is a family $M_i$ with morphisms $\varphi_{ij} : p_1^* M_i \to p_2^* M_j$ on $X_{ij}$, such that $\varphi_{ii}$ is the identity after pullback by the diagonal and $\varphi_{ik} = \varphi_{jk} \circ \varphi_{ij}$ after pullback to $X_{ijk}$.

**Proposition.** The category `DescentData' sq sq₃` is equivalent to `DescentData f`. This is `Pseudofunctor.DescentData'.descentDataEquivalence`.

*Proof sketch.* From descent data in the general form, keep only the morphisms for the pairs of projections $X_{ij} \to X_i$, $X_{ij} \to X_j$. Conversely, a pair $f_1 : Y \to X_{i_1}$, $f_2 : Y \to X_{i_2}$ over $S$ factors uniquely through $X_{i_1 i_2}$, and the morphism for $(f_1, f_2)$ is the pullback of $\varphi_{i_1 i_2}$ along this factorization. The cocycle conditions match because a triple of morphisms factors through $X_{i_1 i_2 i_3}$. The two constructions are the functors `Pseudofunctor.DescentData'.toDescentDataFunctor` and `Pseudofunctor.DescentData'.fromDescentDataFunctor`. ∎

#### Descent data as coalgebras

Assume now that each pullback $g^*$ has a right adjoint $g_*$, so that $F$ is a pseudofunctor to the bicategory `Bicategory.Adj Cat` of adjunctions. Then a morphism $M_{i_1} \to f_{i_1}^* f_{i_2 *} M_{i_2}$ is the same as a morphism of the pullbacks to the fibre product, when base change holds. The structure `Pseudofunctor.DescentDataAsCoalgebra` uses this form: its fields are objects $M_i$ and morphisms $M_{i_1} \to f_{i_1}^* f_{i_2 *} M_{i_2}$, with a counit condition (`Pseudofunctor.DescentDataAsCoalgebra.counit`) and a coassociativity condition (`Pseudofunctor.DescentDataAsCoalgebra.coassoc`).

**Proposition.** For a single morphism $f : X \to S$, the descent data as coalgebras are the coalgebras of the comonad $f^* f_*$ on $F(X)$. This is `Pseudofunctor.DescentDataAsCoalgebra.coalgebraEquivalence`.

So for one morphism, effective descent is the comonadicity of $f^*$: by `Pseudofunctor.isEquivalence_toDescentDataAsCoalgebra_iff_isEquivalence_comonadComparison`, the functor `Pseudofunctor.toDescentDataAsCoalgebra` is an equivalence if and only if the comparison functor of the adjunction to the coalgebras is an equivalence. This links the section with the comonads of Volume 24, Chapter 6.

#### Prestacks

Let $M, N$ be objects of $F(S)$. The presheaf `Pseudofunctor.presheafHom M N` on the category `Over S` sends $p : X \to S$ to the set of morphisms $p^* M \to p^* N$. Its value on the identity of $S$ is $\mathrm{Hom}(M, N)$, by `Pseudofunctor.presheafHomObjHomEquiv`. A compatible family of sections over a family $f$ is the same as a morphism between the descent data of $M$ and $N$, by `Pseudofunctor.DescentData.subtypeCompatibleHomEquiv`.

The class `Pseudofunctor.IsPrestackFor F R` says that the descent functor is fully faithful for the presieve $R$. The theorem `Pseudofunctor.isPrestackFor_iff_isSheafFor` states it as a sheaf condition: $F$ is a prestack for a sieve $R$ if and only if each presheaf `presheafHom M N` is a sheaf for the sieve on `Over.mk (𝟙 S)` that corresponds to $R$. The class `Pseudofunctor.IsPrestack F J` asks that each `presheafHom M N` is a sheaf for the topology `J.over S`, and `Pseudofunctor.IsPrestack.isSheaf` extracts this. The definition `Pseudofunctor.sheafHom` packs the presheaf as a sheaf. For a prestack and a covering family $f$, `Pseudofunctor.fullyFaithfulToDescentData` gives the full faithfulness of `toDescentData f`.

#### Stacks

The class `Pseudofunctor.IsStackFor F R` says that the descent functor of the family of arrows of $R$ is an equivalence (`Pseudofunctor.isStackFor_iff`). It implies `IsPrestackFor` (`Pseudofunctor.IsStackFor.isPrestackFor`). The class `Pseudofunctor.IsStack F J` extends `IsPrestack F J` by the condition that $F$ is a stack for each covering sieve.

**Theorem.** Let $F$ be a stack for $J$ and let $f_i : X_i \to S$ be a family whose sieve is covering. Then `F.toDescentData f` is an equivalence of categories. This is `Pseudofunctor.isEquivalence_toDescentData`.

*Proof.* The descent functor for $f$ and the descent functor for the arrows of the generated sieve differ by the equivalence `pullFunctorEquivalence`, because the two families generate the same sieve. The second functor is an equivalence by the stack condition. ∎

The module `Mathlib.CategoryTheory.Sites.Descent.Precoverage` reduces the conditions to a precoverage. Let $J$ be a precoverage with `HasIsos`, `IsStableUnderBaseChange` and `IsStableUnderComposition`, on a category with pullbacks. Then `Pseudofunctor.IsPrestack.of_precoverage` and `Pseudofunctor.IsStack.of_precoverage` say that it suffices to check the conditions on the covering presieves of $J$, not on all covering sieves of the generated topology. The key step is `Pseudofunctor.DescentData.fullyFaithfulPullFunctor`: for a prestack, the restriction to a finer covering family is fully faithful. From it, `Pseudofunctor.IsStackFor.of_le` passes the stack condition from a covering presieve to a larger one.

#### Common errors

1. The pseudofunctor is contravariant through `LocallyDiscrete Cᵒᵖ`. The pullback along $g$ is `(F.map g.op.toLoc).toFunctor`, and its composition with another pullback agrees with the pullback of the composite only up to the isomorphisms `Pseudofunctor.mapComp`. Use the lemmas `Pseudofunctor.LocallyDiscreteOpToCat.pullHom_pullHom` and `Pseudofunctor.LocallyDiscreteOpToCat.pullHom_id` instead of rewriting functors.
2. In `DescentData` the overlaps are pairs of morphisms from a test object, not fibre products. To get the classical cocycle form, pass through `DescentData'` with chosen pullbacks.
3. The library does not ask that the fibres are groupoids. A stack in the sense of this section is a stack of categories, and a stack in groupoids is a special case.

### Exercises

1. (A) Let $P$ be a presheaf of sets on $C$, viewed as a pseudofunctor with discrete categories as fibres. Show that $P$ is a prestack for $J$ if and only if it is separated, and a stack if and only if it is a sheaf.
2. (A) Show that the field `hom` of a descent datum is an isomorphism, with inverse the morphism for the pair $(f_2, f_1)$.
3. (B) For the family with one member, the identity of $S$, show that `toDescentData` is an equivalence for every pseudofunctor $F$.
4. (B) Let $F$ send a set $X$ to the category of families of sets indexed by $X$, with reindexing as pullback. Show that $F$ is a stack for the topology of jointly surjective families on the category of sets.
5. (B) Deduce from `Pseudofunctor.DescentDataAsCoalgebra.coalgebraEquivalence` that, for a single morphism $f$ with $f^*$ comonadic, the descent along $f$ is effective.
6. (C) Prove that if $F$ is a prestack and two covering families generate sieves with $R \le R'$, then a stack condition for $R$ implies the stack condition for $R'$, following `Pseudofunctor.IsStackFor.of_le`.

### Reference

<?reference?>
