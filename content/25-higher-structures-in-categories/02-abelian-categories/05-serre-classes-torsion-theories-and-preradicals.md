---
title: Serre classes, torsion theories and preradicals
kind: api
modules:
  - Mathlib.CategoryTheory.Abelian.SerreClass.Basic
  - Mathlib.CategoryTheory.Abelian.SerreClass.MorphismProperty
  - Mathlib.CategoryTheory.Abelian.SerreClass.Localization
  - Mathlib.CategoryTheory.Abelian.SerreClass.Bousfield
  - Mathlib.CategoryTheory.Abelian.TorsionTheory.Basic
  - Mathlib.CategoryTheory.Abelian.Preradical.Basic
  - Mathlib.CategoryTheory.Abelian.Preradical.Colon
  - Mathlib.CategoryTheory.Abelian.Preradical.Radical
explains:
  E2: [CategoryTheory.ObjectProperty.IsSerreClass, CategoryTheory.ObjectProperty.prop_iff_of_shortExact, CategoryTheory.ObjectProperty.isoModSerre, CategoryTheory.ObjectProperty.isoModSerre_isInvertedBy_iff, CategoryTheory.ObjectProperty.SerreClassLocalization.abelian, CategoryTheory.ObjectProperty.SerreClassLocalization.isIso_map_iff, CategoryTheory.Abelian.isLocalization_isoModSerre_kernel_of_leftAdjoint, CategoryTheory.Abelian.TorsionTheory, CategoryTheory.Abelian.isTorsionClass_iff_of_wellPowered, CategoryTheory.Abelian.Preradical.isIso_toColon_iff]
  E1: auto
families: []
requires: [V07, V24.C04, V24.C05, V24.C08, V25.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Serre classes, torsion theories and preradicals

### Overview

An abelian category often has a class of objects that a mathematician wants to ignore. The finite abelian groups, the torsion modules and the presheaves that are locally zero are examples. A *Serre class* is a class of objects that contains zero and is closed under subobjects, quotients and extensions. The quotient of an abelian category by a Serre class is again abelian, and its objects are the old objects "up to the class". A *torsion theory* splits a category into a torsion part and a torsion-free part by the vanishing of morphisms. A *preradical* is a subfunctor of the identity, such as the torsion submodule or the socle.

The modules of this section treat these three ideas. The main results are that the localization at a Serre class is abelian, the theorem of Dickson on torsion classes, and the colon construction of Stenström for preradicals. The section uses the abelian categories of Section 1, the diagram lemmas of Section 2 and the exact functors of Section 3. The localization of a category at a class of morphisms is the subject of Chapter 4. This section uses only its universal property: a functor $L : C \to D$ is a localization at $W$ when it inverts $W$ and each functor that inverts $W$ factors through $L$ in a unique way up to isomorphism.

### The library around it

#### Serre classes

Let $C$ be an abelian category and $P$ a property of objects, of type `ObjectProperty C`. The class `ObjectProperty.IsSerreClass P` extends four classes: `ContainsZero`, `IsClosedUnderSubobjects`, `IsClosedUnderQuotients` and `IsClosedUnderExtensions`. The properties `⊤` and `IsZero` are Serre classes. A third instance says that the inverse image of a Serre class by an exact functor $F : D \to C$ is a Serre class. In particular, the kernel `Functor.kernel F` of an exact functor, the class of objects $X$ with $F X = 0$, is a Serre class. In abelian groups, the finite groups, the torsion groups and the $p$-groups for a prime $p$ are Serre classes.

**Proposition.** Let $P$ be a Serre class and $0 \to X_1 \to X_2 \to X_3 \to 0$ a short exact sequence. Then $P(X_2)$ holds if and only if $P(X_1)$ and $P(X_3)$ hold. If $X_1 \to X_2 \to X_3$ is only exact at $X_2$, then $P(X_1)$ and $P(X_3)$ still give $P(X_2)$.

*Proof.* The first claim is closure under subobjects, quotients and extensions. For the second claim, let $I$ be the image of $X_1 \to X_2$ and $Q$ the image of $X_2 \to X_3$. Then $I$ is a quotient of $X_1$ and $Q$ is a subobject of $X_3$, so both satisfy $P$. Exactness gives a short exact sequence $0 \to I \to X_2 \to Q \to 0$, and closure under extensions gives $P(X_2)$. $\square$

The two claims are `ObjectProperty.prop_iff_of_shortExact` and `ObjectProperty.prop_X₂_of_exact`.

#### Isomorphisms modulo a Serre class

The file `SerreClass.MorphismProperty` defines three classes of morphisms from a Serre class $P$. A morphism $f$ is in `P.monoModSerre` when $P(\ker f)$ holds, in `P.epiModSerre` when $P(\mathrm{coker}\, f)$ holds, and in `P.isoModSerre` when both hold. The last class is the infimum of the first two. Each monomorphism is mono modulo $P$ (`monomorphisms_le_monoModSerre`), each epimorphism is epi modulo $P$, and each isomorphism is an isomorphism modulo $P$ (`isomorphisms_le_isoModSerre`). For a monomorphism $f$, the lemma `isoModSerre_iff_of_mono` reduces the condition to the cokernel, and `isoModSerre_iff_of_epi` is the dual. The simp lemmas `isoModSerre_zero_iff`, `monoModSerre_zero_iff` and `epiModSerre_zero_iff` treat the zero morphism $0 : X \to Y$: it is an isomorphism modulo $P$ if and only if $P(X)$ and $P(Y)$ hold.

The file registers the closure properties of these classes as instances. The three classes are multiplicative, stable under retracts, and stable under base change and cobase change, and `isoModSerre` has the two-out-of-three property. The proofs of composition use the exact sequence of Section 2 for a composite $f \circ g$:

$$0 \to \ker g \to \ker(f \circ g) \to \ker f \to \mathrm{coker}\, g \to \mathrm{coker}(f \circ g) \to \mathrm{coker}\, f \to 0.$$

If $P(\ker g)$ and $P(\ker f)$ hold, exactness at $\ker(f \circ g)$ and `prop_X₂_of_exact` give $P(\ker(f \circ g))$. The other cases use exactness at the other places of the sequence.

**Theorem.** Let $F : C \to D$ be an exact functor between abelian categories. Then $F$ inverts each isomorphism modulo $P$ if and only if $F(X) = 0$ for each $X$ with $P(X)$.

*Proof.* Assume that $F$ inverts `P.isoModSerre`, and let $P(X)$ hold. The map $0 \to X$ is mono, and its cokernel is $X$, so it is an isomorphism modulo $P$. Then $F(0) \to F(X)$ is an isomorphism, and $F(X) = 0$. Conversely, assume that $F$ kills $P$, and let $f$ be an isomorphism modulo $P$. Since $F$ is exact, $F(\ker f)$ is the kernel of $F(f)$ and $F(\mathrm{coker}\, f)$ is its cokernel. Both are zero, so $F(f)$ is mono and epi, hence an isomorphism. $\square$

The theorem is `ObjectProperty.isoModSerre_isInvertedBy_iff`, and the statement `P ≤ F.kernel` expresses the right side.

#### The localization is abelian

Let $L : C \to D$ be a localization functor for `P.isoModSerre`. The file `SerreClass.Localization` first proves that `P.isoModSerre` has a calculus of left fractions and a calculus of right fractions, as two instances. So each morphism of $D$ has the form $L(s)^{-1} \circ L(f)$, and also the form $L(f) \circ L(s)^{-1}$, with $s$ an isomorphism modulo $P$. The lemmas `exists_isoModSerre_comp_eq_zero_iff` and `exists_comp_isoModSerre_eq_zero_iff` describe when $f$ becomes zero after a composition with such an $s$: exactly when the image of $f$ satisfies $P$.

From now on assume that $D$ is preadditive and that $L$ is additive. The namespace `ObjectProperty.SerreClassLocalization` holds the following results.

| Lean name | Statement |
|---|---|
| `isZero_obj_iff` | $L(X) = 0$ if and only if $P(X)$ |
| `map_eq_zero_iff` | $L(f) = 0$ if and only if $P(\mathrm{im}\, f)$ |
| `mono_map_iff` | $L(f)$ is mono if and only if $f$ is mono modulo $P$ |
| `epi_map_iff` | $L(f)$ is epi if and only if $f$ is epi modulo $P$ |
| `isIso_map_iff` | $L(f)$ is an isomorphism if and only if $f$ is an isomorphism modulo $P$ |
| `inverseImage_isomorphisms` | the morphisms that $L$ inverts are exactly `P.isoModSerre` |
| `abelian` | the category $D$ is abelian |
| `preservesFiniteLimits` | $L$ preserves finite limits, and `preservesFiniteColimits` is the dual |
| `exactFunctor_comp_iff` | $G : D \to E$ is exact if and only if $L \circ G$ is exact |

The definition `abelian` builds the instance `Abelian D` from the lemmas `hasKernels`, `hasCokernels`, `hasFiniteProducts`, `isNormalMonoCategory` and `isNormalEpiCategory`. The result `abelian` is a definition, not an instance, because $D$ has its preadditive structure from outside.

The universal property is about exact functors. The functor `SerreClassLocalization.whiskeringLeft` sends an exact functor $G : D \to E$ to the exact functor $L \circ G$, on the categories of exact functors of the form `D ⥤ₑ E`. The definition `fullyFaithfulWhiskeringLeft` shows that it is fully faithful, and `essImage_whiskeringLeft` says that its essential image consists of the exact functors that invert `P.isoModSerre`. With the theorem of the previous part, these are the exact functors that kill $P$. So $L$ is the universal exact functor that kills $P$, and $D$ is the *Serre quotient* $C/P$.

#### Bousfield localization

The file `SerreClass.Bousfield` gives a source of Serre quotients. Let $G : D \to C$ be an exact functor. Then `isoModSerre_kernel_eq_inverseImage_isomorphisms` says that a morphism $f$ of $D$ is an isomorphism modulo the kernel of $G$ if and only if $G(f)$ is an isomorphism. Now assume that $G$ has a fully faithful right adjoint $F$. Together with `Adjunction.isLocalization`, the lemma gives the theorem `isLocalization_isoModSerre_kernel_of_leftAdjoint`: the functor $G$ is a localization at `G.kernel.isoModSerre`. So $C$ is the Serre quotient of $D$ by the objects that $G$ kills. The third result, `isoModSerre_kernel_eq_isLocal_of_rightAdjoint`, writes the same class as the class `ObjectProperty.isLocal` of the essential image of $F$, the language of Bousfield localization in Chapter 4. The main example is sheafification. The sheafification of presheaves of abelian groups is exact, and its right adjoint, the inclusion of sheaves, is fully faithful. So the sheaves of abelian groups are the Serre quotient of the presheaves by the presheaves whose sheafification is zero.

#### Torsion theories

The file `TorsionTheory.Basic` uses the orthogonals of a property of objects. In a category with zero morphisms, the left orthogonal of $F$ is the class of the objects $X$ such that each morphism $X \to Y$ with $Y$ in $F$ is zero, and the right orthogonal is the dual. The structure `Abelian.TorsionTheory T F` says that $T$ is the left orthogonal of $F$ and $F$ is the right orthogonal of $T$. Its fields are `leftOrthogonal_eq` and `rightOrthogonal_eq`, and `TorsionTheory.torsion_iff` and `TorsionTheory.torsionFree_iff` unfold them. In abelian groups, the torsion groups and the torsion-free groups form a torsion theory: a nonzero element of finite order in $Y$ gives a nonzero map from a finite cyclic group to $Y$.

The classes `IsTorsionClass P` and `IsTorsionFreeClass P` say that $P$ is the torsion class, or the torsion-free class, of some torsion theory. The definitions are $P = {}^\perp(P^\perp)$ and $P = ({}^\perp P)^\perp$, and `IsTorsionClass.torsionTheory` builds the torsion theory $(P, P^\perp)$. Each property gives two torsion theories: `TorsionTheory.generated_by` has torsion-free class $P^\perp$, and `TorsionTheory.cogenerated_by` has torsion class ${}^\perp P$. A left orthogonal is always a torsion class, and a right orthogonal is always a torsion-free class, by two instances. The lemma `TorsionTheory.op` passes to the opposite category and exchanges the two classes.

A torsion class is closed under quotients, extensions and colimits of each shape, and a torsion-free class is closed under subobjects, extensions and limits of each shape. These closure facts are instances. The converse is the theorem of Dickson.

**Theorem (Dickson).** Let $C$ be a well-powered abelian category with coproducts. A property $P$ of objects is a torsion class if and only if it is closed under quotients, extensions and coproducts.

*Proof sketch.* Assume the closure properties. For an object $X$, let $t(X)$ be the sum of the subobjects of $X$ in $P$. It exists because $C$ is well-powered, and it is a quotient of a coproduct of objects of $P$, so $P(t(X))$ holds. The quotient $X / t(X)$ is in $P^\perp$. Indeed, let $A \to X / t(X)$ be a morphism with $P(A)$, and let $I$ be its image. Then $P(I)$ holds, and the inverse image of $I$ in $X$ is an extension of $I$ by $t(X)$, so it satisfies $P$ and lies in $t(X)$. Thus $I = 0$. Now let $X$ be in ${}^\perp(P^\perp)$. The projection $X \to X / t(X)$ is zero, so $X = t(X)$ and $P(X)$ holds. $\square$

The theorem is `Abelian.isTorsionClass_iff_of_wellPowered`, with the hypotheses `LocallySmall`, `WellPowered` and `HasCoproducts` at a universe `w`. Closure under coproducts is written as closure under colimits of the shapes `Discrete J`. The dual theorem `isTorsionFreeClass_iff_of_wellPowered` assumes that `Cᵒᵖ` is well-powered and that $C$ has products. The name `isTorsionClass_iff` is not Dickson's theorem: it is the lemma that unfolds the class `IsTorsionClass`.

#### Preradicals

A preradical on $C$ is a subfunctor of the identity functor: a functor $r : C \to C$ with a natural monomorphism $r \to \mathrm{id}$. In modules over a ring, the torsion submodule, the socle and the Jacobson radical $\mathrm{rad}(M)$ are preradicals. Mathlib defines `Abelian.Preradical C` as `MonoOver (𝟭 C)`, so the preradicals form a preorder category. For `Φ : Preradical C`, the functor is `Φ.r` and the monomorphism is `Φ.ι`. The simp lemma `Preradical.r_map_ι_app` says that $r(\iota_X) = \iota_{r X}$. The class `Preradical.IsIdempotent` says that $r(r X) = r X$, in the form that the map $r(r X) \to r X$ given by $\iota$ is an isomorphism for each $X$.

The file `Preradical.Colon` first gives the quotient functor `Φ.quotient`, the cokernel of `Φ.ι`, with the projection `Φ.π`. The short exact sequence $0 \to r X \to X \to X / r X \to 0$ is `Φ.shortComplexObj X`. The colon $(\Phi : \Psi)$ of two preradicals is defined at $X$ as the inverse image of $\Psi(X / \Phi X)$ under $X \to X / \Phi X$. In Lean, `Preradical.colon Φ Ψ` is a pullback in the functor category, and `isPullback_colon_obj` is the pullback square at an object. The map `toColon Φ Ψ` is the inclusion $\Phi \le (\Phi : \Psi)$.

**Proposition.** The inclusion $\Phi \to (\Phi : \Psi)$ is an isomorphism if and only if $\Psi(X / \Phi X) = 0$ for each $X$.

*Proof.* At $X$, the pullback square identifies $(\Phi : \Psi)(X) / \Phi(X)$ with $\Psi(X / \Phi X)$, since $X \to X / \Phi X$ is epi with kernel $\Phi(X)$. So the inclusion is an isomorphism at $X$ exactly when this quotient is zero. $\square$

The theorem `Preradical.isIso_toColon_iff` states that `toColon Φ Ψ` is an isomorphism if and only if the functor `Φ.quotient ⋙ Ψ.r` is a zero object. The file `Preradical.Radical` defines a *radical* as a preradical with $(\Phi : \Phi) = \Phi$. The property is `Preradical.isRadical C`, and `Abelian.Radical C` is the full subcategory of the radicals. The lemma `isRadical_iff_isZero` gives the usual definition: $\Phi$ is a radical when $\Phi(X / \Phi X) = 0$ for each $X$. The torsion submodule is a radical, because $M / t(M)$ is torsion-free. The Jacobson radical of modules is also a radical. The socle is idempotent but not a radical: for $M = \mathbb{Z}/p^2$ the socle is $p\mathbb{Z}/p^2$, and the quotient $\mathbb{Z}/p$ is its own socle. In the classical theory an idempotent radical is the same as a torsion theory, through $t(X) = r(X)$, but the files of this section do not state this correspondence.

#### Common errors

1. `SerreClassLocalization.abelian` is a definition, not an instance, and it assumes that $D$ is already preadditive and that $L$ is additive. A proof must provide these instances and then use `letI := SerreClassLocalization.abelian L P`.
2. The lemma `isTorsionClass_iff` only unfolds `IsTorsionClass`. Dickson's theorem is `isTorsionClass_iff_of_wellPowered`, and it needs a universe `w` for the size conditions.
3. A preradical is an object of `MonoOver (𝟭 C)`, so a morphism of preradicals is a morphism over the identity. Its natural transformation is `(toColon Φ Ψ).hom.left`, not `toColon Φ Ψ` itself, as in the statement of `isIso_toColon_hom_left_app_iff`.

### Exercises

1. (A) Show that the finite abelian groups form a Serre class in `ModuleCat ℤ`, and that the free abelian groups do not.
2. (A) Let $P$ be a Serre class. Show that a composite of two isomorphisms modulo $P$ is an isomorphism modulo $P$, with the exact sequence of the kernels and cokernels of a composite.
3. (B) Let $P$ be the class of torsion abelian groups. Show that the multiplication by $n \ne 0$ on $\mathbb{Z}$ is an isomorphism modulo $P$, and identify the Serre quotient $\mathrm{Ab}/P$ with the category of $\mathbb{Q}$-vector spaces.
4. (B) Prove that a torsion class is closed under quotients and extensions, directly from the definition as a left orthogonal.
5. (B) Show that the socle of modules over $\mathbb{Z}$ is an idempotent preradical, and compute the colon of the socle with itself on $\mathbb{Z}/p^3$.
6. (C) Let $(T, F)$ be a torsion theory in a well-powered abelian category with coproducts. Show that $X \mapsto t(X)$, the largest subobject of $X$ in $T$, is an idempotent radical, and that $T$ is the class of the objects with $t(X) = X$.

### Reference

<?reference?>
