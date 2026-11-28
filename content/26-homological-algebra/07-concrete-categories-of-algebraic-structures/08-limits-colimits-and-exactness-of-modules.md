---
title: Limits, colimits and exactness of modules
kind: api
modules:
  - Mathlib.Algebra.Category.ModuleCat.Limits
  - Mathlib.Algebra.Category.ModuleCat.Colimits
  - Mathlib.Algebra.Category.ModuleCat.FilteredColimits
  - Mathlib.Algebra.Category.ModuleCat.Products
  - Mathlib.Algebra.Category.ModuleCat.Biproducts
  - Mathlib.Algebra.Category.ModuleCat.Kernels
  - Mathlib.Algebra.Category.ModuleCat.Images
  - Mathlib.Algebra.Category.ModuleCat.EpiMono
  - Mathlib.Algebra.Category.ModuleCat.AB
  - Mathlib.Algebra.Category.ModuleCat.Subobject
  - Mathlib.Algebra.Category.ModuleCat.Simple
  - Mathlib.Algebra.Category.ModuleCat.Free
  - Mathlib.Algebra.Category.ModuleCat.Injective
  - Mathlib.Algebra.Category.ModuleCat.InjectiveDimension
  - Mathlib.Algebra.Category.ModuleCat.ProjectiveDimension
  - Mathlib.Algebra.Category.ModuleCat.Ext.Basic
  - Mathlib.Algebra.Category.ModuleCat.Ext.Finite
  - Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
  - Mathlib.Algebra.Category.ModuleCat.LeftResolution
  - Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
  - Mathlib.Algebra.Category.ModuleCat.Ulift
  - Mathlib.Algebra.Category.ModuleCat.Algebra
  - Mathlib.Algebra.Category.ModuleCat.Descent
  - Mathlib.Algebra.Category.ModuleCat.Localization
explains:
  E2: [ModuleCat.HasLimits.limitConeIsLimit, ModuleCat.kernelIsoKer, ModuleCat.cokernelIsoRangeQuotient, ModuleCat.epi_iff_surjective, instIsGrothendieckAbelianModuleCat, simple_iff_isSimpleModule, ModuleCat.free_shortExact, Module.injective_iff_injective_object, ModuleCat.finite_ext, comonadicExtendScalars]
  E1: auto
families: []
requires: [V24.C04, V24.C08, V25.C02, V26.C04, V07, V09]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Limits, colimits and exactness of modules

### Overview

Section 2 proves that `ModuleCat R` is abelian and has enough projectives and enough injectives. This section describes the files that make the abelian structure usable. They identify each categorical construction with the construction of linear algebra: the kernel with `LinearMap.ker`, the cokernel with the quotient by the range, the product with the product of modules, the coproduct with the direct sum, and the subobjects with the submodules. They also prove the Grothendieck axioms, so `ModuleCat R` is a Grothendieck abelian category.

The second half collects the homological facts about modules that the library proves in the language of categories. A short exact sequence of free modules splits into a basis. Injective modules are injective objects. Ext groups exist and are finitely generated over a Noetherian ring. Restriction of scalars and localization are exact, and extension of scalars along a faithfully flat map is comonadic, which is the start of descent theory.

### The library around it

#### Limits

The file `Mathlib.Algebra.Category.ModuleCat.Limits` proves that the limit of a diagram $F \colon J \to \mathrm{Mod}_R$ is the submodule of sections, as for groups in Section 4. The submodule `ModuleCat.sectionsSubmodule F` of $\prod_j F(j)$ contains the families $(x_j)$ with $F(u)(x_j) = x_k$ for each $u \colon j \to k$. The cone `ModuleCat.HasLimits.limitCone F` has this submodule as its point, and `ModuleCat.HasLimits.limitConeIsLimit` proves the universal property. The forgetful functors to types and to abelian groups preserve limits, by `ModuleCat.forget_preservesLimitsOfSize` and `ModuleCat.forget₂AddCommGroup_preservesLimitsOfSize`. The same file also gives `ModuleCat.directLimitIsColimit`: the direct limit `Module.DirectLimit` of a directed system of modules is the colimit in `ModuleCat R`.

#### Colimits

The file `Mathlib.Algebra.Category.ModuleCat.Colimits` takes a different path. The colimit of the underlying abelian groups exists by Section 4. For $r \in R$, multiplication by $r$ is a natural transformation of the diagram of groups, so it induces an endomorphism of the colimit. These endomorphisms define the module structure `ModuleCat.HasColimit.coconePointSMul`, and `ModuleCat.HasColimit.isColimitColimitCocone` proves the universal property. Because of this construction, the forgetful functor to `AddCommGrpCat` preserves colimits, `ModuleCat.forget₂PreservesColimitsOfSize`. The cocone `ModuleCat.finsuppCocone R M ι` gives a concrete coproduct of copies of one module: $M^{(\iota)}$, the finitely supported functions, is the coproduct of $\iota$ copies of $M$, by `ModuleCat.finsuppCoconeIsColimit`.

Filtered colimits have their own construction. The file `Mathlib.Algebra.Category.ModuleCat.FilteredColimits` puts a module structure on the filtered colimit of sets, with $r \cdot [x_j] = [r x_j]$, by `ModuleCat.FilteredColimits.colimit_smul_mk_eq`. So the forgetful functor to types preserves filtered colimits, `ModuleCat.FilteredColimits.forget_preservesFilteredColimits`, which general colimits do not satisfy.

#### Products, biproducts, kernels and images

| Lean name | Statement |
|---|---|
| `ModuleCat.productConeIsLimit` | $\prod_i M_i$ with the projections is a product |
| `ModuleCat.piIsoPi` | the categorical product is isomorphic to $\prod_i M_i$ |
| `ModuleCat.coprodIsoDirectSum` | the coproduct is isomorphic to $\bigoplus_i M_i$ |
| `ModuleCat.biprodIsoProd` | the biproduct $M \oplus N$ is isomorphic to $M \times N$ |
| `ModuleCat.biproductIsoPi` | a finite biproduct is isomorphic to $\prod_i M_i$ |
| `ModuleCat.kernelIsoKer` | the kernel of $f$ is isomorphic to `LinearMap.ker f` |
| `ModuleCat.cokernelIsoRangeQuotient` | the cokernel of $f$ is isomorphic to $N / \operatorname{range} f$ |
| `ModuleCat.imageIsoRange` | the image of $f$ is isomorphic to `LinearMap.range f` |
| `ModuleCat.subobjectModule` | subobjects of $M$ correspond to submodules, as an order isomorphism |

The isomorphisms come with simp lemmas, such as `ModuleCat.kernelIsoKer_inv_kernel_ι` and `ModuleCat.cokernel_π_cokernelIsoRangeQuotient_hom`, that say how the maps of the category correspond to the inclusion `Submodule.subtype` and the projection `Submodule.mkQ`. These lemmas let a proof move from the abstract kernel to the concrete one and back. Since subobjects are submodules, a set, the category is well powered, `ModuleCat.wellPowered_moduleCat`.

The file `Mathlib.Algebra.Category.ModuleCat.Biproducts` also proves the splitting lemma in the language of linear maps. If $0 \to A \xrightarrow{f} M \xrightarrow{g} B \to 0$ is exact and $f$ has a left inverse, then $M \cong A \times B$, by `lequivProdOfLeftSplitExact`. If $g$ has a right inverse, the same holds, by `lequivProdOfRightSplitExact`.

#### Monomorphisms, epimorphisms and simple objects

The file `Mathlib.Algebra.Category.ModuleCat.EpiMono` proves `ModuleCat.mono_iff_injective` and `ModuleCat.epi_iff_surjective`. Proof for epimorphisms: if $f \colon M \to N$ is an epimorphism, then the two maps $N \to N / \operatorname{range} f$, the projection and zero, agree after $f$, so they are equal, and the range is $N$. The forgetful functor to types preserves both, so a proof can pass to the underlying functions with `ModuleCat.forget_preservesEpimorphisms`.

The file `Mathlib.Algebra.Category.ModuleCat.Simple` relates the categorical notion of a simple object to the algebraic one. `simple_iff_isSimpleModule` says that `ModuleCat.of R M` is simple if and only if $M$ is a simple module, that is, $M \neq 0$ and its only submodules are $0$ and $M$. The proof uses `ModuleCat.subobjectModule`: subobjects are submodules, and monomorphisms are injective maps. The lemma `simple_of_finrank_eq_one` says that a module of dimension one over a field is simple.

#### The Grothendieck axioms

The file `Mathlib.Algebra.Category.ModuleCat.AB` proves AB5, AB4 and AB4*: filtered colimits are exact, coproducts are exact and products are exact. The instances are `instAB5ModuleCat`, `instAB4ModuleCat` and `instAB4StarModuleCat`. AB5 holds because filtered colimits are computed on the sets, and an element of a filtered colimit that maps to zero is zero at some stage. AB4* holds because a product of injective maps is injective and a product of surjective maps is surjective, by the axiom of choice. The ring is a separator, `ModuleCat.isSeparator`: two maps $f, g \colon M \to N$ with $f \circ h = g \circ h$ for each $h \colon R \to M$ agree, because $h$ can send $1$ to any $m \in M$. Together these facts give `instIsGrothendieckAbelianModuleCat`.

#### Free modules in exact sequences

The file `Mathlib.Algebra.Category.ModuleCat.Free` treats a short exact sequence $0 \to X_1 \xrightarrow{f} X_2 \xrightarrow{g} X_3 \to 0$. Let $(v_i)$ be a basis of $X_1$ and let $(w_k)$ be a basis of $X_3$. Choose $u_k \in X_2$ with $g(u_k) = w_k$. Then the family $(f(v_i)) \cup (u_k)$ is a basis of $X_2$. Proof: it spans, because for $x \in X_2$ one can subtract a combination of the $u_k$ to get an element of the kernel of $g$, which is the range of $f$. It is linearly independent, because a relation, after $g$, gives a relation among the $w_k$, so the coefficients of the $u_k$ vanish, and then injectivity of $f$ kills the others. The two halves are `ModuleCat.span_exact` and `ModuleCat.linearIndependent_shortExact`. The basis is `ModuleCat.Basis.ofShortExact`, and `ModuleCat.free_shortExact` says that $X_2$ is free. Over a ring with the strong rank condition, ranks add, by `ModuleCat.free_shortExact_rank_add` and `ModuleCat.free_shortExact_finrank_add`.

#### Injectives, dimensions and Ext

The file `Mathlib.Algebra.Category.ModuleCat.Injective` proves `Module.injective_iff_injective_object`: the predicate `Module.Injective R M` of linear algebra, defined by extension along injective linear maps, is the predicate `CategoryTheory.Injective` of the object. This is the link between the Baer criterion of linear algebra and the injective resolutions of Chapter 4. The files on dimensions give the invariance of `CategoryTheory.projectiveDimension` and `CategoryTheory.injectiveDimension` under isomorphisms of modules, even along a ring isomorphism, by `ModuleCat.projectiveDimension_eq_of_semiLinearEquiv` and `ModuleCat.injectiveDimension_eq_of_semiLinearEquiv`. A nonzero projective module has projective dimension zero, by `ModuleCat.projectiveDimension_eq_zero_of_projective`.

The instance `instHasExtModuleCatOfSmall` gives the Ext groups of Chapter 5 for modules, through enough projectives. Over a commutative Noetherian ring, `ModuleCat.finite_ext` proves that $\operatorname{Ext}^i(N, M)$ is a finitely generated $R$-module when $N$ and $M$ are. Proof sketch: by induction on $i$. Choose a surjection $R^n \to N$ with kernel $K$, finitely generated because $R$ is Noetherian. The long exact sequence gives a surjection $\operatorname{Ext}^{i}(K, M) \to \operatorname{Ext}^{i+1}(N, M)$, since $\operatorname{Ext}^{i+1}(R^n, M) = 0$, and the source is finitely generated by induction. The lemma `CategoryTheory.Abelian.Ext.postcomp_smul_id_eq_zero_of_mem_annihilator` says that an element $r$ that kills $N$ also kills each $\operatorname{Ext}^n(N, M)$. The definition `ModuleCat.projectiveResolution` gives a functorial projective resolution: each module is a quotient of the free module on its elements.

#### Exactness of the functors of change of rings

Let $f \colon R \to R'$ be a ring map. Restriction of scalars is exact, by `ModuleCat.restrictScalars_map_exact`, because it does not change the underlying groups. The file `Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact` proves this directly, so that the result holds in all universes. The functor `ModuleCat.uliftFunctor` moves a module to a higher universe. It is fully faithful and exact, and it preserves projective and injective objects.

For commutative rings, the file `Mathlib.Algebra.Category.ModuleCat.Localization` defines the localization functor `ModuleCat.localizedModuleFunctor`, $M \mapsto S^{-1}M$. It is exact, by `ModuleCat.localizedModuleFunctor_map_exact`, because localization is flat. The file `Mathlib.Algebra.Category.ModuleCat.Descent` proves that extension of scalars along a flat map preserves finite limits, `ModuleCat.preservesFiniteLimits_extendScalars_of_flat`, and that along a faithfully flat map it reflects isomorphisms, `ModuleCat.reflectsIsomorphisms_extendScalars_of_faithfullyFlat`. With the monadicity theorem of Volume 24, these give `comonadicExtendScalars`: extension of scalars along a faithfully flat map is comonadic. So a module over $R$ is the same as a module over $R'$ with descent data. This result is stated in the library and its proof uses the monadicity theorem, which is not repeated here.

#### Common errors

1. Colimits in `ModuleCat R` come from the colimits of abelian groups, not from the colimits of sets. The forgetful functor to types preserves filtered colimits, but not cokernels or coproducts.
2. `simple_iff_isSimpleModule` needs the object in the form `ModuleCat.of R M`. For an object $X$ of `ModuleCat R`, apply it to the carrier of $X$.
3. `ModuleCat.finite_ext` needs `IsNoetherianRing R` and a `Small` instance for the ring in the universe of the modules. Without them the instance does not fire.

### Exercises

1. (A) Use `ModuleCat.cokernelIsoRangeQuotient` to compute the cokernel of multiplication by $n$ on $\mathbb{Z}$ in `ModuleCat ℤ`.
2. (A) Show that $\mathbb{Q}$ is not a simple $\mathbb{Z}$-module, and that $\mathbb{Z}/p$ is simple for each prime $p$.
3. (B) Prove that a product of injective modules is injective, with `Module.injective_iff_injective_object` and the universal property of products.
4. (B) Give a short exact sequence of $\mathbb{Z}$-modules with free ends, and write the basis of the middle term that `ModuleCat.Basis.ofShortExact` builds.
5. (B) Show that in `ModuleCat ℤ` a product of surjective maps is surjective and a direct sum of injective maps is injective, the two facts behind AB4* and AB4.
6. (C) Prove that $\operatorname{Ext}^1_{\mathbb{Z}}(\mathbb{Z}/n, M) \cong M / nM$, and check that it is killed by $n$, as `CategoryTheory.Abelian.Ext.postcomp_smul_id_eq_zero_of_mem_annihilator` predicts.

### Reference

<?reference?>
