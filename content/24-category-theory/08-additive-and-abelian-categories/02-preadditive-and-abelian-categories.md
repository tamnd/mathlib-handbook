---
title: Preadditive, additive and abelian categories
kind: theory
modules:
  - Mathlib.CategoryTheory.Limits.Shapes.Images
explains:
  E3: [CategoryTheory.Limits.MonoFactorisation, CategoryTheory.Limits.IsImage, CategoryTheory.Limits.HasImage, CategoryTheory.Limits.image]
  E2: [CategoryTheory.Limits.image.ι, CategoryTheory.Limits.factorThruImage, CategoryTheory.Limits.image.fac, CategoryTheory.Limits.image.lift, CategoryTheory.Limits.image.lift_fac, CategoryTheory.Limits.ImageFactorisation, CategoryTheory.Limits.HasImages, CategoryTheory.Limits.StrongEpiMonoFactorisation]
  E1: [CategoryTheory.Preadditive, CategoryTheory.Preadditive.add_comp, CategoryTheory.Preadditive.comp_add, CategoryTheory.Preadditive.mono_iff_cancel_zero, CategoryTheory.Limits.biprod.total, CategoryTheory.Limits.HasBinaryBiproduct.of_hasBinaryProduct, CategoryTheory.Limits.isBinaryBilimitOfTotal, CategoryTheory.Functor.Additive, CategoryTheory.Functor.map_add, CategoryTheory.Functor.additive_of_preservesBinaryBiproducts, CategoryTheory.Abelian, CategoryTheory.Abelian.monoIsKernelOfCokernel, CategoryTheory.Abelian.epiIsCokernelOfKernel, CategoryTheory.Abelian.coimageImageComparison, CategoryTheory.Abelian.coimageIsoImage, CategoryTheory.Abelian.ofCoimageImageComparisonIsIso, CategoryTheory.isIso_of_mono_of_epi]
families: []
requires: [V05, V07, V24.C01, V24.C04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Preadditive, additive and abelian categories

### Overview

Section 1 gave zero morphisms, kernels and biproducts without any addition of morphisms. In abelian groups and modules, morphisms can be added, and composition is bilinear. A category with this structure is *preadditive*. With a zero object and biproducts it is *additive*, and if also every morphism has a kernel and a cokernel and every monomorphism and epimorphism is of the expected kind, it is *abelian*. Abelian categories are the setting of homological algebra.

This section proves that in a preadditive category products are biproducts, that additive functors preserve biproducts, and that in an abelian category a morphism that is mono and epi is an isomorphism. It defines images and exactness, and points to Volume 25 for the theory of abelian categories and to Volume 26 for homological algebra. As in Section 1, Mathlib's `f ≫ g` is the textbook $g \circ f$.

### Definitions

**Definition (Preadditive category).** A category $C$ is *preadditive* if each $\mathrm{Hom}(X, Y)$ is an abelian group and composition is bilinear: $(g + g') \circ f = g \circ f + g' \circ f$ and $g \circ (f + f') = g \circ f + g \circ f'$.

Bilinearity gives $g \circ 0 = g \circ (0 + 0) = g \circ 0 + g \circ 0$, so $g \circ 0 = 0$, and likewise $0 \circ f = 0$. A preadditive category therefore has zero morphisms in the sense of Section 1. A morphism $f$ is mono if and only if $f \circ g = 0$ implies $g = 0$, since $f \circ g = f \circ h$ is $f \circ (g - h) = 0$.

::: mathlib

`CategoryTheory.Preadditive` · `Mathlib.CategoryTheory.Preadditive.Basic`

A class holding an `AddCommGroup (X ⟶ Y)` instance for all objects and the laws `add_comp` and `comp_add`. The criterion for monos is `Preadditive.mono_iff_cancel_zero`. The category `ModuleCat R` is preadditive by the instance `ModuleCat.instPreadditive`.

<?decl CategoryTheory.Preadditive?>
:::

**Definition (Additive category and functor).** A preadditive category is *additive* if it has a zero object and a biproduct of every two objects. A functor $F$ between preadditive categories is *additive* if each map $\mathrm{Hom}(X, Y) \to \mathrm{Hom}(FX, FY)$ is a group homomorphism.

::: mathlib

`CategoryTheory.Functor.Additive` · `Mathlib.CategoryTheory.Preadditive.AdditiveFunctor`

A class on a functor with the field `map_add`, used through `Functor.map_add : F.map (f + g) = F.map f + F.map g`. Mathlib has no separate class for additive categories; it combines `Preadditive` with `HasZeroObject` and `HasFiniteBiproducts`.

<?decl CategoryTheory.Functor.Additive?>
:::

**Definition (Abelian category).** A preadditive category $C$ is *abelian* if it has finite products, every morphism has a kernel and a cokernel, every monomorphism is a kernel of some morphism, and every epimorphism is a cokernel of some morphism.

::: mathlib

`CategoryTheory.Abelian` · `Mathlib.CategoryTheory.Abelian.Basic`

A class extending `Preadditive`, with finite products, kernels and cokernels, and the classes saying that monos are normal and epis are normal. The definitions `Abelian.monoIsKernelOfCokernel` and `Abelian.epiIsCokernelOfKernel` give the sharper fact that a mono is the kernel of its own cokernel, and dually.

<?decl CategoryTheory.Abelian?>
:::

**Definition (Image).** Let $f : X \to Y$. A *mono factorisation* of $f$ is a factorization $f = m \circ e$ through an object $I$ with $m : I \to Y$ a monomorphism. It is an *image* of $f$ if for every mono factorisation $f = m' \circ e'$ through $I'$ there is a morphism $u : I \to I'$ with $m' \circ u = m$. Since $m'$ is mono, $u$ is unique and $u \circ e = e'$.

::: mathlib

`CategoryTheory.Limits.MonoFactorisation` · `Mathlib.CategoryTheory.Limits.Shapes.Images`

A structure with the object `I`, the mono `m` and `e` with `fac : e ≫ m = f`. `IsImage F` holds the map `lift` to every other factorisation, and `HasImage f` says that an image exists. Then `image f` is the object, `image.ι f` the mono, `factorThruImage f` the first map, with `image.fac`, and `image.lift F'` the comparison with `image.lift_fac`.

<?decl CategoryTheory.Limits.MonoFactorisation?>
:::

**Definition (Exactness).** In an abelian category, let $X \xrightarrow{f} Y \xrightarrow{g} Z$ with $g \circ f = 0$, and let $f = m \circ e$ be an image factorization. Since $e$ is an epimorphism (Remark below) and $g \circ m \circ e = 0$, also $g \circ m = 0$, so $m$ factors through the kernel of $g$. The pair is *exact* if this map from the image of $f$ to the kernel of $g$ is an isomorphism. In modules, this says $\operatorname{im} f = \ker g$.

::: mathlib

`CategoryTheory.ShortComplex.Exact` · `Mathlib.Algebra.Homology.ShortComplex.Exact`

Mathlib phrases exactness for a `ShortComplex C`, a pair `f`, `g` with `f ≫ g = 0`, by the vanishing of its homology. In an abelian category, `ShortComplex.exact_iff_kernel_ι_comp_cokernel_π_zero` says it is exact if and only if `kernel.ι g ≫ cokernel.π f = 0`.

:::

### Theorems and proofs

**Theorem (Products are biproducts).** Let $C$ be preadditive and $(P, p_1, p_2)$ a product of $X$ and $Y$. Let $i_1 : X \to P$ have components $(\mathrm{id}_X, 0)$ and $i_2 : Y \to P$ have components $(0, \mathrm{id}_Y)$. Then $i_1 \circ p_1 + i_2 \circ p_2 = \mathrm{id}_P$, and $(P, i_1, i_2)$ is a coproduct, so $P$ is a biproduct. Conversely, a bicone with $i_1 \circ p_1 + i_2 \circ p_2 = \mathrm{id}_P$ is a bilimit.

*Proof.* The bicone equations hold by the definition of $i_1$ and $i_2$. By bilinearity, $p_1 \circ (i_1 \circ p_1 + i_2 \circ p_2) = \mathrm{id}_X \circ p_1 + 0 \circ p_2 = p_1$, and in the same way $p_2 \circ (i_1 \circ p_1 + i_2 \circ p_2) = p_2$. A morphism into the product is determined by its components, so $i_1 \circ p_1 + i_2 \circ p_2 = \mathrm{id}_P$.

Now take the converse statement, for any bicone with this total relation. Given $a : X \to W$ and $b : Y \to W$, put $h = a \circ p_1 + b \circ p_2$. Then $h \circ i_1 = a \circ p_1 \circ i_1 + b \circ p_2 \circ i_1 = a$ and $h \circ i_2 = b$. If $h'$ also satisfies $h' \circ i_1 = a$ and $h' \circ i_2 = b$, then
$$h' = h' \circ (i_1 \circ p_1 + i_2 \circ p_2) = a \circ p_1 + b \circ p_2 = h.$$
So $(P, i_1, i_2)$ is a coproduct. Dually, $k = i_1 \circ c + i_2 \circ d$ is the unique map with $p_1 \circ k = c$ and $p_2 \circ k = d$, so $(P, p_1, p_2)$ is a product. Applied to the bicone of the first part, this proves the theorem. $\square$

::: mathlib

`CategoryTheory.Limits.HasBinaryBiproduct.of_hasBinaryProduct` · `Mathlib.CategoryTheory.Preadditive.Biproducts`

In a preadditive category, a binary product gives a binary biproduct. The total relation is `biprod.total : biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr = 𝟙 _`, and `isBinaryBilimitOfTotal` is the converse part of the theorem.

<?decl CategoryTheory.Limits.HasBinaryBiproduct.of_hasBinaryProduct?>
:::

**Theorem (Additive functors preserve biproducts).** Let $F : C \to D$ be an additive functor between preadditive categories and $(P, p_1, p_2, i_1, i_2)$ a biproduct in $C$. Then $(FP, Fp_1, Fp_2, Fi_1, Fi_2)$ is a biproduct in $D$.

*Proof.* A group homomorphism sends $0$ to $0$, so $F$ preserves zero morphisms, and $F$ preserves identities and composites. The four bicone equations therefore hold for the image. By the previous theorem $i_1 \circ p_1 + i_2 \circ p_2 = \mathrm{id}_P$, and additivity gives $F i_1 \circ F p_1 + F i_2 \circ F p_2 = F(\mathrm{id}_P) = \mathrm{id}_{FP}$. By the converse part of the previous theorem, the image bicone is a bilimit. $\square$

The converse holds too: a functor between additive categories that preserves binary biproducts is additive, because $f + g$ is the composite $Y \oplus Y \to Y$ of the codiagonal after $X \to X \oplus X \to Y \oplus Y$. Mathlib has it as `Functor.additive_of_preservesBinaryBiproducts`.

**Theorem (Abelian categories are balanced).** In an abelian category, a morphism that is both a monomorphism and an epimorphism is an isomorphism.

*Proof.* Let $f : X \to Y$ be mono and epi. Since $f$ is mono, it is a kernel of some $g : Y \to Z$. Then $g \circ f = 0 = 0 \circ f$, and $f$ is epi, so $g = 0$. By Section 1, the kernel inclusion of a zero morphism is an isomorphism; kernels are unique up to a unique isomorphism compatible with the inclusions, so $f$, being a kernel of $g = 0$, is an isomorphism. $\square$

::: mathlib

`CategoryTheory.isIso_of_mono_of_epi` · `Mathlib.CategoryTheory.Balanced`

In a category with a `Balanced` instance, a mono and epi is an iso; the theorem says that abelian categories are balanced.

<?decl CategoryTheory.isIso_of_mono_of_epi?>
:::

**Remark (Coimage and image).** For $f : X \to Y$ in an abelian category, put $\operatorname{coim} f = \operatorname{coker}(\ker f)$ and $\operatorname{im} f = \ker(\operatorname{coker} f)$. There is a canonical morphism $\operatorname{coim} f \to \operatorname{im} f$ through which $f$ factors, and it is an isomorphism; in particular every morphism factors as an epimorphism followed by a monomorphism, and $\ker(\operatorname{coker} f)$ is an image of $f$. Conversely, a preadditive category with kernels and cokernels in which these comparison maps are isomorphisms is abelian. The proofs belong to the theory of abelian categories in Volume 25.

::: mathlib

`CategoryTheory.Abelian.coimageIsoImage` · `Mathlib.CategoryTheory.Abelian.Basic`

The isomorphism `Abelian.coimage f ≅ Abelian.image f`, built from `Abelian.coimageImageComparison`. The converse construction is `Abelian.ofCoimageImageComparisonIsIso`.

<?decl CategoryTheory.Abelian.coimageIsoImage?>
:::

### Examples

**Example (Modules are abelian).** Let $R$ be a ring. The category of $R$-modules is preadditive with pointwise addition of linear maps, and Section 1 gave its zero object, kernels, cokernels and biproducts. A monomorphism $m : M \to N$ is injective (test it against maps from $R$), and it is a kernel of the quotient map $q : N \to N / m(M)$: a map $g : W \to N$ with $q \circ g = 0$ lands in $m(M)$, and factors uniquely through $m$ because $m$ is injective. An epimorphism $e : M \to N$ is surjective (test it against the quotient $N \to N / e(M)$ and the zero map), and it is a cokernel of $\ker e \to M$ by the first isomorphism theorem: a map $h : M \to W$ that vanishes on $\ker e$ factors uniquely through $M / \ker e \cong N$. Hence the category is abelian, and the image of $f$ is the submodule $f(M)$. Abelian groups are the case $R = \mathbb{Z}$.

::: mathlib

`ModuleCat.abelian` · `Mathlib.Algebra.Category.ModuleCat.Abelian`

The instance `Abelian (ModuleCat R)`. For abelian groups the instance is `AddCommGrpCat.instAbelian` in `Mathlib.Algebra.Category.Grp.Abelian`.

:::

**Counterexample (Free abelian groups).** The full subcategory of finitely generated free abelian groups is additive: it is closed under $\mathbb{Z}^m \oplus \mathbb{Z}^n = \mathbb{Z}^{m + n}$ and contains $0$. It is not abelian. Multiplication by $2$ on $\mathbb{Z}$ is a monomorphism, since it is injective. It is also an epimorphism there: if $g \circ 2 = h \circ 2$ for $g, h : \mathbb{Z} \to \mathbb{Z}^n$, then $2 (g - h) = 0$, and $\mathbb{Z}^n$ has no $2$-torsion, so $g = h$. It is not an isomorphism, so the balanced theorem fails. Its cokernel in the subcategory is $0$, since $h \circ 2 = 0$ forces $h = 0$, so the mono $2$ is not the kernel of its cokernel.

### The library around it

Images in `Mathlib.CategoryTheory.Limits.Shapes.Images` are defined in any category; `HasImages` asks for all of them, and `StrongEpiMonoFactorisation` records factorizations whose first map is a strong epimorphism. An abelian category has images, and its strong epi and mono factorizations come from the coimage and the image. The preadditive part of the library is in `Mathlib.CategoryTheory.Preadditive`, and the abelian part in `Mathlib.CategoryTheory.Abelian`: pseudoelements, the five lemma and the snake lemma, exact functors and Grothendieck abelian categories. These are treated in Volume 25. Short complexes, homology, the long exact sequence and derived functors, in `Mathlib.Algebra.Homology`, are the subject of Volume 26.

### Exercises

1. (A) Show that a preadditive category with a terminal object has a zero object.
2. (A) Show that in a preadditive category $f$ is epi if and only if $g \circ f = 0$ implies $g = 0$.
3. (B) Show that the category of finite abelian groups is abelian, and that the category of torsion free abelian groups is not.
4. (B) In an additive category, show that the sum of $f, g : X \to Y$ equals $\nabla \circ (f \oplus g) \circ \Delta$, with $\Delta : X \to X \oplus X$ the diagonal and $\nabla : Y \oplus Y \to Y$ the codiagonal. Deduce that the addition on hom groups is determined by the category.
5. (B) In the category of modules, show that the map from the image of $f$ to the kernel of $g$ is the inclusion $f(X) \subseteq \ker g$, so exactness means $\ker g = f(X)$. Deduce that $0 \to X \xrightarrow{f} Y$ is exact if and only if $f$ is injective.
6. (C) Prove the Remark on coimage and image in the category of modules, using the first isomorphism theorem.

### Notes and history

Additive and abelian categories were introduced by Buchsbaum in 1955, under the name exact categories, and by Grothendieck in the 1957 Tôhoku paper, which set out the axioms used here and the conditions AB3 to AB5 that make derived functors and sheaf cohomology work. Freyd and Mitchell proved that every small abelian category embeds fully and exactly into a category of modules, which justifies diagram chases by elements. Exercise 4 is the reason that additivity is a property of a category with biproducts.

### Reference

<?reference?>
