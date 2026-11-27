---
title: Zero objects, kernels and biproducts
kind: theory
modules:
  - Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
  - Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
  - Mathlib.CategoryTheory.Limits.Shapes.Kernels
  - Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
explains:
  E3: [CategoryTheory.Limits.HasZeroObject, CategoryTheory.Limits.IsZero, CategoryTheory.Limits.HasZeroMorphisms, CategoryTheory.Limits.kernel, CategoryTheory.Limits.cokernel, CategoryTheory.Limits.BinaryBicone, CategoryTheory.Limits.HasBinaryBiproduct]
  E2: [CategoryTheory.Limits.isZero_zero, CategoryTheory.Limits.IsZero.iso, CategoryTheory.Limits.HasZeroObject.zeroIsoTerminal, CategoryTheory.Limits.HasZeroMorphisms.ext, CategoryTheory.Limits.comp_zero, CategoryTheory.Limits.zero_comp, CategoryTheory.Limits.HasZeroObject.zeroMorphismsOfZeroObject, CategoryTheory.Limits.IsZero.iff_id_eq_zero, CategoryTheory.Limits.zero_of_comp_mono, CategoryTheory.Limits.HasKernel, CategoryTheory.Limits.kernel.ι, CategoryTheory.Limits.kernel.lift, CategoryTheory.Limits.kernel.condition, CategoryTheory.Limits.KernelFork, CategoryTheory.Limits.cokernel.π, CategoryTheory.Limits.cokernel.desc, CategoryTheory.Limits.equalizer_as_kernel, CategoryTheory.Limits.isZero_kernel_of_mono, CategoryTheory.Limits.kernel.ι_of_mono, CategoryTheory.Limits.kernelZeroIsoSource, CategoryTheory.Limits.BinaryBicone.IsBilimit, CategoryTheory.Limits.BinaryBicone.isLimitSndKernelFork, CategoryTheory.Limits.biprod.inl, CategoryTheory.Limits.biprod.fst, CategoryTheory.Limits.biprod.isoProd]
  E1: auto
families: []
requires: [V05, V07, V24.C01, V24.C04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Zero objects, kernels and biproducts

### Overview

The categories of abelian groups and of modules share features that sets and topological spaces lack. There is an object that is both initial and terminal, every hom set has a distinguished zero map, every morphism has a kernel and a cokernel, and the product of two objects is also their coproduct. This section sets up these notions in a general category, using only the limits of Chapter 4. Addition of morphisms is not assumed; it is the subject of Section 2.

In Mathlib, `f ≫ g` is "first $f$, then $g$", the textbook $g \circ f$. The text writes composition in the textbook order.

### Definitions

**Definition (Zero object).** An object $0$ of a category $C$ is a *zero object* if it is both initial and terminal: for every $X$ there is exactly one morphism $0 \to X$ and exactly one morphism $X \to 0$.

::: mathlib

`CategoryTheory.Limits.IsZero` · `Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects`

The predicate `IsZero X` says that `X` has unique morphisms to and from every object. The class `HasZeroObject C` asserts that some object is zero; it provides `0 : C` with `isZero_zero`. Any two zero objects are isomorphic by `IsZero.iso`, and `HasZeroObject.zeroIsoTerminal` identifies `0` with the terminal object.

<?decl CategoryTheory.Limits.IsZero?>
:::

**Definition (Zero morphisms).** A category $C$ *has zero morphisms* if each hom set $\mathrm{Hom}(X, Y)$ has a chosen element $0_{X,Y}$ such that $f \circ 0 = 0$ and $0 \circ g = 0$ for all composable $f$ and $g$.

::: mathlib

`CategoryTheory.Limits.HasZeroMorphisms` · `Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms`

A class whose data is an instance `Zero (X ⟶ Y)` for all objects and whose fields are `comp_zero : f ≫ (0 : Y ⟶ Z) = 0` and `zero_comp : (0 : X ⟶ Y) ≫ f = 0`. The lemma `HasZeroMorphisms.ext` says that two such structures are equal, and `HasZeroObject.zeroMorphismsOfZeroObject` builds one from a zero object.

<?decl CategoryTheory.Limits.HasZeroMorphisms?>
:::

**Definition (Kernel and cokernel).** Let $C$ have zero morphisms and $f : X \to Y$. A *kernel* of $f$ is an object $K$ with a morphism $\iota : K \to X$ such that $f \circ \iota = 0$, universal with this property: for every $g : W \to X$ with $f \circ g = 0$ there is a unique $u : W \to K$ with $\iota \circ u = g$. Equivalently, it is an equalizer of $f$ and $0$. A *cokernel* of $f$ is a morphism $\pi : Y \to Q$ with $\pi \circ f = 0$, universal among such morphisms; it is a coequalizer of $f$ and $0$.

::: mathlib

`CategoryTheory.Limits.kernel` · `Mathlib.CategoryTheory.Limits.Shapes.Kernels`

A kernel fork of `f` is a `KernelFork f`, a fork on the pair `f` and `0`, and `HasKernel f` says that a limiting one exists. Then `kernel f` is its vertex, `kernel.ι f` the inclusion with `kernel.condition f : kernel.ι f ≫ f = 0`, and `kernel.lift f g w` the induced map. By `equalizer_as_kernel` the kernel inclusion is the equalizer inclusion of `f` and `0`. The dual names are `cokernel f`, `cokernel.π f` and `cokernel.desc f g w`.

<?decl CategoryTheory.Limits.kernel?>
:::

**Definition (Binary biproduct).** Let $C$ have zero morphisms. A *binary bicone* on $X$ and $Y$ is an object $P$ with morphisms $p_1 : P \to X$, $p_2 : P \to Y$, $i_1 : X \to P$ and $i_2 : Y \to P$ such that
$$p_1 \circ i_1 = \mathrm{id}_X, \qquad p_2 \circ i_2 = \mathrm{id}_Y, \qquad p_2 \circ i_1 = 0, \qquad p_1 \circ i_2 = 0.$$
It is a *bilimit* if $(P, p_1, p_2)$ is a product and $(P, i_1, i_2)$ is a coproduct. A *biproduct* $X \oplus Y$ is the vertex of a bilimit bicone.

::: mathlib

`CategoryTheory.Limits.BinaryBicone` · `Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts`

A structure with `pt`, `fst`, `snd`, `inl`, `inr` and the four equations. `BinaryBicone.IsBilimit` holds a limit for the cone and a colimit for the cocone. `HasBinaryBiproduct X Y` says that a bilimit bicone exists; then `X ⊞ Y` is the biproduct with `biprod.fst` and `biprod.inl`, and `biprod.isoProd` identifies it with the product `X ⨯ Y`.

<?decl CategoryTheory.Limits.BinaryBicone?>
:::

### Theorems and proofs

**Theorem (Zero morphisms are unique).** A category has at most one system of zero morphisms.

*Proof.* Let $0$ and $0'$ be two systems. For objects $X$ and $Y$, consider $0_{X,Y} \circ 0'_{X,X}$. By the law $0 \circ g = 0$ of the first system it equals $0_{X,Y}$, and by the law $f \circ 0' = 0'$ of the second system it equals $0'_{X,Y}$. Hence $0_{X,Y} = 0'_{X,Y}$. $\square$

So having zero morphisms is a property of a category, not extra structure, and Mathlib's `HasZeroMorphisms.ext` records this.

**Theorem (Zero objects give zero morphisms).** If $C$ has a zero object, then $0_{X,Y} : X \to 0 \to Y$ is a system of zero morphisms. In a category with zero morphisms, an object $Z$ is a zero object if and only if $\mathrm{id}_Z = 0$.

*Proof.* Write $0_{X,Y} = b \circ a$ with $a : X \to 0$ and $b : 0 \to Y$, the unique maps. For $f : Y \to Y'$, the composite $f \circ b$ is a morphism $0 \to Y'$, so it is the unique one and $f \circ 0_{X,Y} = 0_{X,Y'}$. For $g : X' \to X$, $a \circ g$ is the unique map $X' \to 0$, so $0_{X,Y} \circ g = 0_{X',Y}$.

For the second claim, let $Z$ be a zero object. Then $\mathrm{id}_Z$ and $0_{Z,Z}$ are both morphisms $Z \to Z$, and there is only one, as $Z$ is terminal. Conversely, let $\mathrm{id}_Z = 0$. For any $f : Z \to Y$, $f = f \circ \mathrm{id}_Z = f \circ 0 = 0$, so $0$ is the only morphism $Z \to Y$; it exists. Dually, every $g : X \to Z$ equals $\mathrm{id}_Z \circ g = 0$. Hence $Z$ is initial and terminal. $\square$

::: mathlib

`CategoryTheory.Limits.IsZero.iff_id_eq_zero` · `Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms`

The second claim, `IsZero X ↔ 𝟙 X = 0`.

<?decl CategoryTheory.Limits.IsZero.iff_id_eq_zero?>
:::

**Theorem (Kernels and monomorphisms).** Let $C$ have zero morphisms and let $\iota : K \to X$ be a kernel of $f : X \to Y$.

1. $\iota$ is a monomorphism.
2. If $f$ is a monomorphism, then $K$ is a zero object, and $\iota = 0$.
3. If $f = 0$, then $\iota$ is an isomorphism.

*Proof.* (1) Let $u, v : W \to K$ with $\iota \circ u = \iota \circ v =: g$. Then $f \circ g = f \circ \iota \circ u = 0 \circ u = 0$, so $g$ factors through $\iota$ by a unique map. Both $u$ and $v$ are such factorizations, so $u = v$.

(2) Here $f \circ \iota = 0 = f \circ 0_{K,X}$, and $f$ is mono, so $\iota = 0$. Then $\iota \circ \mathrm{id}_K = 0 = \iota \circ 0_{K,K}$, and $\iota$ is mono by (1), so $\mathrm{id}_K = 0$. By the previous theorem $K$ is a zero object.

(3) If $f = 0$, then $\mathrm{id}_X$ satisfies $f \circ \mathrm{id}_X = 0$, so there is a unique $u : X \to K$ with $\iota \circ u = \mathrm{id}_X$. Then $\iota \circ (u \circ \iota) = \iota = \iota \circ \mathrm{id}_K$, and since $\iota$ is mono, $u \circ \iota = \mathrm{id}_K$. $\square$

::: mathlib

`CategoryTheory.Limits.isZero_kernel_of_mono` · `Mathlib.CategoryTheory.Limits.Shapes.Kernels`

Part (2): for a mono `f`, `IsZero (kernel f)`. The equation `kernel.ι f = 0` is `kernel.ι_of_mono`, and part (3) is the isomorphism `kernelZeroIsoSource : kernel 0 ≅ X`. The lemma `zero_of_comp_mono` says that `g ≫ f = 0` with `f` mono forces `g = 0`, the step used in (2).

<?decl CategoryTheory.Limits.isZero_kernel_of_mono?>
:::

**Theorem (Biproduct inclusions are kernels).** Let $(P, p_1, p_2, i_1, i_2)$ be a binary bicone whose cone is a product. Then $i_1 : X \to P$ is a kernel of $p_2$.

*Proof.* By the bicone equations $p_2 \circ i_1 = 0$. Let $g : W \to P$ with $p_2 \circ g = 0$. The morphisms $g$ and $i_1 \circ p_1 \circ g$ from $W$ to $P$ agree after $p_1$, since $p_1 \circ i_1 \circ p_1 \circ g = p_1 \circ g$, and after $p_2$, since $p_2 \circ i_1 \circ p_1 \circ g = 0 = p_2 \circ g$. A morphism into a product is determined by its components, so $g = i_1 \circ (p_1 \circ g)$, and $u = p_1 \circ g$ is a factorization. It is unique, since $i_1 \circ u = i_1 \circ u'$ gives $u = p_1 \circ i_1 \circ u = p_1 \circ i_1 \circ u' = u'$. $\square$

::: mathlib

`CategoryTheory.Limits.BinaryBicone.isLimitSndKernelFork` · `Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts`

From `IsLimit c.toCone`, the kernel fork of `c.snd` given by `c.inl` is a limit.

<?decl CategoryTheory.Limits.BinaryBicone.isLimitSndKernelFork?>
:::

### Examples

**Example (Modules).** In the category of modules over a ring $R$ (Volume 7), the zero module is a zero object and the zero maps are the zero morphisms. The kernel of $f : M \to N$ is the inclusion of the submodule $\ker f$: if $f \circ g = 0$, then $g$ lands in $\ker f$, and the factorization is $g$ with smaller codomain. The cokernel is the quotient map $N \to N / \operatorname{im} f$, by the universal property of quotient modules. The product $M \times N$ with the inclusions $m \mapsto (m, 0)$ and $n \mapsto (0, n)$ is a biproduct: a pair of linear maps $a : M \to L$ and $b : N \to L$ induces $(m, n) \mapsto a(m) + b(n)$, and it is the only linear map extending both, since $(m, n) = (m, 0) + (0, n)$. Abelian groups are the case $R = \mathbb{Z}$.

::: mathlib

`ModuleCat.kernelIsoKer` · `Mathlib.Algebra.Category.ModuleCat.Kernels`

The isomorphism from the categorical kernel to the submodule `ker f`. The cokernel is identified with the quotient by the range in `ModuleCat.cokernelIsoRangeQuotient`, and `ModuleCat.biprodIsoProd` identifies the biproduct with the product module. For abelian groups, `AddCommGrpCat.biprodIsoProd` in `Mathlib.Algebra.Category.Grp.Biproducts` does the same.

:::

**Counterexample (Sets and groups).** The category of sets has no zero object: the initial object is $\varnothing$ and the terminal object is a point, and there is no map from a point to $\varnothing$. The category of groups has a zero object, the trivial group, and the kernels of the categorical sense are the usual kernels. It has no biproduct of $\mathbb{Z}$ with itself: a biproduct would be both the product $\mathbb{Z} \times \mathbb{Z}$, which is abelian, and the coproduct, the free product $\mathbb{Z} * \mathbb{Z}$ of Chapter 4, which is not abelian, and these are not isomorphic.

### The library around it

The file `Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects` treats `IsZero` as the basic notion and defines `HasZeroObject` from it; the zero object `0` is a choice, and lemmas are stated with `IsZero` where possible, so they apply to any zero object. Zero morphisms are a class that is a proposition up to `HasZeroMorphisms.ext`. Kernels and cokernels in `Mathlib.CategoryTheory.Limits.Shapes.Kernels` are special forks and cofork, with their own constructors `KernelFork.ofι` and `CokernelCofork.ofπ`, so that the limit API of Chapter 4 applies. The file `Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts` treats binary biproducts, and `Mathlib.CategoryTheory.Limits.Shapes.Biproducts` treats biproducts of families, with `HasFiniteBiproducts`. Images, the factorization of a morphism as an epimorphism followed by a monomorphism, live in `Mathlib.CategoryTheory.Limits.Shapes.Images` and appear in Section 2.

### Exercises

1. (A) Show that in the category of pointed sets the one point set is a zero object, and describe the kernel of a pointed map.
2. (A) Show that in a category with zero morphisms, $0 : X \to Y$ is a monomorphism if and only if $X$ is a zero object.
3. (B) Show that a cokernel $\pi : Y \to Q$ of any morphism is an epimorphism, and that a cokernel of an epimorphism has $Q$ a zero object. Explain why this is the dual of the theorem on kernels.
4. (B) In abelian groups, let $\iota : \ker f \to X$ be the kernel of $f : X \to Y$. Compute the cokernel of $\iota$ and show that $\iota$ is a kernel of it.
5. (B) In a category with zero morphisms, show that the bicone equations determine $p_1, p_2$ from $i_1, i_2$ when the cocone is a coproduct, and conversely.
6. (C) Show that in the category of commutative monoids the product $M \times N$ is a biproduct, while in the category of monoids $\mathbb{N} \times \mathbb{N}$ is not a coproduct of $\mathbb{N}$ with itself.

### Notes and history

Kernels and cokernels in the categorical sense, and the duality between them, were set out in Mac Lane's 1950 paper on duality for groups and in Buchsbaum's thesis of 1955, which called such categories exact categories. Grothendieck's 1957 Tôhoku paper made zero objects, kernels, cokernels and biproducts the axioms of additive and abelian categories. Biproducts are also called direct sums. In Mathlib the notation `X ⊞ Y` keeps the biproduct apart from the product `X ⨯ Y` and the coproduct `X ⨿ Y`, which are isomorphic to it but not equal.

### Reference

<?reference?>
