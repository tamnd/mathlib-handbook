---
title: The structure of abelian categories
kind: theory
modules:
  - Mathlib.CategoryTheory.Abelian.Basic
  - Mathlib.CategoryTheory.Abelian.NonPreadditive
  - Mathlib.CategoryTheory.Abelian.Images
  - Mathlib.CategoryTheory.Abelian.Opposite
explains:
  E3: [CategoryTheory.Abelian, CategoryTheory.Abelian.image, CategoryTheory.Abelian.coimage, CategoryTheory.Abelian.coimageImageComparison, CategoryTheory.Abelian.coimageIsoImage, CategoryTheory.Abelian.ofCoimageImageComparisonIsIso, CategoryTheory.Abelian.epi_pullback_of_epi_f, CategoryTheory.NonPreadditiveAbelian, CategoryTheory.NonPreadditiveAbelian.preadditive, CategoryTheory.instAbelianOpposite]
  E2: [CategoryTheory.Abelian.factorThruImage, CategoryTheory.Abelian.image.ι, CategoryTheory.Abelian.coimage.π, CategoryTheory.Abelian.factorThruCoimage, CategoryTheory.Abelian.image.fac, CategoryTheory.Abelian.coimage_image_factorisation, CategoryTheory.Abelian.instEpiFactorThruImage, CategoryTheory.Abelian.instMonoFactorThruCoimage, CategoryTheory.Abelian.instIsIsoCoimageImageComparison, CategoryTheory.Abelian.imageIsoImage, CategoryTheory.Abelian.imageStrongEpiMonoFactorisation, CategoryTheory.Abelian.hasPullbacks, CategoryTheory.Abelian.hasFiniteLimits, CategoryTheory.Abelian.hasFiniteColimits, CategoryTheory.Abelian.mono_pushout_of_mono_f, CategoryTheory.Abelian.epi_snd_of_isLimit, CategoryTheory.NonPreadditiveAbelian.σ, CategoryTheory.NonPreadditiveAbelian.sub_def, CategoryTheory.NonPreadditiveAbelian.abelian, CategoryTheory.kernelOpOp, CategoryTheory.cokernelOpOp]
  E1: auto
families: []
requires: [V07, V24.C01, V24.C04, V24.C08, V25.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The structure of abelian categories

### Overview

Volume 24, Chapter 8 defined an abelian category and proved that a morphism that is mono and epi is an isomorphism there. It stated, without proof, that the coimage and the image of a morphism are isomorphic. This section proves that statement and the other basic facts that make diagram chases possible. Each morphism factors as an epimorphism followed by a monomorphism through its image. Abelian categories have all finite limits and colimits, and the pullback of an epimorphism is an epimorphism. Conversely, the coimage-image isomorphism characterizes abelian categories. Two more results show that the definition does not depend on small choices: the group structure on morphisms follows from the other axioms, and the opposite of an abelian category is abelian.

In the text $g \circ f$ is the textbook composite, and Mathlib writes `f ≫ g`. In this chapter $C$ is abelian unless the text says otherwise.

### Definitions

**Definition (Abelian category).** A category $C$ is *abelian* if it is preadditive, has finite products, kernels and cokernels, and each monomorphism is the kernel of some morphism and each epimorphism is the cokernel of some morphism.

By Chapter 1, Section 1, the finite products are biproducts. A monomorphism that is a kernel of some map is a kernel of its own cokernel, as Volume 24 shows, and dually for epimorphisms.

**Definition (Image and coimage).** Let $f : X \to Y$. Its *image* is $\mathrm{im}\, f = \ker(\mathrm{coker}\, f)$, with the monomorphism $i : \mathrm{im}\, f \to Y$. Its *coimage* is $\mathrm{coim}\, f = \mathrm{coker}(\ker f)$, with the epimorphism $p : X \to \mathrm{coim}\, f$.

Since $\mathrm{coker}(f) \circ f = 0$, the map $f$ factors as $f = i \circ e$ with a unique $e : X \to \mathrm{im}\, f$. Dually, $f \circ \ker f = 0$ gives $f = m \circ p$ with a unique $m : \mathrm{coim}\, f \to Y$.

**Definition (Comparison map).** The *coimage-image comparison* is the unique $\varphi : \mathrm{coim}\, f \to \mathrm{im}\, f$ with $i \circ \varphi \circ p = f$.

It exists in each preadditive category with kernels and cokernels. The map $e$ kills $\ker f$, because $i \circ e \circ \ker f = f \circ \ker f = 0$ and $i$ is mono. So $e = \varphi \circ p$ for a unique $\varphi$, and then $i \varphi p = i e = f$. Uniqueness follows because $i$ is mono and $p$ is epi.

::: mathlib

`CategoryTheory.Abelian.coimageImageComparison` · `Mathlib.CategoryTheory.Abelian.Images`

The map `Abelian.coimage f ⟶ Abelian.image f` for a preadditive category with kernels and cokernels. The factorizations are `Abelian.factorThruImage f`, `Abelian.image.ι f`, `Abelian.coimage.π f` and `Abelian.factorThruCoimage f`. The file also has the comparison as a natural transformation, `coimageImageComparisonFunctor`.

<?decl CategoryTheory.Abelian.coimageImageComparison?>
:::

### Theorems and proofs

**Theorem (Epi-mono factorization).** For each $f : X \to Y$ in an abelian category, the map $e : X \to \mathrm{im}\, f$ is an epimorphism. Dually, $m : \mathrm{coim}\, f \to Y$ is a monomorphism.

*Proof.* Let $q : \mathrm{im}\, f \to Q$ be the cokernel of $e$, and let $k : K \to \mathrm{im}\, f$ be the kernel of $q$. Since $q \circ e = 0$, the map $e$ factors as $e = k \circ e'$. The composite $i \circ k$ is a monomorphism. In an abelian category it is the kernel of some $c : Y \to W$. Then $c \circ f = c \circ i \circ k \circ e' = 0$, so $c$ factors through the cokernel $\pi$ of $f$, say $c = c' \circ \pi$. Since $i = \ker \pi$, $c \circ i = c' \circ \pi \circ i = 0$. So $i$ factors through $\ker c = i \circ k$: there is $t$ with $i = i \circ k \circ t$. As $i$ is mono, $k \circ t = 1$. Then $k \circ t \circ k = k$, and $k$ is mono, so $t \circ k = 1$. So $k$ is an isomorphism. From $q \circ k = 0$ follows $q = 0$. A map whose cokernel is zero is an epimorphism: if $g \circ e = 0$, then $g$ factors through $q = 0$, so $g = 0$. In a preadditive category this is the definition of epi. The second claim is the dual statement. $\square$

**Theorem (Coimage-image isomorphism).** In an abelian category the comparison map $\varphi : \mathrm{coim}\, f \to \mathrm{im}\, f$ is an isomorphism.

*Proof.* From $i \circ \varphi \circ p = f = i \circ e$ and $i$ mono, $\varphi \circ p = e$. The map $e$ is epi by the previous theorem. If $a \circ \varphi = b \circ \varphi$, then $a \circ e = b \circ e$, so $a = b$. So $\varphi$ is epi. From $i \circ \varphi \circ p = f = m \circ p$ and $p$ epi, $i \circ \varphi = m$. The map $m$ is mono, so $\varphi$ is mono in the same way. A morphism of an abelian category that is mono and epi is an isomorphism, by Volume 24, Chapter 8. $\square$

So each $f$ has a factorization $f = i \circ e$ with $e$ epi and $i$ mono, unique up to unique isomorphism. Mathlib shows that it is a strong epi-mono factorization, so `Abelian.imageIsoImage` identifies `Abelian.image f` with the general image `Limits.image f` of Volume 24.

**Theorem (Characterization by the comparison map).** Let $C$ be preadditive with finite products, kernels and cokernels. If the comparison map of each morphism is an isomorphism, then $C$ is abelian.

*Proof.* Let $f : X \to Y$ be mono. Then $\ker f = 0$, and the cokernel of the zero map $0 \to X$ is $1_X$. So $p$ is an isomorphism, and $f = i \circ \varphi \circ p$ with $\varphi \circ p$ an isomorphism. Hence $f$ is isomorphic over $Y$ to $i = \ker(\mathrm{coker}\, f)$, and $f$ is a kernel of $\mathrm{coker}\, f$. The proof for epimorphisms is dual. $\square$

**Theorem (Finite limits and the pullback of an epimorphism).** An abelian category has all finite limits and finite colimits. Let $f : X \to Z$ be an epimorphism and $g : Y \to Z$ any map. In the pullback square with $f p_1 = g p_2$, the map $p_2 : P \to Y$ is an epimorphism. Dually, a pushout of a monomorphism is a monomorphism.

*Proof.* The equalizer of $a, b : X \to Y$ is the kernel of $a - b$. With finite products, all finite limits exist, by Volume 24, Chapter 4. The dual argument gives finite colimits. For the pullback, let $h = [f, -g] : X \oplus Y \to Z$. A pair $(u, v)$ with $f u = g v$ is the same as a map $\langle u, v \rangle$ with $h \circ \langle u, v \rangle = 0$. So the pullback is $k = \langle p_1, p_2 \rangle = \ker h$. Since $h \circ \iota_1 = f$ is epi, $h$ is epi. Every epimorphism is the cokernel of its kernel, so $h = \mathrm{coker}\, k$. Now let $u : Y \to W$ with $u \circ p_2 = 0$. Then $[0, u] \circ k = 0 \circ p_1 + u \circ p_2 = 0$. So $[0, u] = v \circ h$ for some $v : Z \to W$. Composition with $\iota_1$ gives $0 = v \circ f$, and $f$ is epi, so $v = 0$. Then $[0, u] = 0$ and $u = [0, u] \circ \iota_2 = 0$. $\square$

In a general category the pullback of a monomorphism is a monomorphism. The theorem is the less formal statement about epimorphisms, and it fails for example in the category of rings: the inclusion $\mathbb{Z} \to \mathbb{Q}$ is epi there.

**Theorem (Abelian without a given addition).** Let $C$ have a zero object, finite products and coproducts, kernels and cokernels, and let each monomorphism be a kernel and each epimorphism a cokernel. Then $C$ has a preadditive structure, and with it $C$ is abelian. By Chapter 1, Section 1, this structure is the only one.

*Outline of the proof.* The diagonal $\Delta : X \to X \times X$ is a monomorphism, so it is the kernel of its cokernel $\sigma' : X \times X \to Q$. A study of images shows that $r = \sigma' \circ \langle 1, 0 \rangle : X \to Q$ is an isomorphism, and $\sigma = r^{-1} \circ \sigma'$ is the *subtraction*. Then $f - g = \sigma \circ \langle f, g \rangle$ and $f + g = f - (0 - g)$. A number of identities, all derived from $\sigma \circ \Delta = 0$ and $\sigma \circ \langle 1, 0 \rangle = 1$, give the axioms of an abelian group and the bilinearity of composition. The full proof is the file `Abelian.NonPreadditive`, which follows Borceux. $\square$

**Theorem (Duality).** If $C$ is abelian, then $C^{\mathrm{op}}$ is abelian.

*Proof.* The opposite of a preadditive category is preadditive, with the same groups $\mathrm{Hom}_{C^{\mathrm{op}}}(Y, X) = \mathrm{Hom}_C(X, Y)$. Finite products of $C^{\mathrm{op}}$ are finite coproducts of $C$, which exist because the finite products of $C$ are biproducts. A kernel in $C^{\mathrm{op}}$ is a cokernel in $C$ and the reverse. A monomorphism of $C^{\mathrm{op}}$ is an epimorphism of $C$, which is a cokernel in $C$, so it is a kernel in $C^{\mathrm{op}}$. The fourth axiom is the same argument with the roles exchanged. $\square$

Duality halves the work in each later proof: a statement about kernels and monomorphisms gives, by the theorem, the dual statement about cokernels and epimorphisms.

### Examples

**Example (Modules).** In `ModuleCat R`, $\mathrm{coim}\, f = M / \ker f$ and $\mathrm{im}\, f = f(M)$, with the usual inclusion. The comparison map is the isomorphism $M / \ker f \cong f(M)$ of the first isomorphism theorem, Volume 7. So the coimage-image theorem is the first isomorphism theorem in an abelian category.

**Counterexample (Free abelian groups of finite rank).** Let $C$ be the category of free abelian groups of finite rank. It is preadditive with finite biproducts. It has kernels, since a subgroup of a free group of finite rank is free. It has cokernels: the cokernel of $f : A \to B$ is $B / \mathrm{im}\, f$ modulo its torsion. For $f = 2 : \mathbb{Z} \to \mathbb{Z}$, $\ker f = 0$ and $\mathrm{coker}\, f = 0$, so $\mathrm{coim}\, f = \mathbb{Z}$, $\mathrm{im}\, f = \mathbb{Z}$, and the comparison map is $2$, which is not an isomorphism. So $C$ is not abelian. The same $f$ is mono and epi but not an isomorphism.

**Example (The opposite of modules).** By duality, $(\mathrm{ModuleCat}\, R)^{\mathrm{op}}$ is abelian. There a kernel is a cokernel of modules, and an injective module of `ModuleCat R` becomes a projective object of the opposite category. Section 3 uses this.

### The library around it

::: mathlib

`CategoryTheory.Abelian` · `Mathlib.CategoryTheory.Abelian.Basic`

A class that extends `Preadditive`, `IsNormalMonoCategory` and `IsNormalEpiCategory`, with the fields `has_finite_products`, `has_kernels` and `has_cokernels`. The file proves `coimageIsoImage`, the instances `hasFiniteLimits` and `hasFiniteColimits`, the theorems `epi_pullback_of_epi_f` and `mono_pushout_of_mono_f`, and the converse `ofCoimageImageComparisonIsIso`, which the Stacks project uses as its definition.

<?decl CategoryTheory.Abelian?>
:::

::: mathlib

`CategoryTheory.NonPreadditiveAbelian` · `Mathlib.CategoryTheory.Abelian.NonPreadditive`

The class without the group structure. The subtraction is `NonPreadditiveAbelian.σ`, and `NonPreadditiveAbelian.preadditive` is the resulting preadditive structure. The instance `NonPreadditiveAbelian.abelian` in `Abelian.Basic` completes the circle.

<?decl CategoryTheory.NonPreadditiveAbelian?>
:::

The file `Abelian.Opposite` has the instance `Abelian Cᵒᵖ` and the isomorphisms that compare kernels and cokernels, such as `kernelOpOp` and `cokernelOpOp`.

Common errors of a learner:

- `Abelian.image f` and `Limits.image f` are different definitions. They are isomorphic by `Abelian.imageIsoImage`, but a lemma about one does not apply to the other by rewriting.
- In Mathlib a theorem with a limit in its statement has the limit as a class argument, for example `[HasPullback f g]`. In a proof, `Abelian.hasPullbacks` gives the instance.

### Exercises

1. (A) Show that $f$ is mono if and only if $\ker f = 0$, and epi if and only if $\mathrm{coker}\, f = 0$, in a preadditive category with kernels and cokernels.
2. (A) Compute the image and the coimage of the map $\mathbb{Z} \to \mathbb{Z}/6$, $n \mapsto 2n$, in `ModuleCat ℤ`, and check the comparison map.
3. (B) Let $f : X \to Y$ be in an abelian category. Prove that $\ker(\mathrm{coker}\, f) \to Y$ and $\mathrm{coim}\, f \to Y$ are isomorphic as objects over $Y$.
4. (B) Prove that in an abelian category a pushout of a monomorphism is a monomorphism, by duality from the theorem on pullbacks.
5. (B) In an abelian category, let $f : X \to Z$ be epi and $g : Y \to Z$. Show that the map $P \to X \oplus Y$ from the pullback is the kernel of $[f, -g]$, and that $X \oplus Y \to Z$ is its cokernel.
6. (C) Let $C$ be the category of torsion-free abelian groups. Decide which axioms of an abelian category hold in $C$, and find a morphism whose comparison map is not an isomorphism.

### Notes and history

The axioms of an abelian category are from Grothendieck's paper on homological algebra of 1957, after earlier work of Buchsbaum and of Mac Lane on exact categories and duality. The characterization by the comparison map is the form in the Stacks project. The construction of the addition from the other axioms follows the second volume of Borceux's *Handbook of Categorical Algebra*, which the Mathlib file cites.

The Mathlib files are by Markus Himmel, Johan Commelin and Kim Morrison (the basic file), Markus Himmel (the non-preadditive form), Markus Himmel and Kim Morrison (images), and Kim Morrison (the opposite category).

### Reference

<?reference?>
