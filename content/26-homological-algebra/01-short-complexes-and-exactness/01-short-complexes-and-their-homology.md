---
title: Short complexes and their homology
kind: theory
modules:
  - Mathlib.Algebra.Homology.ShortComplex.Basic
  - Mathlib.Algebra.Homology.ShortComplex.LeftHomology
  - Mathlib.Algebra.Homology.ShortComplex.RightHomology
  - Mathlib.Algebra.Homology.ShortComplex.Homology
explains:
  E3: [CategoryTheory.ShortComplex, CategoryTheory.ShortComplex.LeftHomologyData, CategoryTheory.ShortComplex.RightHomologyData, CategoryTheory.ShortComplex.HomologyData, CategoryTheory.ShortComplex.homology, CategoryTheory.ShortComplex.leftRightHomologyComparison', CategoryTheory.ShortComplex.homologyMap]
  E2: [CategoryTheory.ShortComplex.Hom, CategoryTheory.ShortComplex.homMk, CategoryTheory.ShortComplex.isoMk, CategoryTheory.ShortComplex.op, CategoryTheory.ShortComplex.LeftHomologyData.ofHasKernelOfHasCokernel, CategoryTheory.ShortComplex.RightHomologyData.ofHasCokernelOfHasKernel, CategoryTheory.ShortComplex.LeftHomologyMapData, CategoryTheory.ShortComplex.RightHomologyMapData, CategoryTheory.ShortComplex.HasHomology, CategoryTheory.ShortComplex.cycles, CategoryTheory.ShortComplex.opcycles, CategoryTheory.ShortComplex.iCycles, CategoryTheory.ShortComplex.pOpcycles, CategoryTheory.ShortComplex.homologyπ, CategoryTheory.ShortComplex.homologyι, CategoryTheory.ShortComplex.leftHomologyIso, CategoryTheory.ShortComplex.rightHomologyIso, CategoryTheory.ShortComplex.isIso_leftRightHomologyComparison, CategoryTheory.ShortComplex.hasHomology_of_isIsoLeftRightHomologyComparison, CategoryTheory.CategoryWithHomology, CategoryTheory.ShortComplex.homologyMap_comp, CategoryTheory.ShortComplex.homologyFunctor, CategoryTheory.ShortComplex.LeftHomologyData.op]
  E1: auto
families: []
requires: [V07, V24.C04, V24.C08, V25.C01, V25.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Short complexes and their homology

### Overview

A complex of abelian groups is a sequence of maps in which each composite of two consecutive maps is zero. Its homology at one place depends only on three objects and two maps: the map that comes in and the map that goes out. This section studies that local piece, the *short complex* $X_1 \xrightarrow{f} X_2 \xrightarrow{g} X_3$ with $g \circ f = 0$. For abelian groups the homology is $\ker g / \operatorname{im} f$. In a general category there are two ways to build it from kernels and cokernels. The *left* way takes the kernel $K$ of $g$ first and then the cokernel of the induced map $X_1 \to K$. The *right* way takes the cokernel $Q$ of $f$ first and then the kernel of the induced map $Q \to X_3$. The two results are related by a canonical morphism, and a *homology data* is a choice of both together with an isomorphism between them.

Mathlib builds all of homology on this local piece: the homology of a chain complex at degree $i$ is the homology of its short complex at $i$. The definitions ask only for zero morphisms, so they apply also to the opposite category.

In the text $g \circ f$ is the textbook composite, and Mathlib writes `f ≫ g`. The category $C$ has zero morphisms in the sense of Volume 24, Chapter 8. Kernels and cokernels are limits and colimits as in Volume 24, Chapter 4.

### Definitions

**Definition (Short complex).** A *short complex* $S$ in $C$ consists of three objects $X_1, X_2, X_3$ and two morphisms $f : X_1 \to X_2$ and $g : X_2 \to X_3$ with $g \circ f = 0$. A *morphism* $\varphi : S \to S'$ of short complexes is a triple $(\tau_1, \tau_2, \tau_3)$ of morphisms $\tau_k : X_k \to X'_k$ with $\tau_2 \circ f = f' \circ \tau_1$ and $\tau_3 \circ g = g' \circ \tau_2$. Composition is componentwise, and the short complexes form a category $\mathrm{ShortComplex}(C)$.

**Definition (Left homology data).** A *left homology data* $h$ for $S$ consists of objects $K$ and $H$ and morphisms $i : K \to X_2$ and $\pi : K \to H$ such that:

1. $g \circ i = 0$, and $i$ is a kernel of $g$;
2. let $f' : X_1 \to K$ be the unique morphism with $i \circ f' = f$; it exists because $g \circ f = 0$; then $\pi \circ f' = 0$, and $\pi$ is a cokernel of $f'$.

The object $H$ is the *left homology* of $S$ for this data, and $K$ is the object of *cycles*.

**Definition (Right homology data).** A *right homology data* $h$ for $S$ consists of objects $Q$ and $H$ and morphisms $p : X_2 \to Q$ and $\iota : H \to Q$ such that:

1. $p \circ f = 0$, and $p$ is a cokernel of $f$;
2. let $g' : Q \to X_3$ be the unique morphism with $g' \circ p = g$; then $g' \circ \iota = 0$, and $\iota$ is a kernel of $g'$.

The object $H$ is the *right homology* for this data, and $Q$ is the object of *opcycles*.

The two definitions are dual. A left homology data of $S$ is the same as a right homology data of the opposite short complex $S^{\mathrm{op}} : X_3 \xrightarrow{g^{\mathrm{op}}} X_2 \xrightarrow{f^{\mathrm{op}}} X_1$ in $C^{\mathrm{op}}$, because a kernel in $C$ is a cokernel in $C^{\mathrm{op}}$.

**Definition (Homology data).** A *homology data* for $S$ is a left homology data $h_L = (K, H_L, i, \pi)$, a right homology data $h_R = (Q, H_R, p, \iota)$ and an isomorphism $e : H_L \to H_R$ such that
$$\iota \circ e \circ \pi = p \circ i : K \to Q.$$
The short complex $S$ *has homology* if a homology data exists. Then the *homology* $H(S)$ is the left homology of a homology data that the axiom of choice picks once and for all.

**Definition (Category with homology).** A category $C$ with zero morphisms is a *category with homology* if each short complex in $C$ has homology. Section 2 proves that each abelian category is a category with homology.

In $\mathbb{Z}$-modules the left homology is $\ker g / \operatorname{im} f$ and the right homology is $\ker(X_2/\operatorname{im} f \to X_3)$. The second is the set of classes $x + \operatorname{im} f$ with $g(x) = 0$, which is again $\ker g / \operatorname{im} f$. The condition on $e$ says that the two descriptions are matched by the identity on representatives.

### Theorems and proofs

The first results say that the data exist when the kernels and cokernels exist, and that the objects they give do not depend on the choices up to a unique isomorphism.

**Proposition (Existence of left homology data).** If $g$ has a kernel $i : K \to X_2$ and the induced map $f' : X_1 \to K$ has a cokernel $\pi : K \to H$, then $(K, H, i, \pi)$ is a left homology data for $S$.

*Proof.* The two conditions of the definition are the hypotheses. The only point to check is $\pi \circ f' = 0$, which holds for each cokernel of $f'$. $\square$

The dual statement for right homology data holds with the dual proof.

**Theorem (Morphisms of left homology data).** Let $\varphi : S \to S'$ be a morphism of short complexes, $h = (K, H, i, \pi)$ a left homology data for $S$ and $h' = (K', H', i', \pi')$ a left homology data for $S'$. There are unique morphisms $\varphi_K : K \to K'$ and $\varphi_H : H \to H'$ with
$$i' \circ \varphi_K = \tau_2 \circ i, \qquad \pi' \circ \varphi_K = \varphi_H \circ \pi.$$

*Proof.* First $\varphi_K$. The composite $g' \circ \tau_2 \circ i$ is $\tau_3 \circ g \circ i = 0$, because $\varphi$ commutes with $g$ and $g \circ i = 0$. Since $i'$ is a kernel of $g'$, the morphism $\tau_2 \circ i$ factors as $i' \circ \varphi_K$ for a unique $\varphi_K$.

Next, compare the induced maps $f'_S : X_1 \to K$ and $f'_{S'} : X'_1 \to K'$. The two morphisms $\varphi_K \circ f'_S$ and $f'_{S'} \circ \tau_1$ from $X_1$ to $K'$ agree after $i'$:
$$i' \circ \varphi_K \circ f'_S = \tau_2 \circ i \circ f'_S = \tau_2 \circ f = f' \circ \tau_1 = i' \circ f'_{S'} \circ \tau_1.$$
A kernel is a monomorphism, so $\varphi_K \circ f'_S = f'_{S'} \circ \tau_1$. Then $\pi' \circ \varphi_K \circ f'_S = \pi' \circ f'_{S'} \circ \tau_1 = 0$. Since $\pi$ is a cokernel of $f'_S$, the morphism $\pi' \circ \varphi_K$ factors as $\varphi_H \circ \pi$ for a unique $\varphi_H$.

Uniqueness of $\varphi_K$ holds because $i'$ is a monomorphism. Uniqueness of $\varphi_H$ holds because $\pi$ is an epimorphism. $\square$

**Corollary (Independence of the choice).** Two left homology data $h_1$, $h_2$ of the same short complex $S$ have isomorphic left homology objects, by a unique isomorphism compatible with the maps $\pi$ and $i$. The same holds for right homology data.

*Proof.* Apply the theorem to $\varphi = 1_S$ in both directions. This gives $\alpha : H_1 \to H_2$ and $\beta : H_2 \to H_1$. The composite $\beta \circ \alpha$ satisfies the conditions of the theorem for $1_S$ from $h_1$ to $h_1$, and so does $1_{H_1}$. By uniqueness $\beta \circ \alpha = 1$. In the same way $\alpha \circ \beta = 1$. $\square$

The same uniqueness gives functoriality: the map on $H$ induced by $\psi \circ \varphi$ is the composite of the maps induced by $\varphi$ and by $\psi$, because the composite satisfies the conditions that characterize the map for $\psi \circ \varphi$. So, when every short complex has homology, $S \mapsto H(S)$ is a functor $\mathrm{ShortComplex}(C) \to C$.

**Theorem (Comparison of left and right homology).** Let $h_L = (K, H_L, i, \pi)$ be a left homology data and $h_R = (Q, H_R, p, \iota)$ a right homology data for $S$. There is a unique morphism $\gamma : H_L \to H_R$ with
$$\iota \circ \gamma \circ \pi = p \circ i.$$

*Proof.* Let $f' : X_1 \to K$ be the map induced by $f$. Then $p \circ i \circ f' = p \circ f = 0$. Since $\pi$ is a cokernel of $f'$, there is a unique $u : H_L \to Q$ with $u \circ \pi = p \circ i$. Let $g' : Q \to X_3$ be the map induced by $g$. Then
$$g' \circ u \circ \pi = g' \circ p \circ i = g \circ i = 0.$$
Since $\pi$ is an epimorphism, $g' \circ u = 0$. Since $\iota$ is a kernel of $g'$, there is a unique $\gamma : H_L \to H_R$ with $\iota \circ \gamma = u$. This $\gamma$ has the required property. If $\gamma_1$ also has it, then $\iota \circ \gamma_1 \circ \pi = \iota \circ \gamma \circ \pi$, and $\gamma_1 = \gamma$ because $\iota$ is a monomorphism and $\pi$ is an epimorphism. $\square$

**Theorem (Homology data and the comparison).** Let $h_L$ and $h_R$ be as above. Then $S$ has a homology data with left part $h_L$ and right part $h_R$ if and only if $\gamma$ is an isomorphism. In that case the isomorphism of the homology data is $\gamma$. If $S$ has homology, then the comparison map is an isomorphism for every pair $(h_L, h_R)$.

*Proof.* If $\gamma$ is an isomorphism, then $(h_L, h_R, \gamma)$ is a homology data by the definition. Conversely, let $(h_L, h_R, e)$ be a homology data. The isomorphism $e$ satisfies $\iota \circ e \circ \pi = p \circ i$, so $e = \gamma$ by the uniqueness in the comparison theorem. Thus $\gamma$ is an isomorphism.

For the last claim let $(h_L^0, h_R^0, e_0)$ be a homology data. The theorem on morphisms for $1_S$ gives $\varphi_K : K \to K^0$ and $\alpha : H_L \to H_L^0$ with $i^0 \circ \varphi_K = i$ and $\pi^0 \circ \varphi_K = \alpha \circ \pi$. Its dual gives $\psi_Q : Q^0 \to Q$ and $\beta : H_R^0 \to H_R$ with $\psi_Q \circ p^0 = p$ and $\iota \circ \beta = \psi_Q \circ \iota^0$. By the corollary, $\alpha$ and $\beta$ are isomorphisms. Then
$$\iota \circ \beta \circ e_0 \circ \alpha \circ \pi = \psi_Q \circ \iota^0 \circ e_0 \circ \pi^0 \circ \varphi_K = \psi_Q \circ p^0 \circ i^0 \circ \varphi_K = p \circ i.$$
So $\beta \circ e_0 \circ \alpha$ has the property that characterizes $\gamma$, and $\gamma$ is a composite of three isomorphisms. $\square$

Thus neither side is preferred, and homology exists when the two sides agree through $\gamma$. In an abelian category both are the image of $p \circ i : K \to Q$, as Section 2 shows, so the comparison is always an isomorphism there.

**Proposition (Duality).** If $h = (K, H, i, \pi)$ is a left homology data of $S$, then $(K^{\mathrm{op}}, H^{\mathrm{op}}, i^{\mathrm{op}}, \pi^{\mathrm{op}})$ is a right homology data of $S^{\mathrm{op}}$, and conversely. Thus $S$ has homology if and only if $S^{\mathrm{op}}$ has homology, and $H(S^{\mathrm{op}}) \cong H(S)^{\mathrm{op}}$.

*Proof.* A morphism is a kernel in $C$ if and only if its opposite is a cokernel in $C^{\mathrm{op}}$. The map $f' : X_1 \to K$ becomes the map $K^{\mathrm{op}} \to X_1^{\mathrm{op}}$ induced by $f^{\mathrm{op}}$, and the condition on $e$ is symmetric. $\square$

### Examples

**Example (A cyclic group of order 8).** Let $S$ be $\mathbb{Z}/8 \xrightarrow{4} \mathbb{Z}/8 \xrightarrow{4} \mathbb{Z}/8$, where $4$ means multiplication by $4$. The composite is multiplication by $16$, which is zero on $\mathbb{Z}/8$. The left way: the kernel of $g$ is $K = \{0, 2, 4, 6\} \cong \mathbb{Z}/4$, and the image of $f$ is $\{0, 4\}$. The induced map $f' : \mathbb{Z}/8 \to K$ has image $\{0, 4\}$, so $H_L = K/\{0,4\} \cong \mathbb{Z}/2$, generated by the class of $2$. The right way: the cokernel of $f$ is $Q = \mathbb{Z}/8 / \{0, 4\} \cong \mathbb{Z}/4$. The induced map $g' : Q \to \mathbb{Z}/8$ sends the class of $x$ to $4x$. Its kernel is the set of classes of even $x$, which is $\{0, 2\} \subset \mathbb{Z}/4$, so $H_R \cong \mathbb{Z}/2$. The comparison sends the class of $2$ in $H_L$ to the class of $2$ in $Q$, which generates $H_R$. So $\gamma$ is an isomorphism, as the theorem predicts.

**Example (Multiplication by 2 and zero).** Let $S$ be $\mathbb{Z} \xrightarrow{2} \mathbb{Z} \xrightarrow{0} 0$. Then $K = \mathbb{Z}$, $f' = 2$ and $H_L = \mathbb{Z}/2$. On the right, $Q = \mathbb{Z}/2$, $g' = 0$, and $H_R = Q = \mathbb{Z}/2$ with $\iota$ the identity. The comparison is the identity of $\mathbb{Z}/2$.

**Example (A polynomial ring).** Let $k$ be a field and $A = k[x]/(x^3)$, with basis $1, x, x^2$. Let $S$ be $A \xrightarrow{x^2} A \xrightarrow{x} A$, with multiplication maps. The composite is multiplication by $x^3 = 0$. The kernel of multiplication by $x$ is the span of $x^2$. The image of multiplication by $x^2$ is also the span of $x^2$. So $H(S) = 0$. If $g$ is replaced by multiplication by $x^2$, the kernel becomes the span of $x$ and $x^2$, while the image of $f$ stays the span of $x^2$. Then $H(S) \cong k$, spanned by the class of $x$.

**Counterexample (Homology is not a function of the objects).** The short complexes $\mathbb{Z} \xrightarrow{1} \mathbb{Z} \to 0$ and $\mathbb{Z} \xrightarrow{0} \mathbb{Z} \to 0$ have the same three objects. The first has homology $0$ and the second has homology $\mathbb{Z}$. Also, a morphism of short complexes can induce zero on homology without being zero: the morphism $(2, 2, 0)$ from $\mathbb{Z} \xrightarrow{2} \mathbb{Z} \to 0$ to itself induces multiplication by $2$ on $\mathbb{Z}/2$, which is zero.

### The library around it

::: mathlib
`CategoryTheory.ShortComplex` · `Mathlib.Algebra.Homology.ShortComplex.Basic`

The structure has the fields `X₁`, `X₂`, `X₃`, `f`, `g` and `zero : f ≫ g = 0`. The source says that the notion was first introduced in the Liquid Tensor Experiment. A morphism `φ : S₁ ⟶ S₂` is a `ShortComplex.Hom` with fields `τ₁`, `τ₂`, `τ₃` and the two squares `comm₁₂` and `comm₂₃`. `ShortComplex.homMk` and `ShortComplex.isoMk` build morphisms and isomorphisms from components, and `ShortComplex.op` is the opposite complex.

<?decl CategoryTheory.ShortComplex?>
:::

::: mathlib
`CategoryTheory.ShortComplex.LeftHomologyData` · `Mathlib.Algebra.Homology.ShortComplex.LeftHomology`

The fields are `K`, `H`, `i`, `π` and the proofs `wi : i ≫ S.g = 0`, `hi : IsLimit (KernelFork.ofι i wi)`, `wπ` and `hπ`, where `hπ` says that `π` is a cokernel of the induced map `f'`. A user rarely builds one by hand: `LeftHomologyData.ofHasKernelOfHasCokernel` uses the chosen kernel and cokernel. A `LeftHomologyMapData` packages the maps $\varphi_K$ and $\varphi_H$ of the theorem; it is a `Unique` type, which is the uniqueness part of the proof.

<?decl CategoryTheory.ShortComplex.LeftHomologyData?>
:::

::: mathlib
`CategoryTheory.ShortComplex.RightHomologyData` · `Mathlib.Algebra.Homology.ShortComplex.RightHomology`

The fields are `Q`, `H`, `p`, `ι` with `wp`, `hp`, `wι` and `hι`, and `g'` is the induced map from `Q`. `LeftHomologyData.op` turns a left homology data of `S` into a right homology data of `S.op`.

<?decl CategoryTheory.ShortComplex.RightHomologyData?>
:::

::: mathlib
`CategoryTheory.ShortComplex.HomologyData` · `Mathlib.Algebra.Homology.ShortComplex.Homology`

A homology data has the fields `left`, `right`, `iso : left.H ≅ right.H` and `comm : left.π ≫ iso.hom ≫ right.ι = left.i ≫ right.p`, which is the condition $\iota \circ e \circ \pi = p \circ i$. The class `HasHomology S` asserts that one exists. The class `CategoryWithHomology C` asserts that every short complex has homology. The source says that the idea to use this notion for the definition of homology is due to A. Topaz.

<?decl CategoryTheory.ShortComplex.HomologyData?>
:::

::: mathlib
`CategoryTheory.ShortComplex.homology` · `Mathlib.Algebra.Homology.ShortComplex.Homology`

Under `[S.HasHomology]`, `S.homology` is the left homology `S.homologyData.left.H` of the chosen data. The isomorphisms `S.leftHomologyIso` and `S.rightHomologyIso` identify it with the left and right homology. The maps `S.homologyπ : S.cycles ⟶ S.homology` and `S.homologyι : S.homology ⟶ S.opcycles` come from the two sides, and `S.iCycles : S.cycles ⟶ S.X₂` and `S.pOpcycles : S.X₂ ⟶ S.opcycles` are the kernel and the cokernel.

<?decl CategoryTheory.ShortComplex.homology?>
:::

::: mathlib
`CategoryTheory.ShortComplex.leftRightHomologyComparison'` · `Mathlib.Algebra.Homology.ShortComplex.Homology`

For a left homology data `h₁` and a right homology data `h₂`, this is the morphism $\gamma$ of the comparison theorem. The instance `isIso_leftRightHomologyComparison` says that it is an isomorphism under `HasHomology`, and `hasHomology_of_isIsoLeftRightHomologyComparison` is the converse.

<?decl CategoryTheory.ShortComplex.leftRightHomologyComparison'?>
:::

::: mathlib
`CategoryTheory.ShortComplex.homologyMap` · `Mathlib.Algebra.Homology.ShortComplex.Homology`

For `φ : S₁ ⟶ S₂`, `homologyMap φ : S₁.homology ⟶ S₂.homology` is the map of the theorem on morphisms. The lemmas `homologyMap_comp` and `homologyMap_id` give functoriality, and `ShortComplex.homologyFunctor C` is the functor under `CategoryWithHomology C`. A `HomologyMapData` computes it with other data than the chosen one.

<?decl CategoryTheory.ShortComplex.homologyMap?>
:::

Common errors of a learner:

- `f ≫ g = 0` is $g \circ f = 0$. The arrow `≫` composes from left to right.
- `S.homology` needs `[S.HasHomology]`. In an abelian category the instance comes from `CategoryWithHomology`, which Section 2 provides.
- The map `f'` of a left homology data goes to `K`, not to `X₂`. The cokernel condition is on `f'`, and a cokernel of `f` itself gives the opcycles instead.
- The object `S.cycles` is a kernel of `g` up to isomorphism. Lemmas are stated for `iCycles` and `liftCycles`, not for a particular construction of the kernel.

### Exercises

1. (A) Compute the left and the right homology of $\mathbb{Z}/12 \xrightarrow{6} \mathbb{Z}/12 \xrightarrow{2} \mathbb{Z}/12$, and the comparison map between them.
2. (A) Show that $\mathbb{Z}/9 \xrightarrow{3} \mathbb{Z}/9 \xrightarrow{3} \mathbb{Z}/9$ has homology $0$, and that $\mathbb{Z}/9 \xrightarrow{0} \mathbb{Z}/9 \xrightarrow{3} \mathbb{Z}/9$ has homology $\mathbb{Z}/3$.
3. (A) Show that a morphism of short complexes is an isomorphism if and only if its components are isomorphisms.
4. (B) Let $f = 0$. Show that $(\ker g, \ker g, i, 1)$ is a left homology data, and describe a right homology data. *Hint:* the cokernel of a zero map $X_1 \to X_2$ is the identity of $X_2$.
5. (B) Let $k$ be a field and $V$ a finite dimensional $k$-vector space with an endomorphism $T$ such that $T^2 = 0$. Show that the homology of $V \xrightarrow{T} V \xrightarrow{T} V$ has dimension $\dim V - 2 \operatorname{rank} T$.
6. (C) Let $C$ be the category of free abelian groups of finite rank. Show that the short complex $\mathbb{Z} \xrightarrow{2} \mathbb{Z} \to 0$ has a left homology data in $C$ with $H = 0$, and that the comparison theorem still holds. Explain why the answer differs from the homology $\mathbb{Z}/2$ in all abelian groups. *Hint:* a map from $\mathbb{Z}$ to a torsion free group that kills $2$ is zero.

### Notes and history

The homology of complexes of modules, as cycles modulo boundaries, is treated in Cartan and Eilenberg, *Homological Algebra* (1956). Grothendieck, in the Tohoku paper of 1957, set homological algebra in abelian categories. The symmetric presentation through left and right homology data is the form that Mathlib uses. The source says that the short complexes were first introduced in the Liquid Tensor Experiment, and that the homology data arose at its end.

The Mathlib Author of `ShortComplex.Basic`, `ShortComplex.LeftHomology`, `ShortComplex.RightHomology` and `ShortComplex.Homology` is Joël Riou.

### Reference

<?reference?>
