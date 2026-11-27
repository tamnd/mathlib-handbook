---
title: The long exact homology sequence
kind: theory
modules:
  - Mathlib.Algebra.Homology.HomologySequence
  - Mathlib.Algebra.Homology.HomologySequenceLemmas
  - Mathlib.Algebra.Homology.HomologicalComplexLimits
explains:
  E3: [HomologicalComplex.opcyclesToCycles, HomologicalComplex.HomologySequence.composableArrows₃_exact, HomologicalComplex.HomologySequence.snakeInput, CategoryTheory.ShortComplex.ShortExact.δ, CategoryTheory.ShortComplex.ShortExact.homology_exact₂, HomologicalComplex.HomologySequence.δ_naturality, HomologicalComplex.HomologySequence.quasiIso_τ₃, HomologicalComplex.isLimitOfEval]
  E2: [HomologicalComplex.HomologySequence.composableArrows₃, HomologicalComplex.natTransOpCyclesToCycles, HomologicalComplex.opcyclesToCycles_naturality, HomologicalComplex.opcyclesToCycles_iCycles, HomologicalComplex.pOpcycles_opcyclesToCycles, HomologicalComplex.homologyι_opcyclesToCycles, HomologicalComplex.opcyclesToCycles_homologyπ, HomologicalComplex.cycles_left_exact, HomologicalComplex.opcycles_right_exact, CategoryTheory.ShortComplex.ShortExact.homology_exact₁, CategoryTheory.ShortComplex.ShortExact.homology_exact₃, CategoryTheory.ShortComplex.ShortExact.δ_eq, CategoryTheory.ShortComplex.ShortExact.δ_comp, CategoryTheory.ShortComplex.ShortExact.comp_δ, CategoryTheory.ShortComplex.ShortExact.mono_δ, CategoryTheory.ShortComplex.ShortExact.epi_δ, CategoryTheory.ShortComplex.ShortExact.isIso_δ, CategoryTheory.ShortComplex.ShortExact.δIso, HomologicalComplex.HomologySequence.mapSnakeInput, HomologicalComplex.HomologySequence.composableArrows₅, HomologicalComplex.HomologySequence.composableArrows₅_exact, HomologicalComplex.HomologySequence.mono_homologyMap_τ₃, HomologicalComplex.HomologySequence.epi_homologyMap_τ₃, HomologicalComplex.HomologySequence.isIso_homologyMap_τ₃, CategoryTheory.ShortComplex.ShortExact.exactAt_X₁, CategoryTheory.ShortComplex.ShortExact.acyclic_X₁, CategoryTheory.ShortComplex.ShortExact.acyclic_X₂, CategoryTheory.ShortComplex.ShortExact.acyclic_X₃, HomologicalComplex.coneOfHasLimitEval, HomologicalComplex.isLimitConeOfHasLimitEval, HomologicalComplex.coconeOfHasColimitEval, HomologicalComplex.isColimitCoconeOfHasColimitEval, HomologicalComplex.isColimitOfEval, HomologicalComplex.instHasLimitsOfShape, HomologicalComplex.instHasColimitsOfShape, HomologicalComplex.instHasFiniteLimits, HomologicalComplex.instHasFiniteColimits, HomologicalComplex.instPreservesLimitsOfShapeEvalOfHasLimitsOfShape, HomologicalComplex.preservesLimitsOfShape_of_eval, HomologicalComplex.instMonoFOfHasFiniteLimits, HomologicalComplex.instEpiFOfHasFiniteColimits, HomologicalComplex.instPreservesLimitsOfShapeSingle]
  E1: auto
families: []
requires: [V07, V24.C04, V24.C08, V25.C02, V26.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The long exact homology sequence

### Overview

A short exact sequence of complexes $0 \to K_1 \to K_2 \to K_3 \to 0$ does not give a short exact sequence of homology objects. The failure is measured by a *connecting morphism* $\delta : H_i(K_3) \to H_j(K_1)$, one for each pair of indices with $c.\mathrm{Rel}(i, j)$, and the homology objects with these morphisms form a long exact sequence. For a chain complex indexed by $\mathbb{N}$ it is
$$\cdots \to H_{n+1}(K_3) \xrightarrow{\delta} H_n(K_1) \to H_n(K_2) \to H_n(K_3) \xrightarrow{\delta} H_{n-1}(K_1) \to \cdots \to H_0(K_3) \to 0.$$
This sequence is the main computational tool of homological algebra. It computes the homology of one complex from the other two, it proves that the derived functors of Chapter 4 form $\delta$-functors, and it gives the two-out-of-three property of quasi-isomorphisms in short exact sequences.

The proof is an application of the snake lemma of Chapter 1, Section 3, to a diagram built from the cycles and opcycles of Section 2. The first step is a four-term exact sequence for one complex. The second step makes the snake input. The connecting morphism then has the usual description by elements: lift, apply the differential, and pull back.

The last part of the section shows that limits and colimits of complexes are computed degreewise. This gives kernels, cokernels and products in the category of complexes, and it is the reason why Section 2 could compute kernels degree by degree.

In this section $C$ is an abelian category unless the text says otherwise.

### Definitions

**Definition (The map from opcycles to cycles).** Let $K$ be a complex with homology at $i$ and at $j$. The differential $d_{ij}$ satisfies $d_{ij} \circ d_{\mathrm{prev}(i), i} = 0$ and $d_{j, \mathrm{next}(j)} \circ d_{ij} = 0$. So $d_{ij}$ factors through the cokernel $Z'_i(K)$ of $d_{\mathrm{prev}(i), i}$ and through the kernel $Z_j(K)$ of $d_{j, \mathrm{next}(j)}$. The result is a morphism
$$\bar d_{ij} : Z'_i(K) \to Z_j(K), \qquad \iota_j \circ \bar d_{ij} \circ p_i = d_{ij},$$
where $p_i : X_i \to Z'_i(K)$ and $\iota_j : Z_j(K) \to X_j$ are the canonical maps. It is natural in $K$.

**Definition (The snake input of a short exact sequence).** Let $S : 0 \to K_1 \xrightarrow{f} K_2 \xrightarrow{g} K_3 \to 0$ be a short exact sequence of complexes and $c.\mathrm{Rel}(i, j)$. The *snake input* of $S$ at $(i, j)$ is the diagram with four rows
$$\begin{array}{ccccc} H_i(K_1) & \to & H_i(K_2) & \to & H_i(K_3) \\ \downarrow && \downarrow && \downarrow \\ Z'_i(K_1) & \to & Z'_i(K_2) & \to & Z'_i(K_3) \\ \downarrow && \downarrow && \downarrow \\ Z_j(K_1) & \to & Z_j(K_2) & \to & Z_j(K_3) \\ \downarrow && \downarrow && \downarrow \\ H_j(K_1) & \to & H_j(K_2) & \to & H_j(K_3) \end{array}$$
where the middle vertical maps are $\bar d_{ij}$, the upper vertical maps are $\iota' : H_i \to Z'_i$ and the lower vertical maps are $\pi : Z_j \to H_j$.

**Definition (Connecting morphism).** The *connecting morphism* $\delta : H_i(K_3) \to H_j(K_1)$ of $S$ at $(i, j)$ is the connecting morphism of the snake lemma for this snake input.

### Theorems and proofs

**Lemma (Four-term sequence).** Let $C$ be a preadditive category with homology, $K$ a complex and $c.\mathrm{Rel}(i, j)$. The sequence
$$H_i(K) \xrightarrow{\iota'} Z'_i(K) \xrightarrow{\bar d_{ij}} Z_j(K) \xrightarrow{\pi} H_j(K)$$
is exact: $\iota'$ is a kernel of $\bar d_{ij}$ and $\pi$ is a cokernel of $\bar d_{ij}$.

*Proof.* Because $c.\mathrm{Rel}(i, j)$ holds, $c.\mathrm{next}(i) = j$ and $c.\mathrm{prev}(j) = i$ (Section 1). By the right homology of Chapter 1, $\iota' : H_i(K) \to Z'_i(K)$ is a kernel of the induced map $Z'_i(K) \to X_{\mathrm{next}(i)} = X_j$, which is $\iota_j \circ \bar d_{ij}$. Since $\iota_j$ is a monomorphism, a morphism $u$ into $Z'_i(K)$ satisfies $\iota_j \circ \bar d_{ij} \circ u = 0$ if and only if $\bar d_{ij} \circ u = 0$. So $\iota'$ is also a kernel of $\bar d_{ij}$. Dually, by the left homology, $\pi : Z_j(K) \to H_j(K)$ is a cokernel of the induced map $X_{\mathrm{prev}(j)} = X_i \to Z_j(K)$, which is $\bar d_{ij} \circ p_i$. Since $p_i$ is an epimorphism, $\pi$ is also a cokernel of $\bar d_{ij}$. $\square$

**Lemma (Exactness of cycles and opcycles).** Let $S$ be a short exact sequence of complexes. For each $i$ the sequences
$$0 \to Z_i(K_1) \to Z_i(K_2) \to Z_i(K_3), \qquad Z'_i(K_1) \to Z'_i(K_2) \to Z'_i(K_3) \to 0$$
are exact.

*Proof.* Write the argument for modules; the abelian case is the same with refinements in place of elements (Volume 25, Chapter 2), and the second sequence is dual to the first. Put $n = \mathrm{next}(i)$. The map $Z_i(K_1) \to Z_i(K_2)$ is the restriction of the injective $f_i$, so it is injective. Let $y \in Z_i(K_2)$ with $g_i(y) = 0$. By exactness in degree $i$, $y = f_i(x)$ for some $x \in X_{1,i}$. Then $f_n(d x) = d f_i(x) = d y = 0$, and $f_n$ is injective, so $d x = 0$ and $x \in Z_i(K_1)$. $\square$

The map $Z_i(K_2) \to Z_i(K_3)$ is not surjective in general: this is the failure that $\delta$ measures.

**Theorem (Long exact homology sequence).** Let $S : 0 \to K_1 \to K_2 \to K_3 \to 0$ be a short exact sequence of complexes in $C$ and $c.\mathrm{Rel}(i, j)$. The sequence
$$H_i(K_1) \to H_i(K_2) \to H_i(K_3) \xrightarrow{\delta} H_j(K_1) \to H_j(K_2) \to H_j(K_3)$$
is exact. In particular, for each $i$ the sequence $H_i(K_1) \to H_i(K_2) \to H_i(K_3)$ is exact.

*Proof.* Check the hypotheses of the snake lemma for the snake input. The middle rows are exact by the lemma on cycles and opcycles, with $Z'_i(K_1) \to Z'_i(K_2) \to Z'_i(K_3) \to 0$ and $0 \to Z_j(K_1) \to Z_j(K_2) \to Z_j(K_3)$. The vertical sequences are exact by the four-term lemma, so the top row is the row of kernels of the maps $\bar d_{ij}$ and the bottom row is the row of cokernels. The squares commute because $\bar d_{ij}$, $\iota'$ and $\pi$ are natural in the complex. The snake lemma gives exactness of
$$\ker \bar d^{(1)} \to \ker \bar d^{(2)} \to \ker \bar d^{(3)} \xrightarrow{\delta} \operatorname{coker} \bar d^{(1)} \to \operatorname{coker} \bar d^{(2)} \to \operatorname{coker} \bar d^{(3)},$$
which is the sequence of the theorem. $\square$

For a chain complex indexed by $\mathbb{N}$ the pairs $(n+1, n)$ give a sequence for each $n$, and consecutive ones overlap in three terms. They join into one long exact sequence. At the end, $H_0(K_2) \to H_0(K_3) \to 0$ is exact: the cokernels $H_0 = Z'_0$ by Section 2, and the opcycles sequence is right exact.

**Proposition (The connecting morphism by elements).** Let $C$ be a category of modules. Let $z \in X_{3,i}$ with $d z = 0$. Choose $y \in X_{2,i}$ with $g_i(y) = z$. Then $d y \in X_{2,j}$ is $f_j(x)$ for a unique $x \in X_{1,j}$, the element $x$ is a cycle, and $\delta[z] = [x]$.

*Proof.* The element $y$ exists because $g_i$ is surjective. Then $g_j(d y) = d g_i(y) = d z = 0$, so $d y = f_j(x)$ for a unique $x$ by exactness in degree $j$. Put $k = \mathrm{next}(j)$. Then $f_k(d x) = d d y = 0$, and $f_k$ is injective, so $x$ is a cycle. The snake lemma of Chapter 1 computes $\delta$ in the same way: the class of $z$ in $\ker \bar d^{(3)} = H_i(K_3)$ lifts to the class of $y$ in $Z'_i(K_2)$, its image under $\bar d^{(2)}$ is $d y \in Z_j(K_2)$, which comes from $x \in Z_j(K_1)$, and $\delta[z]$ is the class of $x$ in $\operatorname{coker} \bar d^{(1)} = H_j(K_1)$. $\square$

The result does not depend on the choice of $y$: another lift is $y + f_i(w)$, which changes $x$ by $d w$, a boundary.

**Theorem (Naturality of the connecting morphism).** Let $\varphi : S \to S'$ be a morphism of short exact sequences of complexes, with components $\varphi_1, \varphi_2, \varphi_3$. Then $H_j(\varphi_1) \circ \delta = \delta' \circ H_i(\varphi_3)$.

*Proof.* The morphism $\varphi$ gives a morphism of snake inputs, since all the maps are natural. The connecting morphism of the snake lemma is natural in the snake input (Chapter 1, Section 3). For modules it follows from the proposition: if $y$ lifts $z$ and $d y = f_j(x)$, then $\varphi_{2,i}(y)$ lifts $\varphi_{3,i}(z)$ and $d \varphi_{2,i}(y) = f'_j(\varphi_{1,j}(x))$. $\square$

**Corollary (Two of three in short exact sequences).** Let $\varphi : S \to S'$ be a morphism of short exact sequences of complexes. If $\varphi_1$ and $\varphi_2$ are quasi-isomorphisms, so is $\varphi_3$. If $K_2$ is acyclic, then each $\delta$ with $c.\mathrm{Rel}(i, j)$ is an isomorphism $H_i(K_3) \cong H_j(K_1)$.

*Proof.* For the first part, take $i$ and the five-term part of the two long sequences
$$H_i(K_1) \to H_i(K_2) \to H_i(K_3) \xrightarrow{\delta} H_j(K_1) \to H_j(K_2)$$
with $c.\mathrm{Rel}(i, j)$, and the maps $H(\varphi)$ between them. The squares commute by functoriality and by naturality. The four outer maps are isomorphisms, so the middle map $H_i(\varphi_3)$ is an isomorphism by the five lemma of Volume 25. If no $j$ follows $i$, then $H_i = Z'_i$ for the three complexes, the sequence $H_i(K_1) \to H_i(K_2) \to H_i(K_3) \to 0$ is exact by the lemma on opcycles, and the five lemma with two zero objects at the end gives the result. For the second part, $\delta$ sits between $H_i(K_2) = 0$ and $H_j(K_2) = 0$ in an exact sequence. $\square$

**Theorem (Limits are degreewise).** Let $C$ be a category with zero morphisms, $J$ a small category and $F : J \to \mathrm{Ch}_c(C)$ a functor. Suppose that each functor $F_n : J \to C$, $a \mapsto F(a)_n$, has a limit $L_n$. Then the objects $L_n$ form a complex $L$, and $L$ is a limit of $F$. The evaluation functors preserve this limit. Dually for colimits.

*Proof.* Let $\lambda_{a,n} : L_n \to F(a)_n$ be the projections. For $c.\mathrm{Rel}(n, m)$ the maps $d^{F(a)}_{nm} \circ \lambda_{a,n}$ form a cone over $F_m$, because morphisms of complexes commute with differentials. So there is a unique $d_{nm} : L_n \to L_m$ with $\lambda_{a,m} \circ d_{nm} = d^{F(a)}_{nm} \circ \lambda_{a,n}$. Put $d_{nm} = 0$ if the relation fails. Then $\lambda_{a,k} \circ d_{mk} \circ d_{nm} = d \circ d \circ \lambda_{a,n} = 0$ for all $a$, so $d_{mk} \circ d_{nm} = 0$ by the uniqueness in the limit. The $\lambda_{a}$ are morphisms of complexes by construction. For a cone $(M, \mu)$ over $F$, the degreewise limit gives unique maps $M_n \to L_n$, and they commute with the differentials by the same uniqueness. $\square$

In particular, a category of complexes has all finite limits when $C$ has them, kernels are degreewise, and a monomorphism of complexes is a monomorphism in each degree.

### Examples

**Example (Reduction modulo $n$).** Let $m, n \ge 1$ and $K$ the complex $\mathbb{Z} \xrightarrow{m} \mathbb{Z}$ in degrees $1$ and $0$. Multiplication by $n$ is an injective morphism $K \to K$, and its cokernel is $\bar K : \mathbb{Z}/n \xrightarrow{m} \mathbb{Z}/n$. The short exact sequence $0 \to K \xrightarrow{n} K \to \bar K \to 0$ gives
$$0 \to H_1(\bar K) \xrightarrow{\delta} H_0(K) \xrightarrow{n} H_0(K) \to H_0(\bar K) \to 0,$$
because $H_1(K) = \ker m = 0$. With $H_0(K) = \mathbb{Z}/m$, this says $H_1(\bar K) \cong \ker(n : \mathbb{Z}/m \to \mathbb{Z}/m)$ and $H_0(\bar K) \cong \mathbb{Z}/m \otimes \mathbb{Z}/n$. Both are cyclic of order $\gcd(m, n)$. Take $m = 6$ and $n = 4$. Then $H_1(\bar K) = \{a \in \mathbb{Z}/4 : 6a = 0\} = \{0, 2\}$. For $z = 2$, the lift is $y = 2 \in \mathbb{Z}$, $d y = 12 = 4 \cdot 3$, so $x = 3$ and $\delta[2] = [3] \in \mathbb{Z}/6$. The kernel of multiplication by $4$ on $\mathbb{Z}/6$ is $\{0, 3\}$, as exactness at $H_0(K)$ requires.

**Example (A shift by the connecting morphism).** Let $K_1 = \mathbb{Z}[0]$, $K_3 = \mathbb{Z}[1]$ and $K_2$ the complex $\mathbb{Z} \xrightarrow{1} \mathbb{Z}$ in degrees $1$ and $0$. The morphism $K_1 \to K_2$ is the identity in degree $0$ and zero in degree $1$, and the morphism $K_2 \to K_3$ is the identity in degree $1$ and zero in degree $0$. Both commute with the differentials, and the sequence is short exact in each degree, so it is short exact by Section 2. The complex $K_2$ is acyclic, so $\delta : H_1(K_3) = \mathbb{Z} \to H_0(K_1) = \mathbb{Z}$ is an isomorphism. By the proposition, $z = 1$ lifts to $y = 1$, $d y = 1$, and $\delta = 1$.

**Counterexample (Homology is not exact).** In the previous example the sequence $0 \to H_0(K_1) \to H_0(K_2) \to H_0(K_3) \to 0$ is $0 \to \mathbb{Z} \to 0 \to 0 \to 0$, which is not exact at $H_0(K_1)$. In degree $1$ the sequence $0 \to H_1(K_2) \to H_1(K_3) \to 0$ is $0 \to 0 \to \mathbb{Z} \to 0$, which is not exact at $H_1(K_3)$. So the homology functor does not preserve monomorphisms or epimorphisms: it is neither left exact nor right exact. Only the long sequence with $\delta$ is exact. The theorem also needs exactness of $S$ at $K_2$. In $0 \to \mathbb{Z}[0] \xrightarrow{2} \mathbb{Z}[0] \to 0 \to 0$ the first map is a monomorphism and the second an epimorphism, but the sequence is not exact at the middle, and $H_0(K_1) \to H_0(K_2) \to H_0(K_3)$ is $\mathbb{Z} \xrightarrow{2} \mathbb{Z} \to 0$, which is not exact.

### The library around it

::: mathlib
`HomologicalComplex.opcyclesToCycles` · `Mathlib.Algebra.Homology.HomologySequence`

`K.opcyclesToCycles i j : K.opcycles i ⟶ K.cycles j` is $\bar d_{ij}$, with the equations `pOpcycles_opcyclesToCycles` and `opcyclesToCycles_iCycles`. `opcyclesToCycles_naturality` and the natural transformation `natTransOpCyclesToCycles` give the naturality.

<?decl HomologicalComplex.opcyclesToCycles?>
:::

::: mathlib
`HomologicalComplex.HomologySequence.composableArrows₃_exact` · `Mathlib.Algebra.Homology.HomologySequence`

The four-term lemma, as exactness of `composableArrows₃ K i j : ComposableArrows C 3`, under `c.Rel i j` and `CategoryWithHomology C`. The lemmas `homologyι_opcyclesToCycles` and `opcyclesToCycles_homologyπ` are the two vanishing composites.

<?decl HomologicalComplex.HomologySequence.composableArrows₃_exact?>
:::

::: mathlib
`HomologicalComplex.HomologySequence.snakeInput` · `Mathlib.Algebra.Homology.HomologySequence`

`snakeInput hS i j hij : ShortComplex.SnakeInput C` is the snake input of the definition. Its rows `L₁` and `L₂` are exact by `opcycles_right_exact` and `cycles_left_exact`, which take an exact `S` with `Epi S.g` or `Mono S.f`.

<?decl HomologicalComplex.HomologySequence.snakeInput?>
:::

::: mathlib
`CategoryTheory.ShortComplex.ShortExact.δ` · `Mathlib.Algebra.Homology.HomologySequence`

`hS.δ i j hij : S.X₃.homology i ⟶ S.X₁.homology j`. For chain complexes, `c.Rel (n + 1) n` holds, so `δ` lowers the degree by one; for cochain complexes it raises it. `δ_eq` is the proposition by elements, in the form with morphisms from an object `A` in place of elements. `comp_δ` and `δ_comp` are the vanishing composites, `mono_δ`, `epi_δ` and `isIso_δ` the cases with an acyclic middle term, and `δIso` the resulting isomorphism.

<?decl CategoryTheory.ShortComplex.ShortExact.δ?>
:::

::: mathlib
`CategoryTheory.ShortComplex.ShortExact.homology_exact₂` · `Mathlib.Algebra.Homology.HomologySequence`

Exactness of $H_i(K_1) \to H_i(K_2) \to H_i(K_3)$. `homology_exact₁` is exactness at $H_j(K_1)$ and `homology_exact₃` at $H_i(K_3)$. The library states the three pieces as separate short complexes, not as one infinite sequence.

<?decl CategoryTheory.ShortComplex.ShortExact.homology_exact₂?>
:::

::: mathlib
`HomologicalComplex.HomologySequence.δ_naturality` · `Mathlib.Algebra.Homology.HomologySequenceLemmas`

For `φ : S₁ ⟶ S₂` between short exact sequences, `hS₁.δ i j hij ≫ homologyMap φ.τ₁ j = homologyMap φ.τ₃ i ≫ hS₂.δ i j hij`. It comes from `mapSnakeInput`, the morphism of snake inputs. `composableArrows₅` and `composableArrows₅_exact` package the six-term sequence.

<?decl HomologicalComplex.HomologySequence.δ_naturality?>
:::

::: mathlib
`HomologicalComplex.HomologySequence.quasiIso_τ₃` · `Mathlib.Algebra.Homology.HomologySequenceLemmas`

The first part of the corollary: `QuasiIso φ.τ₁ → QuasiIso φ.τ₂ → QuasiIso φ.τ₃`. The degreewise forms are `mono_homologyMap_τ₃`, `epi_homologyMap_τ₃` and `isIso_homologyMap_τ₃`. In this edition only the version for `τ₃` is present; the versions for `τ₁` and `τ₂` are not. The related lemmas `ShortExact.acyclic_X₁`, `acyclic_X₂`, `acyclic_X₃` and `exactAt_X₁` derive acyclicity of one term from homology conditions on the maps.

<?decl HomologicalComplex.HomologySequence.quasiIso_τ₃?>
:::

::: mathlib
`HomologicalComplex.isLimitOfEval` · `Mathlib.Algebra.Homology.HomologicalComplexLimits`

A cone over a diagram of complexes is a limit if its image under each `eval C c i` is a limit. `coneOfHasLimitEval` and `isLimitConeOfHasLimitEval` are the construction of the theorem, with `coconeOfHasColimitEval`, `isColimitCoconeOfHasColimitEval` and `isColimitOfEval` the duals. The instances `instHasLimitsOfShape`, `instHasFiniteLimits` and `instPreservesLimitsOfShapeEvalOfHasLimitsOfShape` record the consequences, `preservesLimitsOfShape_of_eval` tests preservation degreewise, and `instMonoFOfHasFiniteLimits` says that `φ.f n` is a monomorphism when `φ` is one.

<?decl HomologicalComplex.isLimitOfEval?>
:::

Common errors of a learner:

- The indices of `δ` follow `c.Rel i j`, not the order of the degrees. For a `ChainComplex` the call is `hS.δ (n + 1) n rfl`, and the proof `rfl` works because `(ComplexShape.down ℕ).Rel (n + 1) n` is `n + 1 = n + 1`; with `hS.δ n (n + 1)` no proof exists.
- A short exact sequence of complexes is a `ShortComplex (HomologicalComplex C c)` with a proof of `ShortExact`. A family of short exact sequences of objects is not enough as data; use `shortExact_of_degreewise_shortExact` of Section 2 to make the proof.
- `homology_exact₂` needs `ShortExact`, not only `Exact`, although the statement is only about the middle.

### Exercises

1. (A) Let $0 \to K_1 \to K_2 \to K_3 \to 0$ be short exact with $K_1$ and $K_3$ acyclic. Show that $K_2$ is acyclic.
2. (A) In the example on reduction modulo $n$, compute $\delta$ for $m = 12$ and $n = 8$ on a generator of $H_1(\bar K)$.
3. (A) Show that $\delta$ is zero for a short exact sequence of complexes that splits as a sequence of complexes.
4. (B) Let $K$ be a complex of torsion-free abelian groups. Use the sequence $0 \to K \xrightarrow{p} K \to K/p \to 0$ to show that $H_n(K/p) = 0$ for all $n$ implies that multiplication by $p$ is bijective on all $H_n(K)$.
5. (B) Let $M$ be the chain complex indexed by $\mathbb{Z}$ with $X_n = \mathbb{Z}/4$ and all differentials equal to $2$. Find a short exact sequence $0 \to K_1 \to M \to K_3 \to 0$ in which $K_1$ and $K_3$ have $\mathbb{Z}/2$ in each degree and zero differentials, and compute $\delta$.
6. (B) Prove the second part of the lemma on cycles and opcycles for modules: $Z'_i(K_1) \to Z'_i(K_2) \to Z'_i(K_3) \to 0$ is exact.
7. (C) Let $0 \to K_1 \to K_2 \to K_3 \to 0$ be short exact and suppose $\varphi_1, \varphi_3$ are quasi-isomorphisms in a morphism of such sequences. Show that $\varphi_2$ is a quasi-isomorphism, a case that the library of this edition does not state.

### Notes and history

The long exact homology sequence appears in algebraic topology for the pair of a space and a subspace, and Eilenberg and Steenrod made it one of their axioms for homology. Its algebraic form, for any short exact sequence of complexes, is in Cartan and Eilenberg (1956). The construction through the snake lemma applied to opcycles and cycles is the standard modern form.

The Mathlib Author of `HomologySequence`, `HomologySequenceLemmas` and `HomologicalComplexLimits` is Joël Riou.

### Reference

<?reference?>
