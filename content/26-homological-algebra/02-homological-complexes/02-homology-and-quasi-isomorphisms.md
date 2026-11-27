---
title: Homology and quasi-isomorphisms
kind: theory
modules:
  - Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
  - Mathlib.Algebra.Homology.QuasiIso
  - Mathlib.Algebra.Homology.SingleHomology
  - Mathlib.Algebra.Homology.HomologicalComplexAbelian
explains:
  E3: [HomologicalComplex.sc, HomologicalComplex.homology, HomologicalComplex.cycles, HomologicalComplex.homologyMap, HomologicalComplex.ExactAt, QuasiIsoAt, QuasiIso, HomologicalComplex.singleObjHomologySelfIso, HomologicalComplex.exact_iff_degreewise_exact]
  E2: [HomologicalComplex.shortComplexFunctor, HomologicalComplex.sc', HomologicalComplex.isoSc', HomologicalComplex.HasHomology, HomologicalComplex.opcycles, HomologicalComplex.iCycles, HomologicalComplex.pOpcycles, HomologicalComplex.toCycles, HomologicalComplex.liftCycles, HomologicalComplex.homologyπ, HomologicalComplex.homologyι, HomologicalComplex.homologyIsCokernel, HomologicalComplex.homologyIsoSc', HomologicalComplex.cyclesMap, HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_add, HomologicalComplex.homologyFunctor, HomologicalComplex.gradedHomologyFunctor, HomologicalComplex.exactAt_iff, HomologicalComplex.exactAt_iff_isZero_homology, HomologicalComplex.Acyclic, HomologicalComplex.acyclic_iff, ChainComplex.isoHomologyι₀, CochainComplex.isoHomologyπ₀, quasiIsoAt_iff, quasiIsoAt_iff_isIso_homologyMap, quasiIsoAt_iff_exactAt, quasiIso_comp, quasiIso_of_comp_left, quasiIso_of_comp_right, quasiIso_of_isIso, HomologicalComplex.quasiIso, HomologicalComplex.instHasTwoOutOfThreePropertyQuasiIso, ChainComplex.quasiIsoAt₀_iff, HomologicalComplex.exactAt_single_obj, HomologicalComplex.singleObjCyclesSelfIso, HomologicalComplex.homologyFunctorSingleIso, ChainComplex.exactAt_succ_single_obj, HomologicalComplex.instAbelian, HomologicalComplex.shortExact_iff_degreewise_shortExact, HomologicalComplex.shortExact_of_degreewise_shortExact]
  E1: auto
families: []
requires: [V07, V24.C08, V25.C02, V26.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Homology and quasi-isomorphisms

### Overview

The homology of a complex at an index $i$ measures the failure of exactness at $i$: it is the group of cycles modulo the group of boundaries. Chapter 1 did all the work for one place. A complex $K$ gives at each $i$ the short complex $X_{\mathrm{prev}(i)} \to X_i \to X_{\mathrm{next}(i)}$, and the homology $H_i(K)$ is the homology of that short complex. All properties of homology at one index, such as functoriality, the comparison of left and right homology and the description in an abelian category, come from Chapter 1 without new proofs.

This section defines the homology of a complex, exactness at an index and acyclic complexes, and computes the homology of single complexes and of small complexes over $\mathbb{Z}$ and over polynomial rings. It then defines *quasi-isomorphisms*, the morphisms that induce isomorphisms on all homology objects. They are the morphisms that the derived category of Chapter 5 inverts. Last, it states that the complexes in an abelian category form an abelian category, in which exactness is tested degree by degree. Section 3 uses this for the long exact sequence.

The section uses Section 1 for complexes and Chapter 1 for short complexes. The category $C$ has zero morphisms, and from the theorems on abelian categories on it is abelian.

### Definitions

**Definition (Short complex at an index).** Let $K$ be a complex of shape $c$ and $i$ an index. The *short complex of $K$ at $i$* is
$$K.\mathrm{sc}(i) : X_{c.\mathrm{prev}(i)} \xrightarrow{d_{\mathrm{prev}(i), i}} X_i \xrightarrow{d_{i, \mathrm{next}(i)}} X_{c.\mathrm{next}(i)}.$$
It is a short complex because all composites of differentials vanish (Section 1). A morphism $\varphi : K \to L$ gives the morphism $(\varphi_{\mathrm{prev}(i)}, \varphi_i, \varphi_{\mathrm{next}(i)})$ of short complexes, so $K \mapsto K.\mathrm{sc}(i)$ is a functor.

**Definition (Homology of a complex).** The complex $K$ *has homology at $i$* if $K.\mathrm{sc}(i)$ has homology. Then
$$H_i(K) = H(K.\mathrm{sc}(i)), \qquad Z_i(K) = \text{cycles of } K.\mathrm{sc}(i), \qquad Z'_i(K) = \text{opcycles of } K.\mathrm{sc}(i).$$
So $Z_i(K)$ is a kernel of $d_{i, \mathrm{next}(i)}$ and $Z'_i(K)$ is a cokernel of $d_{\mathrm{prev}(i), i}$. In an abelian category the *boundaries* $B_i(K)$ are the image of the map $X_{\mathrm{prev}(i)} \to Z_i(K)$ induced by the differential, and $H_i(K) = Z_i(K)/B_i(K)$ by the definition of left homology data. For a cochain complex the same objects are written $H^i$, $Z^i$, $B^i$.

**Definition (Exactness at an index, acyclic).** The complex $K$ is *exact at $i$* if $K.\mathrm{sc}(i)$ is exact, and *acyclic* if it is exact at every $i$. When $K$ has homology at $i$, exactness at $i$ is equivalent to $H_i(K) = 0$.

**Definition (Quasi-isomorphism).** Let $\varphi : K \to L$ be a morphism of complexes with homology at $i$. It is a *quasi-isomorphism at $i$* if $H_i(\varphi) : H_i(K) \to H_i(L)$ is an isomorphism. It is a *quasi-isomorphism* if it is one at every $i$.

### Theorems and proofs

**Proposition (Functoriality and additivity).** Let $C$ be a category with homology. Then $K \mapsto H_i(K)$ is a functor from complexes of shape $c$ to $C$. If $C$ is preadditive, then $H_i(\varphi + \psi) = H_i(\varphi) + H_i(\psi)$.

*Proof.* The homology functor is the composite of $K \mapsto K.\mathrm{sc}(i)$ and the homology functor of short complexes of Chapter 1, Section 1. For additivity, let $h$ be a homology data with left part $(K_0, H, \iota, \pi)$ and a second data $h'$ for the target. The maps of cycles satisfy $\iota' \circ (\varphi + \psi)_K = (\varphi_i + \psi_i) \circ \iota = \iota' \circ (\varphi_K + \psi_K)$, so $(\varphi + \psi)_K = \varphi_K + \psi_K$ because $\iota'$ is a monomorphism. Then $\pi' \circ (\varphi_K + \psi_K) = (\varphi_H + \psi_H) \circ \pi$, and the uniqueness of the induced map gives $(\varphi + \psi)_H = \varphi_H + \psi_H$. $\square$

**Proposition (Homology at the ends).** Let $K$ be a chain complex indexed by $\mathbb{N}$. Then $H_0(K)$ is a cokernel of $d_{10} : X_1 \to X_0$. Let $L$ be a cochain complex indexed by $\mathbb{N}$. Then $H^0(L)$ is a kernel of $d^{01} : X^0 \to X^1$.

*Proof.* For the shape $\mathrm{down}(\mathbb{N})$ no $j$ satisfies $j + 1 = 0$, so nothing follows $0$, and $c.\mathrm{next}(0) = 0$. The differential $d_{00}$ is zero by axiom 1 of complexes. So $K.\mathrm{sc}(0)$ is $X_1 \xrightarrow{d_{10}} X_0 \xrightarrow{0} X_0$. For a short complex with $g = 0$, a right homology data is $(Q, Q, p, 1)$ where $p$ is a cokernel of $f$: the induced map $g' : Q \to X_0$ is zero, and the identity of $Q$ is a kernel of a zero map. So $H_0(K)$ is the cokernel of $d_{10}$. The cochain case is dual. $\square$

**Theorem (Homology of a single complex).** Let $C$ have a zero object, $A$ an object and $j$ an index. Then $H_j(A[j]) \cong A$, and $A[j]$ is exact at every $i \ne j$.

*Proof.* At $j$, the short complex is $X_{\mathrm{prev}(j)} \xrightarrow{0} A \xrightarrow{0} X_{\mathrm{next}(j)}$, since all differentials of $A[j]$ are zero. The kernel of the zero map $A \to X_{\mathrm{next}(j)}$ is the identity of $A$, and the induced map $X_{\mathrm{prev}(j)} \to A$ is zero, with the identity as a cokernel. So $(A, A, 1, 1)$ is a left homology data, and dually $(A, A, 1, 1)$ is a right homology data. The comparison map is the identity, and $H_j(A[j]) \cong A$. At $i \ne j$, the middle object is $0$. A short complex with a zero middle object has the left homology data $(0, 0, 0, 0)$, so its homology is $0$. $\square$

This holds whether or not $j$ has a predecessor or a successor: the formula of the definition never needs a case distinction.

**Theorem (Quasi-isomorphisms).** Let $C$ be a category with homology.

1. Each isomorphism of complexes is a quasi-isomorphism.
2. If $\varphi$ and $\psi$ are quasi-isomorphisms, so is $\psi \circ \varphi$.
3. If two of $\varphi$, $\psi$, $\psi \circ \varphi$ are quasi-isomorphisms, so is the third.
4. Let $K, L$ be acyclic. Every morphism $K \to L$ is a quasi-isomorphism.

*Proof.* A functor sends isomorphisms to isomorphisms, which gives 1. By functoriality $H_i(\psi \circ \varphi) = H_i(\psi) \circ H_i(\varphi)$. In any category, if two of $a$, $b$, $b \circ a$ are isomorphisms, so is the third: if $a$ and $b \circ a$ are, then $b = (b \circ a) \circ a^{-1}$; if $b$ and $b \circ a$ are, then $a = b^{-1} \circ (b \circ a)$. This gives 2 and 3. For 4, all $H_i(K)$ and $H_i(L)$ are zero, and each morphism between zero objects is an isomorphism. $\square$

The class of quasi-isomorphisms has the two-out-of-three property. It contains the isomorphisms but much more. Chapter 3 shows that each homotopy equivalence is a quasi-isomorphism, and Chapter 5 inverts all quasi-isomorphisms.

**Theorem (Complexes in an abelian category).** Let $C$ be abelian. The category of complexes of shape $c$ in $C$ is abelian, and the kernels and cokernels are computed degreewise. A short complex $K_1 \to K_2 \to K_3$ of complexes is exact if and only if each short complex $X_{1,i} \to X_{2,i} \to X_{3,i}$ of objects is exact. The same holds for short exactness.

*Proof.* Section 1 gives the preadditive structure. Finite products are degreewise, with the induced differentials. For $\varphi : K \to L$, the kernels $\ker \varphi_i$ form a complex: the differential $d_{ij}$ of $K$ restricts to $\ker \varphi_i \to \ker \varphi_j$, because $\varphi_j \circ d_{ij} = d_{ij} \circ \varphi_i$ vanishes on $\ker \varphi_i$. This complex is a kernel of $\varphi$: a morphism $\theta : M \to K$ with $\varphi \circ \theta = 0$ factors uniquely in each degree, and the factorizations commute with the differentials because the inclusions are monomorphisms. Cokernels are dual. The canonical map from the coimage to the image is degreewise the canonical map of $\varphi_i$, which is an isomorphism in $C$ by Volume 25, Chapter 2. A morphism of complexes that is an isomorphism in each degree is an isomorphism, so the category is abelian.

For exactness use criterion 2 of Chapter 1, Section 2: $S$ is exact if and only if $p \circ i = 0$, with $i$ a kernel of $g$ and $p$ a cokernel of $f$. Kernels and cokernels are degreewise, so $p \circ i$ is degreewise the corresponding map for the short complex in degree $i$, and a morphism of complexes is zero if and only if each component is zero. For short exactness, a morphism of complexes is a monomorphism if and only if its kernel is zero, which by the first part means that each component has zero kernel. Epimorphisms are dual. $\square$

### Examples

**Example (An endomorphism as a complex).** Let $M$ be an $R$-module and $T : M \to M$ an endomorphism. The chain complex $K_T$ with $X_1 = X_0 = M$, $d_{10} = T$ and all other objects $0$ has
$$H_1(K_T) = \ker T, \qquad H_0(K_T) = \operatorname{coker} T,$$
by the proposition on the ends for $H_0$, and because $X_2 = 0$ for $H_1$. Some values:

- $M = \mathbb{Z}$, $T = n$ with $n \ne 0$: $H_1 = 0$ and $H_0 = \mathbb{Z}/n$.
- $M = \mathbb{Z}/12$, $T = 4$: $H_1 = \{0, 3, 6, 9\} \cong \mathbb{Z}/4$ and $H_0 = (\mathbb{Z}/12)/\{0, 4, 8\} \cong \mathbb{Z}/4$.
- $M = \mathbb{Z}[x]$, $T$ multiplication by $x$: $H_1 = 0$ and $H_0 = \mathbb{Z}[x]/(x) \cong \mathbb{Z}$, the evaluation at $0$.
- $M = \mathbb{Q}[x]$, $T = D$ the derivative: $H_1 = \mathbb{Q}$, the constants, and $H_0 = 0$. Over $\mathbb{Z}$, $H_0 = \bigoplus_{n \ge 1} \mathbb{Z}/(n+1)$ by Section 1.

**Example (A periodic complex).** Let $T$ be an endomorphism of $M$ with $T^2 = 0$. The chain complex indexed by $\mathbb{Z}$ with $X_n = M$ and every differential equal to $T$ has $H_n = \ker T / \operatorname{im} T$ for every $n$. For $M = \mathbb{Z}/4$ and $T = 2$, $\ker T = \operatorname{im} T = \{0, 2\}$, so the complex is acyclic. For $M = \mathbb{Z}/8$ and $T = 4$, $\ker T = \{0, 2, 4, 6\}$ and $\operatorname{im} T = \{0, 4\}$, so $H_n \cong \mathbb{Z}/2$ for every $n$. For $M = k[x]/(x^2)$ and $T = x$, the kernel and the image are both $(x)$, and the complex is acyclic.

**Example (A resolution is a quasi-isomorphism).** Let $n \ge 1$ and $K$ the complex $\mathbb{Z} \xrightarrow{n} \mathbb{Z}$ in degrees $1$ and $0$. By Section 1, the reduction $\varepsilon : \mathbb{Z} \to \mathbb{Z}/n$ defines $\varphi : K \to (\mathbb{Z}/n)[0]$. In degree $0$, $H_0(K) = \mathbb{Z}/n$ and $H_0(\varphi)$ is the map $\mathbb{Z}/n \to \mathbb{Z}/n$ induced by $\varepsilon$, the identity. In degree $1$, $H_1(K) = \ker n = 0$, and $H_1$ of the single complex is $0$. In degrees $\ge 2$ both are $0$. So $\varphi$ is a quasi-isomorphism.

**Counterexample (Quasi-isomorphisms have no inverse).** In the previous example there is no quasi-isomorphism $(\mathbb{Z}/n)[0] \to K$ for $n \ge 2$. A morphism $(\mathbb{Z}/n)[0] \to K$ is a map $\eta : \mathbb{Z}/n \to \mathbb{Z}$ in degree $0$, and each such map is zero because $\mathbb{Z}$ has no torsion. So it induces zero on $H_0$, which is not an isomorphism of $\mathbb{Z}/n$. Also, the morphism $0 \to L$ to the acyclic complex $L : \mathbb{Z} \xrightarrow{1} \mathbb{Z}$ is a quasi-isomorphism and not an isomorphism.

### The library around it

::: mathlib
`HomologicalComplex.sc` · `Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex`

`K.sc i` is `(shortComplexFunctor C c i).obj K`, with objects `K.X (c.prev i)`, `K.X i` and `K.X (c.next i)`. The variant `K.sc' i j k` uses arbitrary indices, and `K.isoSc' i j k` identifies it with `K.sc j` when `c.prev j = i` and `c.next j = k`. Use `sc'` when the indices are given by a formula such as `n + 1`, so that `c.prev` need not be computed.

<?decl HomologicalComplex.sc?>
:::

::: mathlib
`HomologicalComplex.homology` · `Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex`

`K.homology i` is `(K.sc i).homology` under `[K.HasHomology i]`, which holds in a `CategoryWithHomology`. The maps are `K.homologyπ i : K.cycles i ⟶ K.homology i` and `K.homologyι i : K.homology i ⟶ K.opcycles i`. `homologyIsCokernel` says that `homologyπ j` is a cokernel of `K.toCycles i j : K.X i ⟶ K.cycles j`, which is $H = Z/B$. The index of this edition has no declaration for the boundaries as a subobject; they enter only as the image of `toCycles`. `ChainComplex.isoHomologyι₀` and `CochainComplex.isoHomologyπ₀` are the proposition on the ends.

<?decl HomologicalComplex.homology?>
:::

::: mathlib
`HomologicalComplex.cycles` · `Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex`

`K.cycles i` is `(K.sc i).cycles`, with `K.iCycles i : K.cycles i ⟶ K.X i` and `K.liftCycles` to map into it. `K.opcycles i` and `K.pOpcycles i` are the dual objects. A proof about cycles uses `iCycles` and the lemma that it is a monomorphism, never a construction of the kernel.

<?decl HomologicalComplex.cycles?>
:::

::: mathlib
`HomologicalComplex.homologyMap` · `Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex`

`homologyMap φ i` is the map on `homology i`, with `homologyMap_comp` and `homologyMap_add`. `homologyFunctor C c i` is the functor, and `gradedHomologyFunctor` collects all degrees into a graded object. `cyclesMap φ i` is the map on cycles.

<?decl HomologicalComplex.homologyMap?>
:::

::: mathlib
`HomologicalComplex.ExactAt` · `Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex`

`K.ExactAt i` is `(K.sc i).Exact`. `exactAt_iff_isZero_homology` is the form with homology, and `exactAt_iff` uses `sc'`. `K.Acyclic` is `∀ i, K.ExactAt i`.

<?decl HomologicalComplex.ExactAt?>
:::

::: mathlib
`QuasiIsoAt` · `Mathlib.Algebra.Homology.QuasiIso`

The class `QuasiIsoAt f i` asks that `(shortComplexFunctor C c i).map f` is a quasi-isomorphism of short complexes, `CategoryTheory.ShortComplex.QuasiIso`, which is the statement `quasiIsoAt_iff`. `quasiIsoAt_iff_isIso_homologyMap` gives the form of the definition, and `quasiIsoAt_iff_exactAt` treats acyclic complexes. `ChainComplex.quasiIsoAt₀_iff` works with `sc' K 1 0 0` in degree `0`.

<?decl QuasiIsoAt?>
:::

::: mathlib
`QuasiIso` · `Mathlib.Algebra.Homology.QuasiIso`

The class `QuasiIso f` is `∀ i, QuasiIsoAt f i`. The instances `quasiIso_of_isIso` and `quasiIso_comp` are parts 1 and 2 of the theorem, and `quasiIso_of_comp_left` and `quasiIso_of_comp_right` are part 3. `HomologicalComplex.quasiIso C c` is the class as a `MorphismProperty`, with the instance `instHasTwoOutOfThreePropertyQuasiIso`; Chapter 5 localizes at it.

<?decl QuasiIso?>
:::

::: mathlib
`HomologicalComplex.singleObjHomologySelfIso` · `Mathlib.Algebra.Homology.SingleHomology`

This is the isomorphism `((single C c j).obj A).homology j ≅ A`. `exactAt_single_obj` gives exactness at `i ≠ j`, `singleObjCyclesSelfIso` is the version for cycles, and `homologyFunctorSingleIso` is the natural isomorphism of functors.

<?decl HomologicalComplex.singleObjHomologySelfIso?>
:::

::: mathlib
`HomologicalComplex.exact_iff_degreewise_exact` · `Mathlib.Algebra.Homology.HomologicalComplexAbelian`

For `S : ShortComplex (HomologicalComplex C c)` with `C` abelian, `S.Exact ↔ ∀ i, (S.map (eval C c i)).Exact`. The instance `HomologicalComplex.instAbelian` is the first part of the theorem, and `shortExact_iff_degreewise_shortExact` is the version for short exact sequences.

<?decl HomologicalComplex.exact_iff_degreewise_exact?>
:::

Common errors of a learner:

- `K.homology i` and `(K.sc i).homology` are the same, but `K.homology (n + 1)` is about `K.sc (n + 1)`, whose first object is `K.X (c.prev (n + 1))`. Rewrite `c.prev` with `prev_eq'` or use `sc'`.
- A quasi-isomorphism is not an isomorphism in the derived sense until Chapter 5. In the category of complexes it is a class of morphisms with no inverses.
- `HomologicalComplex.Acyclic` means exact at every index, including the ends. A resolution $P \to M$ is not acyclic; its augmented complex is.

### Exercises

1. (A) Compute $H_1$ and $H_0$ of $\mathbb{Z}/18 \xrightarrow{6} \mathbb{Z}/18$, placed in degrees $1$ and $0$.
2. (A) Compute the homology of the chain complex $\mathbb{Z} \xrightarrow{2} \mathbb{Z} \xrightarrow{0} \mathbb{Z} \xrightarrow{3} \mathbb{Z}$, in degrees $3, 2, 1, 0$.
3. (A) Show that a complex is acyclic if and only if the morphism $0 \to K$ is a quasi-isomorphism.
4. (B) Let $k$ be a field and $K$ a bounded complex of finite dimensional $k$-vector spaces. Show that $\sum_i (-1)^i \dim X_i = \sum_i (-1)^i \dim H_i(K)$.
5. (B) Let $R = k[x]$ and $T$ multiplication by $x^2$ on $M = k[x]/(x^3)$. Compute $H_1(K_T)$ and $H_0(K_T)$ and their dimensions over $k$.
6. (B) Give a morphism of complexes that induces an isomorphism on $H_0$ and is not a quasi-isomorphism. *Hint:* use two complexes concentrated in degrees $1$ and $0$.
7. (C) Show directly, without the theorem on abelian categories, that a short complex of complexes of abelian groups which is short exact in each degree has the property that the cycles form a left exact sequence $0 \to Z_i(K_1) \to Z_i(K_2) \to Z_i(K_3)$.

### Notes and history

Homology groups as cycles modulo boundaries are the starting point of algebraic topology, and the algebraic treatment is in Cartan and Eilenberg (1956). Quasi-isomorphisms are the weak equivalences that Verdier inverted to construct the derived category.

The Mathlib Author of `ShortComplex.HomologicalComplex`, `SingleHomology` and `HomologicalComplexAbelian` is Joël Riou. The Mathlib Authors of `QuasiIso` are Kim Morrison and Joël Riou.

### Reference

<?reference?>
