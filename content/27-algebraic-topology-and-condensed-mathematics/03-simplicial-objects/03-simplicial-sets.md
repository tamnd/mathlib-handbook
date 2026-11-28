---
title: Simplicial sets
kind: theory
modules:
  - Mathlib.AlgebraicTopology.SimplicialComplex.Basic
  - Mathlib.AlgebraicTopology.SimplicialSet.Basic
  - Mathlib.AlgebraicTopology.SimplicialSet.Boundary
  - Mathlib.AlgebraicTopology.SimplicialSet.Degenerate
  - Mathlib.AlgebraicTopology.SimplicialSet.Dimension
  - Mathlib.AlgebraicTopology.SimplicialSet.Finite
  - Mathlib.AlgebraicTopology.SimplicialSet.FiniteColimits
  - Mathlib.AlgebraicTopology.SimplicialSet.FiniteProd
  - Mathlib.AlgebraicTopology.SimplicialSet.Horn
  - Mathlib.AlgebraicTopology.SimplicialSet.HornColimits
  - Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
  - Mathlib.AlgebraicTopology.SimplicialSet.Monomorphisms
  - Mathlib.AlgebraicTopology.SimplicialSet.NonDegenerateSimplices
  - Mathlib.AlgebraicTopology.SimplicialSet.NonDegenerateSimplicesColimit
  - Mathlib.AlgebraicTopology.SimplicialSet.Nonsingular
  - Mathlib.AlgebraicTopology.SimplicialSet.Op
  - Mathlib.AlgebraicTopology.SimplicialSet.Presentable
  - Mathlib.AlgebraicTopology.SimplicialSet.ProdStdSimplex
  - Mathlib.AlgebraicTopology.SimplicialSet.ProdStdSimplexOne
  - Mathlib.AlgebraicTopology.SimplicialSet.PushoutProduct
  - Mathlib.AlgebraicTopology.SimplicialSet.RegularEpi
  - Mathlib.AlgebraicTopology.SimplicialSet.Simplices
  - Mathlib.AlgebraicTopology.SimplicialSet.Skeleton
  - Mathlib.AlgebraicTopology.SimplicialSet.Splitting
  - Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
  - Mathlib.AlgebraicTopology.SimplicialSet.StdSimplexOne
  - Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
  - Mathlib.AlgebraicTopology.SimplicialSet.Subdivision
  - Mathlib.AlgebraicTopology.SimplicialSet.Nonempty
  - Mathlib.AlgebraicTopology.SimplicialSet.NonDegenerateSimplicesSubcomplex
  - Mathlib.AlgebraicTopology.SimplicialSet.NonsingularColimit
  - Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits
  - Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexEvaluation
  - Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexOp
explains:
  E3: [SSet, SSet.stdSimplex, SSet.yonedaEquiv, SSet.boundary, SSet.horn, SSet.horn_eq_iSup, SSet.Subcomplex, SSet.nonDegenerate, SSet.exists_nonDegenerate, SSet.unique_nonDegenerate_simplex, SSet.relativeCellComplexOfMono, SSet.horn₂₁.isPushout]
  E2: [SSet.hom_ext, SSet.Truncated, SSet.Augmented, SSet.stdSimplex.objEquiv, SSet.stdSimplex.asOrderHom, SSet.stdSimplex.face, SSet.stdSimplex.mem_nonDegenerate_iff_strictMono, SSet.stdSimplex.isoNerve, SSet.boundary_eq_iSup, SSet.boundary.ι, SSet.mem_horn_iff, SSet.face_le_horn, SSet.horn.ι, SSet.horn.hom_ext, SSet.Subcomplex.range, SSet.degenerate, SSet.degenerate_eq_iUnion_range_σ, SSet.unique_nonDegenerate_dim, SSet.unique_nonDegenerate_map, SSet.mono_of_nonDegenerate, SSet.S, SSet.N, SSet.isColimitCoconeN, SSet.Finite, SSet.HasDimensionLT, SSet.finite_of_hasDimensionLT, SSet.instFiniteTensorObj, SSet.finite_of_isColimit, SSet.skeleton, SSet.iSup_skeleton, SSet.relativeCellComplexCellsEquiv, SSet.Nonsingular, SSet.prodStdSimplex.isoNerve, SSet.prodStdSimplex₁.nonDegenerateEquiv, SSet.stdSimplex.objMk₁, SSet.horn₂₁.ι₀₁, SSet.horn₂₁.ι₁₂, SSet.horn.IsCompatible, SSet.horn.IsCompatible.desc, SSet.Subcomplex.unionProd, SSet.Subcomplex.unionProd.pushoutObjObj, SSet.instIsStableUnderCobaseChangeMonomorphisms, SSet.Finite.instIsFinitelyPresentable, SSet.instIsRegularEpiCategory, SSet.splitting, SSet.op, SSet.opEquivalence, SSet.ex, SSet.sd, SSet.sdExAdjunction, AbstractSimplicialComplex, PreAbstractSimplicialComplex]
  E1: auto
families: []
requires: [V24.C01, V24.C02, V24.C03, V24.C04, V25.C03]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Simplicial sets

### Overview

A simplicial set is a simplicial object in the category of sets. It is a combinatorial model of a space: the $n$-simplices are the elements of $X_n$, the faces $d_i$ give the boundary of a simplex, and the degeneracies $s_j$ give the collapsed copies of lower simplices. The standard simplex $\Delta[n]$ represents the functor $X \mapsto X_n$, so a map $\Delta[n] \to X$ is the same as an $n$-simplex of $X$.

This section defines simplicial sets, the standard simplices, boundaries, horns and subcomplexes. It proves the Yoneda description of $n$-simplices, the description of horns by faces and the Eilenberg-Zilber lemma, which writes each simplex uniquely as a degeneracy of a nondegenerate simplex. From the lemma it proves that each skeleton is obtained from the one below by attaching standard simplices along their boundaries. It then reads finiteness, nonsingular simplicial sets, products and the horn $\Lambda[2,1]$, which Chapter 4 fills.

### Definitions

**Definition (Simplicial set).** A *simplicial set* is a functor $X : \Delta^{\mathrm{op}} \to \mathbf{Set}$. For $x \in X_n$ and a monotone $\theta : [m] \to [n]$, write $\theta^* x = X(\theta)(x) \in X_m$. A morphism of simplicial sets is a natural transformation.

**Definition (Standard simplex).** The *standard $n$-simplex* is the representable functor $\Delta[n] = \mathrm{Hom}_\Delta(-, [n])$. Its $m$-simplices are the monotone maps $a : [m] \to [n]$, written as sequences $(a(0), \dots, a(m))$ with $a(0) \leq \dots \leq a(m)$, and $\theta^* a = a \theta$. The *identity simplex* is $\iota_n = \mathrm{id}_{[n]} \in \Delta[n]_n$.

**Definition (Subcomplex).** A *subcomplex* $A \subseteq X$ is a family of subsets $A_n \subseteq X_n$ with $\theta^* A_n \subseteq A_m$ for each $\theta : [m] \to [n]$. The subcomplexes of $X$ form a complete lattice under inclusion, with unions and intersections taken degreewise. The subcomplex *generated* by $x \in X_n$ is $\langle x \rangle$, with $\langle x \rangle_m = \{\theta^* x : \theta : [m] \to [n]\}$.

**Definition (Boundary and horn).** The *boundary* $\partial\Delta[n] \subseteq \Delta[n]$ is the subcomplex of the maps $a : [m] \to [n]$ that are not surjective. For $0 \leq i \leq n$, the *horn* $\Lambda[n, i] \subseteq \Delta[n]$ is the subcomplex of the maps $a$ with $a([m]) \cup \{i\} \neq [n]$. The horn is *inner* if $0 < i < n$.

Both families are closed under $\theta^*$, since the image of $a \theta$ is contained in the image of $a$. For $0 \leq j \leq n$, write $\partial_j \Delta[n] = \langle \delta_j \rangle$ for the $j$-th face, the subcomplex of the maps that miss $j$.

**Definition (Degenerate simplex).** A simplex $x \in X_n$ is *degenerate* if $x = s_j y$ for some $j$ and some $y \in X_{n-1}$, and *nondegenerate* otherwise. Every $0$-simplex is nondegenerate.

**Definition (Skeleton, dimension and finiteness).** The *$n$-skeleton* $\mathrm{sk}_n X$ is the subcomplex generated by the nondegenerate simplices of dimension less than $n$. The simplicial set $X$ has *dimension less than $d$* if every simplex of dimension at least $d$ is degenerate. It is *finite* if it has finitely many nondegenerate simplices.

**Definition (Nonsingular).** A simplicial set $X$ is *nonsingular* if for each nondegenerate $x \in X_n$ the map $\Delta[n] \to X$ that $x$ classifies is injective.

### Theorems and proofs

**Theorem (Yoneda for the standard simplex).** For each simplicial set $X$, the map $\mathrm{Hom}(\Delta[n], X) \to X_n$, $\varphi \mapsto \varphi_n(\iota_n)$, is a bijection, natural in $X$ and $[n]$. Its inverse sends $x$ to the map $\bar x$ with $\bar x_m(a) = a^* x$.

*Proof.* The map $\bar x$ is natural: $\bar x_k(a \theta) = (a \theta)^* x = \theta^* a^* x = \theta^* \bar x_m(a)$. Also $\bar x_n(\iota_n) = x$. Conversely, for a map $\varphi$ and $a \in \Delta[n]_m$, naturality applied to $\iota_n$ and $a$ gives $\varphi_m(a) = \varphi_m(a^* \iota_n) = a^* \varphi_n(\iota_n)$, so $\varphi = \overline{\varphi_n(\iota_n)}$. Naturality in $X$ is immediate, and naturality in $[n]$ is the identity $\overline{\theta^* x} = \bar x \circ \Delta[\theta]$, which holds on each $a$. $\square$

So the faces of $x$ are the composites of $\bar x$ with the maps $\Delta[n-1] \to \Delta[n]$ given by the $\delta_j$, and the subcomplex $\langle x \rangle$ is the image of $\bar x$.

**Proposition (Horns and boundaries by faces).** For $n \geq 1$, $$\partial\Delta[n] = \bigcup_{j=0}^{n} \partial_j \Delta[n], \qquad \Lambda[n, i] = \bigcup_{j \neq i} \partial_j \Delta[n].$$

*Proof.* A map $a : [m] \to [n]$ lies in $\partial_j \Delta[n]$ if and only if it misses $j$, because $\delta_j$ is a monotone bijection onto $[n] \setminus \{j\}$, so $a$ factors through $\delta_j$ exactly when $j \notin a([m])$. Now $a$ is not surjective if and only if it misses some $j$, and $a([m]) \cup \{i\} \neq [n]$ if and only if it misses some $j \neq i$. $\square$

**Theorem (Eilenberg-Zilber lemma).** Let $X$ be a simplicial set and $x \in X_n$. There is a pair $(p, y)$ with $p : [n] \to [k]$ surjective and $y \in X_k$ nondegenerate such that $x = p^* y$, and this pair is unique.

*Proof.* Existence, by induction on $n$. If $x$ is nondegenerate, take $p = \mathrm{id}$ and $y = x$. Otherwise $x = s_j x' = \sigma_j^* x'$ with $x' \in X_{n-1}$. By induction $x' = q^* y$ with $q$ surjective and $y$ nondegenerate, and then $x = (q \sigma_j)^* y$ with $q \sigma_j$ surjective.

Uniqueness. Let $x = p^* y = q^* z$ with $p : [n] \to [k]$ and $q : [n] \to [l]$ surjective and $y$, $z$ nondegenerate. A surjection of $\Delta$ has a section: choose $p' : [k] \to [n]$ with $p p' = \mathrm{id}$, for example $p'(c) = \min p^{-1}(c)$. Then $$y = (p p')^* y = p'^* p^* y = p'^* x = p'^* q^* z = (q p')^* z.$$ Factor $q p' = \iota e$ with $e$ surjective and $\iota$ injective (Section 1). Then $y = e^* (\iota^* z)$. Since $y$ is nondegenerate, $e$ is the identity: a surjection $e \neq \mathrm{id}$ has a position $j$ with $e(j) = e(j+1)$, so $e = g \sigma_j$ as in the normal form proof of Section 1, and then $y = s_j(g^* \iota^* z)$ would be degenerate. So $q p' : [k] \to [l]$ is injective and $k \leq l$. The same argument with the roles exchanged gives $l \leq k$. So $k = l$ and $q p'$ is an injective monotone map $[k] \to [k]$, which is the identity. Hence $y = z$.

It remains to show $p = q$. Let $a \in [n]$ and choose the section $p'$ with $p'(p(a)) = a$, which is possible since any choice of one point in each fibre is a section. The argument above gives $q p' = \mathrm{id}$, so $q(a) = q p'(p(a)) = p(a)$. $\square$

**Corollary (Degenerate simplices).** A simplex $x \in X_n$ is degenerate if and only if $x = p^* y$ for a surjection $p$ that is not the identity. If $x = \theta^* y$ with $x$ nondegenerate, then $\theta$ is injective.

*Proof.* For the first statement, a surjection $p \neq \mathrm{id}$ has a position $j$ with $p(j) = p(j+1)$, so $p = g \sigma_j$ as in the normal form proof of Section 1, and $p^* y = s_j (g^* y)$. For the second, factor $\theta = \iota e$. Then $x = e^* (\iota^* y)$, and $e$ is the identity since $x$ is nondegenerate. $\square$

**Theorem (Attaching cells).** Let $A \subseteq X$ be a subcomplex, and let $X^{(n)} = A \cup \mathrm{sk}_n X$. Let $\Sigma_n$ be the set of nondegenerate $n$-simplices of $X$ that are not in $A$. Then the square $$\begin{array}{ccc} \coprod_{\Sigma_n} \partial\Delta[n] & \longrightarrow & X^{(n)} \\ \downarrow & & \downarrow \\ \coprod_{\Sigma_n} \Delta[n] & \xrightarrow{(\bar x)} & X^{(n+1)} \end{array}$$ is a pushout, and $X = \bigcup_n X^{(n)}$. So the inclusion $A \to X$ is a transfinite composite of pushouts of coproducts of boundary inclusions.

*Proof.* The top map exists: a simplex $a$ of $\partial\Delta[n]$ is not surjective, so $a = \iota e$ with $\iota : [r] \to [n]$ injective and $r < n$, and $\bar x(a) = e^* (\iota^* x)$ lies in $\mathrm{sk}_n X$. Pushouts of simplicial sets are computed degreewise, and a pushout of sets along an injection $B \subseteq D$ is $C \sqcup (D \setminus B)$. So it is enough to show, in each degree $m$, that the map $(x, a) \mapsto a^* x$ from the pairs with $x \in \Sigma_n$ and $a : [m] \to [n]$ surjective is a bijection onto $X^{(n+1)}_m \setminus X^{(n)}_m$.

Each such $a^* x$ has the Eilenberg-Zilber pair $(a, x)$. It is not in $\mathrm{sk}_n X$, since every simplex of $\mathrm{sk}_n X$ is $\theta^* w$ with $w$ nondegenerate of dimension less than $n$, hence has a nondegenerate part of dimension less than $n$. It is not in $A$: otherwise $x = a'^* a^* x \in A$ for a section $a'$ of $a$. The map is injective by uniqueness in the lemma. It is surjective: a simplex $z \in X^{(n+1)}_m \setminus X^{(n)}_m$ is $\theta^* w$ with $w$ nondegenerate of dimension at most $n$, and by the lemma $z = a^* y$ with $y$ nondegenerate; $y$ is of dimension $n$ and not in $A$, or else $z$ would lie in $X^{(n)}$. Finally each simplex has a nondegenerate part of some dimension $n$, so it lies in $X^{(n+1)}$. $\square$

### Examples

**Example (The horn Λ[2,1]).** The simplices of $\Lambda[2,1]$ are the maps $a : [m] \to [2]$ that miss $0$ or miss $2$. The nondegenerate ones are the vertices $0, 1, 2$ and the edges $(0,1)$ and $(1,2)$. The edge $(0,2)$ is not in the horn, since $\{0,2\} \cup \{1\} = [2]$, and neither is the $2$-simplex $(0,1,2)$. So $\Lambda[2,1]$ is two edges glued at the vertex $1$, the pushout of $\Delta[1] \leftarrow \Delta[0] \rightarrow \Delta[1]$ along the vertex $1$ of the first edge and the vertex $0$ of the second. By the Yoneda theorem, a map $\Lambda[2,1] \to X$ is a pair of edges $f, g \in X_1$ with $d_0 f = d_1 g$: two composable arrows. A *filler* is a $2$-simplex $\tau \in X_2$ with $d_2 \tau = f$ and $d_0 \tau = g$; its third face $d_1 \tau$ is an edge from the source of $f$ to the target of $g$, a candidate composite. In the nerve of a category, Chapter 4 shows that the filler exists and is unique, with $d_1 \tau = g \circ f$.

**Example (The boundary of Δ[2]).** The nondegenerate simplices of $\partial\Delta[2]$ are the three vertices and the three edges $(0,1)$, $(1,2)$ and $(0,2)$: a hollow triangle. The attaching theorem with $A = \partial\Delta[2]$ and $X = \Delta[2]$ has $\Sigma_2 = \{(0,1,2)\}$ and $\Sigma_n = \emptyset$ otherwise, so $\Delta[2]$ is one $2$-cell attached to $\partial\Delta[2]$ along its boundary.

**Example (The square Δ[1] × Δ[1]).** An $m$-simplex of $\Delta[1] \times \Delta[1]$ is a pair of monotone maps $[m] \to [1]$, that is a monotone path in the poset $[1] \times [1]$. The nondegenerate $2$-simplices are the two maximal chains $(0,0) < (1,0) < (1,1)$ and $(0,0) < (0,1) < (1,1)$, two triangles that share the diagonal edge from $(0,0)$ to $(1,1)$. There are five nondegenerate edges and four vertices.

**Counterexample (A simplicial set that is not nonsingular).** Let $S = \Delta[1] / \partial\Delta[1]$, the pushout that collapses both vertices of $\Delta[1]$ to one point. Its nondegenerate simplices are one vertex and one edge $e$. The map $\Delta[1] \to S$ classified by $e$ sends both vertices of $\Delta[1]$ to the same vertex, so it is not injective, and $S$ is not nonsingular. Its geometric picture is a circle, which is a fine space; nonsingularity is a property of the combinatorial model.

### The library around it

::: mathlib
`SSet.stdSimplex` · `Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex`

`SSet` is `SimplicialObject (Type u)`, with `SSet.Truncated` and `SSet.Augmented`, and `SSet.hom_ext` compares two maps degreewise. `stdSimplex` is the functor `SimplexCategory ⥤ SSet` with notation `Δ[n]`, defined through `uliftYoneda`. `stdSimplex.objEquiv` identifies `Δ[n] _⦋m⦌` with `⦋m⦌ ⟶ ⦋n⦌`, and `asOrderHom` reads a simplex as a monotone map. `SSet.yonedaEquiv : (Δ[n] ⟶ X) ≃ X _⦋n⦌` is the Yoneda theorem. `stdSimplex.face S` is the subcomplex of simplices with image in the finset `S`, and `mem_nonDegenerate_iff_strictMono` says that the nondegenerate simplices of `Δ[n]` are the strictly monotone maps. `stdSimplex.isoNerve` identifies `Δ[n]` with the nerve of `Fin (n + 1)`.

<?decl SSet.stdSimplex?>
:::

::: mathlib
`SSet.horn` · `Mathlib.AlgebraicTopology.SimplicialSet.Horn`

`horn n i` is a `Subcomplex` of `Δ[n]` with notation `Λ[n, i]`, and `mem_horn_iff` is the definition: `Set.range (asOrderHom x) ∪ {i} ≠ Set.univ`. `horn_eq_iSup` is the proposition, the supremum of `face {j}ᶜ` over `j ≠ i`, and `face_le_horn` is one inclusion. `horn.ι` gives the faces `Δ[n] ⟶ Λ[n + 1, i]`, and `horn.hom_ext` says that a map out of a horn is fixed by its faces. For the boundary, `boundary n` has notation `∂Δ[n]`, `boundary_eq_iSup` is the first half of the proposition and `boundary.ι` gives the faces.

<?decl SSet.horn?>
:::

In `HornColimits`, `horn₂₁.ι₀₁` and `horn₂₁.ι₁₂` are the two edges of $\Lambda[2,1]$, and `horn₂₁.isPushout` is the pushout of the first example. `horn.IsCompatible` is the condition on a family of maps `Δ[n] ⟶ X` that they glue to a map out of `Λ[n + 1, i]`, and `IsCompatible.desc` glues them.

::: mathlib
`SSet.exists_nonDegenerate` · `Mathlib.AlgebraicTopology.SimplicialSet.Degenerate`

`X.degenerate n` and `X.nonDegenerate n` are sets of `n`-simplices, and `degenerate_eq_iUnion_range_σ` says that the degenerate `(n + 1)`-simplices are the union of the images of the `σ i`. `exists_nonDegenerate` is the existence half of the Eilenberg-Zilber lemma, with an `Epi f`. The uniqueness half is split into `unique_nonDegenerate_dim`, `unique_nonDegenerate_simplex` and `unique_nonDegenerate_map`. `mono_of_nonDegenerate` is the second statement of the corollary.

<?decl SSet.exists_nonDegenerate?>
:::

`X.S` is the type of all simplices, preordered by inclusion of the generated subcomplexes, and `X.N` is the partially ordered type of nondegenerate simplices; `isColimitCoconeN` shows that `X` is the colimit of the subcomplexes `⟨x⟩` over `X.N`. `SSet.splitting` is the splitting of Section 2 with `N n = X.nonDegenerate n`, which is the Eilenberg-Zilber lemma in the language of split simplicial objects.

::: mathlib
`SSet.relativeCellComplexOfMono` · `Mathlib.AlgebraicTopology.SimplicialSet.Skeleton`

For a monomorphism `i : X ⟶ Y`, `relativeCellComplexOfMono i` is a relative cell complex with basic cells `∂Δ[n].ι`, built on the filtration `Subcomplex.range i ⊔ Y.skeleton n`. This is the attaching theorem. `relativeCellComplexCellsEquiv` identifies its cells with the nondegenerate simplices of `Y` outside the range of `i`. `skeleton` is the monotone family of subcomplexes and `iSup_skeleton` says that its supremum is `⊤`.

<?decl SSet.relativeCellComplexOfMono?>
:::

`HasDimensionLT X d` asks that `X.degenerate n = ⊤` for `d ≤ n`, and `SSet.Finite` that `X.N` is finite; `finite_of_hasDimensionLT` gives finiteness from finite dimension and finitely many nondegenerate simplices in each degree below it. Finite products and finite colimits of finite simplicial sets are finite (`instFiniteTensorObj` and `finite_of_isColimit`), and `Finite.instIsFinitelyPresentable` makes a finite simplicial set finitely presentable. `Nonsingular X` asks that `yonedaEquiv.symm x` is a monomorphism for each nondegenerate `x`. `instIsStableUnderCobaseChangeMonomorphisms` and its neighbours record that monomorphisms are stable under pushout, and `instIsRegularEpiCategory` says that each epimorphism is regular.

The product `X ⊗ Y` is the cartesian product, computed degreewise. `prodStdSimplex.isoNerve` identifies `Δ[p] ⊗ Δ[q]` with the nerve of the poset `Fin (p + 1) × Fin (q + 1)`, and `prodStdSimplex₁.nonDegenerateEquiv` enumerates the $p + 1$ nondegenerate $(p+1)$-simplices of `Δ[p] ⊗ Δ[1]`, the case $p = 1$ of which is the square example. `stdSimplex.objMk₁` names the simplices of `Δ[1]`. For subcomplexes `A ⊆ X` and `B ⊆ Y`, `Subcomplex.unionProd A B` is $X \times B \cup A \times Y$, and `unionProd.pushoutObjObj` identifies it with the pushout used in Chapter 4. `SSet.op` reverses the order of each simplex through `SimplexCategory.rev`, and `opEquivalence` is the resulting involution. `SSet.sd` and `SSet.ex` are the subdivision functor and Kan's functor $\mathrm{Ex}$, with `sdExAdjunction`. `AbstractSimplicialComplex ι` is a down-closed family of nonempty finsets of `ι` that contains the singletons, built on `PreAbstractSimplicialComplex`.

A simplicial set is nonempty, `SSet.Nonempty X`, when it has a simplex in some degree, and `SSet.Nonempty.mk` builds the proof from one simplex. Then each `X _⦋n⦌` is nonempty, because the degeneracies carry a vertex to each degree. `SSet.nonempty_of_hom` transports nonemptiness along a map, and `SSet.notNonempty_iff_hasDimensionLT_zero` says that the empty simplicial set is the one of dimension less than $0$. An empty simplicial set is initial, by `SSet.isInitialOfNotNonempty`.

For a subcomplex `A` of `X`, the type `A.N` of `SSet.Subcomplex.N` holds the nondegenerate simplices of `X` that are not in `A`, with the order of `X.N` (`SSet.Subcomplex.N.le_iff`). These are the cells that the attaching theorem adds to `A`. `SSet.Subcomplex.existsN` says that each simplex outside `A` is a degeneracy of such a simplex, and `SSet.Subcomplex.N.cases` splits `X.N` into the simplices that lie in `A` and the ones of `A.N`. `SSet.Subcomplex.N.orderIsoOfIso` transports `A.N` along an isomorphism, and `SSet.Subcomplex.N.opEquiv` along the opposite: the subcomplex `SSet.Subcomplex.op A` of `X.op` is defined by `SSet.Subcomplex.mem_op_obj_iff`.

When `X` is nonsingular (`SSet.Nonsingular`), the subcomplex generated by a nondegenerate $n$-simplex is a copy of $\Delta[n]$. Then `SSet.isColimitCoconeN'` says that `X` is the colimit of the standard simplices `Δ[x.dim]` over `x : X.N`, and `SSet.functorN'Iso` compares this diagram with `SSet.functorN`. The diagram factors through the semi-simplex category by `SSet.N.toSemiSimplexCategory`.

The lattice of subcomplexes has colimits that agree with colimits of simplicial sets. `SSet.Subcomplex.BicartSq.isPushout` says that a bicartesian square of subcomplexes, with $A_4 = A_2 \cup A_3$ and $A_1 = A_2 \cap A_3$, is a pushout of simplicial sets. `SSet.Subcomplex.MulticoequalizerDiagram.isColimit` does the same for a union of a family of subcomplexes glued along their pairwise intersections. The functor `SSet.Subcomplex.evaluation X j` sends a subcomplex to its set of `j`-simplices, and an instance says that `SSet.Subcomplex.toSSetFunctor` preserves filtered colimits: a filtered union of subcomplexes is the colimit of the pieces.

Common errors of a learner:

- `Δ[n] _⦋m⦌` is a type of morphisms in `SimplexCategory` only up to `stdSimplex.objEquiv`; a simplex is not literally a function `Fin (m + 1) → Fin (n + 1)`.
- `Λ[n, i]` and `∂Δ[n]` are subcomplexes, not simplicial sets. The coercion to `SSet` and the inclusion `.ι` are separate steps.
- A degenerate simplex is one in the image of some `σ i`. A simplex all of whose faces are degenerate can be nondegenerate.
- `X.S` and `X.N` hold simplices of all dimensions. The nondegenerate simplices of one dimension form `X.nonDegenerate n`.

### Exercises

1. (A) Count the $m$-simplices of $\Delta[n]$, and show that $\Delta[n]$ has $\binom{n+1}{k+1}$ nondegenerate $k$-simplices. *Hint:* nondegenerate means strictly increasing.
2. (A) List the nondegenerate simplices of $\Lambda[3,1]$. *Hint:* the horn has all faces of $\Delta[3]$ except $(0,1,2,3)$ and $(0,2,3)$.
3. (A) For $i < j$, prove that $\partial_i \Delta[n] \cap \partial_j \Delta[n] = \langle \delta_j \delta_i \rangle$. *Hint:* a map misses $i$ and $j$ if and only if it factors through $\delta_j \delta_i$.
4. (B) Show that a map $\Lambda[n, i] \to X$ is the same as a family $x_j \in X_{n-1}$, $j \neq i$, with $d_j x_k = d_{k-1} x_j$ for $j < k$, both different from $i$. *Hint:* use Exercise 3.
5. (B) Show that a subcomplex of a nonsingular simplicial set is nonsingular, and that $\Delta[n]$ is nonsingular. *Hint:* a nondegenerate simplex of $\Delta[n]$ is an injective map.
6. (B) Show that $\Delta[p] \times \Delta[q]$ has $\binom{p+q}{p}$ nondegenerate $(p+q)$-simplices and none of higher dimension. *Hint:* count lattice paths.
7. (C) Let $X$ be a simplicial set and $x \in X_n$ nondegenerate. Show that $\langle x \rangle \cong \Delta[n]$ if $X$ is nonsingular, and give an example where $\langle x \rangle$ has fewer nondegenerate simplices than $\Delta[n]$. *Hint:* use the counterexample.

### Notes and history

Eilenberg and Zilber introduced semi-simplicial complexes and the lemma on degenerate simplices in 1950. Kan (1955 and 1958) developed the combinatorial homotopy theory of simplicial sets and introduced the functor $\mathrm{Ex}$. Gabriel and Zisman (1967) give the systematic treatment of the skeletal filtration and of the Eilenberg-Zilber lemma. Mathlib cites Kerodon for several statements, including nonsingular simplicial sets, and Jardine for the subdivision.

The Mathlib Authors of `SimplicialSet.Basic` and `SimplicialSet.Boundary` are Johan Commelin, Kim Morrison and Adam Topaz, and of `SimplicialSet.StdSimplex` and `SimplicialSet.Horn` Johan Commelin, Kim Morrison, Adam Topaz and Joël Riou. `HornColimits` is by Joël Riou and Nick Ward, `Nonsingular` by Joël Riou, Robin Carlier and Christian Merten, `Monoidal` by Joël Riou and Jack McKoen, `PushoutProduct` by Jack McKoen and `SimplicialComplex.Basic` by Bolton Bailey. The other modules of this section are by Joël Riou.

### Reference

<?reference?>
