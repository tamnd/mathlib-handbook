---
title: Chain complexes and singular homology
kind: theory
modules:
  - Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
  - Mathlib.AlgebraicTopology.MooreComplex
  - Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
  - Mathlib.AlgebraicTopology.SimplicialSet.Homology.HomologyZero
  - Mathlib.AlgebraicTopology.SimplicialSet.Homology.HomotopyInvariance
  - Mathlib.AlgebraicTopology.SimplicialSet.Homology.MapHomologicalComplex
  - Mathlib.AlgebraicTopology.SimplicialSet.Homology.Nondegenerate
  - Mathlib.AlgebraicTopology.SimplicialSet.Homology.Relative
  - Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
  - Mathlib.AlgebraicTopology.SingularHomology.Basic
  - Mathlib.AlgebraicTopology.SingularHomology.HomologyZero
  - Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
  - Mathlib.AlgebraicTopology.SingularSet
  - Mathlib.AlgebraicTopology.TopologicalSimplex
explains:
  E3: [AlgebraicTopology.alternatingFaceMapComplex, AlgebraicTopology.AlternatingFaceMapComplex.d_squared, AlgebraicTopology.normalizedMooreComplex, SSet.chainComplexFunctor, SSet.homology, SSet.homology₀Iso, SSet.Homotopy.congr_homologyMap, SSet.normalizedChainComplex, SSetPair.homologyδ, TopCat.toSSet, sSetTopAdj, AlgebraicTopology.singularHomologyFunctor, TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor]
  E2: [AlgebraicTopology.AlternatingFaceMapComplex.objD, AlgebraicTopology.AlternatingFaceMapComplex.ε, AlgebraicTopology.alternatingCofaceMapComplex, AlgebraicTopology.inclusionOfMooreComplex, AlgebraicTopology.NormalizedMooreComplex.objX, AlgebraicTopology.NormalizedMooreComplex.d_squared, SSet.chainComplex, SSet.chainComplexMap, SSet.ιChainComplex, SSet.chainComplex_hom_ext, SSet.homologyMap, SSet.homologyFunctor, SSet.chainComplexFunctorAdjunction, SSet.homology₀ε, CategoryTheory.SimplicialObject.Homotopy.sSetChainComplexMap, SSet.Homotopy.chainComplexMap, SSet.chainComplexFunctorObjCompMapIso, SSet.toNormalizedChainComplex, SSet.fromNormalizedChainComplex, SSet.ιNormalizedChainComplex_eq_zero, SSet.homotopyEquivNormalizedChainComplex, SSet.isZero_homology_of_hasDimensionLT, SSetPair.chainComplex, SSetPair.homology, SSetPair.shortExact_chainComplexShortComplex, SimplexCategory.toTopHomeo, SSet.stdSimplex.toTopObjIsoI, TopCat.toSSetObjEquiv, SSet.toTop, SSet.toTopSimplex, TopCat.toSSetIsoConst, AlgebraicTopology.singularChainComplexFunctor, AlgebraicTopology.singularChainComplexFunctorIsoOfTotallyDisconnectedSpace, AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace, AlgebraicTopology.singularChainComplexFunctorAdjunction, TopCat.singularHomology₀Iso, TopCat.singularHomology₀ε, TopCat.Homotopy.singularChainComplexFunctorObjMap, SimplexCategory.toTop]
  E1: auto
families: []
requires: [V13.C06, V24.C04, V24.C05, V24.C08, V25.C02, V26.C01, V26.C02, V26.C03, V27.C01, V27.C03, V27.C04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Chain complexes and singular homology

### Overview

The alternating sum of the face maps of a simplicial object squares to zero. So each simplicial object in a preadditive category gives a chain complex, and each simplicial set gives a chain complex of free modules. Applied to the singular simplicial set of a space, the same construction gives singular homology.

This section builds the alternating face map complex and the normalized Moore complex. It defines the homology of a simplicial set with coefficients in an object $R$, computes it in degree $0$, and shows that degenerate simplices do not change it. It then defines the topological simplex, the singular simplicial set, geometric realization and singular homology. It proves homotopy invariance and the long exact sequence of a pair.

Mathlib writes `f ≫ g` for $g \circ f$. In this text $\delta_i$ and $\sigma_i$ are the face and degeneracy maps $X_{n+1} \to X_n$ and $X_n \to X_{n+1}$ of a simplicial object $X$, as in Chapter 3.

### Definitions

Let $C$ be a preadditive category and let $X$ be a simplicial object in $C$.

**Definition (Alternating face map complex).** The chain complex $K(X)$ has $K(X)_n = X_n$ for $n \ge 0$ and the differential $d_{n+1} : X_{n+1} \to X_n$ given by
$$d_{n+1} = \sum_{i=0}^{n+1} (-1)^i \delta_i .$$
A map $f : X \to Y$ of simplicial objects commutes with each $\delta_i$, so it gives a map of complexes $K(f)$. This defines a functor from simplicial objects in $C$ to chain complexes in $C$ indexed by $\mathbb{N}$.

::: mathlib
`AlgebraicTopology.alternatingFaceMapComplex` · `Mathlib.AlgebraicTopology.AlternatingFaceMapComplex`

The functor `SimplicialObject C ⥤ ChainComplex C ℕ` for a preadditive category `C`. The differential is `AlternatingFaceMapComplex.objD X n`, the sum over `i : Fin (n + 2)` of `(-1) ^ (i : ℕ) • X.δ i`. The dual for cosimplicial objects is `alternatingCofaceMapComplex`.

<?decl AlgebraicTopology.alternatingFaceMapComplex?>
:::

**Definition (Normalized Moore complex).** Let $C$ be abelian. The normalized Moore complex $N(X)$ has $N(X)_0 = X_0$ and
$$N(X)_n = \bigcap_{i=1}^{n} \ker(\delta_i : X_n \to X_{n-1}) \qquad (n \ge 1),$$
with the differential induced by $\delta_0$. On $N(X)_{n+1}$ the faces $\delta_1, \dots, \delta_{n+1}$ vanish, so $d_{n+1}$ restricts to $\delta_0$ there, and $N(X)$ is a subcomplex of $K(X)$.

::: mathlib
`AlgebraicTopology.normalizedMooreComplex` · `Mathlib.AlgebraicTopology.MooreComplex`

The functor `SimplicialObject C ⥤ ChainComplex C ℕ` for an abelian category `C`. Its objects `NormalizedMooreComplex.objX X n` are infima of `kernelSubobject (X.δ k.succ)`, so $\delta_0$ is never in the list. The inclusion into the alternating face map complex is `inclusionOfMooreComplex`.

<?decl AlgebraicTopology.normalizedMooreComplex?>
:::

Now let $X$ be a simplicial set, and let $C$ be preadditive with coproducts. For $R$ in $C$, a map of sets $X_{n+1} \to X_n$ induces a map of coproducts $\coprod_{X_{n+1}} R \to \coprod_{X_n} R$ that sends the summand of $x$ to the summand of its image.

**Definition (Chain complex of a simplicial set).** The complex $C_\bullet(X; R)$ is the alternating face map complex of the simplicial object $n \mapsto \coprod_{x \in X_n} R$. Write $\iota_x : R \to C_n(X; R)$ for the inclusion of the summand of $x$. The differential satisfies
$$d \circ \iota_x = \sum_{i=0}^{n+1} (-1)^i \iota_{\delta_i x}, \qquad x \in X_{n+1}.$$
If $C$ has homology, the *homology* $H_n(X; R)$ is the homology of this complex in degree $n$. For $C$ the category of abelian groups and $R = \mathbb{Z}$, $C_n(X;\mathbb{Z})$ is the free abelian group on $X_n$.

::: mathlib
`SSet.chainComplexFunctor` · `Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic`

The functor `C ⥤ SSet ⥤ ChainComplex C ℕ`, with `X.chainComplex R` for its value. The inclusion of a summand is `SSet.ιChainComplex x`, and `SSet.chainComplex_hom_ext` is the extensionality for maps out of the chains.

<?decl SSet.chainComplexFunctor?>
:::

::: mathlib
`SSet.homology` · `Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic`

`X.homology R n` is `(X.chainComplex R).homology n`. The map of a morphism `f` is `SSet.homologyMap f R n`, and `SSet.homologyFunctor` packs these into a functor `SSet ⥤ C`.

<?decl SSet.homology?>
:::

**Definition (Normalized chains).** The *normalized chain complex* of $X$ has in degree $n$ the coproduct of copies of $R$ over the nondegenerate $n$-simplices of $X$. Its differential is the alternating sum of faces in which every degenerate face is sent to $0$.

::: mathlib
`SSet.normalizedChainComplex` · `Mathlib.AlgebraicTopology.SimplicialSet.Homology.Nondegenerate`

The normalized chain complex of a simplicial set with coefficients in `R`. The maps `SSet.toNormalizedChainComplex` and `SSet.fromNormalizedChainComplex` give a retraction and a section, and `SSet.homotopyEquivNormalizedChainComplex` is a homotopy equivalence with `X.chainComplex R`.

<?decl SSet.normalizedChainComplex?>
:::

The topology enters through the standard simplices. The *topological $n$-simplex* is
$$|\Delta^n| = \{ t \in \mathbb{R}^{n+1} : t_i \ge 0, \ \textstyle\sum_i t_i = 1 \}.$$
A monotone map $\theta : [m] \to [n]$ gives the affine map $|\Delta^m| \to |\Delta^n|$ that sends the vertex $e_j$ to $e_{\theta(j)}$. So the simplices form a cosimplicial space, `SimplexCategory.toTop`.

**Definition (Singular simplicial set).** For a space $Y$, the singular simplicial set $\operatorname{Sing}(Y)$ has as $n$-simplices the continuous maps $|\Delta^n| \to Y$. A map $\theta : [m] \to [n]$ acts by precomposition with $|\theta|$.

**Definition (Geometric realization).** The realization $|X|$ of a simplicial set $X$ is the left Kan extension of $[n] \mapsto |\Delta^n|$ along the Yoneda embedding. Concretely, $|X|$ is the colimit of $|\Delta^n|$ over the category of simplices $\Delta[n] \to X$.

::: mathlib
`TopCat.toSSet` · `Mathlib.AlgebraicTopology.SingularSet`

The singular simplicial set functor `TopCat ⥤ SSet`. The equivalence `TopCat.toSSetObjEquiv` identifies its $n$-simplices with `C(StdSimplex ℝ (Fin (n + 1)), X)`. Geometric realization is `SSet.toTop`, with notation `|X|`.

<?decl TopCat.toSSet?>
:::

::: mathlib
`sSetTopAdj` · `Mathlib.AlgebraicTopology.SingularSet`

The adjunction `SSet.toTop ⊣ TopCat.toSSet`. The isomorphism `SSet.toTopSimplex` says that the realization of `Δ[n]` is the topological simplex.

<?decl sSetTopAdj?>
:::

**Definition (Singular homology).** The singular chain complex of $Y$ with coefficients in $R$ is $C_\bullet(\operatorname{Sing}(Y); R)$. Its homology is the singular homology $H_n(Y; R)$.

::: mathlib
`AlgebraicTopology.singularHomologyFunctor` · `Mathlib.AlgebraicTopology.SingularHomology.Basic`

For each `n`, a functor `C ⥤ TopCat ⥤ C`. It is the composite of `singularChainComplexFunctor C`, which is `SSet.chainComplexFunctor C` composed with `TopCat.toSSet`, and the homology functor in degree `n`.

<?decl AlgebraicTopology.singularHomologyFunctor?>
:::

### Theorems and proofs

**Theorem (The square of the differential).** For each simplicial object $X$ in a preadditive category, $d_{n+1} \circ d_{n+2} = 0$ in $K(X)$.

*Proof.* Expand the product:
$$d_{n+1} d_{n+2} = \sum_{i=0}^{n+1} \sum_{j=0}^{n+2} (-1)^{i+j} \delta_i \delta_j .$$
The simplicial identity for faces reads $\delta_i \delta_j = \delta_{j-1} \delta_i$ for $i < j$. Split the pairs $(i,j)$ into the set $A$ with $i < j$ and the set $B$ with $i \ge j$. The map $(i, j) \mapsto (j-1, i)$ sends $A$ bijectively onto $B$: for $i < j$ the pair $(j-1, i)$ has $j - 1 \ge i$, and the inverse is $(k, l) \mapsto (l, k+1)$. The identity says that the term of $(i, j) \in A$ is $(-1)^{i+j} \delta_{j-1}\delta_i$, and the term of its image in $B$ is $(-1)^{i+j-1}\delta_{j-1}\delta_i$. The two terms cancel, so the whole sum is $0$. $\square$

The same argument proves that the differential of $N(X)$ squares to $0$, because it is a restriction of $d$.

**Proposition (Homology in degree zero).** Let $X$ be a simplicial set and $R$ an abelian group. Then $H_0(X; R) \cong \bigoplus_{\pi_0(X)} R$, where $\pi_0(X)$ is the quotient of $X_0$ by the equivalence relation generated by $\delta_1 e \sim \delta_0 e$ for $e \in X_1$.

*Proof.* The complex ends with $d_1 : C_1 \to C_0$ and $d_0 = 0$, so $H_0 = C_0 / \operatorname{im} d_1$. For $e \in X_1$ and $r \in R$, $d_1(r\, e) = r\,\delta_0 e - r\,\delta_1 e$. Define $\varphi : C_0 \to \bigoplus_{\pi_0(X)} R$ by $r\, x \mapsto r\,[x]$. It is onto, and it kills $\operatorname{im} d_1$ because $[\delta_0 e] = [\delta_1 e]$. Let $U \subseteq C_0$ be the image of $d_1$. For $x \sim y$ there is a chain $x = x_0, x_1, \dots, x_k = y$ in which consecutive vertices are the two ends of an edge, so $r\,x - r\,y \in U$. Now take $c = \sum r_x x$ with $\varphi(c) = 0$. In each class $P$ of $\pi_0(X)$ fix a vertex $x_P$; then $\sum_{x \in P} r_x = 0$, and $\sum_{x \in P} r_x x = \sum_{x \in P} r_x (x - x_P)$ lies in $U$. So $\ker \varphi = U$ and $\varphi$ induces the isomorphism. $\square$

::: mathlib
`SSet.homology₀Iso` · `Mathlib.AlgebraicTopology.SimplicialSet.Homology.HomologyZero`

The isomorphism `X.homology R 0 ≅ ∐ (fun _ : π₀ X ↦ R)`. The map `SSet.homology₀ε` to `R` is an isomorphism when `X` is connected. For spaces, `TopCat.singularHomology₀Iso` uses the path components `ZerothHomotopy X`.

<?decl SSet.homology₀Iso?>
:::

**Proposition (Degenerate simplices are zero in normalized chains).** Let $x = \sigma_i y$ be a degenerate $(n+1)$-simplex. The quotient map $C_\bullet(X;R) \to C^{N}_\bullet(X; R)$ sends $\iota_x$ to $0$, and it is a map of complexes. It is a homotopy equivalence.

*Proof.* The first claim is the definition. For the second, let $D_n \subseteq C_n$ be spanned by the degenerate simplices. The quotient $C_n / D_n$ is the normalized group. So it suffices to show $d(D_{n+1}) \subseteq D_n$. Take $x = \sigma_j y$. The simplicial identities give $\delta_i \sigma_j = \sigma_{j-1} \delta_i$ for $i < j$, $\delta_j \sigma_j = \delta_{j+1}\sigma_j = \mathrm{id}$, and $\delta_i \sigma_j = \sigma_j \delta_{i-1}$ for $i > j+1$. In $d x = \sum_i (-1)^i \delta_i x$ the terms with $i \ne j, j+1$ are degenerate, and the terms with $i = j$ and $i = j+1$ are $(-1)^j y$ and $(-1)^{j+1} y$, which cancel. So $dx \in D_n$. The homotopy equivalence is a special case of the theorem of Section 3, which compares $K(X)$ and $N(X)$ for a simplicial abelian group; Mathlib applies it to $n \mapsto \coprod_{X_n} R$. $\square$

**Theorem (Homotopy invariance).** Let $f, g : X \to Y$ be maps of simplicial sets and $H : X \times \Delta[1] \to Y$ a homotopy from $f$ to $g$. Then $H_n(f) = H_n(g)$ for each $n$. The same holds for homotopic continuous maps and singular homology.

*Proof.* A homotopy of simplicial sets is the same as a combinatorial simplicial homotopy, a family $h_j : X_n \to Y_{n+1}$ for $0 \le j \le n$, with relations between $h_j$ and the faces and degeneracies (Chapter 3, Section 2). Set $s_n = \sum_{j=0}^n (-1)^j h_j : C_n(X) \to C_{n+1}(Y)$. The relations between $h_j$ and the faces pair the terms of $d s + s d$: the terms $\delta_i h_j$ with $i \ne j, j+1$ cancel against the terms $h_{j'} \delta_{i'}$, and the terms $\delta_j h_j$ and $\delta_{j+1} h_j$ telescope, which leaves only $\delta_0 h_0 = g$ and $\delta_{n+1} h_n = f$. So $d s + s d = g - f$. Check degree $0$: for a vertex $x$, $h_0 x$ is the edge $H(x, 0 \to 1)$ from $f(x)$ to $g(x)$, so $d s_0 x = \delta_0 h_0 x - \delta_1 h_0 x = g(x) - f(x)$, and there is no term $s d$. So $s$ is a chain homotopy between $g$ and $f$, and homotopic chain maps induce the same map on homology by Volume 26, Chapter 3. For spaces, a homotopy $Y \times I \to Z$ gives a map $\operatorname{Sing}(Y) \times \Delta[1] \to \operatorname{Sing}(Z)$ by the adjunction and the homeomorphism $|\Delta[1]| \cong I$, and the first case applies. $\square$

::: mathlib
`SSet.Homotopy.congr_homologyMap` · `Mathlib.AlgebraicTopology.SimplicialSet.Homology.HomotopyInvariance`

A homotopy `H : SSet.Homotopy f g` gives `SSet.homologyMap f R n = SSet.homologyMap g R n`. The chain homotopy is `SSet.Homotopy.chainComplexMap`, built on `CategoryTheory.SimplicialObject.Homotopy.toChainHomotopy` from Chapter 3.

<?decl SSet.Homotopy.congr_homologyMap?>
:::

::: mathlib
`TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor` · `Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance`

For `H : TopCat.Homotopy f g`, the maps induced by `f` and `g` on singular homology agree in every degree. The homeomorphism `SSet.stdSimplex.toTopObjIsoI` between `|Δ[1]|` and the unit interval is the link between the two notions of homotopy.

<?decl TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor?>
:::

**Theorem (Long exact sequence of a pair).** Let $i : A \to X$ be a monomorphism of simplicial sets and let $C_\bullet(X, A; R)$ be the cokernel of $C_\bullet(A;R) \to C_\bullet(X;R)$. There is a long exact sequence
$$\cdots \to H_{n}(A) \to H_n(X) \to H_n(X, A) \xrightarrow{\ \partial\ } H_{n-1}(A) \to \cdots \to H_0(X, A) \to 0 .$$

*Proof.* In degree $n$ the map $C_n(A) \to C_n(X)$ is the inclusion of the coproduct over $A_n$ into the coproduct over $X_n$, because $i$ is injective on simplices. Its cokernel is the coproduct over $X_n \setminus A_n$, and the sequence $0 \to C_n(A) \to C_n(X) \to C_n(X,A) \to 0$ is split exact. So the sequence of complexes is short exact, and the long exact sequence of Volume 26, Chapter 2 gives the result. The sequence ends with $H_0(X,A) \to 0$ because $C_{-1}(A) = 0$. $\square$

::: mathlib
`SSetPair.homologyδ` · `Mathlib.AlgebraicTopology.SimplicialSet.Homology.Relative`

For a pair `P : SSetPair` from Chapter 4, `SSetPair.homologyδ R n m` is the connecting map `P.homology R n ⟶ P.left.homology R m` when `m + 1 = n`. Exactness at the three places is `SSetPair.homology_exact₁`, `homology_exact₂` and `homology_exact₃`.

<?decl SSetPair.homologyδ?>
:::

**Proposition (Totally disconnected spaces).** Let $Y$ be a totally disconnected space. Then $H_0(Y;R) \cong \bigoplus_{Y} R$ and $H_n(Y; R) = 0$ for $n \ge 1$.

*Proof.* The simplex $|\Delta^n|$ is convex, hence connected. A continuous image of a connected space is connected, and in $Y$ the connected sets are points. So every singular simplex is constant, and $\operatorname{Sing}(Y)$ is the constant simplicial set with value $Y$. All its face maps are identities. Then $d_{n+1} = \sum_{i=0}^{n+1} (-1)^i \cdot \mathrm{id}$, which is $0$ for $n+1$ odd and $\mathrm{id}$ for $n+1 \ge 2$ even. The complex is
$$R[Y] \xleftarrow{\ 0\ } R[Y] \xleftarrow{\ 1\ } R[Y] \xleftarrow{\ 0\ } R[Y] \xleftarrow{\ 1\ } \cdots$$
In degree $0$ the homology is $R[Y]$. In odd degree $2k+1$ the kernel is everything and the image of $d_{2k+2} = 1$ is everything. In even degree $2k \ge 2$ the kernel of $d_{2k} = 1$ is $0$. $\square$

### Examples

**Example (The point).** For $X = \Delta[0]$ there is one simplex in each degree, and the complex is the one in the last proof with $Y$ a point: $\mathbb{Z} \xleftarrow{0} \mathbb{Z} \xleftarrow{1} \mathbb{Z} \xleftarrow{0} \cdots$. So $H_0 = \mathbb{Z}$ and $H_n = 0$ for $n \ge 1$. The normalized complex is $\mathbb{Z}$ in degree $0$ and $0$ elsewhere, because each simplex of degree at least $1$ is degenerate. The Moore complex agrees: $N_1 = \ker(\delta_1 : \mathbb{Z} \to \mathbb{Z}) = 0$, since $\delta_1$ is the identity.

**Example (The boundary of the 2-simplex).** The boundary $\partial\Delta[2]$ has the vertices $0, 1, 2$ and the nondegenerate edges $[01], [02], [12]$, and no nondegenerate simplex of dimension $2$. Use normalized chains. For an edge $[ab]$, $\delta_0 [ab] = b$ and $\delta_1 [ab] = a$, so $d[ab] = b - a$. A chain $\alpha [01] + \beta [02] + \gamma [12]$ is a cycle when the coefficients of $0$, $1$ and $2$ in its boundary vanish: $-\alpha - \beta = 0$, $\alpha - \gamma = 0$ and $\beta + \gamma = 0$. The solutions are $\alpha = \gamma = -\beta$, so $Z_1 = \mathbb{Z} \cdot ([01] - [02] + [12])$. There are no $2$-chains, so $H_1 = \mathbb{Z}$, generated by the loop around the triangle. The image of $d$ is spanned by $1 - 0$ and $2 - 0$, which is the group of chains with coefficient sum $0$, so $H_0 = \mathbb{Z}$. This is the homology of a circle.

**Example (A Lean statement).** Singular homology with integer coefficients is an object of `ModuleCat ℤ`.

```lean
open AlgebraicTopology CategoryTheory in
noncomputable example (X : TopCat.{0}) (n : ℕ) : ModuleCat.{0} ℤ :=
  ((singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj (ModuleCat.of ℤ ℤ)).obj X
```

### The library around it

The library has two layers. The first layer is algebra on simplicial objects: `alternatingFaceMapComplex` and `normalizedMooreComplex`. The second layer applies it to the simplicial object $n \mapsto \coprod_{X_n} R$ of a simplicial set, with coefficients in any preadditive category with coproducts.

::: mathlib
`SSet.isZero_homology_of_hasDimensionLT` · `Mathlib.AlgebraicTopology.SimplicialSet.Homology.Nondegenerate`

If `X` has no nondegenerate simplex of dimension at least `d` (the class `SSet.HasDimensionLT X d` of Chapter 3), then the homology vanishes in degrees at least `d`.

<?decl SSet.isZero_homology_of_hasDimensionLT?>
:::

::: mathlib
`AlgebraicTopology.singularChainComplexFunctorIsoOfTotallyDisconnectedSpace` · `Mathlib.AlgebraicTopology.SingularHomology.Basic`

The isomorphism of the singular complex of a totally disconnected space with the complex `R ←0 R ←1 R ←0 ⋯` of coproducts over the space.

<?decl AlgebraicTopology.singularChainComplexFunctorIsoOfTotallyDisconnectedSpace?>
:::

The source file `SingularSet` lists two goals as work to do: the singular set is a Kan complex, and the adjunction between realization and the singular set is a Quillen equivalence. The index of this edition has no declaration for either. It also has no declaration for the excision theorem of singular homology.

Common errors of a learner: The first error is to forget the face $\delta_0$ in the Moore complex. The intersection runs over $i = 1, \dots, n$, and $\delta_0$ is the differential. The second error is to treat `SSet.homology` as a group. It is an object of $C$, and the coefficients $R$ are an object of $C$, not a ring. The third error is to apply `SSetPair` homology to any map. The pair must come from a monomorphism.

### Exercises

1. (A) Let $X = \Delta[1]$. List its nondegenerate simplices and compute $H_n(\Delta[1]; \mathbb{Z})$ with normalized chains. *Hint:* there are two vertices and one edge.
2. (A) Compute $d_1$ and $d_2$ of $K(X)$ for $X = \Delta[0]$ and check that $d_1 d_2 = 0$. *Hint:* both are sums of identities with signs.
3. (A) Let $X = \partial\Delta[2]$ and $R = \mathbb{Z}/2$. Compute $H_0$ and $H_1$. *Hint:* the computation in the examples works over any ring.
4. (B) Show that the Moore complex $N(X)_1$ of a simplicial abelian group is $\ker \delta_1$ and that $d = \delta_0$ maps it into $X_0$. Show that the image of $N_1 \to N_0$ equals the image of $\delta_0 - \delta_1 : X_1 \to X_0$. *Hint:* write $x \in X_1$ as $(x - \sigma_0\delta_1 x) + \sigma_0 \delta_1 x$.
5. (B) Let $Y$ be a path connected space. Show that $H_0(Y;\mathbb{Z}) = \mathbb{Z}$. *Hint:* a path is a singular $1$-simplex, by the homeomorphism $|\Delta^1| \cong [0,1]$.
6. (C) Compute the homology of the simplicial set $\Delta[1] / \partial\Delta[1]$, the pushout of $\partial \Delta[1] \to \Delta[1]$ along $\partial\Delta[1] \to \Delta[0]$. *Hint:* one nondegenerate vertex and one nondegenerate edge, and $d = 0$.
7. (C) Use the long exact sequence of the pair $(\Delta[2], \partial\Delta[2])$ and the homology of $\partial\Delta[2]$ to compute $H_n(\Delta[2], \partial\Delta[2])$. *Hint:* $\Delta[2]$ has the homology of a point because it has a contracting homotopy, or compute it with its seven nondegenerate simplices.

### Notes and history

Poincaré introduced homology in 1895 through chains of cells. Singular homology works for every space, and the axioms of Eilenberg and Steenrod in Section 2 isolate its formal properties. Eilenberg and Zilber studied simplicial sets in 1950, and Kan developed their homotopy theory in 1955 and 1958.

The file `SingularHomology.HomotopyInvariance` states that homotopy invariance was first formalized in Lean 3 in 2022 by Brendan Seamus Murphy with a different proof.

The Mathlib Authors of these files, from the copyright headers: `AlternatingFaceMapComplex` by Joël Riou, Adam Topaz and Johan Commelin; `MooreComplex` by Kim Morrison; `SimplicialSet.Homology.Basic` and `Relative` by Joël Riou and Andrew Yang; `HomologyZero`, `MapHomologicalComplex`, `Nondegenerate` and `TopAdj` by Joël Riou; the two `HomotopyInvariance` files by Fabian Odermatt and Joël Riou; `SingularHomology.Basic` by Andrew Yang; `SingularSet` by Johan Commelin, Kim Morrison and Adam Topaz; `TopologicalSimplex` by Johan Commelin, Adam Topaz and Joël Riou.

### Reference

<?reference?>
