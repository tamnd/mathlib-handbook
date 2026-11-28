---
title: The Dold-Kan correspondence
kind: theory
modules:
  - Mathlib.AlgebraicTopology.DoldKan.Compatibility
  - Mathlib.AlgebraicTopology.DoldKan.Decomposition
  - Mathlib.AlgebraicTopology.DoldKan.Degeneracies
  - Mathlib.AlgebraicTopology.DoldKan.Equivalence
  - Mathlib.AlgebraicTopology.DoldKan.EquivalenceAdditive
  - Mathlib.AlgebraicTopology.DoldKan.EquivalencePseudoabelian
  - Mathlib.AlgebraicTopology.DoldKan.Faces
  - Mathlib.AlgebraicTopology.DoldKan.FunctorGamma
  - Mathlib.AlgebraicTopology.DoldKan.FunctorN
  - Mathlib.AlgebraicTopology.DoldKan.GammaCompN
  - Mathlib.AlgebraicTopology.DoldKan.Homotopies
  - Mathlib.AlgebraicTopology.DoldKan.HomotopyEquivalence
  - Mathlib.AlgebraicTopology.DoldKan.NCompGamma
  - Mathlib.AlgebraicTopology.DoldKan.NReflectsIso
  - Mathlib.AlgebraicTopology.DoldKan.Normalized
  - Mathlib.AlgebraicTopology.DoldKan.PInfty
  - Mathlib.AlgebraicTopology.DoldKan.Projections
  - Mathlib.AlgebraicTopology.DoldKan.SplitSimplicialObject
explains:
  E3: [AlgebraicTopology.DoldKan.Hσ, AlgebraicTopology.DoldKan.P, AlgebraicTopology.DoldKan.HigherFacesVanish, AlgebraicTopology.DoldKan.PInfty, AlgebraicTopology.DoldKan.σ_comp_PInfty, AlgebraicTopology.DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex, AlgebraicTopology.DoldKan.Γ₀, CategoryTheory.Abelian.DoldKan.equivalence, CategoryTheory.Idempotents.DoldKan.equivalence, CategoryTheory.Preadditive.DoldKan.equivalence]
  E2: [AlgebraicTopology.DoldKan.hσ, AlgebraicTopology.DoldKan.homotopyHσToZero, AlgebraicTopology.DoldKan.c, AlgebraicTopology.DoldKan.P_succ, AlgebraicTopology.DoldKan.Q, AlgebraicTopology.DoldKan.P_f_idem, AlgebraicTopology.DoldKan.HigherFacesVanish.induction, AlgebraicTopology.DoldKan.HigherFacesVanish.of_P, AlgebraicTopology.DoldKan.comp_P_eq_self_iff, AlgebraicTopology.DoldKan.P_is_eventually_constant, AlgebraicTopology.DoldKan.QInfty, AlgebraicTopology.DoldKan.PInfty_idem, AlgebraicTopology.DoldKan.degeneracy_comp_PInfty, AlgebraicTopology.DoldKan.decomposition_Q, AlgebraicTopology.DoldKan.homotopyPInftyToId, AlgebraicTopology.DoldKan.PInftyToNormalizedMooreComplex, AlgebraicTopology.DoldKan.N₁_iso_normalizedMooreComplex_comp_toKaroubi, AlgebraicTopology.DoldKan.N₁, AlgebraicTopology.DoldKan.N₂, AlgebraicTopology.DoldKan.Γ₂, AlgebraicTopology.DoldKan.Γ₀.splitting, AlgebraicTopology.DoldKan.Γ₀.Obj.Termwise.mapMono, AlgebraicTopology.DoldKan.Γ₀.Obj.Termwise.mapMono_δ₀, AlgebraicTopology.DoldKan.Γ₀.Obj.Termwise.mapMono_eq_zero, AlgebraicTopology.DoldKan.Isδ₀, AlgebraicTopology.DoldKan.N₁Γ₀, AlgebraicTopology.DoldKan.N₂Γ₂, AlgebraicTopology.DoldKan.Γ₂N₂, AlgebraicTopology.DoldKan.PInfty_comp_map_mono_eq_zero, AlgebraicTopology.DoldKan.compatibility_N₂_N₁_karoubi, AlgebraicTopology.DoldKan.Compatibility.equivalence, CategoryTheory.Abelian.DoldKan.N, CategoryTheory.Abelian.DoldKan.Γ, CategoryTheory.Abelian.DoldKan.comparisonN, CategoryTheory.Idempotents.DoldKan.N, CategoryTheory.Idempotents.DoldKan.Γ, CategoryTheory.SimplicialObject.Splitting.nondegComplex, CategoryTheory.SimplicialObject.Splitting.homotopyEquivNondegComplex]
  E1: auto
families: []
requires: [V24.C04, V24.C08, V25.C01, V25.C02, V26.C02, V26.C03, V27.C03]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The Dold-Kan correspondence

### Overview

A simplicial abelian group looks much richer than a chain complex: it has $n+1$ faces and $n+1$ degeneracies in each degree, tied by the simplicial identities. The Dold-Kan correspondence says that the extra structure carries no information. The normalized Moore complex $N$ is an equivalence between simplicial abelian groups and chain complexes in degrees $\ge 0$, and the same holds in any abelian category. Its inverse $\Gamma$ builds a simplicial object out of a complex by formal degeneracies.

The correspondence lets homological algebra and simplicial homotopy theory pass results back and forth. Through it a chain complex becomes a simplicial abelian group, hence a Kan complex, and the homotopy groups of that Kan complex are the homology groups of the complex. This section follows the Mathlib proof. It defines the projections $P_q$ and their limit $P_\infty$, proves that $P_\infty$ projects onto the Moore complex and kills degenerate simplices, and deduces that the Moore complex is homotopy equivalent to the alternating face map complex of Section 1. It then defines $\Gamma$, states the equivalence in its three forms in Mathlib, and computes it by hand in degrees $0$ and $1$.

Write $K(X)$ for the alternating face map complex and $N(X)$ for the Moore complex, as in Section 1. Mathlib has the notations `K[X]` and `N[X]`. Maps compose from right to left in the text and from left to right in Mathlib.

### Definitions

Let $C$ be preadditive and $X$ a simplicial object in $C$. Recall $d = \sum_i (-1)^i \delta_i$ on $K(X)$.

**Definition (The maps $h$ and $H_\sigma$).** For $q \ge 0$ define $h^{(q)}_n : X_n \to X_{n+1}$ by
$$h^{(q)}_n = 0 \ \text{ if } n < q, \qquad h^{(q)}_n = (-1)^{n-q} \sigma_{n-q} \ \text{ if } n \ge q .$$
Let $H_\sigma^{(q)} = d h^{(q)} + h^{(q)} d$ be the null homotopic chain map on $K(X)$ that $h^{(q)}$ defines.

**Definition (Projections).** Define chain maps $P_q : K(X) \to K(X)$ by $P_0 = \mathrm{id}$ and $P_{q+1} = (\mathrm{id} + H_\sigma^{(q)}) \circ P_q$. Write $Q_q = \mathrm{id} - P_q$.

::: mathlib
`AlgebraicTopology.DoldKan.P` · `Mathlib.AlgebraicTopology.DoldKan.Projections`

`P q : K[X] ⟶ K[X]`, defined by recursion: `P (q + 1) = P q ≫ (𝟙 _ + Hσ q)`. The map `Hσ q` of `Mathlib.AlgebraicTopology.DoldKan.Homotopies` is the null homotopic map of `hσ q`, and `homotopyHσToZero q` is the homotopy. `P_f_idem` says that each component of `P q` is idempotent.

<?decl AlgebraicTopology.DoldKan.P?>
:::

**Definition (Higher faces vanish).** A map $\varphi : Y \to X_m$ satisfies $\mathrm{HFV}_q$ if $\delta_i \varphi = 0$ for the last $q$ face maps, that is for $m - q < i \le m$. The first face $\delta_0$ never counts. So $\mathrm{HFV}_m$ for $\varphi$ means that $\varphi$ factors through $N(X)_m$ in the abelian case.

::: mathlib
`AlgebraicTopology.DoldKan.HigherFacesVanish` · `Mathlib.AlgebraicTopology.DoldKan.Faces`

`HigherFacesVanish q φ` for `φ : Y ⟶ X _⦋n + 1⦌` asks `φ ≫ X.δ j.succ = 0` for each `j : Fin (n + 1)` with `n + 1 ≤ j + q`. The key lemma is `HigherFacesVanish.induction`.

<?decl AlgebraicTopology.DoldKan.HigherFacesVanish?>
:::

**Definition (The projection $P_\infty$).** In degree $m$ the maps $P_q$ are equal for all $q \ge m$ (proved below). The chain map $P_\infty$ has degree $m$ component $(P_m)_m$, and $Q_\infty = \mathrm{id} - P_\infty$.

::: mathlib
`AlgebraicTopology.DoldKan.PInfty` · `Mathlib.AlgebraicTopology.DoldKan.PInfty`

`PInfty : K[X] ⟶ K[X]`, built with `ChainComplex.ofHom` from the components `(P n).f n`. The lemma `P_is_eventually_constant` justifies the choice, and `PInfty_idem` says `PInfty ≫ PInfty = PInfty`.

<?decl AlgebraicTopology.DoldKan.PInfty?>
:::

**Definition (The functor $\Gamma$).** Let $K$ be a chain complex in $C$ with finite coproducts. Set
$$\Gamma(K)_n = \bigoplus_{e : [n] \twoheadrightarrow [m]} K_m ,$$
a sum over the surjective monotone maps out of $[n]$. For $\theta : [n'] \to [n]$ and the summand of $e$, factor $e \circ \theta = i \circ e'$ with $e' : [n'] \twoheadrightarrow [m']$ surjective and $i : [m'] \to [m]$ injective. Then $\theta^*$ sends the summand $K_m$ of $e$ to the summand $K_{m'}$ of $e'$ by the map
$$K_m \to K_{m'} : \quad \mathrm{id} \ \text{ if } i = \mathrm{id}, \qquad d \ \text{ if } i = \delta^0 : [m-1] \to [m], \qquad 0 \ \text{ otherwise}.$$
The number of surjections $[n] \twoheadrightarrow [m]$ is $\binom{n}{m}$: such a map is fixed by the $m$ places among the $n$ gaps $j, j+1$ where it steps up.

::: mathlib
`AlgebraicTopology.DoldKan.Γ₀` · `Mathlib.AlgebraicTopology.DoldKan.FunctorGamma`

The functor `ChainComplex C ℕ ⥤ SimplicialObject C`. The map $K_m \to K_{m'}$ is `Γ₀.Obj.Termwise.mapMono K i`, with `mapMono_δ₀` for the differential and `mapMono_eq_zero` for the other monomorphisms; the test for $\delta^0$ is `Isδ₀`. The object comes with a splitting, `Γ₀.splitting K`, in the sense of Chapter 3.

<?decl AlgebraicTopology.DoldKan.Γ₀?>
:::

### Theorems and proofs

Throughout, $X$ is a simplicial object in a preadditive category, and the simplicial identities of Chapter 3 hold:
$$\delta_i \sigma_j = \sigma_{j-1}\delta_i \ (i < j), \quad \delta_j \sigma_j = \delta_{j+1}\sigma_j = \mathrm{id}, \quad \delta_i \sigma_j = \sigma_j \delta_{i-1} \ (i > j+1), \quad \sigma_j \sigma_i = \sigma_i \sigma_{j-1} \ (i < j).$$

**Lemma (One step of the projection).** Let $\varphi : Y \to X_m$ satisfy $\mathrm{HFV}_q$ and put $p = m - q$. If $p \ge 1$, then
$$(\mathrm{id} + H_\sigma^{(q)})\varphi = \varphi - \sigma_{p-1} \delta_p \varphi ,$$
and this map satisfies $\mathrm{HFV}_{q+1}$. If $p \le 0$, then $H_\sigma^{(q)} \varphi = 0$.

*Proof.* Let $p \ge 1$. In degree $m$, $H_\sigma^{(q)} = h_{m-1} d + d h_m$ with $h_{m-1} = (-1)^{p-1}\sigma_{p-1}$ and $h_m = (-1)^p \sigma_p$. The first part is $(-1)^{p-1} \sum_{i=0}^{m} (-1)^i \sigma_{p-1}\delta_i \varphi$, and the terms with $i \ge p+1$ vanish by $\mathrm{HFV}_q$. In the second part, $(-1)^p \sum_{k=0}^{m+1} (-1)^k \delta_k \sigma_p \varphi$, use the identities. For $k < p$ the term is $\sigma_{p-1}\delta_k\varphi$. The terms $k = p$ and $k = p+1$ are $\varphi$ with opposite signs and cancel. For $k \ge p+2$ the term is $\sigma_p \delta_{k-1}\varphi = 0$. So
$$H_\sigma^{(q)}\varphi = (-1)^{p-1}\sum_{i=0}^{p} (-1)^i \sigma_{p-1}\delta_i\varphi + (-1)^p \sum_{k=0}^{p-1} (-1)^k \sigma_{p-1}\delta_k\varphi = -\sigma_{p-1}\delta_p\varphi .$$
Let $\psi = \varphi - \sigma_{p-1}\delta_p\varphi$. Then $\delta_p\psi = \delta_p\varphi - \delta_p\varphi = 0$. For $i > p$, $\delta_i \sigma_{p-1}\delta_p = \sigma_{p-1}\delta_{i-1}\delta_p = \sigma_{p-1}\delta_p\delta_i$, and $\delta_i\varphi = 0$, so $\delta_i \psi = 0$. This is $\mathrm{HFV}_{q+1}$.

Let $p \le 0$. If $q > m$, both $h_{m-1}$ and $h_m$ vanish. If $q = m$, then $h_{m-1} = 0$ and $h_m = \sigma_0$, and $d\sigma_0\varphi = \varphi - \varphi + \sum_{k \ge 2} (-1)^k \sigma_0\delta_{k-1}\varphi = 0$, since $\delta_i \varphi = 0$ for all $i \ge 1$. $\square$

**Corollary (Formula for $P_\infty$).** In degree $m \ge 1$,
$$P_\infty = (\mathrm{id} - \sigma_0\delta_1)(\mathrm{id} - \sigma_1\delta_2)\cdots(\mathrm{id} - \sigma_{m-1}\delta_m),$$
where the factor on the right acts first. Its image satisfies $\mathrm{HFV}_m$, and $P_\infty \varphi = \varphi$ when $\varphi$ satisfies $\mathrm{HFV}_m$. In particular $P_q = P_m$ in degree $m$ for $q \ge m$.

*Proof.* The identity satisfies $\mathrm{HFV}_0$. Apply the lemma $m$ times, with $p = m, m-1, \dots, 1$. After these steps $p \le 0$, and the later factors act as the identity. If $\varphi$ already satisfies $\mathrm{HFV}_m$, each $\delta_p\varphi$ is zero and each factor fixes $\varphi$. $\square$

**Theorem (Degeneracies die).** For each $i$, $P_\infty \circ \sigma_i = 0$ as a map $X_{m-1} \to X_m$.

*Proof.* Apply the factors of the formula from the right. Consider a factor with $p > i+1$ acting on $\sigma_i y$. Then $\delta_p\sigma_i = \sigma_i\delta_{p-1}$ and $\sigma_{p-1}\sigma_i = \sigma_i\sigma_{p-2}$, so
$$(\mathrm{id} - \sigma_{p-1}\delta_p)\sigma_i y = \sigma_i(y - \sigma_{p-2}\delta_{p-1}y).$$
The result has the form $\sigma_i y'$ again. The next factor is the one with $p = i+1$, and $(\mathrm{id} - \sigma_i\delta_{i+1})\sigma_i y' = \sigma_i y' - \sigma_i y' = 0$. The remaining factors send $0$ to $0$. $\square$

::: mathlib
`AlgebraicTopology.DoldKan.σ_comp_PInfty` · `Mathlib.AlgebraicTopology.DoldKan.Degeneracies`

`X.σ i ≫ PInfty.f (n + 1) = 0`. The general form `degeneracy_comp_PInfty` kills `X.map θ.op` for each $\theta$ that is not injective.

<?decl AlgebraicTopology.DoldKan.σ_comp_PInfty?>
:::

**Theorem (Normalized and unnormalized chains).** Let $C$ be abelian. The inclusion $N(X) \to K(X)$ is a homotopy equivalence, with homotopy inverse $P_\infty : K(X) \to N(X)$. Each $X_m$ is the direct sum of $N(X)_m$ and the subobject $D_m$ generated by the images of the degeneracies.

*Proof.* Each $P_q$ is homotopic to the identity, by induction: $P_{q+1} = P_q + H_\sigma^{(q)} P_q$, and $H_\sigma^{(q)} P_q$ is null homotopic since $H_\sigma^{(q)}$ is. In each degree $P_\infty$ agrees with some $P_q$, and the homotopies of the $P_q$ agree in each degree from some $q$ on, so $P_\infty \simeq \mathrm{id}$. By the corollary $P_\infty$ lands in $N(X)$ and is the identity on $N(X)$. So $P_\infty \circ \mathrm{incl} = \mathrm{id}_{N(X)}$ and $\mathrm{incl} \circ P_\infty = P_\infty \simeq \mathrm{id}_{K(X)}$. For the sum, $P_\infty$ is idempotent with image $N_m$. Expand the product formula: $Q_\infty = \mathrm{id} - P_\infty$ is a sum of maps of the form $\sigma_j \circ (\cdots)$, so its image lies in $D_m$. By the theorem on degeneracies $P_\infty$ kills $D_m$, so $D_m \subseteq \ker P_\infty = \operatorname{im} Q_\infty$. So $D_m$ is the image of $Q_\infty$ and $X_m = N_m \oplus D_m$. $\square$

::: mathlib
`AlgebraicTopology.DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex` · `Mathlib.AlgebraicTopology.DoldKan.HomotopyEquivalence`

A `HomotopyEquiv` between `(normalizedMooreComplex A).obj X` and `(alternatingFaceMapComplex A).obj X`. The homotopy from `PInfty` to the identity is `homotopyPInftyToId`.

<?decl AlgebraicTopology.DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex?>
:::

The source of `Decomposition` notes that the degenerate subcomplex $D$ is not yet defined in Mathlib. The index of this edition has no declaration for $D$ or for the decomposition $X_m = N_m \oplus D_m$ as stated above; Mathlib uses $Q_\infty$ in its place, and `decomposition_Q` writes $Q_q$ as a sum of terms $\sigma \circ \delta \circ P$.

**Theorem (Dold-Kan correspondence).** Let $A$ be an abelian category. The functors $N$ and $\Gamma$ are inverse equivalences between simplicial objects in $A$ and chain complexes in $A$ indexed by $\mathbb{N}$.

*Proof.* First, $N\Gamma(K) \cong K$. Use $P_\infty$ in place of $N$, which is allowed by the last theorem. The summand of $e : [n] \twoheadrightarrow [m]$ with $m < n$ is the image of the summand $K_m$ of $\mathrm{id}_{[m]}$ under $e^*$, and $e^*$ factors through a degeneracy, so $P_\infty$ kills it. On the summand $K_n$ of $\mathrm{id}_{[n]}$, the face $\delta_i$ for $i \ge 1$ comes from $\delta^i$, an injective map that is not $\delta^0$, so it acts by $0$. So $\mathrm{HFV}_n$ holds on $K_n$ and $P_\infty$ is the identity there. Hence $N\Gamma(K)_n = K_n$, and the differential $\delta_0$ acts on $K_n$ by $d$, from the rule for $\delta^0$. These identifications are natural in $K$.

Second, $\Gamma N(X) \cong X$. Define $\Gamma N(X)_n \to X_n$ on the summand of $e$ by $e^* : N(X)_m \to X_n$. This is a simplicial map, by the same factorization rule and the fact that $P_\infty$ kills the images of non-injective maps. It is an epimorphism by induction on $n$: $X_n = N_n \oplus D_n$, and $D_n$ is covered by the $\sigma_j X_{n-1}$, which are covered by induction. Mathlib proves that it is an isomorphism by passing to idempotent completions. It shows that $\Gamma_2 N_2 \cong \mathrm{id}$ on the Karoubi envelope of simplicial objects, where both sides are compared through $P_\infty$, and that $N$ reflects isomorphisms. $\square$

::: mathlib
`CategoryTheory.Abelian.DoldKan.equivalence` · `Mathlib.AlgebraicTopology.DoldKan.Equivalence`

The equivalence `SimplicialObject A ≌ ChainComplex A ℕ` for an abelian category `A`. Its functor is `Abelian.DoldKan.N`, which is by definition `normalizedMooreComplex A`, and its inverse is `Abelian.DoldKan.Γ`. The isomorphism `comparisonN` compares `N` with the functor of the pseudoabelian case.

<?decl CategoryTheory.Abelian.DoldKan.equivalence?>
:::

::: mathlib
`CategoryTheory.Idempotents.DoldKan.equivalence` · `Mathlib.AlgebraicTopology.DoldKan.EquivalencePseudoabelian`

The same equivalence for an idempotent complete preadditive category `C` with finite coproducts. Here `N` is defined from `N₁`, which sends `X` to `K[X]` with the idempotent `PInfty` in the Karoubi envelope, and `Γ` is `Γ₀`.

<?decl CategoryTheory.Idempotents.DoldKan.equivalence?>
:::

::: mathlib
`CategoryTheory.Preadditive.DoldKan.equivalence` · `Mathlib.AlgebraicTopology.DoldKan.EquivalenceAdditive`

For any preadditive category `C` with finite coproducts, an equivalence `Karoubi (SimplicialObject C) ≌ Karoubi (ChainComplex C ℕ)` between the idempotent completions, with functors `N₂` and `Γ₂`. The two other forms are derived from it.

<?decl CategoryTheory.Preadditive.DoldKan.equivalence?>
:::

### Examples

**Example (Degree 0 and 1 of $N$).** In degree $1$, $P_\infty = \mathrm{id} - \sigma_0\delta_1$. Check: $\delta_1(x - \sigma_0\delta_1 x) = \delta_1 x - \delta_1 x = 0$, since $\delta_1\sigma_0 = \mathrm{id}$. So $N_1 = \ker\delta_1$, and every $x \in X_1$ splits as $(x - \sigma_0\delta_1 x) + \sigma_0(\delta_1 x)$, with the first term in $N_1$ and the second degenerate. In degree $0$, $P_\infty = \mathrm{id}$ and $N_0 = X_0$. The differential $N_1 \to N_0$ is $\delta_0$.

**Example (Degree 0 and 1 of $\Gamma$).** Let $K$ be a complex of abelian groups. Then $\Gamma(K)_0 = K_0$, and $\Gamma(K)_1 = K_1 \oplus K_0$, with the summands of $\mathrm{id}_{[1]}$ and of $[1] \twoheadrightarrow [0]$. The faces are
$$\delta_0(x, y) = dx + y, \qquad \delta_1(x, y) = y,$$
and the degeneracy is $\sigma_0(y) = (0, y)$. The rule gives these maps: on the summand $K_1$, $\delta_0$ comes from $\delta^0$ and acts by $d$, while $\delta_1$ comes from $\delta^1$ and acts by $0$; on the summand $K_0$, both composites $[0] \to [1] \to [0]$ are the identity. Check the identities: $\delta_0\sigma_0 y = y$ and $\delta_1\sigma_0 y = y$. Then $N(\Gamma K)_1 = \ker\delta_1 = \{(x, 0)\} \cong K_1$, and $\delta_0(x, 0) = dx$. So $N\Gamma K$ agrees with $K$ in degrees $0$ and $1$. In degree $2$, $\Gamma(K)_2 = K_2 \oplus K_1 \oplus K_1 \oplus K_0$, with $\binom{2}{1} = 2$ copies of $K_1$.

**Example (Eilenberg-MacLane objects).** Let $K = \mathbb{Z}[1]$, the complex with $\mathbb{Z}$ in degree $1$ and $0$ elsewhere. Then $\Gamma(K)_n = \mathbb{Z}^{\binom{n}{1}} = \mathbb{Z}^n$. The only nonzero homology of $K$ is in degree $1$. The simplicial abelian group $\Gamma(K)$ is a model of the circle as a $K(\mathbb{Z}, 1)$. For $K = \mathbb{Z}[0]$, $\Gamma(K)$ is the constant simplicial group $\mathbb{Z}$.

**Example (A Lean statement).** The inverse functor of the abelian equivalence is $\Gamma$ by definition.

```lean
open CategoryTheory in
example {A : Type*} [Category A] [Abelian A] :
    (Abelian.DoldKan.equivalence : SimplicialObject A ≌ ChainComplex A ℕ).inverse =
      Abelian.DoldKan.Γ :=
  Abelian.DoldKan.equivalence_inverse
```

### The library around it

The proof in Mathlib runs through idempotent completions. The functor `N₁` sends $X$ to the pair $(K(X), P_\infty)$ in the Karoubi envelope of chain complexes, which avoids kernels and so works in any preadditive category. The equivalence of Karoubi envelopes in `EquivalenceAdditive` is the core result. For an idempotent complete category the Karoubi envelope adds nothing, which gives `Idempotents.DoldKan.equivalence`. For an abelian category `comparisonN` replaces `N₁` by the normalized Moore complex.

::: mathlib
`CategoryTheory.SimplicialObject.Splitting.homotopyEquivNondegComplex` · `Mathlib.AlgebraicTopology.DoldKan.SplitSimplicialObject`

For a split simplicial object, the complex `Splitting.nondegComplex` of the nondegenerate summands is homotopy equivalent to the alternating face map complex. Section 1 uses this for the normalized chains of a simplicial set.

<?decl CategoryTheory.SimplicialObject.Splitting.homotopyEquivNondegComplex?>
:::

The file `Compatibility` gives a general tool that builds an equivalence with good definitional properties from a weaker one; it is how `Abelian.DoldKan.equivalence` has `Γ` as its inverse by `rfl`. The index of this edition has no declaration that the homotopy groups of a simplicial abelian group are the homology groups of its Moore complex.

Common errors of a learner: The first error is to include $\delta_0$ in the definition of $N$. The second error is to read $P_q$ as a projection onto $N$ for every $q$; it only kills the last $q$ faces, and the limit $P_\infty$ is the projection. The third error is to look for `AlgebraicTopology.DoldKan.equivalence`. The equivalence lives in the namespaces `CategoryTheory.Abelian.DoldKan`, `CategoryTheory.Idempotents.DoldKan` and `CategoryTheory.Preadditive.DoldKan`, and `AlgebraicTopology.DoldKan.Compatibility.equivalence` is the general tool. The fourth error is to forget the order of composition: `P (q + 1) = P q ≫ (𝟙 _ + Hσ q)` applies $P_q$ first.

### Exercises

1. (A) Let $X$ be the constant simplicial abelian group with value $M$. Show that $N(X)_0 = M$ and $N(X)_n = 0$ for $n \ge 1$. *Hint:* all faces are the identity.
2. (A) Write out $\Gamma(K)_2$ for a complex $K$ of abelian groups and compute the face $\delta_1 : \Gamma(K)_2 \to \Gamma(K)_1$ on each of the four summands. *Hint:* factor $e \circ \delta^1$ as a surjection followed by an injection.
3. (A) Show from the formula for $P_\infty$ that in degree $2$, $P_\infty = (\mathrm{id} - \sigma_0\delta_1)(\mathrm{id} - \sigma_1\delta_2)$, and check directly that $\delta_1 P_\infty = \delta_2 P_\infty = 0$. *Hint:* use $\delta_2\sigma_0 = \sigma_0\delta_1$.
4. (B) Let $K = \mathbb{Z}[1]$. Compute the faces $\Gamma(K)_2 = \mathbb{Z}^2 \to \Gamma(K)_1 = \mathbb{Z}$. *Hint:* the two summands come from $\sigma^0, \sigma^1 : [2] \to [1]$.
5. (B) Show that a map of simplicial abelian groups $f$ is an isomorphism if $N(f)$ is an isomorphism. *Hint:* use the equivalence, or the decomposition $X_n = \bigoplus_e e^*N_m$.
6. (C) Show that $Q_\infty$ restricted to $D_m$ is the identity, and deduce that the complex $D$ of degenerate chains is contractible in the abelian case. *Hint:* $K(X) = N(X) \oplus D$ as complexes, and $N(X) \to K(X)$ is a homotopy equivalence.
7. (C) Let $K$ be the complex $\mathbb{Z} \xrightarrow{1} \mathbb{Z}$ in degrees $1$ and $0$. Show that $\Gamma(K)_n \cong \mathbb{Z}^{n+1}$. Let $Z$ be the quotient of the free simplicial abelian group $\mathbb{Z}[\Delta[1]]$ by the constant subgroup spanned by the vertex $0$ and its degeneracies. Show that $\Gamma(K) \cong Z$. *Hint:* compute $N(Z)$ from the nondegenerate simplices $[01]$ and $1$, and use the equivalence.

### Notes and history

Dold and Kan found the correspondence independently and published it in 1958. Kan studied simplicial sets and their homotopy theory from 1955. The approach through the projections $P_q$ and the Karoubi envelope follows the comments in the source file `Equivalence`, which cites the book *Simplicial Homotopy Theory* by Goerss and Jardine for the definition of $\Gamma$.

The Mathlib Authors of all files in `AlgebraicTopology.DoldKan`: Joël Riou.

### Reference

<?reference?>
