---
title: Functoriality, long exact sequences and cyclic groups
kind: theory
modules:
  - Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
  - Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
  - Mathlib.RepresentationTheory.Homological.GroupHomology.LongExactSequence
  - Mathlib.RepresentationTheory.Homological.FiniteCyclic
  - Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic
  - Mathlib.RepresentationTheory.Homological.GroupHomology.FiniteCyclic
  - Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro
  - Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
explains:
  E3: [groupCohomology.map, groupCohomology.δ, groupCohomology.isIso_δ_of_isZero, Rep.FiniteCyclicGroup.groupCohomologyIsoEven, Rep.FiniteCyclicGroup.groupCohomologyIsoOdd, groupCohomology.coindIso, tateCohomology, TateCohomology.isoGroupCohomology]
  E2: [groupCohomology.H1InfRes_exact, Rep.FiniteCyclicGroup.groupHomologyIsoOdd, groupCohomology.map_cochainsFunctor_shortExact, Rep.FiniteCyclicGroup.resolution, groupCohomology.cochainsMap, groupCohomology.map_id, groupCohomology.map_comp, groupCohomology.map_eq_zero, groupCohomology.HInfRes, groupCohomology.functor, groupCohomology.resNatTrans, groupCohomology.infNatTrans, groupCohomology.mapShortComplex₂_exact, groupCohomology.δ_naturality, groupHomology.δ, groupHomology.mapShortComplex₂_exact, Rep.FiniteCyclicGroup.leftRegular.range_norm_eq_ker_applyAsHom_sub, Rep.FiniteCyclicGroup.leftRegular.range_applyAsHom_sub_eq_ker_norm, Rep.FiniteCyclicGroup.normHomCompSub, Rep.FiniteCyclicGroup.subCompNormHom, Rep.FiniteCyclicGroup.groupCohomologyIso₀, Rep.FiniteCyclicGroup.groupHomologyIso₀, Rep.FiniteCyclicGroup.groupHomologyIsoEven, Rep.tateNorm, Rep.tateNorm_eq, Rep.tateNorm_comp_d, tateComplex, tateComplexFunctor, tateCohomologyFunctor, tateComplex_d_neg_one, TateCohomology.δ, TateCohomology.exact₁, TateCohomology.exact₃, TateCohomology.map_tateComplexFunctor_shortExact, TateCohomology.isoGroupHomology]
  E1: auto
families: []
requires: [V25.C02, V26.C02, V26.C03, V26.C04, V26.C07]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Functoriality, long exact sequences and cyclic groups

### Overview

Sections 1 and 2 treat one pair $(G, A)$ at a time. This section relates different pairs. A homomorphism of groups with a compatible map of modules gives a map in cohomology, with restriction and inflation as the main cases. A short exact sequence of representations gives a long exact sequence. Shapiro's lemma computes the cohomology of a subgroup as the cohomology of the group with coinduced coefficients.

For a finite cyclic group the trivial module has a resolution of period $2$, and the cohomology alternates between two explicit groups. The last part describes Tate cohomology, which joins homology and cohomology of a finite group in one sequence indexed by $\mathbb{Z}$. In the text $g \circ f$ is the textbook composite, and Mathlib writes `f ≫ g`. As in Section 2, $g \cdot a$ means $\rho(g)(a)$.

### Definitions

**Definition (The map of a compatible pair).** Let $f \colon G \to H$ be a homomorphism of groups, let $A$ be a representation of $H$ and let $B$ be a representation of $G$. Write $f^* A$ for $A$ with $G$ acting through $f$. A compatible pair is $(f, \varphi)$ with $\varphi \colon f^* A \to B$ a map of representations of $G$. The map $x \mapsto \varphi \circ x \circ f^n$ on inhomogeneous cochains commutes with the differentials and gives $H^n(H, A) \to H^n(G, B)$.

For a subgroup $S \le G$, the inclusion $S \to G$ with $\varphi = \mathrm{id}$ gives the restriction $\mathrm{res} \colon H^n(G, A) \to H^n(S, A)$. For a normal subgroup $S$, the quotient map $G \to G/S$ with the inclusion $A^S \to A$ gives the inflation $\mathrm{inf} \colon H^n(G/S, A^S) \to H^n(G, A)$. Here $A^S$ is a representation of $G/S$ because $S$ acts trivially on it.

::: mathlib
`groupCohomology.map` · `Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality`

For `f : G →* H` and `φ : res f A ⟶ B`, the term `map f φ n` is the map $H^n(H, A) \to H^n(G, B)$. It is induced by `cochainsMap f φ`. The lemmas `map_id` and `map_comp` state functoriality, and `map_eq_zero` states that the map is zero in degrees $n \ge 1$ when `f` is trivial. The functor $H^n(G, -)$ is `groupCohomology.functor k G n`. Restriction and inflation are `resNatTrans` and `infNatTrans`, and `H1InfRes_exact` is the exactness of the inflation and restriction sequence below.

<?decl groupCohomology.map?>
:::

**Definition (Coinduced representation).** Let $S \le G$ be a subgroup and let $A$ be a representation of $S$. The coinduced representation is $\mathrm{Coind}_S^G A = \mathrm{Hom}_{k[S]}(k[G], A)$, the $k$-module of functions $\phi \colon G \to A$ with $\phi(s g) = s \cdot \phi(g)$ for $s \in S$, with $G$ acting by $(g \cdot \phi)(x) = \phi(x g)$. The restriction functor $\mathrm{Res} \colon \mathrm{Rep}_k G \to \mathrm{Rep}_k S$ is left adjoint to $\mathrm{Coind}$: a map $\psi \colon \mathrm{Res}\, M \to A$ corresponds to $m \mapsto (g \mapsto \psi(g \cdot m))$.

**Definition (Norm element).** Let $G$ be a finite group. The norm element of $k[G]$ is $N = \sum_{h \in G} h$. On a representation $A$ it acts by $N a = \sum_h h \cdot a$. The image $N A$ lies in $A^G$, and the augmentation ideal $I_G$, spanned by the elements $h - 1$, satisfies $I_G A \subseteq \ker N$.

**Definition (Tate complex).** Let $G$ be finite. The Tate complex of $A$ is the complex indexed by $\mathbb{Z}$ that has the inhomogeneous chains $C_n(G, A)$ in degree $-(n + 1)$ for $n \ge 0$, the inhomogeneous cochains $C^n(G, A)$ in degree $n \ge 0$, and the norm map $C_0(G, A) = A \to A = C^0(G, A)$, $a \mapsto N a$, as the differential from degree $-1$ to degree $0$. The Tate cohomology $\hat{H}^n(G, A)$ is the homology of this complex in degree $n$.

It is a complex because $N(g a - a) = 0$ and $g N a = N a$.

::: mathlib
`tateComplex` · `Mathlib.RepresentationTheory.Homological.TateCohomology.Basic`

`tateComplex M` is a term of `CochainComplex (ModuleCat R) ℤ`. The lemma `tateComplex_d_neg_one` identifies its differential from degree $-1$ to degree $0$ with `Rep.tateNorm M`. The lemmas `Rep.tateNorm_comp_d` and `Rep.d_comp_tateNorm` are the two zero composites above.

<?decl tateComplex?>
:::

### Theorems and proofs

**Theorem (Inflation and restriction).** Let $S$ be a normal subgroup of $G$ and $A$ a representation of $G$. The sequence $0 \to H^1(G/S, A^S) \xrightarrow{\mathrm{inf}} H^1(G, A) \xrightarrow{\mathrm{res}} H^1(S, A)$ is exact.

*Proof.* Write $\pi \colon G \to G/S$. The composite is zero: for a cocycle $f$ of $G/S$, $\mathrm{res}(\mathrm{inf} f)(s) = f(\pi(s)) = f(1) = 0$, since cocycles vanish at $1$ (Section 2). Injectivity of inflation: suppose $f \circ \pi$ is a coboundary, $f(\pi(g)) = g a - a$ for some $a \in A$. For $s \in S$ this gives $0 = f(1) = s a - a$, so $a \in A^S$. So $f$ is the coboundary of $a \in A^S$ on $G/S$. Exactness at $H^1(G, A)$: let $f$ be a $1$-cocycle of $G$ whose restriction to $S$ is a coboundary, $f(s) = s a - a$. Replace $f$ by $f - da$; now $f(s) = 0$ for $s \in S$. The cocycle condition gives $f(g s) = f(g) + g f(s) = f(g)$, so $f$ is constant on the cosets $g S$. It also gives $f(s g) = f(s) + s f(g) = s f(g)$. Since $S$ is normal, $s g = g s'$ with $s' = g^{-1} s g \in S$, so $f(s g) = f(g)$. Thus $s f(g) = f(g)$ for all $s$, and $f$ takes values in $A^S$. Hence $f = \bar{f} \circ \pi$ for a function $\bar{f} \colon G/S \to A^S$, a cocycle, and $[f] = \mathrm{inf}[\bar{f}]$. $\square$

**Theorem (Long exact sequence).** Let $0 \to A \to B \to C \to 0$ be a short exact sequence of representations of $G$. There are connecting maps $\delta \colon H^n(G, C) \to H^{n+1}(G, A)$ such that the sequence $0 \to H^0(G, A) \to H^0(G, B) \to H^0(G, C) \xrightarrow{\delta} H^1(G, A) \to \cdots$ is exact, and $\delta$ is natural in the short exact sequence. The same holds for homology, with $\delta \colon H_{n+1}(G, C) \to H_n(G, A)$.

*Proof.* In degree $n$ the cochain functor sends $A$ to $\mathrm{Fun}(G^n, A)$, and $0 \to \mathrm{Fun}(G^n, A) \to \mathrm{Fun}(G^n, B) \to \mathrm{Fun}(G^n, C) \to 0$ is exact, since exactness is checked pointwise. The long exact sequence of homology of Chapter 2 gives the result. For homology the chain functor sends $A$ to $\bigoplus_{G^n} A$, and a direct sum of short exact sequences is short exact. $\square$

The connecting map has the usual description. Let $z$ be an $n$-cocycle of $C$. Lift it to an $n$-cochain $y$ of $B$. Then $d y$ maps to $d z = 0$ in $C$, so $d y = x$ for a unique $(n+1)$-cochain $x$ of $A$, and $x$ is a cocycle. Then $\delta[z] = [x]$.

::: mathlib
`groupCohomology.δ` · `Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence`

For `hX : X.ShortExact` with `X : ShortComplex (Rep k G)`, `map_cochainsFunctor_shortExact hX` is the short exact sequence of cochain complexes, and `δ hX i j hij` with `hij : i + 1 = j` is the connecting map. Exactness at the three places is `mapShortComplex₁_exact`, `mapShortComplex₂_exact` and `mapShortComplex₃_exact`; naturality is `δ_naturality`. `δ_apply` is the cochain description above, and `groupHomology.δ` is the homology version.

<?decl groupCohomology.δ?>
:::

**Corollary (Isomorphic connecting maps).** If $H^n(G, B) = 0$ and $H^{n+1}(G, B) = 0$, then $\delta \colon H^n(G, C) \to H^{n+1}(G, A)$ is an isomorphism.

*Proof.* The part $H^n(G, B) \to H^n(G, C) \to H^{n+1}(G, A) \to H^{n+1}(G, B)$ of the long exact sequence has zero ends, so $\delta$ is injective and surjective. $\square$

This is `groupCohomology.isIso_δ_of_isZero`, the basis of dimension shifting.

**Theorem (Shapiro's lemma).** Let $S \le G$ and let $A$ be a representation of $S$. For each $n$ there is an isomorphism $H^n(G, \mathrm{Coind}_S^G A) \cong H^n(S, A)$.

*Proof.* Let $P_\bullet \to k$ be a projective resolution of the trivial representation of $G$. Its right adjoint $\mathrm{Coind}$ preserves epimorphisms: a surjection $A \to A'$ of $k[S]$-modules induces a surjection $\mathrm{Hom}_{k[S]}(k[G], A) \to \mathrm{Hom}_{k[S]}(k[G], A')$, because $k[G]$ is a free $k[S]$-module on a set of coset representatives. For a projective $P$ of $\mathrm{Rep}_k G$, the functor $\mathrm{Hom}(\mathrm{Res}\, P, -) \cong \mathrm{Hom}(P, \mathrm{Coind}\, -)$ is the composite of $\mathrm{Coind}$, which preserves epimorphisms, and $\mathrm{Hom}(P, -)$, which preserves epimorphisms; so $\mathrm{Res}\, P$ is projective. Thus $\mathrm{Res}\, P_\bullet \to k$ is a projective resolution of the trivial representation of $S$. The adjunction gives isomorphisms of complexes $\mathrm{Hom}_{k[G]}(P_\bullet, \mathrm{Coind}\, A) \cong \mathrm{Hom}_{k[S]}(\mathrm{Res}\, P_\bullet, A)$. Their homology is $H^n(G, \mathrm{Coind}\, A)$ on the left and $H^n(S, A)$ on the right, since the cohomology does not depend on the resolution (Chapter 4). $\square$

::: mathlib
`groupCohomology.coindIso` · `Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro`

For `S : Subgroup G` and `A : Rep k S`, `coindIso A n` is an isomorphism `groupCohomology (coind S.subtype A) n ≅ groupCohomology A n`. The proof restricts the bar resolution, as above. The homology version, with induction, is `groupHomology.indIso` in `Mathlib.RepresentationTheory.Homological.GroupHomology.Shapiro`.

<?decl groupCohomology.coindIso?>
:::

Now let $G$ be a finite cyclic group of order $n$ with generator $g$. Then $k[G]$ is commutative.

**Theorem (Periodic resolution).** The sequence $\cdots \xrightarrow{g - 1} k[G] \xrightarrow{N} k[G] \xrightarrow{g - 1} k[G] \xrightarrow{N} k[G] \xrightarrow{g - 1} k[G] \xrightarrow{\varepsilon} k \to 0$, where the maps are multiplication by $g - 1$ and $N$ in alternation and $\varepsilon$ is the augmentation, is a free resolution of the trivial representation $k$.

*Proof.* Each term is free of rank $1$ over $k[G]$. Write $x = \sum_{i=0}^{n-1} a_i g^i$. The kernel of $\varepsilon$ is the augmentation ideal $I_G$, spanned by the elements $g^i - 1$. Since $g^i - 1 = (g - 1)(1 + g + \cdots + g^{i-1})$, the ideal $I_G$ equals $(g - 1) k[G]$, the image of multiplication by $g - 1$. Next, $(g - 1) x = 0$ means $g x = x$, that is $a_{i-1} = a_i$ for all $i$ with indices mod $n$, so $x = a_0 N$. Thus $\ker(g - 1) = k N$, which is the image of multiplication by $N$, since $N \cdot a = a N$ for $a \in k$ and $N y = \varepsilon(y) N$ for all $y$. Finally $N x = (\sum_i a_i) N$, so $\ker N = \ker \varepsilon = I_G = \mathrm{im}(g - 1)$. These three facts are exactness at each place. $\square$

**Theorem (Cohomology of a finite cyclic group).** Let $A$ be a representation of the cyclic group $G$ of order $n$ with generator $g$. Then $H^0(G, A) = A^G$, $H^i(G, A) \cong \ker N / (g - 1) A$ for $i$ odd, and $H^i(G, A) \cong A^G / N A$ for $i$ even and nonzero. For homology, $H_0(G, A) = A / (g - 1) A$, $H_i(G, A) \cong A^G / N A$ for $i$ odd, and $H_i(G, A) \cong \ker N / (g - 1) A$ for $i$ even and nonzero.

*Proof.* Use the periodic resolution in the Ext description of Section 1. The map $\mathrm{Hom}_{k[G]}(k[G], A) \to A$, $\psi \mapsto \psi(1)$, is an isomorphism, and under it multiplication by $r \in k[G]$ on $k[G]$ becomes the map $a \mapsto r a$ on $A$. So the cochain complex is $A \xrightarrow{g - 1} A \xrightarrow{N} A \xrightarrow{g - 1} A \xrightarrow{N} \cdots$, with $A$ in degree $0$. Its homology is $\ker(g - 1) = A^G$ in degree $0$, since $g$ generates $G$, then $\ker N / \mathrm{im}(g - 1)$ in odd degree and $\ker(g - 1) / \mathrm{im}\, N = A^G / N A$ in even nonzero degree. For homology, apply $A \otimes_{k[G]} -$ and use $A \otimes_{k[G]} k[G] \cong A$. The chain complex is $\cdots \xrightarrow{N} A \xrightarrow{g - 1} A$ with the last $A$ in degree $0$. Its homology gives the stated groups in the same way. $\square$

::: mathlib
`Rep.FiniteCyclicGroup.groupCohomologyIsoOdd` · `Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic`

`Rep.FiniteCyclicGroup.resolution k g hg` is the periodic projective resolution of the trivial representation, for `[CommGroup G] [Fintype G]` and a proof `hg` that `g` generates `G`. Two `leftRegular` lemmas give its exactness. `groupCohomologyIsoOdd` identifies $H^i(G, A)$ for odd `i` with the homology of the short complex `subCompNormHom A g`, that is $A \xrightarrow{g - 1} A \xrightarrow{N} A$. `groupCohomologyIsoEven` needs `[NeZero i]` and uses `normHomCompSub A g`, that is $A \xrightarrow{N} A \xrightarrow{g - 1} A$. `groupCohomologyIso₀` is degree $0$. The homology versions `groupHomologyIso₀`, `groupHomologyIsoOdd` and `groupHomologyIsoEven` are in `GroupHomology.FiniteCyclic`.

<?decl Rep.FiniteCyclicGroup.groupCohomologyIsoOdd?>
:::

**Theorem (Tate cohomology and ordinary cohomology).** Let $G$ be finite. Then $\hat{H}^n(G, A) \cong H^n(G, A)$ for $n \ge 1$, $\hat{H}^{-(n+1)}(G, A) \cong H_n(G, A)$ for $n \ge 1$, $\hat{H}^0(G, A) = A^G / N A$ and $\hat{H}^{-1}(G, A) = \ker N / I_G A$. A short exact sequence of representations gives a long exact sequence of Tate cohomology indexed by $\mathbb{Z}$.

*Proof.* For $n \ge 1$ the Tate complex agrees with the cochain complex in degrees $n - 1$, $n$ and $n + 1$, so the homology agrees. In the same way the degrees $-n$, $-(n+1)$, $-(n+2)$ carry the chains of degrees $n - 1$, $n$, $n + 1$, so $\hat{H}^{-(n+1)} = H_n$. In degree $0$ the cycles are $\ker d^0 = A^G$ and the boundaries are $N A$. In degree $-1$ the cycles are $\ker N$ and the boundaries are the image of $d_1 \colon C_1(G, A) \to A$, which is $I_G A$ by Section 2. For the long exact sequence, each term of the Tate complex is a chain or cochain module, so the Tate complex functor is exact degreewise. $\square$

::: mathlib
`TateCohomology.isoGroupCohomology` · `Mathlib.RepresentationTheory.Homological.TateCohomology.Basic`

`isoGroupCohomology n` with `[NeZero n]` is a natural isomorphism `tateCohomologyFunctor n ≅ groupCohomology.functor R G n`. `isoGroupHomology m n hmn` with `hmn : m = -(n + 1)` is the homology case. The long exact sequence uses `map_tateComplexFunctor_shortExact`, `TateCohomology.δ`, `exact₁` and `exact₃`. The index of this edition has no declaration for the identification of $\hat{H}^0$ with $A^G / N A$ or of $\hat{H}^{-1}$ with $\ker N / I_G A$.

<?decl TateCohomology.isoGroupCohomology?>
:::

### Examples

**Example (Trivial coefficients $\mathbb{Z}$).** Let $G = \mathbb{Z}/n$ act trivially on $\mathbb{Z}$. Then $g - 1 = 0$ and $N$ is multiplication by $n$. The theorem gives $H^0 = \mathbb{Z}$, $H^i = \ker(n) / 0 = 0$ for $i$ odd and $H^i = \mathbb{Z}/n$ for $i$ even and nonzero. In homology $H_i = \mathbb{Z}/n$ for $i$ odd and $0$ for $i$ even and nonzero; $H_1 = \mathbb{Z}/n$ agrees with $H_1(G, \mathbb{Z}) = G^{\mathrm{ab}}$ of Section 2.

**Example (The group $H^2(\mathbb{Z}/2, \mathbb{Z}/2)$).** Let $G = \mathbb{Z}/2$ act trivially on $\mathbb{Z}/2$. Then $g - 1 = 0$ and $N = 2 = 0$. Every $H^i$ is $\mathbb{Z}/2$. In particular $H^2(\mathbb{Z}/2, \mathbb{Z}/2) \cong \mathbb{Z}/2$, the value used in Section 2.

**Example (Dimension shifting with $\mathbb{Q}/\mathbb{Z}$).** Let $G = \mathbb{Z}/n$ act trivially on the short exact sequence $0 \to \mathbb{Z} \to \mathbb{Q} \to \mathbb{Q}/\mathbb{Z} \to 0$. For $B = \mathbb{Q}$, $N = n$ is bijective and $g - 1 = 0$, so $H^i(G, \mathbb{Q}) = \ker(n) = 0$ for $i$ odd and $\mathbb{Q}/n\mathbb{Q} = 0$ for $i$ even and nonzero. The corollary on connecting maps gives $H^1(G, \mathbb{Q}/\mathbb{Z}) \cong H^2(G, \mathbb{Z})$. The left side is $\mathrm{Hom}(\mathbb{Z}/n, \mathbb{Q}/\mathbb{Z}) \cong \mathbb{Z}/n$ by Section 2, and the right side is $\mathbb{Z}/n$ by the first example. For a general finite group the same argument gives $H^2(G, \mathbb{Z}) \cong \mathrm{Hom}(G, \mathbb{Q}/\mathbb{Z})$, once one knows that $|G|$ kills $H^i(G, A)$ for $i \ge 1$; this section does not prove that fact.

**Example (Hilbert 90 for a cyclic extension).** Let $L/K$ be cyclic Galois with group generated by $\sigma$, and $A = L^\times$. The odd case gives $H^1(G, L^\times) \cong \{x : N_{L/K}(x) = 1\} / \{\sigma(y)/y\}$, so Noether's form of Hilbert 90 (Section 2) gives the classical form. The even case gives $H^2(G, L^\times) \cong K^\times / N_{L/K}(L^\times)$.

### The library around it

The functoriality file also builds the maps by hand in degrees $1$ and $2$, with `mapShortComplexH1` and `mapShortComplexH2`, so that the descriptions of Section 2 are functorial.

Restriction and coinduction live outside the homological folder: `Rep.res` in `Mathlib.RepresentationTheory.Rep.Res`, and `Rep.coind` with `Rep.resCoindAdjunction` in `Mathlib.RepresentationTheory.Coinduced`. Volume 29 treats them.

::: mathlib
`tateCohomology` · `Mathlib.RepresentationTheory.Homological.TateCohomology.Basic`

`tateCohomology M n` is the homology of `tateComplex M` in degree `n : ℤ`.

<?decl tateCohomology?>
:::

Common errors of a learner: The first error is to state the cyclic group theorems without a generator; the declarations take `g` and a proof that it generates, and the answer depends on $g$ only through $g - 1$. The second error is to use the even case in degree $0$; `groupCohomologyIsoEven` needs `[NeZero i]`, and in degree $0$ the answer is $A^G$, not $A^G / N A$. The third error is to confuse the degrees of Tate cohomology: chains of degree $n$ sit in degree $-(n + 1)$, so $H_1$ is $\hat{H}^{-2}$, not $\hat{H}^{-1}$.

### Exercises

1. (A) Compute $H^i(\mathbb{Z}/3, \mathbb{Z}/3)$ and $H^i(\mathbb{Z}/3, \mathbb{Z}/2)$ for trivial actions and all $i$. Hint: $N$ is multiplication by $3$.
2. (A) Let $G = \mathbb{Z}/2$ act on $\mathbb{Z}^2$ by swapping the coordinates. Show that $H^i(G, \mathbb{Z}^2) = 0$ for $i \ge 1$. Hint: $\ker N = \mathbb{Z}(1, -1) = (g - 1)\mathbb{Z}^2$ and $A^G = \mathbb{Z}(1,1) = N A$.
3. (B) Show that $H^n(G, \mathrm{Coind}_1^G A) = 0$ for $n \ge 1$, where $1$ is the trivial subgroup. Deduce that each representation embeds in one with $H^n = 0$ for $n \ge 1$. Hint: Shapiro's lemma and the map $a \mapsto (g \mapsto g a)$.
4. (B) Let $G = \mathbb{Z}/n$ act trivially on $0 \to \mathbb{Z} \xrightarrow{n} \mathbb{Z} \to \mathbb{Z}/n \to 0$. Write the long exact sequence in degrees $0$ to $3$ and check it against the computed groups. Hint: the map $H^2(G, \mathbb{Z}) \to H^2(G, \mathbb{Z})$ is multiplication by $n$, which is zero on $\mathbb{Z}/n$.
5. (B) Prove that the inflation map $H^1(G/S, A^S) \to H^1(G, A)$ is an isomorphism when $H^1(S, A) = 0$. Hint: the theorem of inflation and restriction.
6. (C) The Herbrand quotient of a representation $A$ of a cyclic group is $h(A) = |\hat{H}^0(G, A)| / |\hat{H}^{-1}(G, A)|$ when both are finite. Show that $h$ is multiplicative in short exact sequences. Hint: the long exact sequence of Tate cohomology is periodic of period $2$, so it becomes an exact hexagon.

### Notes and history

The periodic resolution of a cyclic group and the computation of its cohomology are in Cartan and Eilenberg's book of 1956, and the cohomology of groups goes back to Eilenberg and MacLane. Tate introduced his cohomology for class field theory.

The Mathlib files are by these authors, read from their headers: `GroupCohomology.Functoriality`, `GroupCohomology.LongExactSequence`, `GroupHomology.LongExactSequence`, `FiniteCyclic`, `GroupCohomology.FiniteCyclic`, `GroupHomology.FiniteCyclic` and `GroupCohomology.Shapiro` by Amelia Livingston; `TateCohomology.Basic` by Yunzhou Xie and Yaël Dillies.

### Reference

<?reference?>
