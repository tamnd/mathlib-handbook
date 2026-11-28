---
title: The standard resolution
kind: theory
modules:
  - Mathlib.RepresentationTheory.Homological.Resolution
  - Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic
  - Mathlib.RepresentationTheory.Homological.GroupHomology.Basic
explains:
  E3: [Rep.standardResolution, Rep.barResolution, Rep.barComplex.isoStandardComplex, Rep.standardComplex.forget₂ToModuleCatHomotopyEquiv, inhomogeneousCochains.d, groupCohomology, groupCohomologyIsoExt, groupCohomologyIso, groupHomology, groupHomologyIsoTor]
  E2: [Rep.standardComplex, Rep.standardComplex.d, Rep.standardComplex.d_eq, Rep.standardComplex.ε, Rep.standardComplex.d_comp_ε, Rep.standardComplex.x_projective, Rep.standardComplex.quasiIso_forget₂_εToSingle₀, classifyingSpaceUniversalCover, classifyingSpaceUniversalCover.extraDegeneracyAugmentedCechNerve, classifyingSpaceUniversalCover.cechNerveTerminalFromIso, Rep.standardResolution.extIso, Rep.barComplex, Rep.barComplex.d, Rep.barComplex.d_single, Rep.barResolution.extIso, Rep.instHasExt, inhomogeneousCochains.d_eq, groupCohomology.inhomogeneousCochains, groupCohomology.inhomogeneousCochains.d_def, groupCohomology.inhomogeneousCochains.d_comp_d, groupCohomology.inhomogeneousCochainsIso, groupCohomology.cocycles, groupCohomology.cocyclesMk, groupCohomology.π, isZero_groupCohomology_succ_of_subsingleton, groupHomology.inhomogeneousChains, groupHomology.inhomogeneousChains.d, groupHomology.inhomogeneousChainsIso, groupHomology.cycles, groupHomology.π, Rep.Tor, groupHomologyIso, Rep.isZero_Tor_succ_of_projective, isZero_groupHomology_succ_of_subsingleton]
  E1: auto
families: []
requires: [V05.C06, V25.C02, V26.C03, V26.C04, V26.C07]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The standard resolution

### Overview

Let $G$ be a group and $k$ a commutative ring. A $k$-linear representation of $G$ is a $k$-module $A$ with an action of $G$ by $k$-linear maps $\rho(g) \colon A \to A$. It is the same as a module over the group algebra $k[G]$. The trivial representation is $k$ itself, with each $g$ acting as the identity. Group cohomology is the derived functor of the invariants $A \mapsto A^G = \mathrm{Hom}_{k[G]}(k, A)$, so by Chapter 4 it is
$$H^n(G, A) = \mathrm{Ext}^n_{k[G]}(k, A).$$
Group homology is the derived functor of the coinvariants $A \mapsto A_G = k \otimes_{k[G]} A$, so it is $\mathrm{Tor}_n^{k[G]}(k, A)$.

To compute these groups, one needs a projective resolution of the trivial module $k$. This section builds the standard one, proves that it is a projective resolution, and translates the complex $\mathrm{Hom}_{k[G]}(P_\bullet, A)$ into the complex of inhomogeneous cochains, functions $G^n \to A$ with an explicit differential. That complex is the definition of group cohomology in Mathlib. Section 2 computes it in degrees $0$, $1$ and $2$, and Section 3 studies its functoriality and computes it for cyclic groups.

In the text $g \circ f$ is the textbook composite, and Mathlib writes `f ≫ g`. Representations of groups are the subject of Volume 29; here only the module structure over $k[G]$ is needed.

### Definitions

**Definition (Permutation module).** Let $X$ be a set with a left action of $G$. The permutation module $k[X]$ is the free $k$-module on $X$, with $g \cdot \sum a_x x = \sum a_x (gx)$. For $X = G^{n+1}$ with the diagonal action $g \cdot (g_0, \dots, g_n) = (gg_0, \dots, gg_n)$, write $P_n = k[G^{n+1}]$.

**Definition (Standard complex).** The standard complex is the chain complex $P_\bullet$ of $k[G]$-modules with $P_n = k[G^{n+1}]$ and differential $d_n \colon P_n \to P_{n-1}$,
$$d_n(g_0, \dots, g_n) = \sum_{i=0}^{n} (-1)^i (g_0, \dots, \widehat{g_i}, \dots, g_n),$$
where the hat means omission. The augmentation $\varepsilon \colon P_0 = k[G] \to k$ sends each basis element $(g_0)$ to $1$.

Each $d_n$ is $G$-equivariant, because omitting an entry commutes with left multiplication of all entries. The relation $d_{n-1} \circ d_n = 0$ is the usual cancellation of the simplicial identities: omitting $g_i$ then $g_j$ with $i < j$ produces the same tuple as omitting $g_j$ then $g_i$, and the two signs are $(-1)^{i + (j-1)}$ and $(-1)^{j+i}$, which are opposite. Also $\varepsilon \circ d_1 = 0$, because $\varepsilon((g_1) - (g_0)) = 1 - 1 = 0$.

**Definition (Inhomogeneous cochains).** For a representation $A$, the cochain complex $C^\bullet(G, A)$ has $C^n(G, A) = \mathrm{Fun}(G^n, A)$, the $k$-module of all functions $G^n \to A$, and differential $d \colon C^n \to C^{n+1}$,
$$(df)(g_1, \dots, g_{n+1}) = g_1 \cdot f(g_2, \dots, g_{n+1}) + \sum_{j=1}^{n} (-1)^j f(g_1, \dots, g_j g_{j+1}, \dots, g_{n+1}) + (-1)^{n+1} f(g_1, \dots, g_n).$$
Here $G^0$ is a point, so $C^0(G, A) = A$.

**Definition (Group cohomology and homology).** The $n$-th cohomology group of $G$ with coefficients in $A$ is $H^n(G, A) = H^n(C^\bullet(G, A))$. Its elements are classes of $n$-cocycles (functions $f$ with $df = 0$) modulo $n$-coboundaries (functions $d f'$). The group homology $H_n(G, A)$ is the homology of the chain complex $C_n(G, A) = \bigoplus_{G^n} A$ of finitely supported functions $G^n \to A$, with the differential of the theorem in the homology part below.

### Theorems and proofs

**Proposition (The standard complex is free).** Let $G$ be a group. Each $P_n = k[G^{n+1}]$ is a free $k[G]$-module, with basis the tuples $(1, g_1, \dots, g_n)$. So $P_n$ is projective.

*Proof.* The action of $G$ on $G^{n+1}$ is free: $g \cdot (g_0, \dots, g_n) = (g_0, \dots, g_n)$ forces $g g_0 = g_0$, so $g = 1$. Each orbit contains exactly one tuple with first entry $1$: the orbit of $(g_0, \dots, g_n)$ contains $g_0^{-1} \cdot (g_0, \dots, g_n) = (1, g_0^{-1} g_1, \dots, g_0^{-1} g_n)$, and two tuples with first entry $1$ in one orbit differ by an element $g$ with $g \cdot 1 = 1$. A permutation module on a free $G$-set is free over $k[G]$, with one basis element for each orbit: $k[X] = \bigoplus_{\text{orbits}} k[G] \cdot x$. A free module is projective (Chapter 7, Section 2). $\square$

**Theorem (The standard resolution).** The augmented complex
$$\cdots \xrightarrow{d_3} P_2 \xrightarrow{d_2} P_1 \xrightarrow{d_1} P_0 \xrightarrow{\varepsilon} k \to 0$$
is exact. So $P_\bullet \to k$ is a projective resolution of the trivial representation $k$.

*Proof.* It suffices to prove exactness of the underlying complex of $k$-modules, because a sequence of $k[G]$-modules is exact if and only if it is exact as a sequence of $k$-modules. Define $k$-linear maps $h_{-1} \colon k \to P_0$ and $h_n \colon P_n \to P_{n+1}$ by
$$h_{-1}(1) = (1), \qquad h_n(g_0, \dots, g_n) = (1, g_0, \dots, g_n).$$
These maps are not $G$-equivariant, and they do not need to be. Compute $\varepsilon h_{-1} = \mathrm{id}_k$. For $n = 0$, $d_1 h_0(g_0) = d_1(1, g_0) = (g_0) - (1) = (g_0) - h_{-1}\varepsilon(g_0)$. For $n \geq 1$,
$$d_{n+1} h_n(g_0, \dots, g_n) = (g_0, \dots, g_n) + \sum_{i=1}^{n+1} (-1)^i (1, g_0, \dots, \widehat{g_{i-1}}, \dots, g_n) = (g_0, \dots, g_n) - h_{n-1} d_n(g_0, \dots, g_n).$$
So $d h + h d = \mathrm{id}$ in each degree of the augmented complex, with $k$ in degree $-1$. A complex with such a contracting homotopy is exact: if $d x = 0$, then $x = d(hx) + h(dx) = d(hx)$, so $x$ is a boundary. Together with the proposition, this makes $P_\bullet \to k$ a projective resolution. $\square$

The maps $h_n$ are the extra degeneracy of the simplicial set $EG$ with $n$-simplices $G^{n+1}$: they prepend the unit. This is the language of the Mathlib proof.

**Theorem (Inhomogeneous cochains compute Ext).** For each representation $A$, there is an isomorphism of cochain complexes $\mathrm{Hom}_{k[G]}(P_\bullet, A) \cong C^\bullet(G, A)$. Hence $H^n(G, A) \cong \mathrm{Ext}^n_{k[G]}(k, A)$ for all $n$.

*Proof.* By the proposition, a $G$-map $f \colon P_n \to A$ is determined by its values on the basis $(1, g_1, g_1 g_2, \dots, g_1 \cdots g_n)$, where $g_1, \dots, g_n$ are arbitrary. (This is a reparametrization of the basis $(1, h_1, \dots, h_n)$ with $h_i = g_1 \cdots g_i$.) Define
$$\Phi(f)(g_1, \dots, g_n) = f(1, g_1, g_1 g_2, \dots, g_1 \cdots g_n).$$
Then $\Phi \colon \mathrm{Hom}_{k[G]}(P_n, A) \to \mathrm{Fun}(G^n, A)$ is a $k$-linear bijection. Its inverse sends $\phi$ to $f(x_0, \dots, x_n) = x_0 \cdot \phi(x_0^{-1} x_1, x_1^{-1} x_2, \dots, x_{n-1}^{-1} x_n)$.

The differential of $\mathrm{Hom}(P_\bullet, A)$ is $\delta f = f \circ d_{n+1}$. Evaluate at the tuple $x = (1, g_1, g_1 g_2, \dots, g_1 \cdots g_{n+1})$, and write $x_i = g_1 \cdots g_i$:
$$(\delta f)(x) = \sum_{i=0}^{n+1} (-1)^i f(x_0, \dots, \widehat{x_i}, \dots, x_{n+1}).$$
For $i = 0$, the tuple $(x_1, \dots, x_{n+1}) = g_1 \cdot (1, g_2, g_2 g_3, \dots)$, and $G$-linearity gives $g_1 \cdot \Phi(f)(g_2, \dots, g_{n+1})$. For $1 \leq i \leq n$, omitting $x_i$ leaves a tuple whose consecutive quotients are $g_1, \dots, g_i g_{i+1}, \dots, g_{n+1}$, so the term is $(-1)^i \Phi(f)(g_1, \dots, g_i g_{i+1}, \dots, g_{n+1})$. For $i = n+1$, the term is $(-1)^{n+1} \Phi(f)(g_1, \dots, g_n)$. This is the formula for $d \Phi(f)$. So $\Phi$ is an isomorphism of complexes, and it induces isomorphisms in cohomology. By Chapter 4, the cohomology of $\mathrm{Hom}(P_\bullet, A)$ for a projective resolution $P_\bullet$ of $k$ is $\mathrm{Ext}^n(k, A)$, independently of the resolution. $\square$

A byproduct of the proof is that $d \circ d = 0$ on $C^\bullet(G, A)$, which is tedious to check directly in high degrees.

**Theorem (Inhomogeneous chains compute Tor).** Let $C_n(G, A) = \bigoplus_{G^n} A$, and write $a \cdot [g_1, \dots, g_n]$ for the element $a$ placed at $(g_1, \dots, g_n)$. With the differential
$$d(a \cdot [g_1, \dots, g_n]) = g_1^{-1} a \cdot [g_2, \dots, g_n] + \sum_{j=1}^{n-1} (-1)^j a \cdot [\dots, g_j g_{j+1}, \dots] + (-1)^n a \cdot [g_1, \dots, g_{n-1}],$$
the homology of $C_\bullet(G, A)$ is $\mathrm{Tor}_n^{k[G]}(A, k)$, where $A$ is a right $k[G]$-module by $a \cdot g = g^{-1} a$. This is isomorphic to $\mathrm{Tor}_n^{k[G]}(k, A)$.

*Proof.* Then $A \otimes_{k[G]} P_n$ is spanned by the elements $a \otimes (1, g_1, g_1 g_2, \dots)$, and the map $a \cdot [g_1, \dots, g_n] \mapsto a \otimes (1, g_1, g_1 g_2, \dots, g_1 \cdots g_n)$ is an isomorphism $C_n(G, A) \to A \otimes_{k[G]} P_n$, by the freeness of $P_n$. The computation of $\mathrm{id} \otimes d_n$ in these coordinates is the computation of the previous proof, with one change: for $i = 0$, the relation $a \otimes g_1 y = a g_1 \otimes y = g_1^{-1} a \otimes y$ produces the factor $g_1^{-1}$. The homology of $A \otimes_{k[G]} P_\bullet$ is $\mathrm{Tor}_n(A, k)$ by Chapter 4. $\square$

**Corollary (The trivial group).** If $G = \{1\}$, then $H^n(G, A) = 0$ and $H_n(G, A) = 0$ for $n \geq 1$.

*Proof.* Then $k[G] = k$, and $k$ is projective over itself. The complex $0 \to k \to k \to 0$ (with $k$ in degree $0$) is a projective resolution with nothing in positive degrees, so $\mathrm{Ext}^n(k, A) = 0$ and $\mathrm{Tor}_n(k, A) = 0$ for $n \geq 1$. $\square$

### Examples

**Example (Low degrees of the standard complex).** In degree $1$, $d_1(g_0, g_1) = (g_1) - (g_0)$. In degree $2$, $d_2(g_0, g_1, g_2) = (g_1, g_2) - (g_0, g_2) + (g_0, g_1)$. Then $d_1 d_2(g_0, g_1, g_2) = [(g_2) - (g_1)] - [(g_2) - (g_0)] + [(g_1) - (g_0)] = 0$. For $G = \mathbb{Z}/2 = \{1, s\}$, the module $P_1 = k[G^2]$ has rank $4$ over $k$ and rank $2$ over $k[G]$, with basis $(1, 1)$ and $(1, s)$.

**Example (Low degrees of the inhomogeneous complex).** For $n = 0$, a $0$-cochain is an element $m \in A$, and $(dm)(g) = gm - m$. For $n = 1$, $(df)(g, h) = g f(h) - f(gh) + f(g)$. For $n = 2$, $(df)(g, h, l) = g f(h, l) - f(gh, l) + f(g, hl) - f(g, h)$. The check $d(dm) = 0$ reads $g(hm - m) - (ghm - m) + (gm - m) = 0$, which holds term by term.

**Example (Invariants).** $H^0(G, A) = \ker(d \colon A \to \mathrm{Fun}(G, A)) = \{m \in A : gm = m \text{ for all } g\} = A^G$. For $G = \mathbb{Z}/2$ acting on $A = \mathbb{Z}$ by $s \cdot m = -m$, this gives $A^G = \{m : -m = m\} = 0$. For the trivial action, $H^0(G, \mathbb{Z}) = \mathbb{Z}$.

**Example (Coinvariants).** $H_0(G, A) = A / \mathrm{im}(d_1)$, and $d_1(a \cdot [g]) = g^{-1}a - a$. So $H_0(G, A) = A/\langle ga - a \rangle = A_G$, the largest quotient on which $G$ acts trivially. For $\mathbb{Z}/2$ acting on $\mathbb{Z}$ by sign, $A_G = \mathbb{Z}/\langle -m - m \rangle = \mathbb{Z}/2$. So $H^0$ and $H_0$ differ for the same module.

**Example (The size of the complex).** For a finite group of order $|G| = N$, $C^n(G, A) \cong A^{N^n}$. For $G = \mathbb{Z}/2$ and $A = \mathbb{F}_2$, $C^n$ has dimension $2^n$. Section 3 replaces this complex by a periodic one with $C^n$ of dimension $1$, which gives the same cohomology.

### The library around it

::: mathlib
`Rep` · `Mathlib.RepresentationTheory.Rep.Basic`

`Rep k G` is the category of `k`-linear representations of `G`. An object `A` has a `k`-module `A.V` and a representation `A.ρ : Representation k G A.V`. The trivial representation is `Rep.trivial k G k`, a permutation representation is `Rep.ofMulAction k G X`, and `Rep.free k G α` is the free representation on `α`. Mathlib avoids instances `Module k[G] A`, because they would create two scalar actions on the same type. Volume 29 develops this category.

<?decl Rep?>
:::

::: mathlib
`Rep.standardResolution` · `Mathlib.RepresentationTheory.Homological.Resolution`

`Rep.standardComplex k G` is the alternating face map complex of the linearization of `classifyingSpaceUniversalCover G`, the simplicial `G`-set with $n$-simplices `Fin (n + 1) → G`. The formula for the differential is `Rep.standardComplex.d_eq`. Exactness comes from `classifyingSpaceUniversalCover.extraDegeneracyAugmentedCechNerve`, the extra degeneracy of the proof, which gives the homotopy equivalence `Rep.standardComplex.forget₂ToModuleCatHomotopyEquiv` with $k$ in degree $0$. The instance `Rep.standardComplex.x_projective` is the proposition on freeness. `Rep.standardResolution k G : ProjectiveResolution (Rep.trivial k G k)` assembles these facts, and `Rep.standardResolution.extIso` identifies the group `CategoryTheory.Abelian.Ext` with the cohomology of `Hom(P, V)`.

<?decl Rep.standardResolution?>
:::

::: mathlib
`Rep.barResolution` · `Mathlib.RepresentationTheory.Homological.Resolution`

The bar complex `Rep.barComplex k G` has objects `Gⁿ →₀ k[G]`, the free representations with basis $G^n$, and the differential of `Rep.barComplex.d`. The isomorphism `Rep.barComplex.isoStandardComplex` is the change of basis $[g_1, \dots, g_n] \mapsto (1, g_1, g_1 g_2, \dots)$ of the proof. `Rep.barResolution` is the resulting projective resolution. Mathlib uses it, not the standard resolution, to define the inhomogeneous complexes, because its basis is already the set $G^n$.

<?decl Rep.barResolution?>
:::

::: mathlib
`groupCohomologyIsoExt` · `Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic`

`inhomogeneousCochains.d A n` is the differential of the definition, with the indexing $g_0, \dots, g_n$ starting at $0$; `inhomogeneousCochains.d_eq` proves that it agrees with the bar differential under the isomorphism of the proof. `groupCohomology.inhomogeneousCochains A` is the complex, a `CochainComplex (ModuleCat k) ℕ`, and `groupCohomology A n` is defined as its `n`-th homology. `groupCohomologyIsoExt A n` gives `groupCohomology A n ≅ ModuleCat.of k (Ext (Rep.trivial k G k) A n)`, and `groupCohomologyIso A n P` does the same for any projective resolution `P`. `groupCohomology.cocycles A n` and `groupCohomology.π A n` give the cocycles and the projection to cohomology.

<?decl groupCohomologyIsoExt?>
:::

::: mathlib
`groupHomologyIsoTor` · `Mathlib.RepresentationTheory.Homological.GroupHomology.Basic`

`groupHomology.inhomogeneousChains A` has objects `(Fin n → G) →₀ A`, with the differential of the theorem; the first term is `A.ρ (g 0)⁻¹`. `groupHomology A n` is its homology. `Rep.Tor k G n` derives the second variable of $(A, B) \mapsto (A \otimes_k B)_G$, because Mathlib's tensor product needs a commutative ring and $k[G]$ is not commutative in general. `groupHomologyIsoTor A n` identifies `groupHomology A n` with `Tor n A k`.

<?decl groupHomologyIsoTor?>
:::

Common errors of a learner: The first error is to index the inhomogeneous cochains from $1$ in Mathlib: the arguments are `g : Fin n → G`, so the first is `g 0`. The second error is to forget the inverse in group homology: the first term of the chain differential is $\rho(g_0^{-1})$, because $A$ becomes a right module through inverses. The third error is to think that the contracting homotopy $h_n$ proves the standard complex contractible in `Rep k G`; $h_n$ is only $k$-linear, and the complex is not contractible as a complex of representations in general: a contraction in `Rep k G` would give $H^n(G, A) = 0$ for all $A$ and all $n \geq 1$, which fails for $G = \mathbb{Z}/2$ (Section 3). The fourth error is to use the deprecated `groupCohomology.projectiveResolution`; this edition uses `Rep.standardResolution` and `Rep.barResolution`. The fifth error is to expect `groupCohomology A n` to be defined as `CategoryTheory.Abelian.Ext`; it is the homology of the inhomogeneous complex, and `groupCohomologyIsoExt` connects the two.

### Exercises

1. (A) Write out $d_3 \colon P_3 \to P_2$ and check $d_2 d_3 = 0$ on $(g_0, g_1, g_2, g_3)$. Hint: twelve terms cancel in pairs.
2. (A) Show that $H^0(G, \mathrm{Fun}(G, k)) = k$, where $G$ acts on functions by $(g\phi)(x) = \phi(xg)$. Hint: an invariant function is constant.
3. (B) Prove that a $1$-cocycle $f \in C^1(G, A)$ satisfies $f(1) = 0$. Hint: put $g = h = 1$ in $df = 0$.
4. (B) Show that $\mathrm{rank}_{k[G]} P_n = |G|^n$ for a finite group, and that the map $\Phi$ of the proof gives $\mathrm{Hom}_{k[G]}(P_n, A) \cong A^{|G|^n}$ as $k$-modules. Hint: the basis of the proposition.
5. (B) Prove that $H^n(G, A) = 0$ for $n \geq 1$ when $A = \mathrm{Hom}_k(k[G], M)$ with $(g\phi)(x) = \phi(xg)$, for any $k$-module $M$. Hint: $\mathrm{Hom}_{k[G]}(P, \mathrm{Hom}_k(k[G], M)) \cong \mathrm{Hom}_k(P, M)$, and $P_\bullet \to k$ is split exact over $k$.
6. (C) Prove $d \circ d = 0$ on $C^\bullet(G, A)$ directly for $n = 1$, that is, for $f \in C^1$ compute $(d(df))(g, h, l)$. Hint: each of the four terms of $d(df)$ expands into three values of $f$, and the twelve values cancel in pairs.
7. (C) Let $G$ act trivially on $A$. Show that the cup product $C^1 \times C^1 \to C^2$, $(f \smile f')(g, h) = f(g) f'(h)$, for $A = k$, sends a pair of cocycles to a cocycle. Hint: a $1$-cocycle for the trivial action is a homomorphism $G \to k$.

### Notes and history

Eilenberg and MacLane defined the cohomology of groups in the 1940s with the inhomogeneous cochains of this section. Their motivation came from topology: Hurewicz had shown that the homotopy type of an aspherical space depends only on its fundamental group, and Hopf had found that the second homology of such a space depends only on the group. The standard complex is the chain complex of the simplicial set $EG$, whose quotient $EG/G = BG$ is a classifying space; Volume 27 develops this point of view. Cartan and Eilenberg, in *Homological Algebra* (1956), presented group cohomology as $\mathrm{Ext}$ over $\mathbb{Z}[G]$, as in this section.

The Mathlib files `Resolution`, `GroupCohomology.Basic` and `GroupHomology.Basic` are by Amelia Livingston, read from their headers.

### Reference

<?reference?>
