---
title: Spectral sequences
kind: theory
modules:
  - Mathlib.Algebra.Homology.SpectralSequence.Basic
  - Mathlib.Algebra.Homology.SpectralSequence.ComplexShape
  - Mathlib.Algebra.Homology.SpectralObject.Basic
  - Mathlib.Algebra.Homology.SpectralObject.Page
  - Mathlib.Algebra.Homology.SpectralObject.SpectralSequence
  - Mathlib.Algebra.Homology.SpectralObject.HasSpectralSequence
explains:
  E3: [CategoryTheory.SpectralSequence, CategoryTheory.CohomologicalSpectralSequence, CategoryTheory.Abelian.SpectralObject, CategoryTheory.Abelian.SpectralObject.E, CategoryTheory.Abelian.SpectralObject.kernelSequenceE_exact, CategoryTheory.Abelian.SpectralObject.isZero_H_obj_of_isIso, CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore, CategoryTheory.Abelian.SpectralObject.coreE₂Cohomological, CategoryTheory.Abelian.SpectralObject.spectralSequence, CategoryTheory.Abelian.SpectralObject.E₂SpectralSequence]
  E2: [CategoryTheory.SpectralSequence.page, CategoryTheory.SpectralSequence.iso, CategoryTheory.SpectralSequence.Hom, CategoryTheory.SpectralSequence.pageFunctor, CategoryTheory.SpectralSequence.pageHomologyNatIso, CategoryTheory.E₂CohomologicalSpectralSequence, CategoryTheory.CohomologicalSpectralSequenceNat, CategoryTheory.E₂CohomologicalSpectralSequenceNat, CategoryTheory.CohomologicalSpectralSequenceFin, ComplexShape.spectralSequenceNat, ComplexShape.spectralSequenceFin, CategoryTheory.Abelian.SpectralObject.H, CategoryTheory.Abelian.SpectralObject.δ, CategoryTheory.Abelian.SpectralObject.δ_naturality, CategoryTheory.Abelian.SpectralObject.exact₁, CategoryTheory.Abelian.SpectralObject.exact₂, CategoryTheory.Abelian.SpectralObject.exact₃, CategoryTheory.Abelian.SpectralObject.composableArrows₅_exact, CategoryTheory.Abelian.SpectralObject.shortComplex, CategoryTheory.Abelian.SpectralObject.isZero_E_of_isZero_H, CategoryTheory.Abelian.SpectralObject.kernelSequenceE, CategoryTheory.Abelian.SpectralObject.cokernelSequenceE, CategoryTheory.Abelian.SpectralObject.HasSpectralSequence, CategoryTheory.Abelian.SpectralObject.coreE₂CohomologicalNat, CategoryTheory.Abelian.SpectralObject.coreE₂HomologicalNat, CategoryTheory.Abelian.SpectralObject.IsFirstQuadrant, CategoryTheory.Abelian.SpectralObject.IsThirdQuadrant, CategoryTheory.Abelian.SpectralObject.spectralSequencePageXIso, CategoryTheory.Abelian.SpectralObject.spectralSequence_page_d_eq, CategoryTheory.Abelian.SpectralObject.isZero_spectralSequence_page_X_iff, CategoryTheory.Abelian.SpectralObject.E₂SpectralSequenceNat, CategoryTheory.Abelian.SpectralObject.E₂HomologicalSpectralSequenceNat]
  E1: auto
families: []
requires: [V25.C05, V26.C01, V26.C02, V26.C03, V26.C05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Spectral sequences

### Overview

A spectral sequence is a method to compute the cohomology of a complex in steps. A filtration of a complex $K$ gives a first approximation, the cohomology of the graded pieces. Each next page is the cohomology of the previous page for a new differential. In good cases the pages become constant, and the last page gives the graded pieces of a filtration of $H^n(K)$.

Mathlib follows the method of Verdier. It does not start from a filtered complex. It starts from a *spectral object*: a family of objects $H^n(i \leq j)$, one for each arrow of an index category, with long exact sequences for each pair of composable arrows. A filtered complex gives a spectral object through the cohomology of its subquotients, and a triangulated functor with a cohomological functor gives one through the mapping cones of Chapter 3. All the objects of all the pages are then defined by one formula, the object $E^n(f_1, f_2, f_3)$ for three composable arrows.

This section defines spectral sequences and spectral objects as Mathlib does. It proves that $E^n(f_1, f_2, f_3)$ is a subobject of $H^n(f_2 f_3)$, that the second page of the cohomological spectral sequence is $H^{p+q}(q \leq q+1)$, and that for a finite chain the terms $E^n(\text{bottom} \leq q \leq q+1 \leq \text{top})$ are the graded pieces of a filtration of the abutment. The examples compute a spectral object for a short exact sequence of complexes and for the bicomplex of Section 1.

In this section, $C$ is an abelian category. The proofs use elements; in an abelian category, the same arguments hold with generalized elements. Mathlib writes `f ≫ g` for $g \circ f$. For arrows, the text writes $fg$ for the composite of $f : i \to j$ and $g : j \to k$, as Mathlib does.

### Definitions

**Definition (Spectral sequence).** Let $\kappa$ be a type, $c = (c_r)_{r \in \mathbb{Z}}$ a family of complex shapes on $\kappa$, and $r_0 \in \mathbb{Z}$. A *spectral sequence* in $C$ of shape $c$ starting at $r_0$ is:

- for each $r \geq r_0$, a complex $E_r$ of shape $c_r$, the *$r$-th page*;
- for each $r \geq r_0$ and each $x \in \kappa$, an isomorphism $H_x(E_r) \cong (E_{r+1})_x$ between the homology of the page at $x$ and the next page at $x$.

A morphism $E \to E'$ is a family of maps of complexes $E_r \to E'_r$ that commute with the isomorphisms.

**Definition (Cohomological spectral sequence).** A *cohomological spectral sequence* has $\kappa = \mathbb{Z} \times \mathbb{Z}$ and the shape $c_r = \operatorname{up}'(r, 1 - r)$. So the differential of page $r$ is
$$d_r : E_r^{p,q} \to E_r^{p+r, q-r+1}.$$
It is an *$E_2$ spectral sequence* when $r_0 = 2$. The *first quadrant* version has $\kappa = \mathbb{N} \times \mathbb{N}$ and the shape that relates $(p, q)$ to $(p + r, q - r + 1)$ when both pairs are in $\mathbb{N} \times \mathbb{N}$.

The definition has only the pages. It has no limit page and no abutment. The objects to which a spectral sequence converges come from the spectral object, as below.

**Definition (Spectral object).** Let $\iota$ be a category. A *spectral object* $X$ in $C$ indexed by $\iota$ is:

- for each $n \in \mathbb{Z}$, a functor $H^n$ from the category of arrows of $\iota$ to $C$, written $f \mapsto H^n(f)$;
- for composable $f : i \to j$ and $g : j \to k$ and each $n$, a morphism $\delta : H^n(g) \to H^{n+1}(f)$, natural in the pair $(f, g)$;

such that for each composable pair the sequence
$$H^n(f) \to H^n(fg) \to H^n(g) \xrightarrow{\delta} H^{n+1}(f) \to H^{n+1}(fg) \to H^{n+1}(g)$$
is exact. Here $H^n(f) \to H^n(fg)$ is induced by the map of arrows $(\mathrm{id}_i, g) : f \to fg$, and $H^n(fg) \to H^n(g)$ by $(f, \mathrm{id}_k) : fg \to g$.

For a preorder $\iota$, an arrow is a pair $i \leq j$, and the text writes $H^n(i \leq j)$.

**Definition (The object $E$).** For composable arrows $f_1 : i \to j$, $f_2 : j \to k$, $f_3 : k \to l$ and $n \in \mathbb{Z}$, the object $E^n(f_1, f_2, f_3)$ is the homology of the complex
$$H^{n-1}(f_3) \xrightarrow{\delta} H^n(f_2) \xrightarrow{\delta} H^{n+1}(f_1).$$
The composite is zero: the image of the first $\delta$ is the kernel of $H^n(f_2) \to H^n(f_2 f_3)$, and by naturality the second $\delta$ factors through this map, as in the proof of the kernel theorem below. For a preorder, the text writes $E^n(i \leq j \leq k \leq l)$.

**Definition (Data of a spectral sequence).** A *recipe* for a spectral sequence of shape $c$ from a spectral object indexed by a preorder $\iota$ gives, for $r \geq r_0$ and $x \in \kappa$, a degree $\deg(x) \in \mathbb{Z}$ and four indices $i_0(r, x) \leq i_1(x) \leq i_2(x) \leq i_3(r, x)$ in $\iota$, with conditions that relate the indices of $x$ and of the next position $x'$ of the page. The object of page $r$ at $x$ is then
$$E_r^x = E^{\deg x}\bigl(i_0(r, x) \leq i_1(x) \leq i_2(x) \leq i_3(r, x)\bigr).$$
As $r$ grows, $i_0$ goes down and $i_3$ goes up.

For the $E_2$ cohomological spectral sequence, Mathlib takes $\iota = \overline{\mathbb{Z}} = \mathbb{Z} \cup \{-\infty, +\infty\}$ and
$$E_r^{p,q} = E^{p+q}\bigl(q - r + 2 \leq q \leq q + 1 \leq q + r - 1\bigr).$$
The page at infinity is $E^{p+q}(-\infty \leq q \leq q + 1 \leq +\infty)$.

**Definition (First quadrant spectral object).** A spectral object $Y$ indexed by $\overline{\mathbb{Z}}$ is of the *first quadrant* if $H^n(i \leq j) = 0$ when $j \leq 0$, and $H^n(i \leq j) = 0$ when $n < i$.

::: mathlib
`CategoryTheory.SpectralSequence` · `Mathlib.Algebra.Homology.SpectralSequence.Basic`

`SpectralSequence C c r₀` has the fields `page r hr : HomologicalComplex C (c r)` and `iso r r' pq hrr' hr : (page r).homology pq ≅ (page r').X pq`, where `hrr' : r + 1 = r'` and `hr : r₀ ≤ r` are filled in by `lia`. Morphisms are `SpectralSequence.Hom`, and `pageFunctor` and `pageHomologyNatIso` make the pages functorial. `CohomologicalSpectralSequence C r₀` uses the shapes `ComplexShape.up' ⟨r, 1 - r⟩`, and `E₂CohomologicalSpectralSequence C` fixes `r₀ = 2`. The versions `CohomologicalSpectralSequenceNat` and `CohomologicalSpectralSequenceFin` use the shapes `ComplexShape.spectralSequenceNat` on `ℕ × ℕ` and `ComplexShape.spectralSequenceFin l` on `ℤ × Fin l`.

<?decl CategoryTheory.SpectralSequence?>
:::

::: mathlib
`CategoryTheory.Abelian.SpectralObject` · `Mathlib.Algebra.Homology.SpectralObject.Basic`

`SpectralObject C ι` has the field `H : ℤ → ComposableArrows ι 1 ⥤ C` and the connecting maps, used through `X.δ f g n₀ n₁ : (X.H n₀).obj (mk₁ g) ⟶ (X.H n₁).obj (mk₁ f)`. The exactness at the three places is `exact₁`, `exact₂` and `exact₃`, and `composableArrows₅_exact` gives the whole sequence of six terms. Naturality is `δ_naturality`. The source cites Verdier, *Des catégories dérivées des catégories abéliennes*, II.4.

<?decl CategoryTheory.Abelian.SpectralObject?>
:::

### Theorems and proofs

**Lemma (Vanishing on isomorphisms).** Let $X$ be a spectral object and $f : i \to j$ an isomorphism of $\iota$. Then $H^n(f) = 0$ for each $n$.

*Proof.* First let $f = \mathrm{id}_i$. Apply the exact sequence to the pair $(\mathrm{id}_i, \mathrm{id}_i)$. Its middle part is $H^n(\mathrm{id}_i) \to H^n(\mathrm{id}_i) \to H^n(\mathrm{id}_i)$. The two maps are induced by the maps of arrows $(\mathrm{id}_i, \mathrm{id}_i)$, which are identities, so both maps are the identity. Exactness says that the image of the identity is the kernel of the identity, so $H^n(\mathrm{id}_i) = 0$. For an isomorphism $f$, the pair $(\mathrm{id}_i, f)$ is an isomorphism of arrows from $\mathrm{id}_i$ to $f$, with inverse $(\mathrm{id}_i, f^{-1})$. Since $H^n$ is a functor, $H^n(f) \cong H^n(\mathrm{id}_i) = 0$. $\square$

**Theorem (E as a kernel).** Let $f_1 : i \to j$, $f_2 : j \to k$ and $f_3 : k \to l$ be composable. There is an exact sequence
$$0 \to E^n(f_1, f_2, f_3) \to H^n(f_2 f_3) \to H^n(f_3) \oplus H^{n+1}(f_1),$$
where the last map has components $H^n(f_2 f_3) \to H^n(f_3)$ and $\delta : H^n(f_2 f_3) \to H^{n+1}(f_1)$.

*Proof.* Let $a : H^n(f_2) \to H^n(f_2 f_3)$ and $b : H^n(f_2 f_3) \to H^n(f_3)$ be the maps of the exact sequence of the pair $(f_2, f_3)$. Write $\delta_{23} : H^{n-1}(f_3) \to H^n(f_2)$ for its connecting map, and $\delta_{12} : H^n(f_2) \to H^{n+1}(f_1)$ and $\delta' : H^n(f_2 f_3) \to H^{n+1}(f_1)$ for the connecting maps of the pairs $(f_1, f_2)$ and $(f_1, f_2 f_3)$.

Step 1. $\delta' \circ a = \delta_{12}$. The pair of maps of arrows $\mathrm{id} : f_1 \to f_1$ and $(\mathrm{id}_j, f_3) : f_2 \to f_2 f_3$ agree at the common object $j$, so naturality of $\delta$ gives $\delta' \circ H^n(\mathrm{id}_j, f_3) = H^{n+1}(\mathrm{id}) \circ \delta_{12}$, which is the claim.

Step 2. By exactness for the pair $(f_2, f_3)$, $\ker a = \operatorname{im} \delta_{23}$ and $\operatorname{im} a = \ker b$. So $a$ induces an isomorphism $\bar a : H^n(f_2) / \operatorname{im} \delta_{23} \to \ker b$.

Step 3. By definition, $E^n(f_1, f_2, f_3) = \ker \delta_{12} / \operatorname{im} \delta_{23}$, a subobject of $H^n(f_2) / \operatorname{im} \delta_{23}$. Let $y \in H^n(f_2)$. By Step 1, $\delta_{12}(y) = 0$ if and only if $\delta'(a(y)) = 0$. So $\bar a$ maps $E^n(f_1, f_2, f_3)$ isomorphically onto $\ker b \cap \ker \delta'$, which is the kernel of $(b, \delta')$. $\square$

The dual statement holds: there is an exact sequence $H^n(f_1) \oplus H^{n-1}(f_3) \to H^n(f_1 f_2) \to E^n(f_1, f_2, f_3) \to 0$. The proof is the same, with the pair $(f_1, f_2)$ in place of $(f_2, f_3)$.

**Corollary (The second page).** Let $Y$ be a spectral object indexed by $\overline{\mathbb{Z}}$, and let $E$ be its $E_2$ cohomological spectral sequence. Then
$$E_2^{p,q} \cong H^{p+q}(q \leq q + 1).$$

*Proof.* For $r = 2$, the four indices are $q \leq q \leq q + 1 \leq q + 1$, so $f_1 = \mathrm{id}_q$, $f_2 = (q \leq q + 1)$ and $f_3 = \mathrm{id}_{q+1}$. By the lemma, $H^{n-1}(f_3) = 0$ and $H^{n+1}(f_1) = 0$. So the complex that defines $E^{p+q}(f_1, f_2, f_3)$ is $0 \to H^{p+q}(f_2) \to 0$, and its homology is $H^{p+q}(f_2)$. $\square$

**Theorem (Filtration of the abutment).** Let $X$ be a spectral object indexed by the chain $0 < 1 < \cdots < m$. Fix $n$, and let $G_q \subseteq H^n(0 \leq m)$ be the image of $H^n(0 \leq q) \to H^n(0 \leq m)$, for $0 \leq q \leq m$. Then $0 = G_0 \subseteq G_1 \subseteq \cdots \subseteq G_m = H^n(0 \leq m)$, and for $0 \leq q < m$,
$$G_{q+1} / G_q \cong E^n(0 \leq q \leq q + 1 \leq m).$$

*Proof.* The map $H^n(0 \leq q) \to H^n(0 \leq m)$ factors through $H^n(0 \leq q + 1)$, by functoriality of $H^n$ on arrows. So $G_q \subseteq G_{q+1}$. The lemma gives $G_0 = 0$, and $G_m = H^n(0 \leq m)$ because the map is the identity.

Apply the theorem on E as a kernel to $f_1 = (0 \leq q)$, $f_2 = (q \leq q + 1)$, $f_3 = (q + 1 \leq m)$. It gives
$$E^n(0 \leq q \leq q + 1 \leq m) \cong \{ z \in H^n(q \leq m) : z \mapsto 0 \in H^n(q + 1 \leq m),\ \delta(z) = 0 \in H^{n+1}(0 \leq q) \}.$$
The exact sequence of the pair $(0 \leq q, q \leq m)$ is
$$H^n(0 \leq q) \to H^n(0 \leq m) \xrightarrow{\rho_q} H^n(q \leq m) \xrightarrow{\delta} H^{n+1}(0 \leq q).$$
So $\ker \delta = \operatorname{im} \rho_q$, and $\ker \rho_q = G_q$. Hence $\rho_q$ induces an isomorphism $H^n(0 \leq m) / G_q \cong \ker \delta$. The composite of $\rho_q$ with $H^n(q \leq m) \to H^n(q + 1 \leq m)$ is $\rho_{q+1}$, by functoriality. So an element $\rho_q(x)$ goes to zero in $H^n(q + 1 \leq m)$ if and only if $x \in \ker \rho_{q+1} = G_{q+1}$. The isomorphism therefore maps $G_{q+1} / G_q$ onto the set of the display. $\square$

In the $E_2$ indexing, with $i_0 = -\infty$ and $i_3 = +\infty$, the same argument identifies the page at infinity with the graded pieces of a filtration of $H^n(-\infty \leq +\infty)$, when the filtration is finite. This is the sense in which the spectral sequence converges.

**Remark (The construction of Mathlib).** For a recipe that satisfies the conditions of `HasSpectralSequence`, Mathlib defines the differential of page $r$ from $E^{n}(i_0 \leq i_1 \leq i_2 \leq i_3)$ to $E^{n+1}(i_0' \leq i_1' \leq i_2' \leq i_3')$, where the conditions on the recipe give $i_2' = i_0$ and $i_3' = i_1$, so that the six indices form one chain. It then proves that the homology of page $r$ at each position is the object of page $r + 1$. For the $E_2$ cohomological recipe on $\overline{\mathbb{Z}}$, the conditions always hold. For the first quadrant recipe on $\mathbb{N} \times \mathbb{N}$, they follow from the vanishing conditions of a first quadrant spectral object. The proof of the homology isomorphism uses the exact sequences of the lemmas above many times; it is too long for this section.

### Examples

**Example (A short exact sequence of complexes).** Let $0 \to F \to K \to Q \to 0$ be a short exact sequence of complexes of abelian groups. Index by the chain $0 < 1 < 2$, and set $H^n(0 \leq 1) = H^n(F)$, $H^n(1 \leq 2) = H^n(Q)$, $H^n(0 \leq 2) = H^n(K)$ and $H^n(i \leq i) = 0$. The only pair of composable arrows that are not identities is $(0 \leq 1, 1 \leq 2)$, and its sequence is the long exact cohomology sequence of Chapter 2. The theorem on the abutment gives $G_1 = \operatorname{im}(H^n(F) \to H^n(K))$ and
$$G_1 \cong E^n(0 \leq 0 \leq 1 \leq 2) = \operatorname{coker}(\delta : H^{n-1}(Q) \to H^n(F)),$$
$$H^n(K) / G_1 \cong E^n(0 \leq 1 \leq 2 \leq 2) = \ker(\delta : H^n(Q) \to H^{n+1}(F)).$$
Take $K = (\mathbb{Z} \xrightarrow{2} \mathbb{Z})$ in degrees $0$ and $1$, with $F$ the subcomplex $\mathbb{Z}$ in degree $1$, and $Q = \mathbb{Z}$ in degree $0$. Then $\delta : H^0(Q) = \mathbb{Z} \to H^1(F) = \mathbb{Z}$ is multiplication by $2$. So $H^0(K) \cong \ker \delta = 0$ and $H^1(K) \cong \operatorname{coker} \delta = \mathbb{Z}/2$, as a direct computation shows.

**Example (The column filtration of a bicomplex).** Take the bicomplex $K^{p,q} = A^p \otimes A^q$ of Section 1, with $A = (\mathbb{Z} \xrightarrow{2} \mathbb{Z})$ in degrees $-1$ and $0$. The columns with $p \geq 0$ form a subcomplex $F$ of $\operatorname{Tot}(K)$, since $d_h$ raises $p$. Here $F$ is column $0$, $\mathbb{Z} \xrightarrow{2} \mathbb{Z}$ in total degrees $-1$ and $0$, and the quotient $Q$ is column $-1$, $\mathbb{Z} \xrightarrow{-2} \mathbb{Z}$ in total degrees $-2$ and $-1$. So $H^0(F) = \mathbb{Z}/2$ and $H^{-1}(Q) = \mathbb{Z}/2$, and the other groups are zero. The connecting map $\delta : H^{-1}(Q) \to H^0(F)$ sends the class of $b \in K^{-1,0}$ to the class of $D b = d_h b = 2b \in K^{0,0}$, which is zero in $\mathbb{Z}/2$. So $\delta = 0$, and the previous example gives $H^{-1}(\operatorname{Tot} K) \cong \mathbb{Z}/2$ and $H^0(\operatorname{Tot} K) \cong \mathbb{Z}/2$. This agrees with the direct computation of Section 1.

**Example (Degeneration).** Let $Y$ be a first quadrant spectral object with $H^n(q \leq q + 1) = 0$ for all $q \neq 0$. Then $E_2^{p,q} = 0$ for $q \neq 0$. A differential $d_r$ with $r \geq 2$ changes $q$ by $1 - r \neq 0$, so all differentials from page $2$ on are zero, and $E_r^{p,0} = E_2^{p,0}$ for all $r \geq 2$.

### The library around it

::: mathlib
`CategoryTheory.Abelian.SpectralObject.E` · `Mathlib.Algebra.Homology.SpectralObject.Page`

`X.E f₁ f₂ f₃ n₀ n₁ n₂` is the homology of `X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂`, whose maps are two `X.δ`. The kernel theorem is `kernelSequenceE_exact`, for the short complex `kernelSequenceE`; the dual is `cokernelSequenceE`. The lemma `isZero_E_of_isZero_H` gives the vanishing of `E` from that of the middle term, and `isZero_H_obj_of_isIso` is the lemma on isomorphisms.

<?decl CategoryTheory.Abelian.SpectralObject.E?>
:::

::: mathlib
`CategoryTheory.Abelian.SpectralObject.spectralSequence` · `Mathlib.Algebra.Homology.SpectralObject.SpectralSequence`

For `data : SpectralSequenceDataCore ι c r₀` and `[X.HasSpectralSequence data]`, `X.spectralSequence data : SpectralSequence C c r₀`. The objects are identified by `spectralSequencePageXIso`, the differentials by `spectralSequence_page_d_eq`, and `isZero_spectralSequence_page_X_iff` reduces vanishing to `X.E`. For `Y : SpectralObject C EInt`, `Y.E₂SpectralSequence` uses `coreE₂Cohomological`; with `[Y.IsFirstQuadrant]`, `Y.E₂SpectralSequenceNat` uses `coreE₂CohomologicalNat`; with `[Y.IsThirdQuadrant]`, `Y.E₂HomologicalSpectralSequenceNat` uses `coreE₂HomologicalNat`.

<?decl CategoryTheory.Abelian.SpectralObject.spectralSequence?>
:::

The source of spectral objects in Mathlib is the module `Mathlib.Algebra.Homology.HomotopyCategory.SpectralObject`. It proves that the mapping cone gives a spectral object, indexed by `CochainComplex C ℤ`, with values in the homotopy category; it is `HomotopyCategory.spectralObjectMappingCone`. Its documentation notes that each functor from `ι` to cochain complexes, for example a filtered complex, then gives a spectral object indexed by `ι`, after a homological functor is applied. The index of this edition has no declaration for the spectral sequence of a filtered complex or of a bicomplex as a named object, and none for a convergence theorem. The text of this section proves the convergence for a finite chain by hand.

Common errors of a learner:

- A `SpectralSequence` has no abutment. Statements on convergence are statements about the spectral object.
- In `X.δ f g`, the source is `H^n(g)` and the target is `H^{n+1}(f)`; the second arrow comes first.
- `EInt` is `WithBotTop ℤ`. The indices $\pm\infty$ are elements of the index type, so the page at infinity is a value of `X.E`, not a limit.
- In `coreE₂Cohomological`, the index $q$ of the filtration is the second coordinate. A filtration indexed by $p$ needs a change of variables.

### Exercises

1. (A) Check that the differential $d_r$ of a cohomological spectral sequence raises the total degree $p + q$ by $1$. *Hint:* add the two coordinates of $(r, 1 - r)$.
2. (A) Show that $E^n(f_1, f_2, f_3) = 0$ when $H^n(f_2) = 0$. *Hint:* a subquotient of zero is zero.
3. (B) In the example of a short exact sequence, compute $E^n(0 \leq 0 \leq 2 \leq 2)$ and show that it is $H^n(K)$. *Hint:* use the lemma on isomorphisms for the two outer arrows.
4. (B) Let $X$ be indexed by $0 < 1 < 2$. Show that $E^n(0 \leq 1 \leq 2 \leq 2) \cong \ker(H^n(1 \leq 2) \to H^{n+1}(0 \leq 1))$ by the definition, and also from the theorem on E as a kernel. *Hint:* in the theorem, $H^n(f_3) = 0$.
5. (B) For the $E_2$ recipe, show that the object of page $r$ at $(p, q)$ is the object of page $r + 1$ when the incoming and outgoing differentials of page $r$ at $(p, q)$ are zero. *Hint:* use the isomorphism $H(E_r) \cong E_{r+1}$.
6. (C) Let $E$ be a first quadrant $E_2$ cohomological spectral sequence with $E_2^{p,q} = 0$ for $q \notin \{0, 1\}$, from a spectral object whose abutment has a two-step filtration with graded pieces $E_3^{n,0}$ and $E_3^{n-1,1}$. Derive the exact sequence $\cdots \to E_2^{n,0} \to H^n \to E_2^{n-1,1} \xrightarrow{d_2} E_2^{n+1,0} \to H^{n+1} \to \cdots$. *Hint:* all $d_r$ with $r \geq 3$ are zero, $E_3^{n,0}$ is the cokernel of $d_2 : E_2^{n-2,1} \to E_2^{n,0}$, and $E_3^{n-1,1}$ is the kernel of $d_2 : E_2^{n-1,1} \to E_2^{n+1,0}$.
7. (C) Let $X$ be indexed by $0 < 1 < \cdots < m$ and suppose that $H^n(q \leq q + 1) = 0$ for all $q$ and $n$. Prove that $H^n(i \leq j) = 0$ for all $i \leq j$. *Hint:* induction on $j - i$ with the exact sequence of the pair $(i \leq j - 1, j - 1 \leq j)$.

### Notes and history

Spectral sequences come from the work of Jean Leray on sheaf cohomology in the 1940s. The spectral sequence of a filtered complex and of a double complex is in Cartan and Eilenberg, *Homological Algebra* (1956). The spectral objects are in the thesis of Verdier, *Des catégories dérivées des catégories abéliennes*, cited in the Mathlib source.

The Mathlib Authors of all six modules of this section are Joël Riou, in 2026.

### Reference

<?reference?>
