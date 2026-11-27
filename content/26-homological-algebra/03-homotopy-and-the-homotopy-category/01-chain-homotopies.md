---
title: Chain homotopies
kind: theory
modules:
  - Mathlib.Algebra.Homology.Homotopy
  - Mathlib.Algebra.Homology.HomotopyCofiber
  - Mathlib.Algebra.Homology.HomotopyCategory
explains:
  E3: [Homotopy, HomotopyEquiv, Homotopy.nullHomotopicMap, Homotopy.homologyMap_eq, HomologicalComplex.homotopyCofiber, HomologicalComplex.homotopyCofiber.descEquiv, HomotopyCategory, HomotopyCategory.quotient, HomotopyCategory.homologyFunctor]
  E2: [Homotopy.equivSubZero, Homotopy.ofEq, Homotopy.refl, Homotopy.symm, Homotopy.trans, Homotopy.add, Homotopy.compLeft, Homotopy.compRight, Homotopy.comp, Homotopy.mkInductive, Homotopy.mkCoinductive, Homotopy.sub_eq_nullHomotopicMap, HomotopyEquiv.refl, HomotopyEquiv.symm, HomotopyEquiv.trans, HomotopyEquiv.ofIso, HomotopyEquiv.toHomologyIso, CategoryTheory.Functor.mapHomotopy, CategoryTheory.Functor.mapHomotopyEquiv, HomologicalComplex.homotopyEquivalences, HomologicalComplex.HasHomotopyCofiber, HomologicalComplex.homotopyCofiber.inr, HomologicalComplex.homotopyCofiber.inrCompHomotopy, HomologicalComplex.homotopyCofiber.desc, HomologicalComplex.cylinder, HomologicalComplex.cylinder.ι₀, HomologicalComplex.cylinder.ι₁, HomologicalComplex.cylinder.π, HomologicalComplex.cylinder.desc, HomologicalComplex.cylinder.homotopyEquiv, HomologicalComplex.cylinder.homotopy₀₁, Homotopy.map_eq_of_inverts_homotopyEquivalences, homotopic, HomotopyCategory.quotient_map_eq_zero_iff, HomotopyCategory.homotopyOfEq, HomotopyCategory.isoOfHomotopyEquiv, HomotopyCategory.homotopyEquivOfIso, HomotopyCategory.quotient_inverts_homotopyEquivalences, HomotopyCategory.isZero_quotient_obj_iff, HomotopyCategory.homologyFunctorFactors, CategoryTheory.Functor.mapHomotopyCategory, HomologicalComplex.isIso_quotient_map_iff_homotopyEquivalences]
  E1: auto
families: []
requires: [V24.C08, V25.C01, V25.C02, V25.C03, V26.C01, V26.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Chain homotopies

### Overview

Two maps of complexes can differ and still induce the same map on homology. The usual reason is a chain homotopy: a family of maps that shift the degree by one, whose boundary is the difference of the two maps. Homotopy makes projective resolutions unique up to homotopy, and so it makes the derived functors of Chapter 4 well defined.

This section defines homotopies for complexes of every shape and proves that homotopic maps induce the same map on homology. It defines homotopy equivalences and gives an exact complex that is not contractible. It constructs the homotopy cofiber of a map and the cylinder of a complex, and it forms the homotopy category, whose morphisms are the homotopy classes of maps. Section 2 gives this category a triangulated structure.

The category $C$ is preadditive, and abelian where homology appears. Mathlib writes `f ≫ g` for $g \circ f$.

### Definitions

Let $c$ be a complex shape on an index type $\iota$ and let $K$ and $L$ be complexes of shape $c$ in $C$. Recall from Chapter 2 that $d_{ij}$ can be nonzero only if $c.\mathrm{Rel}\, i\, j$, and that `c.next i` and `c.prev i` are the indices after and before $i$.

**Definition (Homotopy).** Let $f, g : K \to L$ be maps of complexes. A *homotopy* from $f$ to $g$ is a family of maps $h_{ij} : K_i \to L_j$ with $h_{ij} = 0$ unless $c.\mathrm{Rel}\, j\, i$, such that for each $i$
$$f_i - g_i = h_{i', i} \circ d_{i, i'} + d_{i'', i} \circ h_{i, i''}, \qquad i' = \mathrm{next}(i), \quad i'' = \mathrm{prev}(i).$$
So $h$ goes against the direction of the differential. For a chain complex the components are $h_n : K_n \to L_{n+1}$ and the condition reads $f_n - g_n = h_{n-1} d_n + d_{n+1} h_n$, with $h_{-1} = 0$. For a cochain complex the components are $h^n : K^n \to L^{n-1}$ and $f^n - g^n = h^{n+1} d^n + d^{n-1} h^n$. The maps $f$ and $g$ are *homotopic*, written $f \simeq g$, if a homotopy from $f$ to $g$ exists.

**Definition (Null homotopic map).** For any family $h$ as above, the right side $dh + hd$ of the formula is a map of complexes $K \to L$. A map of this form is *null homotopic*. So $f \simeq g$ if and only if $f - g \simeq 0$.

**Definition (Homotopy equivalence).** A *homotopy equivalence* from $K$ to $L$ is a pair of maps $f : K \to L$ and $g : L \to K$ with homotopies $g f \simeq 1_K$ and $f g \simeq 1_L$. The complex $K$ is *contractible* if $1_K \simeq 0$, that is, if $K$ is homotopy equivalent to the zero complex. A contraction of $K$ is a homotopy from $1_K$ to $0$.

::: mathlib
`Homotopy` · `Mathlib.Algebra.Homology.Homotopy`

The structure `Homotopy f g` has a field `hom : ∀ i j, C.X i ⟶ D.X j`, a field `zero : ∀ i j, ¬ c.Rel j i → hom i j = 0`, and a field `comm : ∀ i, f.f i = dNext i hom + prevD i hom + g.f i`. Here `dNext i hom` is `C.d i (c.next i) ≫ hom (c.next i) i`, the composite $h \circ d$, and `prevD i hom` is `hom i (c.prev i) ≫ D.d (c.prev i) i`, the composite $d \circ h$. Indexing by all pairs $(i, j)$ lets one structure serve every shape, and `zero` kills the extra components. `Homotopy.nullHomotopicMap hom` is the map $dh + hd$, and `Homotopy.equivSubZero` identifies `Homotopy f g` with `Homotopy (f - g) 0`.

<?decl Homotopy?>
:::

**Definition (Homotopy cofiber).** Let $\varphi : F \to G$ be a map of complexes of shape $c$ and assume that the biproduct $F_j \oplus G_i$ exists whenever $c.\mathrm{Rel}\, i\, j$. The *homotopy cofiber* of $\varphi$ is the complex $\mathrm{Cof}(\varphi)$ with
$$\mathrm{Cof}(\varphi)_i = F_j \oplus G_i \ \text{ if } c.\mathrm{Rel}\, i\, j, \qquad \mathrm{Cof}(\varphi)_i = G_i \ \text{ otherwise},$$
and with the differential $d(x, y) = (-d x, \varphi x + d y)$ in matrix form. For a cochain complex this is $\mathrm{Cof}(\varphi)^n = F^{n+1} \oplus G^n$, which is the mapping cone of Section 2. The map $\mathrm{inr} : G \to \mathrm{Cof}(\varphi)$ is the inclusion $y \mapsto (0, y)$.

The square of the differential is zero: $d(-dx, \varphi x + dy) = (d d x, -\varphi d x + d \varphi x + d d y) = (0, 0)$, because $\varphi$ commutes with $d$.

**Definition (Cylinder).** The *cylinder* of a complex $K$ is the homotopy cofiber of the map $(1, -1) : K \to K \oplus K$. It comes with two maps $\iota_0, \iota_1 : K \to \mathrm{Cyl}(K)$, the two inclusions $K \to K \oplus K$ followed by $\mathrm{inr}$, and a projection $\pi : \mathrm{Cyl}(K) \to K$.

**Definition (Homotopy category).** The relation $\simeq$ on each set of maps $K \to L$ is a congruence (see the proposition below). The *homotopy category* $K(C, c)$ is the quotient category: its objects are the complexes of shape $c$, and its morphisms are the homotopy classes of maps. The quotient functor $Q : \mathrm{HomologicalComplex}(C, c) \to K(C, c)$ is the identity on objects.

### Theorems and proofs

**Proposition (Homotopy is a congruence).** Let $f, f', g, g' : K \to L$, $p : J \to K$ and $q : L \to M$ be maps of complexes.

1. $f \simeq f$; if $f \simeq g$ then $g \simeq f$; if $f \simeq g$ and $g \simeq g'$ then $f \simeq g'$.
2. If $f \simeq g$ and $f' \simeq g'$ then $f + f' \simeq g + g'$.
3. If $f \simeq g$ then $q f \simeq q g$ and $f p \simeq g p$.

*Proof.* Use the formula $f - g = dh + hd$. For part 1, the zero family goes from $f$ to $f$, the family $-h$ from $g$ to $f$, and if $h$ goes from $f$ to $g$ and $k$ from $g$ to $g'$, then $h + k$ goes from $f$ to $g'$. For part 2, $h + h'$ goes from $f + f'$ to $g + g'$. For part 3, $q$ commutes with the differentials, so
$$q f - q g = q d h + q h d = d (q h) + (q h) d.$$
and $q h$, which vanishes where $h$ vanishes, is a homotopy from $q f$ to $q g$. In the same way $h p$ is a homotopy from $f p$ to $g p$. $\square$

By part 3 and transitivity, $f \simeq g$ and $f' \simeq g'$ give $f' f \simeq g' g$. So composition of homotopy classes is well defined, the homotopy category exists, it is preadditive by part 2, and $Q$ is additive.

**Theorem (Homotopic maps agree on homology).** Let $C$ be abelian and let $f \simeq g : K \to L$. Then $H_i(f) = H_i(g)$ for each $i$.

*Proof.* Since $H_i$ is additive, $H_i(f) - H_i(g) = H_i(f - g)$, and it suffices to show that a null homotopic map $u = dh + hd$ induces zero on homology. The proof uses elements; in an abelian category the pseudoelements of Volume 25, Chapter 2 work the same way. Fix $i$, let $i' = \mathrm{next}(i)$ and $i'' = \mathrm{prev}(i)$. Let $z \in K_i$ be a cycle, so $d_{i,i'} z = 0$. Then
$$u_i(z) = h_{i',i}(d_{i,i'} z) + d_{i'',i}(h_{i,i''} z) = d_{i'',i}(h_{i,i''} z).$$
So $u_i(z)$ is a boundary in $L_i$, and its class in $H_i(L)$ is zero. The class of $z$ was arbitrary, so $H_i(u) = 0$. $\square$

**Corollary (Homotopy equivalences are quasi-isomorphisms).** A homotopy equivalence $f : K \to L$ with inverse $g$ induces isomorphisms $H_i(f) : H_i(K) \to H_i(L)$ with inverse $H_i(g)$. A contractible complex is acyclic.

*Proof.* By the theorem, $H_i(g) H_i(f) = H_i(g f) = H_i(1_K) = 1$, and in the same way $H_i(f) H_i(g) = 1$. For contractible $K$, $1_K \simeq 0$ gives $1_{H_i(K)} = 0$. $\square$

**Theorem (Maps out of the homotopy cofiber).** Let $\varphi : F \to G$ and assume that every index $j$ has an index $i$ with $c.\mathrm{Rel}\, i\, j$ (this holds for cochain complexes indexed by $\mathbb{Z}$). For each complex $K$, the maps of complexes $\mathrm{Cof}(\varphi) \to K$ correspond bijectively to pairs $(\alpha, s)$ where $\alpha : G \to K$ is a map of complexes and $s$ is a homotopy from $\alpha \varphi$ to $0$. The map $\beta$ goes to $\alpha = \beta \circ \mathrm{inr}$.

*Proof.* Write it for cochain complexes indexed by $\mathbb{Z}$, where $\mathrm{Cof}(\varphi)^n = F^{n+1} \oplus G^n$. A family of maps $\beta^n : F^{n+1} \oplus G^n \to K^n$ is the same as two families $s^{n+1} : F^{n+1} \to K^n$ and $\alpha^n : G^n \to K^n$ with $\beta^n(x, y) = s^{n+1} x + \alpha^n y$. The family $\beta$ is a map of complexes if and only if $d \beta^n = \beta^{n+1} d$ for each $n$. Evaluate both sides on $(x, y)$:
$$d s^{n+1} x + d \alpha^n y = s^{n+2}(-d x) + \alpha^{n+1}(\varphi x + d y).$$
Take $x = 0$: the condition is $d \alpha^n = \alpha^{n+1} d$, so $\alpha$ is a map of complexes. Take $y = 0$: the condition is $\alpha^{n+1} \varphi^{n+1} = d s^{n+1} + s^{n+2} d$ on $F^{n+1}$. This is the condition that the family $s$, with $s^{m} : F^{m} \to K^{m-1}$, is a homotopy from $\alpha \varphi$ to $0$. By additivity the two conditions are equivalent to the condition on $(x, y)$, so $\beta \mapsto (\alpha, s)$ is a bijection. $\square$

For $\beta = 1$ the pair is $(\mathrm{inr}, s)$ with $s^{n+1}(x) = (x, 0)$, so $\mathrm{inr} \circ \varphi$ is null homotopic.

**Corollary (Homotopies as maps out of the cylinder).** Keep the hypothesis on the shape and assume that $C$ has binary biproducts. Let $f_0, f_1 : K \to L$. A homotopy from $f_0$ to $f_1$ gives a map $\mathrm{Cyl}(K) \to L$ whose composites with $\iota_0$ and $\iota_1$ are $f_0$ and $f_1$. In particular $\pi \iota_0 = \pi \iota_1 = 1_K$, and $\iota_0 \simeq \iota_1$.

*Proof.* A map $\alpha : K \oplus K \to L$ is a pair $(f_0, f_1)$, and $\alpha \circ (1, -1) = f_0 - f_1$. By the theorem, a map $\mathrm{Cyl}(K) \to L$ is a pair $(\alpha, s)$ with $s$ a homotopy from $f_0 - f_1$ to $0$, that is, from $f_0$ to $f_1$. The map $\pi$ comes from $f_0 = f_1 = 1_K$ and the zero homotopy. The identity of $\mathrm{Cyl}(K)$ gives the pair $(\mathrm{inr}, s)$, and $\mathrm{inr}$ is the pair $(\iota_0, \iota_1)$, so $s$ is a homotopy from $\iota_0$ to $\iota_1$. $\square$

**Theorem (Universal property of the homotopy category).** Keep the hypotheses of the corollary. The quotient functor $Q$ sends homotopy equivalences to isomorphisms, and a map $f$ with $Q(f)$ an isomorphism is a homotopy equivalence. A functor $G$ from complexes to a category $D$ factors through $Q$ if and only if $G$ inverts the homotopy equivalences, and then the factorization is unique.

*Proof.* If $(f, g)$ is a homotopy equivalence, then $Q(g) Q(f) = Q(1) = 1$ and $Q(f) Q(g) = 1$. If $Q(f)$ has an inverse, it is $Q(g)$ for some $g$ because $Q$ is full, and $Q(g f) = 1$, $Q(f g) = 1$ say that $g f \simeq 1$ and $f g \simeq 1$. A functor $\bar G \circ Q$ inverts what $Q$ inverts. Conversely, let $G$ invert the homotopy equivalences and let $f_0 \simeq f_1 : K \to L$. Mathlib proves that $\pi : \mathrm{Cyl}(K) \to K$ is a homotopy equivalence with inverse $\iota_0$, so $G(\pi)$ is an isomorphism. The equalities $\pi \iota_0 = \pi \iota_1 = 1_K$ give $G(\iota_0) = G(\iota_1)$. With $\beta$ the map of the corollary, $G(f_0) = G(\beta) G(\iota_0) = G(\beta) G(\iota_1) = G(f_1)$. So $G$ is constant on homotopy classes and factors through the quotient, uniquely because $Q$ is the identity on objects and surjective on maps. $\square$

So $K(C, c)$ is the localization of the category of complexes at the homotopy equivalences, and by the first theorem $H_i$ factors through $Q$.

### Examples

**Example (A contractible complex).** Let $K$ be the cochain complex $\mathbb{Z} \xrightarrow{1} \mathbb{Z}$ in degrees $0$ and $1$. The map $h^1 = 1 : K^1 \to K^0$, with all other components zero, is a contraction. Check the condition in degree $0$: $h^1 d^0 + d^{-1} h^0 = 1 \cdot 1 + 0 = 1$. In degree $1$: $h^2 d^1 + d^0 h^1 = 0 + 1 = 1$.

**Counterexample (Acyclic but not contractible).** Let $K$ be the cochain complex with $K^n = \mathbb{Z}/4$ for every $n \in \mathbb{Z}$ and every differential equal to multiplication by $2$. Then $d^2 = 4 = 0$. The kernel and the image of multiplication by $2$ on $\mathbb{Z}/4$ are both $\{0, 2\}$, so $K$ is acyclic. Assume a contraction $h$ exists. Each $h^n$ is multiplication by some $a_n$. The condition in degree $n$ is $1 = h^{n+1} d^n + d^{n-1} h^n = 2 a_{n+1} + 2 a_n$ in $\mathbb{Z}/4$. The right side is even and $1$ is odd, a contradiction. So $K$ is not contractible, and the zero map $0 \to K$ is a quasi-isomorphism that is not a homotopy equivalence.

**Example (Two homotopic maps).** Let $K$ be the chain complex $\mathbb{Z} \xrightarrow{2} \mathbb{Z}$ in degrees $1$ and $0$. Its homology is $H_0 = \mathbb{Z}/2$ and $H_1 = 0$. Let $f = 1_K$ and $g = 3 \cdot 1_K$. The difference $f - g = -2$ is multiplication by $-2$ in both degrees. Take $h_0 = -1 : K_0 \to K_1$. In degree $0$, $h_{-1} d_0 + d_1 h_0 = 0 + 2 \cdot (-1) = -2$. In degree $1$, $h_0 d_1 + d_2 h_1 = (-1) \cdot 2 + 0 = -2$. So $1 \simeq 3$. On $H_0 = \mathbb{Z}/2$ both maps act as the identity, since $3 \equiv 1 \pmod 2$, as the theorem predicts.

**Example (The homotopy cofiber of the identity).** Let $\varphi = 1_F$ for a cochain complex $F$. Then $\mathrm{Cof}(1_F)^n = F^{n+1} \oplus F^n$ with $d(x, y) = (-dx, x + dy)$. The maps $s^n(x, y) = (y, 0)$ from degree $n$ to degree $n-1$ form a contraction. Check: $(s d + d s)(x, y) = s(-dx, x + dy) + d(y, 0) = (x + dy, 0) + (-dy, y) = (x, y)$. So the cone of an identity is contractible, and it is zero in the homotopy category. Section 2 uses this fact.

### The library around it

::: mathlib
`Homotopy.homologyMap_eq` · `Mathlib.Algebra.Homology.Homotopy`

For `ho : Homotopy f g` the lemma gives `homologyMap f i = homologyMap g i`. The proof passes to the short complexes of Chapter 1 with `Homotopy.toShortComplex`. `HomotopyEquiv.toHomologyIso` gives the isomorphism of homology for a homotopy equivalence.

<?decl Homotopy.homologyMap_eq?>
:::

The constructions of the congruence proposition are `Homotopy.refl`, `symm`, `trans`, `add`, `compLeft`, `compRight` and `comp`, and `Homotopy.ofEq` turns `f = g` into a homotopy. `HomotopyEquiv C D` has fields `hom`, `inv`, `homotopyHomInvId` and `homotopyInvHomId`. The class `HomologicalComplex.homotopyEquivalences C c` is a `MorphismProperty` (Volume 25, Chapter 3). An additive functor acts by `Functor.mapHomotopy` and `Functor.mapHomotopyEquiv`. 

For chain complexes indexed by $\mathbb{N}$, `Homotopy.mkInductive` builds a homotopy `Homotopy e 0` degree by degree: each new component solves an equation that involves only the two components before it. `Homotopy.mkCoinductive` is the version for cochain complexes. Chapter 4 uses it to compare projective resolutions.

::: mathlib
`HomologicalComplex.homotopyCofiber` · `Mathlib.Algebra.Homology.HomotopyCofiber`

The class `HasHomotopyCofiber φ` asks for the biproducts `F.X j ⊞ G.X i` when `c.Rel i j`. The complex `homotopyCofiber φ` has the differential `-fst ≫ F.d ≫ inl + fst ≫ φ ≫ inr + snd ≫ G.d ≫ inr` on the summands, which is the matrix of the definition. `homotopyCofiber.inr φ` is the inclusion of `G`, `inrCompHomotopy` is the homotopy `φ ≫ inr φ ≃ 0`, and `homotopyCofiber.desc` builds a map out of the cofiber from a map `α` and a homotopy `φ ≫ α ≃ 0`. The bijection of the theorem is `descEquiv`, under the hypothesis `hc : ∀ j, ∃ i, c.Rel i j`.

<?decl HomologicalComplex.homotopyCofiber.descEquiv?>
:::

The cylinder is `HomologicalComplex.cylinder K`, with `cylinder.ι₀`, `cylinder.ι₁`, `cylinder.π`, `cylinder.desc`, `cylinder.homotopyEquiv` and `cylinder.homotopy₀₁`. The last step of the universal property is `Homotopy.map_eq_of_inverts_homotopyEquivalences`.

::: mathlib
`HomotopyCategory` · `Mathlib.Algebra.Homology.HomotopyCategory`

The relation `homotopic V c` is a `HomRel`, a congruence by the instance `homotopy_congruence`. `HomotopyCategory V c` is the quotient category, and `HomotopyCategory.quotient V c` is the quotient functor, full, additive and linear. `quotient_map_eq_zero_iff` characterizes the maps that become zero, `homotopyOfEq` extracts a homotopy from an equality in the quotient, and `isoOfHomotopyEquiv` and `homotopyEquivOfIso` translate between isomorphisms and homotopy equivalences.

<?decl HomotopyCategory?>
:::

`HomotopyCategory.quotient_inverts_homotopyEquivalences` and `HomologicalComplex.isIso_quotient_map_iff_homotopyEquivalences` are the first part of the universal property. `isZero_quotient_obj_iff` says that a complex is zero in the homotopy category if and only if it is contractible. `HomotopyCategory.homologyFunctor V c i` is homology on the quotient, with `homologyFunctorFactors`, and `Functor.mapHomotopyCategory` is induced by an additive functor.

Common errors of a learner:

- The homotopy goes against the differential. For a cochain complex the components are `hom i (i - 1)`, not `hom i (i + 1)`. A family in the wrong direction is killed by the field `zero`.
- A homotopy is data, not a proposition. Two homotopies with the same ends need not be equal.
- An acyclic complex need not be zero in the homotopy category (the counterexample with $\mathbb{Z}/4$).

### Exercises

1. (A) Let $u : A \to B$ be a map of abelian groups and view it as a cochain complex in degrees $0$ and $1$. Show that the complex is contractible if and only if $u$ is an isomorphism.
2. (A) Show that the map $n \cdot 1_K$ on the chain complex $K = (\mathbb{Z} \xrightarrow{n} \mathbb{Z})$ is null homotopic. Deduce that $H_0(K) = \mathbb{Z}/n$ is killed by $n$. *Hint:* use $h_0 = 1$.
3. (B) Let $K$ be a complex of vector spaces over a field. Show that $K$ is homotopy equivalent to the complex $H(K)$ of its homology groups with zero differential. *Hint:* split each $K^n$ as $B^n \oplus H^n \oplus E^n$ with $d : E^n \to B^{n+1}$ an isomorphism, and build the contraction of the part $B \oplus E$.
4. (B) Let $A$ and $B$ be abelian groups, viewed as complexes concentrated in degree $0$. Show that no nonzero map $A \to B$ is null homotopic, so the morphisms from $A$ to $B$ in the homotopy category are the group homomorphisms. *Hint:* the components of a homotopy go to degree $-1$ or $+1$.
5. (C) Let $\varphi : F \to G$ be a map of cochain complexes. Show that $\varphi$ is a homotopy equivalence if and only if $\mathrm{Cof}(\varphi)$ is contractible. *Hint:* for one direction use the universal property of the cofiber with $K = F[1]$; for the other, Section 2 gives a cleaner proof with triangles.
6. (C) Let $C$ be abelian. Show that a complex $K$ is contractible if and only if it is acyclic and each short exact sequence $0 \to Z^n \to K^n \to B^{n+1} \to 0$ splits. *Hint:* a contraction gives a section of $d : K^n \to B^{n+1}$; conversely, build $h$ from the splittings.

### Notes and history

Chain homotopy comes from algebraic topology, where a homotopy between continuous maps induces a chain homotopy between the maps of singular chains. Cartan and Eilenberg, *Homological Algebra* (1956), made it the base of the comparison theorem for resolutions. The cylinder and the cofiber copy the topological cylinder and mapping cone.

The Mathlib Authors of `Homotopy` and `HomotopyCategory` are Kim Morrison. The file `HomotopyCofiber` is by Joël Riou.

### Reference

<?reference?>
