---
title: Functoriality of group homology and continuous cohomology
kind: api
modules:
  - Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality
  - Mathlib.RepresentationTheory.Homological.GroupHomology.Shapiro
  - Mathlib.RepresentationTheory.Homological.ContCohomology.Basic
  - Mathlib.RepresentationTheory.Homological.ContCohomology.Functoriality
  - Mathlib.RepresentationTheory.Homological.ContCohomology.LowDegree
  - Mathlib.RepresentationTheory.Homological.ContCohomology.Sha
explains:
  E2: [groupHomology.chainsMap, groupHomology.map, groupHomology.coresNatTrans, groupHomology.coinfNatTrans, groupHomology.H1CoresCoinf_exact, groupHomology.indIso, TopRep.homogeneousCochains, continuousCohomology, ContinuousCohomology.map, ContinuousCohomology.tateShafarevich]
  E1: auto
families: []
requires: [V05.C06, V11.C05, V13.C01, V26.C02, V26.C04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Functoriality of group homology and continuous cohomology

### Overview

Section 3 makes group cohomology a functor of the pair of a group and a representation. This section does the same for group homology, where the direction of the group morphism is the opposite one. A group morphism $f : G \to H$, a $G$-representation $A$, an $H$-representation $B$ and a morphism from $A$ to the restriction of $B$ give a map $H_n(G, A) \to H_n(H, B)$. The special cases are corestriction from a subgroup and coinflation to a quotient group, and in degree $1$ they form an exact sequence. Shapiro's lemma for homology identifies the homology of an induced representation with the homology of the subgroup.

The second part of the section defines continuous cohomology for a topological group $G$ and a topological representation. Galois groups of infinite extensions and the groups of $p$-adic integers are the main examples, and for them the cohomology of the bare group gives the wrong answer. Continuous cohomology uses continuous cochains. It is functorial in the pair of a continuous group morphism and a morphism of representations, its degree $0$ is the module of invariants, and it gives the Tate-Shafarevich group of a Galois module as the kernel of the maps to the cohomology of a family of local Galois groups.

Throughout, $k$ is a commutative ring for group homology and a topological ring for continuous cohomology. Representations of the second part are objects of `TopRep` $k$ $G$ from Volume 29, where each element of $G$ acts by a continuous linear map.

### The library around it

#### Functoriality of group homology

Let $f : G \to H$ be a group morphism, $A$ in `Rep` $k$ $G$, $B$ in `Rep` $k$ $H$ and $\varphi$ a morphism from $A$ to `Rep.res` $f$ $B$. The map `groupHomology.chainsMap` $f$ $\varphi$ is the morphism of inhomogeneous chain complexes of Section 1 that sends a chain $a \cdot [g_1, \dots, g_n]$ to $\varphi(a) \cdot [f(g_1), \dots, f(g_n)]$. The map on homology is `groupHomology.map` $f$ $\varphi$ $n$, from $H_n(G, A)$ to $H_n(H, B)$. The main data are:

| Lean name | Statement |
|---|---|
| `groupHomology.map_id` | the identity pair gives the identity map |
| `groupHomology.map_comp` | the map of a composition of pairs is the composition of the maps |
| `groupHomology.mapIso` | a group isomorphism $G \cong H$ and a compatible linear equivalence $A \cong B$ give an isomorphism of homology |
| `groupHomology.functor` | the functor from `Rep` $k$ $G$ to $k$-modules, for each degree $n$ |
| `groupHomology.chainsFunctor` | the functor that sends a representation to its inhomogeneous chains |
| `groupHomology.mapShortComplexH1` | the map of the explicit short complexes of Section 2 in degree $1$ |
| `groupHomology.mapShortComplexH2` | the same in degree $2$ |

The lemmas `groupHomology.H1π_comp_map` and `groupHomology.H2π_comp_map` say that the map agrees with the explicit maps of cycles in low degrees, written with `groupHomology.mapCycles₁` and `groupHomology.mapCycles₂`. The instance `groupHomology.epi_map_0_of_epi` says that an epimorphism of representations gives an epimorphism in degree $0$, since $H_0$ is the module of coinvariants, a right exact functor.

#### Corestriction and coinflation

For a group morphism $f : G \to H$, the natural transformation `groupHomology.coresNatTrans` $k$ $f$ $n$ goes from restriction along $f$ followed by $H_n(G, -)$ to $H_n(H, -)$. For the inclusion of a subgroup $S$ of $G$, this is corestriction $H_n(S, A) \to H_n(G, A)$. For a normal subgroup $S$, the natural transformation `groupHomology.coinfNatTrans` is coinflation $H_n(G, A) \to H_n(G/S, A_S)$, where $A_S$ is the representation of coinvariants of $A$ under $S$, given by `Rep.quotientToCoinvariantsFunctor`.

In degree $1$ these maps form the short complex `groupHomology.H1CoresCoinf`
$$H_1(S, A) \to H_1(G, A) \to H_1(G/S, A_S),$$
and `groupHomology.H1CoresCoinf_exact` says that it is exact. Its second map is an epimorphism, by an instance. When $S$ acts trivially on $A$, the short complex `groupHomology.H1CoresCoinfOfTrivial` is a simpler form of the same sequence, with $H_1(G/S, A)$ as the last term, and `groupHomology.H1CoresCoinfOfTrivial_exact` is its exactness. This is the dual of the inflation and restriction sequence of Section 3.

#### Shapiro's lemma for homology

For a subgroup $S$ of $G$ and an $S$-representation $A$, `groupHomology.indIso` $S$ $A$ $n$ is an isomorphism from $H_n(G, \operatorname{Ind}_S^G A)$ to $H_n(S, A)$, where `Rep.ind` is induction. The proof restricts a projective resolution $P$ of the trivial $G$-representation to $S$, and uses `groupHomology.coinvariantsTensorResProjectiveResolutionIso`, which identifies the coinvariants of $A \otimes P$ over $S$ with the coinvariants of $\operatorname{Ind} A \otimes P$ over $G$. The cohomology form with coinduction is `groupCohomology.coindIso` of Section 3.

#### Continuous cohomology

For $X$ in `TopRep` $k$ $G$, the cochain complex `TopRep.resolution` $X$ has the objects `TopRep.resolutionX`:
$$X \to C(G, X) \to C(G, C(G, X)) \to \cdots,$$
where $C(G, -)$ is the representation of continuous maps of `TopRep.coind₁Functor`. The first differential `TopRep.d` sends $x$ to the constant map with value $x$, and the next ones are defined by induction, $d_{n+1}(\sigma) = \mathrm{const}(\sigma) - C(G, d_n)(\sigma)$. The lemma `TopRep.d_comp_d` says that $d \circ d = 0$.

The complex `TopRep.homogeneousCochains` $X$ is the image of this complex, from degree $1$, under the functor of invariants `TopRep.invariantsFunctor`. Its terms are invariant continuous maps $G \to C(G, \dots, C(G, X))$, the homogeneous cochains. They are iterated continuous maps and not maps on $G^{n+1}$, so the definition works for topological groups that are not locally compact. The object `continuousCohomology` $n$ $X$ is the homology of this complex in degree $n$, an object of `TopModuleCat` $k$. The cocycles are `ContinuousCohomology.cocycles` and the projection is `ContinuousCohomology.π`.

In degree $0$, `ContinuousCohomology.zeroIso` is an isomorphism from `continuousCohomology` $0$ $X$ to the invariants of $X$, and `ContinuousCohomology.d₀kerIso` is the continuous linear equivalence between the kernel of the first differential and the invariants.

#### Functoriality and the Tate-Shafarevich group

For topological groups $G$ and $H$, a continuous group morphism $\varphi : H \to G$, $X$ in `TopRep` $k$ $G$, $Y$ in `TopRep` $k$ $H$ and a morphism $f$ from `TopRep.res` $\varphi$ $X$ to $Y$, the cochain map `ContinuousCohomology.cochainsMap` $\varphi$ $f$ sends an invariant cochain $\sigma$ to $f \circ \sigma \circ \varphi$. The map on cohomology is `ContinuousCohomology.map` $\varphi$ $f$ $n$, from $H^n(G, X)$ to $H^n(H, Y)$. The lemmas `ContinuousCohomology.map_id` and `ContinuousCohomology.map_comp` give the functoriality, and `ContinuousCohomology.π_map` the compatibility with the cocycles.

Let $K$ be a field, $A$ a topological representation of the absolute Galois group `Field.absoluteGaloisGroup` $K$ over $\mathbb{Z}$, and $f$ a family of field extensions $K_v$ of $K$ indexed by a type $V$. The subgroup `ContinuousCohomology.tateShafarevich` $f$ $A$ $n$ of $H^n(G_K, A)$ is the intersection of the kernels of the maps $H^n(G_K, A) \to H^n(G_{K_v}, A)$ that `Field.absoluteGaloisGroup.map` induces. The lemma `ContinuousCohomology.mem_tateShafarevich` says that a class is in it iff each of these maps sends it to zero, and `ContinuousCohomology.tateShafarevich_eq_iInf` and `ContinuousCohomology.tateShafarevich_eq_ker_pi` give the two other forms. For a number field and its completions this is the classical Tate-Shafarevich group.

#### Common errors

1. Group homology is covariant in the group and continuous cohomology is contravariant. For `groupHomology.map` the group morphism goes from $G$ to $H$ and the morphism of representations goes from $A$ to the restriction of $B$; for `ContinuousCohomology.map` the group morphism goes from $H$ to $G$ and the morphism goes from the restriction of $X$ to $Y$.
2. `continuousCohomology` is an object of `TopModuleCat` $k$, not a $k$-module. To use an element, pass to the underlying $k$-module of this object, as the statement of `ContinuousCohomology.tateShafarevich` does.
3. The library does not yet prove that continuous cohomology agrees with `groupCohomology` for a discrete group, and it has no long exact sequence for continuous cohomology. A proof that needs these facts must prove them first.

### Exercises

1. (A) Write the map `groupHomology.chainsMap` in degree $1$ for the quotient map $\mathbb{Z} \to \mathbb{Z}/n$ and the trivial representation $\mathbb{Z}$, and compute the map on $H_1$.
2. (A) Show that `ContinuousCohomology.zeroIso` is natural: for a morphism of representations over the identity of $G$, the map on $H^0$ is the restriction of the morphism to the invariants.
3. (B) For a normal subgroup $S$ of $G$ and the trivial representation $\mathbb{Z}$, use `groupHomology.H1CoresCoinfOfTrivial_exact` to get the exact sequence $S^{ab} \to G^{ab} \to (G/S)^{ab} \to 0$, and check it for $G = S_3$ and $S$ the alternating group.
4. (B) Use `groupHomology.indIso` to compute $H_n(G, k[G])$ for $n \ge 1$, where $k[G]$ is the regular representation, induced from the trivial subgroup.
5. (B) Use `ContinuousCohomology.tateShafarevich_eq_iInf` to show that a larger family of extensions gives a smaller Tate-Shafarevich group, and that the empty family gives all of $H^n(G_K, A)$.
6. (C) Write the homogeneous cochains of degree $1$ as invariant continuous maps $G \to C(G, X)$, and show that the cocycles of degree $1$ correspond to the continuous crossed homomorphisms $G \to X$.

### Reference

<?reference?>
