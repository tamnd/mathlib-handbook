---
title: Truncations and bounded cochain complexes
kind: api
modules:
  - Mathlib.Algebra.Homology.Embedding.TruncGEHomology
  - Mathlib.Algebra.Homology.Embedding.TruncLE
  - Mathlib.Algebra.Homology.Embedding.TruncLEHomology
  - Mathlib.Algebra.Homology.Embedding.StupidTrunc
  - Mathlib.Algebra.Homology.Embedding.Splitting
  - Mathlib.Algebra.Homology.Embedding.CochainComplex
  - Mathlib.Algebra.Homology.CochainComplexPlus
  - Mathlib.Algebra.Homology.CochainComplexMinus
  - Mathlib.Algebra.Homology.CochainComplexOpposite
explains:
  E2: [HomologicalComplex.truncLE, HomologicalComplex.quasiIso_ιTruncLE_iff_isSupported, HomologicalComplex.shortComplexTruncLE_shortExact, HomologicalComplex.stupidTrunc, CochainComplex.IsStrictlyGE, CochainComplex.IsGE, CochainComplex.quasiIso_πTruncGE_iff, CochainComplex.Plus, CategoryTheory.Functor.mapCochainComplexPlus, CochainComplex.opEquivalence]
  E1: auto
families: []
requires: [V25.C02, V26.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Truncations and bounded cochain complexes

### Overview

A cochain complex $K$ on $\mathbb{Z}$ has two kinds of truncation at a degree $n$. The stupid truncation $\sigma_{\ge n} K$ keeps the objects $K^i$ for $i \ge n$ and puts zero in the other degrees. It is simple, but it changes the homology in degree $n$. The canonical truncation $\tau_{\ge n} K$ puts the cokernel of $K^{n-1} \to K^n$ in degree $n$. It keeps the homology in degrees $i \ge n$ and kills the homology in degrees $i < n$. The truncation $\tau_{\le n} K$ is dual: it puts the cycles $Z^n$ in degree $n$. These truncations are the main tool to compare a complex with its homology, and the derived category of Chapter 5 uses them for its t-structure.

Mathlib defines all truncations along an embedding of complex shapes $e : c \to c'$, as in the previous section. Chapter 6, Section 1 gives the canonical truncation `HomologicalComplex.truncGE` and the projection to it. The modules of this section add the dual truncation, the homology of both truncations, and the stupid truncations. They then specialize everything to cochain complexes on $\mathbb{Z}$, define the conditions "strictly bounded below" and "bounded below in homology", and make the full subcategories of bounded below and bounded above complexes. A last module identifies the opposite of the category of cochain complexes with the cochain complexes in the opposite category.

Throughout, $C$ has a zero object and enough homology for the truncations to exist. The embeddings of interest are `ComplexShape.embeddingUpIntGE` and `ComplexShape.embeddingUpIntLE`, whose images are the integers $\ge p$ and $\le p$.

### The library around it

#### The canonical truncation from above

The truncation `HomologicalComplex.truncLE` needs an instance `ComplexShape.Embedding.IsTruncLE`. It is the extension along $e$ of a complex `HomologicalComplex.truncLE'` of shape $c$, and it comes with a monomorphism `HomologicalComplex.ιTruncLE` into $K$. At a boundary index the object is the cycles object of $K$:

| Lean name | Statement |
|---|---|
| `HomologicalComplex.truncLEXIsoCycles` | at an index $i$ on the boundary, the object of the truncation is the cycles of $K$ at $e(i)$ |
| `HomologicalComplex.truncLEXIso` | at an index not on the boundary, the object is the object of $K$ |
| `HomologicalComplex.truncLEMap` | the map of truncations induced by a morphism |
| `ComplexShape.Embedding.truncLEFunctor` | the truncation as a functor |
| `HomologicalComplex.isIso_ιTruncLE_iff` | the inclusion is an isomorphism iff $K$ is strictly supported in $e$ |

The homology module proves that the inclusion is a quasi-isomorphism in each degree of the image of $e$, with `HomologicalComplex.quasiIsoAt_ιTruncLE`. The statement `HomologicalComplex.quasiIso_ιTruncLE_iff_isSupported` says that the inclusion is a quasi-isomorphism iff $K$ is exact outside the image of $e$. The same modules give the corresponding facts for `HomologicalComplex.truncGE`: the projection `HomologicalComplex.πTruncGE` is a quasi-isomorphism at each degree of the image, and `HomologicalComplex.quasiIso_πTruncGE_iff_isSupported` is the global statement. The lemmas `HomologicalComplex.acyclic_truncGE_iff_isSupportedOutside` and `HomologicalComplex.acyclic_truncLE_iff_isSupportedOutside` say when a truncation is acyclic. A morphism $\varphi$ induces a quasi-isomorphism of truncations iff it is a quasi-isomorphism at the indices of the image, by `HomologicalComplex.quasiIso_truncGEMap_iff` and `HomologicalComplex.quasiIso_truncLEMap_iff`.

#### The short exact sequence of a truncation

In an abelian category, `HomologicalComplex.shortComplexTruncLE` is the short complex
$$0 \to \tau_{\le} K \to K \to Q \to 0$$
in the category of complexes, where $Q$ is the cokernel of the inclusion. The lemma `HomologicalComplex.shortComplexTruncLE_shortExact` says that it is short exact. The cokernel $Q$ is exact at the indices of the image of $e$, by `HomologicalComplex.shortComplexTruncLE_X₃_isSupportedOutside`. The connecting morphisms of its long exact sequence are zero, by `HomologicalComplex.shortComplexTruncLE_shortExact_δ_eq_zero`. So the long exact sequence splits into short exact sequences, and the homology of $K$ is the homology of $\tau_{\le} K$ in the image of $e$ and the homology of $Q$ outside it.

For a pair of complementary embeddings, such as $\mathbb{Z}_{\le n_0}$ and $\mathbb{Z}_{\ge n_1}$ with $n_0 + 1 = n_1$, the map `HomologicalComplex.shortComplexTruncLEX₃ToTruncGE` from $Q$ to $\tau_{\ge n_1} K$ is a quasi-isomorphism. Its composition with $K \to Q$ is the projection $K \to \tau_{\ge n_1} K$, by `HomologicalComplex.g_shortComplexTruncLEX₃ToTruncGE`. This is the form of the sequence $\tau_{\le n_0} K \to K \to \tau_{\ge n_1} K$ that the t-structure on the derived category uses.

#### Stupid truncations

The stupid truncation `HomologicalComplex.stupidTrunc` is the extension along $e$ of the restriction of $K$ along $e$. It needs `ComplexShape.Embedding.IsRelIff`. Its object at $e(i)$ is the object of $K$ by `HomologicalComplex.stupidTruncXIso`, and it is zero at the other indices. There are two canonical maps:

| Lean name | Statement |
|---|---|
| `HomologicalComplex.ιStupidTrunc` | for `ComplexShape.Embedding.IsTruncGE`, the inclusion of the stupid truncation in $K$ |
| `HomologicalComplex.πStupidTrunc` | for `ComplexShape.Embedding.IsTruncLE`, the projection of $K$ to the stupid truncation |
| `HomologicalComplex.isIso_ιStupidTrunc_iff` | the inclusion is an isomorphism iff $K$ is strictly supported in $e$ |
| `HomologicalComplex.isIso_πStupidTrunc_iff` | the same for the projection |
| `HomologicalComplex.isZero_stupidTrunc_iff` | the truncation is zero iff $K$ is strictly supported outside $e$ |
| `ComplexShape.Embedding.stupidTruncFunctor` | the stupid truncation as a functor |

The direction of the maps comes from the differential. For cochain complexes, $\sigma_{\ge n} K$ is a subcomplex of $K$, because no differential goes from degree $n-1$ into it. So the embedding of $\mathbb{Z}_{\ge n}$, which is a `ComplexShape.Embedding.IsTruncGE`, gives an inclusion.

The module `Mathlib.Algebra.Homology.Embedding.Splitting` has one definition. `ComplexShape.Embedding.splittingExtend` extends a degreewise splitting of a short exact sequence of complexes of shape $c$ to a degreewise splitting of the extended sequence.

#### Cochain complexes on the integers

The module `Mathlib.Algebra.Homology.Embedding.CochainComplex` gives short names for the case $c' = \mathbb{Z}$. The four conditions on a cochain complex $K$ and an integer $n$ are:

| Lean name | Statement |
|---|---|
| `CochainComplex.IsStrictlyGE` | $K^i = 0$ for $i < n$, by `CochainComplex.isStrictlyGE_iff` |
| `CochainComplex.IsStrictlyLE` | $K^i = 0$ for $i > n$, by `CochainComplex.isStrictlyLE_iff` |
| `CochainComplex.IsGE` | $K$ is exact in degrees $i < n$, by `CochainComplex.isGE_iff` |
| `CochainComplex.IsLE` | $K$ is exact in degrees $i > n$, by `CochainComplex.isLE_iff` |

All four are type classes. The module proves that they are invariant under isomorphism, that they get weaker as $n$ moves, as in `CochainComplex.isGE_of_ge`, and that they move with the shift, as in `CochainComplex.isGE_shift`. A complex that is strictly concentrated in one degree is a single complex, by `CochainComplex.exists_iso_single`.

The truncations `CochainComplex.truncGE` and `CochainComplex.truncLE` take an integer. Their objects in degree $n$ are given by `CochainComplex.truncGEXIsoOpcycles` and `CochainComplex.truncLEXIsoCycles`. The statement `CochainComplex.quasiIso_πTruncGE_iff` reads
$$\pi : K \to \tau_{\ge n} K \text{ is a quasi-isomorphism} \iff K \text{ is exact in degrees } i < n,$$
and `CochainComplex.quasiIso_ιTruncLE_iff` is the dual. There are instances that make these maps quasi-isomorphisms under `CochainComplex.IsGE` and `CochainComplex.IsLE`, and isomorphisms under `CochainComplex.IsStrictlyGE` and `CochainComplex.IsStrictlyLE`. The lemmas `CochainComplex.acyclic_truncGE_iff` and `CochainComplex.acyclic_truncLE_iff` take two integers with $n_0 + 1 = n_1$. The lemma `CochainComplex.isStrictlySupported_embeddingUpNat_iff_isStrictlyGE_zero` connects the condition `IsStrictlyGE 0` with the embedding of $\mathbb{N}$.

#### Bounded below and bounded above complexes

The predicate `CochainComplex.plus` is an object property of cochain complexes, and `CochainComplex.plus_iff` says that $K$ satisfies it iff $K$ is strictly bounded below for some $n$. The category `CochainComplex.Plus` is the full subcategory. Its inclusion is `CochainComplex.Plus.ι`, and `CochainComplex.Plus.fullyFaithfulι` makes it fully faithful. The class of quasi-isomorphisms in it is `CochainComplex.Plus.quasiIso`, and `CochainComplex.Plus.quasiIso_iff` says that a morphism is in it iff the underlying morphism of complexes is a quasi-isomorphism. The lemmas `CochainComplex.Plus.mono_iff` and `CochainComplex.Plus.epi_iff` compute the monomorphisms and epimorphisms with the underlying complexes.

A functor $F$ that preserves zero morphisms gives `CategoryTheory.Functor.mapCochainComplexPlus`, which commutes with the inclusions by `CategoryTheory.Functor.mapCochainComplexPlusCompι`. It sends homotopy equivalences to homotopy equivalences, by `CategoryTheory.Functor.homotopyEquivalences_mapCochainComplexPlus_map`. A natural transformation gives `CategoryTheory.NatTrans.mapCochainComplexPlus`. The module `Mathlib.Algebra.Homology.CochainComplexMinus` repeats all of this with `CochainComplex.minus`, `CochainComplex.Minus` and `CategoryTheory.Functor.mapCochainComplexMinus` for complexes that are strictly bounded above.

#### The opposite category

The equivalence `CochainComplex.opEquivalence` identifies the opposite of the category of cochain complexes in $C$ on $\mathbb{Z}$ with the cochain complexes in $C^{\mathrm{op}}$ on $\mathbb{Z}$. It sends degree $n$ to degree $-n$. So `CochainComplex.exactAt_op` takes a proof of $n + m = 0$, and `CochainComplex.acyclic_op` preserves acyclicity. Homotopies correspond by `CochainComplex.homotopyOp`, `CochainComplex.homotopyUnop` and the equivalence `CochainComplex.homotopyOpEquiv`. The same module defines the embeddings `ComplexShape.embeddingUpIntDownInt` and `ComplexShape.embeddingDownIntUpInt`, both given by $n \mapsto -n$, and the equivalence `ChainComplex.cochainComplexEquivalence` between chain complexes and cochain complexes on $\mathbb{Z}$.

#### Common errors

1. `CochainComplex.IsGE` is a condition on homology, and `CochainComplex.IsStrictlyGE` is a condition on objects. A complex with nonzero objects in all negative degrees can be exact there. It satisfies `CochainComplex.IsGE` for $0$, but it is not an object of `CochainComplex.Plus`. Apply the truncation first to get a strictly bounded complex.
2. Many lemmas, such as `CochainComplex.acyclic_truncLE_iff`, take the hypothesis $n_0 + 1 = n_1$ as an automatic argument that lia proves. With variables that lia cannot handle, give the proof explicitly.
3. `HomologicalComplex.ιStupidTrunc` needs `ComplexShape.Embedding.IsTruncGE` and `HomologicalComplex.πStupidTrunc` needs `ComplexShape.Embedding.IsTruncLE`. For the canonical truncations the roles are the other way: the inclusion `HomologicalComplex.ιTruncLE` needs `ComplexShape.Embedding.IsTruncLE`.

### Exercises

1. (A) For the complex $0 \to \mathbb{Z} \xrightarrow{2} \mathbb{Z} \to 0$ in degrees $0$ and $1$, write $\tau_{\le 0} K$, $\tau_{\ge 1} K$, $\sigma_{\ge 1} K$ and their homology.
2. (A) Show from the definitions that a complex that satisfies `CochainComplex.IsStrictlyGE` for $n$ also satisfies `CochainComplex.IsGE` for $n$.
3. (B) Prove that $K$ is acyclic iff $\tau_{\ge n} K$ and $\tau_{\le n} K$ are acyclic for one integer $n$, with `CochainComplex.acyclic_truncGE_iff` and `CochainComplex.acyclic_truncLE_iff`.
4. (B) Show that if `CochainComplex.IsGE` and `CochainComplex.IsLE` both hold for $n$, then $K$ is quasi-isomorphic to the single complex of its homology in degree $n$. Use the truncations and `CochainComplex.exists_iso_single`.
5. (B) Show that the stupid truncation does not preserve quasi-isomorphisms, with an acyclic complex of length two.
6. (C) Prove that the image of a bounded below complex under `CochainComplex.opEquivalence` is bounded above.

### Reference

<?reference?>
