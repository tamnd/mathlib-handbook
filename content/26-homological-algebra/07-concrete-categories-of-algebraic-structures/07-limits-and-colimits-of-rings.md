---
title: Limits and colimits of rings
kind: api
modules:
  - Mathlib.Algebra.Category.Ring.Adjunctions
  - Mathlib.Algebra.Category.Ring.Colimits
  - Mathlib.Algebra.Category.Ring.Constructions
  - Mathlib.Algebra.Category.Ring.Epi
  - Mathlib.Algebra.Category.Ring.EqualizerPushout
  - Mathlib.Algebra.Category.Ring.FilteredColimits
  - Mathlib.Algebra.Category.Ring.FilteredColimitsLocal
  - Mathlib.Algebra.Category.Ring.FinitePresentation
  - Mathlib.Algebra.Category.Ring.Instances
  - Mathlib.Algebra.Category.Ring.LinearAlgebra
  - Mathlib.Algebra.Category.Ring.Small
  - Mathlib.Algebra.Category.Ring.Topology
  - Mathlib.Algebra.Category.Ring.Under.Basic
  - Mathlib.Algebra.Category.Ring.Under.Limits
  - Mathlib.Algebra.Category.Ring.Under.Property
explains:
  E2: [CommRingCat.pushoutCoconeIsColimit, CommRingCat.zIsInitial, CommRingCat.subsingleton_of_isTerminal, CommRingCat.equalizerForkIsLimit, RingHom.surjective_iff_epi_and_finite, IsLocalization.epi, CommRingCat.adj, CommRingCat.FilteredColimit.isLocalRing_of_isColimit, CommRingCat.isRegularMono_of_faithfullyFlat, CommRingCat.Under.preservesFiniteLimits_of_flat]
  E1: auto
families: []
requires: [V24.C04, V24.C05, V06, V09]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Limits and colimits of rings

### Overview

Section 1 proves that limits of rings are computed on the underlying sets. This section describes the other limits and colimits of `RingCat` and `CommRingCat` in the library, and the dictionary between categorical words and ring theory. In $\mathbf{CRing}$ the pushout is the tensor product, the coproduct is the tensor product over $\mathbb{Z}$, the initial object is $\mathbb{Z}$ and the terminal object is the zero ring. Filtered colimits are computed on the sets, and a filtered colimit of local rings along local homomorphisms is local. General colimits are quotients of free rings.

The second half of the section works in the category `Under R` of commutative $R$-algebras. Algebraic geometry uses these facts all the time: base change along a flat map preserves finite limits, a faithfully flat map is a regular monomorphism, and a finitely presented algebra is a finitely presentable object. The section ends with the topology on the set of ring maps into a topological ring.

### The library around it

#### Free rings and adjunctions

The file `Mathlib.Algebra.Category.Ring.Adjunctions` gives the free commutative ring on a type. `CommRingCat.free` sends a type $\sigma$ to the polynomial ring $\mathbb{Z}[X_s : s \in \sigma]$, by `CommRingCat.free_obj_coe`, and a map of types to the renaming of variables, by `CommRingCat.free_map_coe`. The adjunction `CommRingCat.adj : CommRingCat.free ⊣ forget CommRingCat` is the universal property of polynomials: a ring map $\mathbb{Z}[X_s] \to A$ is the same as a choice of $a_s \in A$ for each $s$, because the map is evaluation at $(a_s)$ and is fixed by the images of the variables.

Two more adjunctions come from the units. For a commutative ring $R$, `CommRingCat.monoidAlgebra R` sends a commutative monoid $G$ to the monoid algebra $R[G]$, an object of `Under R`. The adjunction `CommRingCat.monoidAlgebraAdj` says that an $R$-algebra map $R[G] \to S$ is the same as a monoid map $G \to S$, where $S$ is a monoid under multiplication. With $R = \mathbb{Z}$, the initial object, `CommRingCat.forget₂Adj` gives the left adjoint of the forgetful functor to `CommMonCat`. Last, `CommRingCat.coyoneda` sends a type $X$ and a ring $R$ to the ring $R^X$ of functions, and `CommRingCat.coyonedaAdj` says that this functor is left adjoint to $\operatorname{Hom}(R, -)$ on the opposite side.

#### Colimits of rings

The file `Mathlib.Algebra.Category.Ring.Colimits` builds all colimits of `RingCat` and `CommRingCat` with the method of the monoid case in Section 4. The inductive type `RingCat.Colimits.Prequotient F` has the formal terms built from the elements of the rings $F(j)$ with zero, one, negation, sum and product. The relation `RingCat.Colimits.Relation F` imposes the ring axioms and the identifications along the maps of the diagram. The quotient is `RingCat.Colimits.ColimitType F`, with the ring structure `RingCat.Colimits.instRingColimitType`, and the cocone `RingCat.Colimits.colimitCocone` is a colimit by `RingCat.Colimits.colimitIsColimit`. The lemmas `RingCat.Colimits.quot_add`, `RingCat.Colimits.quot_mul`, `RingCat.Colimits.quot_neg`, `RingCat.Colimits.quot_zero` and `RingCat.Colimits.quot_one` compute the operations on classes. The instances `RingCat.Colimits.hasColimits_ringCat` and `CommRingCat.Colimits.hasColimits_commRingCat` record the result.

#### Explicit limits and colimits of commutative rings

The general construction is not useful in practice. The file `Mathlib.Algebra.Category.Ring.Constructions` gives the concrete cones.

| Lean name | Statement |
|---|---|
| `CommRingCat.pushoutCoconeIsColimit` | $A \otimes_R B$ is the pushout of $A \leftarrow R \to B$ |
| `CommRingCat.coproductCoconeIsColimit` | $A \otimes_{\mathbb{Z}} B$ is the coproduct |
| `CommRingCat.zIsInitial` | $\mathbb{Z}$ is initial |
| `CommRingCat.punitIsTerminal` | the zero ring is terminal |
| `CommRingCat.prodFanIsLimit` | $A \times B$ is the product |
| `CommRingCat.piFanIsLimit` | $\prod_i R_i$ is the product of a family |
| `CommRingCat.equalizerForkIsLimit` | $\{a : f(a) = g(a)\}$ is the equalizer of $f, g$ |
| `CommRingCat.pullbackConeIsLimit` | $A \times_C B$ is the pullback |

The pushout cocone `CommRingCat.pushoutCocone R A B` has the maps $a \mapsto a \otimes 1$ and $b \mapsto 1 \otimes b$. Proof of the universal property: two maps $\alpha \colon A \to T$ and $\beta \colon B \to T$ that agree on $R$ make $T$ an $R$-algebra and are $R$-algebra maps. The map $a \otimes b \mapsto \alpha(a)\beta(b)$ is well defined, because it is $R$-bilinear, and it is a ring map because $T$ is commutative. It is unique, because the elements $a \otimes b$ generate $A \otimes_R B$. The lemma `CommRingCat.isPushout_tensorProduct` states the same fact as a pushout square, `CommRingCat.isPushout_iff_isPushout` translates it to the predicate `Algebra.IsPushout`, and `CommRingCat.isPushout_of_isLocalization` shows that localization squares are pushouts. `CommRingCat.closure_range_union_range_eq_top_of_isPushout` says that the two images generate the pushout as a ring.

The terminal object is strict: each map from the zero ring to a ring $A$ forces $1 = 0$ in $A$. This is the instance `CommRingCat.commRingCat_hasStrictTerminalObjects`, and `CommRingCat.subsingleton_of_isTerminal` says that a terminal ring has at most one element. Proof: a terminal object is isomorphic to the zero ring, by uniqueness of limits. The initial property of $\mathbb{Z}$ holds because the map $\mathbb{Z} \to A$, $n \mapsto n \cdot 1$, is the only ring map.

The equalizer of $f, g \colon A \to B$ is the subring `RingHom.eqLocus`. The inclusion is a local homomorphism: if $a$ is a unit of $A$ with $f(a) = g(a)$, then $f(a^{-1}) = f(a)^{-1} = g(a)^{-1} = g(a^{-1})$, so $a^{-1}$ is in the equalizer. So `CommRingCat.equalizer_limit_isLocalRing` holds: the equalizer of maps out of a local ring is local. The same idea gives `CommRingCat.pullback_isLocalRing` and `CommRingCat.Limits.isUnit_iff_forall_isUnit`: an element of a limit is a unit when each of its components is a unit. The isomorphism `CommRingCat.piIsoPi` identifies the categorical product with the ring of families.

#### Epimorphisms and localization

Section 1 shows that $\mathbb{Z} \to \mathbb{Q}$ is an epimorphism that is not surjective. The file `Mathlib.Algebra.Category.Ring.Instances` proves `IsLocalization.epi`: each localization $R \to S^{-1}R$ is an epimorphism, by the argument of Section 1 applied to each denominator. The instances `Localization.epi` and `Localization.epi'` follow. The same file proves `isLocalHom_of_isIso` and `CommRingCat.isLocalHom_comp`. The file `Mathlib.Algebra.Category.Ring.Epi` relates the categorical notion to the algebraic one. `CommRingCat.epi_iff_epi` says that $R \to S$ is an epimorphism exactly when `Algebra.IsEpi R S` holds, that is, when $s \otimes 1 = 1 \otimes s$ in $S \otimes_R S$ for each $s$. The theorem `RingHom.surjective_iff_epi_and_finite` says that a ring map is surjective if and only if it is an epimorphism and finite. Proof sketch: a finite epimorphism $R \to S$ makes $S$ a finite $R$-module with $S \otimes_R S \cong S$, and Nakayama's lemma applied to the cokernel of $R \to S$ at each prime gives surjectivity.

#### Faithfully flat maps

Let $f \colon R \to S$ be faithfully flat. The file `Mathlib.Algebra.Category.Ring.EqualizerPushout` proves that the diagram
$$R \xrightarrow{f} S \rightrightarrows S \otimes_R S$$
with the maps $s \mapsto s \otimes 1$ and $s \mapsto 1 \otimes s$ is an equalizer. This is `CommRingCat.isLimitForkPushoutSelfOfFaithfullyFlat`, and it means that $f$ is a regular monomorphism, `CommRingCat.isRegularMono_of_faithfullyFlat`. In the opposite category the dual statement is that $\operatorname{Spec} S \to \operatorname{Spec} R$ is an effective epimorphism, `CommRingCat.Opposite.effectiveEpi_of_faithfullyFlat`. This is the base case of faithfully flat descent. The file `Mathlib.Algebra.Category.Ring.LinearAlgebra` adds `CommRingCat.nontrivial_of_isPushout_of_isField`: the pushout of two nonzero rings over a field is nonzero, because $B \otimes_K C$ contains $B \otimes_K K \cong B$ when $C$ is a nonzero vector space.

#### Filtered colimits and local rings

The file `Mathlib.Algebra.Category.Ring.FilteredColimits` puts a ring structure on the filtered colimit of the underlying sets, as in Section 4 for monoids, for `SemiRingCat`, `CommSemiRingCat`, `RingCat` and `CommRingCat`. The main instances are `RingCat.FilteredColimits.forget_preservesFilteredColimits` and `CommRingCat.FilteredColimits.forget_preservesFilteredColimits`. The type of the colimit is `RingCat.FilteredColimits.R F`. The lemma `CommRingCat.FilteredColimits.nontrivial` says that a filtered colimit of nonzero rings is nonzero, because $1 = 0$ in the colimit would hold already at some stage.

The file `Mathlib.Algebra.Category.Ring.FilteredColimitsLocal` treats a filtered diagram of local rings whose transition maps are local homomorphisms. The colimit $A$ is local, by `CommRingCat.FilteredColimit.isLocalRing_of_isColimit`, and its maximal ideal is the union of the images of the maximal ideals, by `CommRingCat.FilteredColimit.maximalIdeal_eq_iUnion_of_isColimit`. Proof: an element $x \in A$ comes from some $x_j \in A_j$. If $x_j$ is a unit then $x$ is a unit. If $x_j$ is not a unit, then its image in each later $A_k$ is not a unit, because the transition maps are local, so $x$ is not a unit. Hence the nonunits of $A$ are the union of the images of the maximal ideals, `CommRingCat.FilteredColimit.nonunits_eq_iUnion_of_isColimit`, and this union is an ideal because any two elements live in a common $A_k$. The residue field of the colimit is the colimit of the residue fields, `CommRingCat.FilteredColimit.isColimitResidueFieldCocone`. Stalks of the structure sheaf of a scheme are filtered colimits of this form.

#### Algebras as objects under a ring

For a commutative ring $R$, the category `Under R` of arrows $R \to A$ is the category of commutative $R$-algebras. The file `Mathlib.Algebra.Category.Ring.Under.Basic` gives the bridge. `CommRingCat.mkUnder R A` makes an object from an $R$-algebra $A$, `CommRingCat.toAlgHom` turns a morphism into an `AlgHom`, and `AlgHom.toUnder` and `AlgEquiv.toUnder` go back. For an $R$-algebra $S$, the functor `CommRingCat.tensorProd R S : Under R ⥤ Under S` is base change $A \mapsto S \otimes_R A$, and `CommRingCat.tensorProdIsoPushout` identifies it with the categorical pushout functor `CategoryTheory.Under.pushout`.

The file `Mathlib.Algebra.Category.Ring.Under.Limits` computes finite limits in `Under R`: products are products of algebras, `CommRingCat.Under.piFanIsLimit`, and equalizers are the subalgebras `CommRingCat.Under.equalizerFork`. The main theorem is `CommRingCat.Under.preservesFiniteLimits_of_flat`: if $R \to S$ is flat, then base change preserves finite limits. Proof sketch: base change preserves finite products, because $S \otimes_R (A \times B) \cong (S \otimes_R A) \times (S \otimes_R B)$. The equalizer of $f, g \colon A \to B$ is the kernel of $f - g$, an $R$-linear map. Flatness of $S$ means that $S \otimes_R -$ preserves kernels, so it preserves this equalizer. A functor that preserves finite products and equalizers preserves finite limits.

The file `Mathlib.Algebra.Category.Ring.Under.Property` generalizes this to the full subcategory of `Under R` defined by a property $P$ of ring maps. If $P$ is stable under finite products and equalizers, `CommRingCat.Under.hasFiniteLimits` gives finite limits, and `RingHom.HasStableEqualizers.preservesFiniteLimits_pushout` says that base change preserves them.

#### Finite presentation, smallness and topology

The file `Mathlib.Algebra.Category.Ring.FinitePresentation` proves that a finitely presented $R$-algebra $S$ is a finitely presentable object of `Under R`: the functor $\operatorname{Hom}_R(S, -)$ preserves filtered colimits. This is `CommRingCat.preservesFilteredColimits_coyoneda` and `CommRingCat.isFinitelyPresentable_under`. The reason is that a map out of $R[x_1, \dots, x_n]/(f_1, \dots, f_m)$ is a choice of $n$ elements that satisfy $m$ equations, and in a filtered colimit finitely many elements and equations live at one stage. The file `Mathlib.Algebra.Category.Ring.Small` proves `CommRingCat.essentiallySmall_of_finiteType`: rings of finite type over the members of an essentially small class form an essentially small class.

The file `Mathlib.Algebra.Category.Ring.Topology` puts a topology on $\operatorname{Hom}(A, R)$ for a topological ring $R$: the coarsest topology that makes each evaluation $f \mapsto f(a)$ continuous, `CommRingCat.HomTopology.instTopologicalSpaceHom`. When $R$ is $T_1$, `CommRingCat.HomTopology.isClosedEmbedding_hom` embeds it as a closed subset of $R^A$, so $\operatorname{Hom}(A, R)$ is compact when $R$ is compact. `CommRingCat.HomTopology.mvPolynomialHomeomorph` identifies $\operatorname{Hom}(A[X_i], R)$ with $\operatorname{Hom}(A, R) \times R^I$.

#### Common errors

1. The coproduct in `CommRingCat` is the tensor product, not the product. The product $A \times B$ is the categorical product, by `CommRingCat.prodFanIsLimit`.
2. An epimorphism of rings need not be surjective. Use `RingHom.surjective_iff_epi_and_finite` when the map is finite, and expect localizations to be epimorphisms that are not surjective.
3. `Under R` is the category of commutative $R$-algebras only. For algebras that are not commutative, use `AlgCat R`, described in Section 11.

### Exercises

1. (A) Compute the pushout of $\mathbb{Z}[x] \leftarrow \mathbb{Z} \to \mathbb{Z}[y]$ and of $\mathbb{Z}/2 \leftarrow \mathbb{Z} \to \mathbb{Z}/3$ in $\mathbf{CRing}$.
2. (A) Show that $\mathbb{Z}$ has exactly one ring map to each ring, and deduce `CommRingCat.zIsInitial`.
3. (B) Show that the inclusion $\mathbb{Z} \to \mathbb{Z}[i]$ is finite and not surjective, and deduce from `RingHom.surjective_iff_epi_and_finite` that it is not an epimorphism.
4. (B) Prove that the colimit of $\mathbb{Z}_{(p)} \to \mathbb{Z}_{(p)}[t]_{(p,t)} \to \cdots$ along local maps is local, by the argument for `CommRingCat.FilteredColimit.isLocalRing_of_isColimit`.
5. (B) Give a map $R \to S$ that is not flat and an equalizer in `Under R` that base change along it does not preserve. Hint: $\mathbb{Z} \to \mathbb{Z}/2$.
6. (C) Prove that $\mathbb{Z} \to \prod_p \mathbb{Z}_p$ is faithfully flat, and write the equalizer diagram of `CommRingCat.isLimitForkPushoutSelfOfFaithfullyFlat` for it.

### Reference

<?reference?>
