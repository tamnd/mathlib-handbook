---
title: Operations on properties of objects
kind: api
modules:
  - Mathlib.CategoryTheory.ObjectProperty.CompleteLattice
  - Mathlib.CategoryTheory.ObjectProperty.Opposite
  - Mathlib.CategoryTheory.ObjectProperty.Equivalence
  - Mathlib.CategoryTheory.ObjectProperty.Comma
  - Mathlib.CategoryTheory.ObjectProperty.InheritedFromHom
  - Mathlib.CategoryTheory.ObjectProperty.Retract
  - Mathlib.CategoryTheory.ObjectProperty.ContainsZero
  - Mathlib.CategoryTheory.ObjectProperty.EpiMono
  - Mathlib.CategoryTheory.ObjectProperty.Kernels
  - Mathlib.CategoryTheory.ObjectProperty.Extensions
  - Mathlib.CategoryTheory.ObjectProperty.Subobject
  - Mathlib.CategoryTheory.ObjectProperty.HasFiniteResolution.Basic
  - Mathlib.CategoryTheory.ObjectProperty.HasFiniteResolution.Projective
  - Mathlib.CategoryTheory.ObjectProperty.Orthogonal
  - Mathlib.CategoryTheory.ObjectProperty.OrthogonalLimits
  - Mathlib.CategoryTheory.Abelian.OrthogonalClosed
  - Mathlib.CategoryTheory.ObjectProperty.Local
  - Mathlib.CategoryTheory.ObjectProperty.SiteLocal
  - Mathlib.CategoryTheory.ObjectProperty.Shift
  - Mathlib.CategoryTheory.ObjectProperty.ShiftAdditive
  - Mathlib.CategoryTheory.ObjectProperty.ClosureShift
explains:
  E2: [CategoryTheory.ObjectProperty.retractClosure, CategoryTheory.ObjectProperty.prop_biprod, CategoryTheory.ObjectProperty.gc_rightOrthogonal_leftOrthogonal, CategoryTheory.ObjectProperty.instIsClosedUnderExtensionsLeftOrthogonal, CategoryTheory.ObjectProperty.leftOrthogonal_rightOrthogonal_eq_self, CategoryTheory.ObjectProperty.hasFiniteResolutionOfLength, CategoryTheory.MorphismProperty.isLocal_iSup, CategoryTheory.ObjectProperty.shiftClosure_eq_iSup]
  E1: auto
families: []
requires: [V24.C01, V24.C02, V24.C04, V25.C01, V25.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Operations on properties of objects

### Overview

Section 1 defined a property of objects `P : ObjectProperty C` as a predicate on the objects of a category $C$, with its full subcategory and its closure under isomorphisms. This section collects the operations and the closure conditions that the library puts on such a property. Some of them are formal: the lattice operations, the transport to the opposite category, along an equivalence and to a comma category. Others use the structure of $C$: closure under retracts, subobjects, quotients, kernels, cokernels and extensions, the orthogonal of a property in a category with zero morphisms, the objects that are local for a class of morphisms, and the stability under a shift functor.

A reader needs these conditions to state the definitions of later chapters in a short form. A Serre class is a property closed under subobjects, quotients and extensions. A torsion class is the left orthogonal of a property. A triangulated subcategory is a property that is stable under the shift and closed under extensions in triangles. A Bousfield localization uses the objects that are local for a class of morphisms. Each condition is a Lean class on `P`, so instances give it for new properties.

In the text $g \circ f$ is the textbook composite, and Mathlib writes `f ≫ g`. All names are in the namespace `CategoryTheory`.

### The library around it

#### The lattice of properties

The type `ObjectProperty C` is the function type `C → Prop`, so it is a complete lattice with the pointwise order. The module `Mathlib.CategoryTheory.ObjectProperty.CompleteLattice` gives the membership lemmas of the operations, which are the simp normal form for a goal of the form `(P ⊔ Q) X`.

| Lean name | Statement |
|---|---|
| `ObjectProperty.prop_sup_iff` | $(P \sqcup Q)(X) \iff P(X) \lor Q(X)$ |
| `ObjectProperty.prop_inf_iff` | $(P \sqcap Q)(X) \iff P(X) \land Q(X)$ |
| `ObjectProperty.prop_iSup_iff` | $(\bigsqcup_a P_a)(X) \iff \exists a,\ P_a(X)$ |
| `ObjectProperty.isoClosure_sup` | the isomorphism closure commutes with $\sqcup$ |
| `ObjectProperty.nonempty_iff_ne_bot` | `P.Nonempty` holds if and only if $P \neq \bot$ |
| `ObjectProperty.ι_map_top` | the image of $\top$ under `P.ι` is `P.isoClosure` |

Instances say that the lattice operations keep closure under isomorphisms. Most classes of this section have similar instances for $\top$ and $\sqcap$.

#### Opposites, equivalences and comma categories

The module `Mathlib.CategoryTheory.ObjectProperty.Opposite` moves a property between $C$ and $C^{\mathrm{op}}$. For `P : ObjectProperty C`, the property `P.op` holds at `X : Cᵒᵖ` when `P` holds at `X.unop`, and `ObjectProperty.unop` goes back. The two maps are inverse (`ObjectProperty.op_unop`), monotone in both directions (`ObjectProperty.op_monotone_iff`), and they commute with $\sqcup$, $\sqcap$ and `isoClosure`. The equivalence `P.opEquivalence : P.op.FullSubcategory ≌ P.FullSubcategoryᵒᵖ` says that the full subcategory of the opposite is the opposite of the full subcategory. The closure under subobjects, quotients and extensions comes with lemmas such as `ObjectProperty.isClosedUnderSubobjects_op_iff`, which turn a statement about `P.op` into the dual statement about `P`.

The module `Mathlib.CategoryTheory.ObjectProperty.Equivalence` gives `Equivalence.congrFullSubcategory`. An equivalence `e : C ≌ D` and properties $P$ on $C$ and $Q$ on $D$ with $Q$ closed under isomorphisms and `Q.inverseImage e.functor = P` give an equivalence of the full subcategories. The lemma `ObjectProperty.isEquivalence_ιOfLE_iff` says that for $P \le Q$ the inclusion `ιOfLE` is an equivalence if and only if $Q \le \bar P$, where $\bar P$ is the isomorphism closure.

The module `Mathlib.CategoryTheory.ObjectProperty.Comma` defines `ObjectProperty.comma F₁ F₂ P₁ P₂` on the comma category `Comma F₁ F₂`. By `ObjectProperty.comma_iff` it holds at an object $X$ when $P_1$ holds at `X.left` and $P_2$ holds at `X.right`. Instances transfer closure under isomorphisms, stability under retracts and smallness.

The module `Mathlib.CategoryTheory.ObjectProperty.InheritedFromHom` relates a property of objects $P$ to a property of morphisms $Q$. The class `P.InheritedFromSource Q` says that $P(X)$ implies $P(Y)$ for each $f : X \to Y$ in $Q$, and `P.InheritedFromTarget Q` says that $P(Y)$ implies $P(X)$. A property closed under isomorphisms is inherited along `MorphismProperty.isomorphisms C`, and the opposite swaps source and target.

#### Retracts

An object $X$ is a *retract* of $Y$ when there are $i : X \to Y$ and $r : Y \to X$ with $r \circ i = 1_X$. In Mathlib this is the structure `Retract X Y`. The class `P.IsStableUnderRetracts` asks that $P(Y)$ implies $P(X)$ for each retract, and `ObjectProperty.prop_of_retract` is the lemma to apply. The closure is `P.retractClosure`, the property of the retracts of the objects of $P$.

**Proposition.** `P.retractClosure` is stable under retracts, and it is the smallest such property above $P$.

*Proof.* Let $X$ be a retract of $Y$ by $(i, r)$ and $Y$ a retract of $Z$ by $(i', r')$, with $P(Z)$. Then $(r \circ r') \circ (i' \circ i) = r \circ i = 1_X$, so $X$ is a retract of $Z$. This gives the first claim. Each object of $P$ is a retract of itself, so $P$ is below the closure. A property $Q$ above $P$ and stable under retracts contains each retract of an object of $P$. $\square$

The library states this as `ObjectProperty.le_retractClosure` and `ObjectProperty.retractClosure_le_iff`, with `ObjectProperty.retractClosure_retractClosure` as a consequence. A property stable under retracts is closed under isomorphisms, since an isomorphism is a retraction. In a category with zero morphisms, each summand of a biproduct is a retract, so `IsStableUnderRetracts.of_biprod_left`, `IsStableUnderRetracts.of_biprod_right` and `IsStableUnderRetracts.of_biproduct` say that the summands of an object of $P$ are in $P$.

#### Zero objects, subobjects and quotients

The class `P.ContainsZero` in `Mathlib.CategoryTheory.ObjectProperty.ContainsZero` asks that some zero object satisfies $P$. With closure under isomorphisms, `ObjectProperty.prop_of_isZero` gives $P(Z)$ for each zero object $Z$. The full subcategory then has a zero object. The same module defines the *kernel* of a functor, `Functor.kernel F`, the property of the objects that $F$ sends to a zero object. This is the kernel in the sense of a Serre quotient or of a triangulated functor, not the kernel of a morphism.

The module `Mathlib.CategoryTheory.ObjectProperty.EpiMono` defines two classes. `P.IsClosedUnderSubobjects` asks that $P(Y)$ implies $P(X)$ for each monomorphism $X \to Y$, and `P.IsClosedUnderQuotients` asks that $P(X)$ implies $P(Y)$ for each epimorphism $X \to Y$. The lemmas `ObjectProperty.prop_of_mono` and `ObjectProperty.prop_of_epi` apply them. The opposite exchanges the two classes. For a short exact sequence $0 \to X_1 \to X_2 \to X_3 \to 0$, `ObjectProperty.prop_X₁_of_shortExact` and `ObjectProperty.prop_X₃_of_shortExact` give $P(X_1)$ and $P(X_3)$ from $P(X_2)$.

The module `Mathlib.CategoryTheory.ObjectProperty.Subobject` has one result, `ObjectProperty.prop_subobjectSSup`. Let $C$ be well-powered with coproducts, images and equalizers, and let $P$ be closed under quotients and coproducts. Then the supremum of a set of subobjects of $X$ that satisfy $P$ satisfies $P$. The supremum is the image of the map from the coproduct of the subobjects, so it is a quotient of an object of $P$. So each object has a largest subobject in $P$, the *$P$-part* of $X$.

#### Kernels, cokernels and extensions

The module `Mathlib.CategoryTheory.ObjectProperty.Kernels` works in a category with zero morphisms. For a property of morphisms $W$, `MorphismProperty.kernels W` and `MorphismProperty.cokernels W` are the properties of the objects that are a kernel or a cokernel of a morphism of $W$. The class `P.IsClosedUnderKernels` asks that the kernel of each morphism between objects of $P$ is in $P$: by `ObjectProperty.isClosedUnderKernels_iff` it is the inequality `(MorphismProperty.ofObjectProperty P P).kernels ≤ P`. The lemma `ObjectProperty.prop_kernel` applies it. Closure under subobjects implies closure under kernels, and closure under quotients implies closure under cokernels. For a property closed under kernels, `ObjectProperty.createsKernels` says that the inclusion `P.ι` creates kernels, so the full subcategory has kernels and `P.ι` preserves them.

The module `Mathlib.CategoryTheory.ObjectProperty.Extensions` defines the class `P.IsClosedUnderExtensions`: for each short exact sequence $0 \to X_1 \to X_2 \to X_3 \to 0$, the conditions $P(X_1)$ and $P(X_3)$ give $P(X_2)$. The lemma to apply is `ObjectProperty.prop_X₂_of_shortExact`. The class passes to the opposite and to an inverse image along an exact functor.

**Proposition.** In a preadditive category with a zero object, a property closed under extensions is closed under binary biproducts.

*Proof.* Let $P(X_1)$ and $P(X_2)$. The sequence $0 \to X_1 \to X_1 \oplus X_2 \to X_2 \to 0$, with the inclusion and the projection of the biproduct, is split exact, so it is short exact. Closure under extensions gives $P(X_1 \oplus X_2)$. $\square$

This is `ObjectProperty.prop_biprod`.

#### Finite resolutions

The module `Mathlib.CategoryTheory.ObjectProperty.HasFiniteResolution.Basic` defines when an object has a resolution of finite length by objects of $P$. The inductive property `P.hasFiniteResolutionOfLength n` has two constructors. Each object of $P$ has a resolution of length $0$. If $0 \to X_1 \to X_2 \to X_3 \to 0$ is short exact, $P(X_2)$ holds and $X_1$ has a resolution of length $n$, then $X_3$ has a resolution of length $n + 1$. So $X$ has an exact sequence $0 \to E_n \to \dots \to E_0 \to X \to 0$ with all $E_i$ in $P$. The property `P.hasFiniteResolution` asks for some length, by `ObjectProperty.hasFiniteResolution_iff`.

The two properties are monotone in $P$ and preserved by an exact functor that sends $P$ into $Q$ (`hasFiniteResolution.map_exactFunctor`). The lemma `hasFiniteResolutionOfLength.property_of_isClosedUnderQuotients` says that the construction adds nothing when $P$ is closed under quotients, since then $X_3$ is a quotient of $X_2$. The module `Mathlib.CategoryTheory.ObjectProperty.HasFiniteResolution.Projective` links the construction to homological algebra: in an abelian category with enough projectives, `hasFiniteResolutionOfLength.iff_hasProjectiveDimensionLE` says that $X$ has a resolution of length $n$ by projective objects if and only if `HasProjectiveDimensionLE X n`.

#### Orthogonals and the theorem of Dickson

Let $C$ have zero morphisms. The module `Mathlib.CategoryTheory.ObjectProperty.Orthogonal` defines two orthogonals of a property $P$:

$$P^{\perp} = \{ Y \mid \mathrm{Hom}(X, Y) = 0 \text{ for each } X \in P \}, \qquad {}^{\perp}P = \{ X \mid \mathrm{Hom}(X, Y) = 0 \text{ for each } Y \in P \}.$$

In Lean, $P^{\perp}$ is `P.rightOrthogonal` and ${}^{\perp}P$ is `P.leftOrthogonal`.

**Proposition.** For properties $P$ and $Q$, $P \le {}^{\perp}Q$ if and only if $Q \le P^{\perp}$. So the two orthogonals form an antitone Galois connection, and $P^{\perp} = ({}^{\perp}(P^{\perp}))^{\perp}$.

*Proof.* Both conditions say that $\mathrm{Hom}(X, Y) = 0$ for each $X \in P$ and $Y \in Q$. The identity is a formal consequence of a Galois connection: $P \le {}^{\perp}(P^{\perp})$ gives $({}^{\perp}(P^{\perp}))^{\perp} \le P^{\perp}$ by antitonicity, and $P^{\perp} \le ({}^{\perp}(P^{\perp}))^{\perp}$ is the unit at $P^{\perp}$. $\square$

The library states the equivalence as `ObjectProperty.le_leftOrthogonal_iff_le_rightOrthogonal` and the Galois connection, through the order dual, as `ObjectProperty.gc_rightOrthogonal_leftOrthogonal`. The triple identity is `ObjectProperty.rightOrthogonal_leftOrthogonal_rightOrthogonal`. The module `Mathlib.CategoryTheory.ObjectProperty.OrthogonalLimits` adds the closure instances: ${}^{\perp}P$ is closed under quotients and under colimits of each shape, and $P^{\perp}$ is closed under subobjects and limits of each shape.

The module `Mathlib.CategoryTheory.Abelian.OrthogonalClosed` adds closure under extensions, in a preadditive balanced category.

**Proposition.** The left orthogonal ${}^{\perp}P$ is closed under extensions.

*Proof.* Let $0 \to X_1 \xrightarrow{f} X_2 \xrightarrow{g} X_3 \to 0$ be short exact with $X_1, X_3 \in {}^{\perp}P$, and let $k : X_2 \to Y$ with $Y \in P$. Then $k \circ f = 0$, since $X_1 \in {}^{\perp}P$. The morphism $g$ is a cokernel of $f$, so $k = l \circ g$ for some $l : X_3 \to Y$. Then $l = 0$, since $X_3 \in {}^{\perp}P$, and so $k = 0$. $\square$

The dual argument with the kernel $f$ of $g$ gives the same for $P^{\perp}$. So a left orthogonal is closed under quotients, coproducts and extensions. The converse is a theorem of Dickson on torsion classes.

**Theorem (Dickson).** Let $C$ be an abelian category that is locally small and well-powered with coproducts, and let $P$ be closed under quotients, extensions and coproducts. Then ${}^{\perp}(P^{\perp}) = P$.

*Proof sketch.* The inclusion $P \le {}^{\perp}(P^{\perp})$ is formal. Let $X \in {}^{\perp}(P^{\perp})$ and let $A \subseteq X$ be the largest subobject in $P$, from `ObjectProperty.prop_subobjectSSup`. The lemma `ObjectProperty.rightOrthogonal_cokernel_sSup` says that $X / A \in P^{\perp}$: the image $B$ of a map $Z \to X/A$ with $Z \in P$ is in $P$, its preimage in $X$ is an extension of $B$ by $A$, so it is in $P$ and lies in $A$, and so $B = 0$ and the map is zero. Now the projection $X \to X/A$ is zero, since $X \in {}^{\perp}(P^{\perp})$. So $A \to X$ is an epimorphism, and $X$ is a quotient of $A$, hence in $P$. $\square$

The theorem is `ObjectProperty.leftOrthogonal_rightOrthogonal_eq_self`, with the hard inclusion `ObjectProperty.leftOrthogonal_rightOrthogonal_le`. The torsion theories of Chapter 2 use it in `Abelian.isTorsionClass_iff`.

#### Local objects

The orthogonal above uses zero morphisms. The module `Mathlib.CategoryTheory.ObjectProperty.Local` gives the version for a class of morphisms in any category. For `W : MorphismProperty C`, an object $Z$ is *$W$-local* when for each $f : X \to Y$ in $W$ the map $\mathrm{Hom}(Y, Z) \to \mathrm{Hom}(X, Z)$, $g \mapsto g \circ f$, is bijective. This is `W.isLocal`, with the membership lemma `MorphismProperty.isLocal_iff`. The dual is `W.isColocal`.

The local objects form an antitone function of $W$: a larger class of morphisms has fewer local objects (`MorphismProperty.isLocal_antitone`). A supremum of classes gives the infimum of their local objects, `MorphismProperty.isLocal_iSup`, since an object is local for $\bigsqcup_i W_i$ exactly when it is local for each $W_i$. The local objects are closed under limits of each shape, and the colocal objects under colimits of each shape. Section 1 of Chapter 4 uses the local objects for Bousfield localization.

#### Local properties on a site

The module `Mathlib.CategoryTheory.ObjectProperty.SiteLocal` uses a precoverage `K : Precoverage C`, a family of covering presieves of each object. The class `P.IsLocal K` says that $P$ is local for $K$: for each covering presieve $R$ of $X$, $P(X)$ holds if and only if $P(Y)$ holds for each $Y \to X$ in $R$. The two fields are `IsLocal.component`, which passes $P$ from $X$ to each member of a cover, and `IsLocal.of_presieve`, which glues. The lemma `ObjectProperty.iff_of_zeroHypercover` gives the same statement for a cover in the form `Precoverage.ZeroHypercover`, and `IsLocal.mk_of_zeroHypercover` is a constructor from this form. The sites of Chapter 6 give the examples.

#### Shifts

Let $C$ have a shift by an additive monoid $A$, as in Chapter 5. The module `Mathlib.CategoryTheory.ObjectProperty.Shift` defines `P.shift a`, with $(P.\mathrm{shift}\ a)(X) \iff P(X[a])$ by `ObjectProperty.prop_shift_iff`. The class `P.IsStableUnderShiftBy a` asks $P \le P.\mathrm{shift}\ a$, and `P.IsStableUnderShift A` asks this for each $a$. A stable property gives a shift on the full subcategory, the instance `ObjectProperty.hasShift`, and the inclusion commutes with the shifts, `ObjectProperty.commShiftι`. The module `Mathlib.CategoryTheory.ObjectProperty.ShiftAdditive` adds that the shift functors of the full subcategory are additive when those of $C$ are.

The closure `P.shiftClosure A` holds at $X$ when $X \cong Y[a]$ for some $Y$ in $P$ and some $a$. It is stable under the shift and closed under isomorphisms, and `ObjectProperty.shiftClosure_le_iff` says it is the smallest such property above $P$. For a group, the closure is a union of shifts.

**Proposition.** Let $G$ be an additive group and $P$ closed under isomorphisms. Then $P.\mathrm{shiftClosure}\ G = \bigsqcup_g P.\mathrm{shift}\ g$.

*Proof.* If $X \cong Y[a]$ with $P(Y)$, then $X[-a] \cong Y[a][-a] \cong Y$, so $P(X[-a])$, and $X$ is in $P.\mathrm{shift}(-a)$. Conversely, if $P(X[g])$ then $X \cong X[g][-g]$, so $X$ is in the closure. $\square$

This is `ObjectProperty.shiftClosure_eq_iSup`. The module `Mathlib.CategoryTheory.ObjectProperty.ClosureShift` has two instances: the retract closure and the limits closure `P.limitsClosure J` of a stable property are stable, the second one for a group.

#### Common errors

1. The direction of the orthogonals is easy to swap. `P.rightOrthogonal` holds at $Y$ when each morphism *into* $Y$ from $P$ is zero, and `P.leftOrthogonal` holds at $X$ when each morphism *out of* $X$ into $P$ is zero. Check with `ObjectProperty.rightOrthogonal_iff` before a proof.
2. `IsClosedUnderKernels` is about kernels of morphisms *between objects of $P$*. It is not the same as `MorphismProperty.kernels W` for a class $W$, which is a property of objects built from a class of morphisms, and not `Functor.kernel F`, the objects sent to zero.
3. Many lemmas of the form `prop_of_isZero` or `prop_zero` need `P.IsClosedUnderIsomorphisms` as well as the main class, since `ContainsZero` gives only one zero object. A proof that fails with a missing instance often needs the isomorphism closure first.

### Exercises

1. (A) Show that the property of the injective objects of an abelian category is stable under retracts, and that it is closed under binary biproducts.
2. (A) Show that $P^{\perp}$ is closed under subobjects and under products in a category with zero morphisms.
3. (B) In the category of abelian groups, let $P$ be the property of the torsion groups. Compute $P^{\perp}$ and ${}^{\perp}(P^{\perp})$, and check the theorem of Dickson in this case.
4. (B) Show that a property closed under subobjects and quotients in an abelian category is closed under kernels, cokernels and images.
5. (B) Let $W = \{ 2 : \mathbb{Z} \to \mathbb{Z} \}$ in the category of abelian groups. Show that a group $Z$ is $W$-local if and only if multiplication by $2$ is bijective on $Z$.
6. (C) Let $P$ be closed under quotients. Show that `P.hasFiniteResolution` is $P$. Then let $P$ be the free abelian groups of finite rank, and show that `P.hasFiniteResolution` is the property of the finitely generated abelian groups.

### Reference

<?reference?>
