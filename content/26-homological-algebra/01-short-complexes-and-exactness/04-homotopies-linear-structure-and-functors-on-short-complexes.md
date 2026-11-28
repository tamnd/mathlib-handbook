---
title: Homotopies, linear structure and functors on short complexes
kind: api
modules:
  - Mathlib.Algebra.Homology.ShortComplex.Preadditive
  - Mathlib.Algebra.Homology.ShortComplex.Linear
  - Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
  - Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
  - Mathlib.Algebra.Homology.ShortComplex.QuasiIso
explains:
  E2: [CategoryTheory.ShortComplex.Homotopy, CategoryTheory.ShortComplex.Homotopy.homologyMap_congr, CategoryTheory.ShortComplex.homologyMap_add, CategoryTheory.Functor.PreservesHomology, CategoryTheory.ShortComplex.mapHomologyIso, CategoryTheory.Functor.exact_tfae, CategoryTheory.ShortComplex.QuasiIso, CategoryTheory.ShortComplex.quasiIso_of_epi_of_isIso_of_mono]
  E1: auto
families: []
requires: [V24.C08, V25.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Homotopies, linear structure and functors on short complexes

### Overview

Section 1 defines a short complex $X_1 \xrightarrow{f} X_2 \xrightarrow{g} X_3$ and its homology, and Section 2 defines exactness. Those sections need only zero morphisms. This section adds the structure that appears when the category $C$ is preadditive or linear, and it studies how a functor $F : C \to D$ acts on homology.

The five modules hold four groups of results. First, the morphisms of short complexes form an abelian group, and the homology is an additive functor. Second, there is a notion of homotopy between two morphisms of short complexes, and homotopic morphisms induce the same map on homology. Third, a functor that preserves the relevant kernels and cokernels preserves left and right homology data, and so it commutes with homology. Fourth, a quasi-isomorphism of short complexes is a morphism that induces an isomorphism on homology. The exact functors between abelian categories are characterized by their action on exact sequences.

Mathlib writes `f ≫ g` for the composite $g \circ f$. The names of this section live in the namespaces `CategoryTheory.ShortComplex` and `CategoryTheory.Functor`.

### The library around it

#### The additive structure

Let $C$ be preadditive and let $S_1$, $S_2$ be short complexes in $C$. The module `Mathlib.Algebra.Homology.ShortComplex.Preadditive` adds the instance `CategoryTheory.ShortComplex.instAddCommGroupHom`, and with it `CategoryTheory.ShortComplex.instPreadditive`. The sum of two morphisms is the sum of the components. The simp lemmas `CategoryTheory.ShortComplex.add_τ₁`, `CategoryTheory.ShortComplex.sub_τ₂` and `CategoryTheory.ShortComplex.neg_τ₃` state this for each of the three components.

Every homology construction of Section 1 is additive. Each lemma name is the name of the map with the word add, sub or neg at the end.

| Lean name | Statement |
|---|---|
| `CategoryTheory.ShortComplex.homologyMap_add` | $H(\varphi + \varphi') = H(\varphi) + H(\varphi')$ |
| `CategoryTheory.ShortComplex.homologyMap_neg` | $H(-\varphi) = -H(\varphi)$ |
| `CategoryTheory.ShortComplex.cyclesMap_sub` | the map on cycles of $\varphi - \varphi'$ |
| `CategoryTheory.ShortComplex.opcyclesMap_add` | the map on opcycles of $\varphi + \varphi'$ |
| `CategoryTheory.ShortComplex.leftHomologyMap_add` | the same for left homology |
| `CategoryTheory.ShortComplex.homologyFunctor_additive` | the homology functor is additive |

The primed forms, such as `CategoryTheory.ShortComplex.homologyMap'_add`, take explicit homology data. Their proof is the same in each case. If $\gamma$ is a homology map data for $\varphi$ and $\gamma'$ one for $\varphi'$, then the sums of the components form a homology map data for $\varphi + \varphi'$. The definitions `CategoryTheory.ShortComplex.LeftHomologyMapData.add` and `CategoryTheory.ShortComplex.HomologyMapData.add` build it. A homology map data is unique, so the map on homology is the sum. The instances `CategoryTheory.ShortComplex.cyclesFunctor_additive` and `CategoryTheory.ShortComplex.opcyclesFunctor_additive` give the additivity of the other functors.

The module `Mathlib.Algebra.Homology.ShortComplex.Linear` repeats this for a category that is linear over a ring $R$. The instance `CategoryTheory.ShortComplex.instLinear` makes the category of short complexes $R$-linear, and `CategoryTheory.ShortComplex.homologyMap_smul` says $H(a \varphi) = a\, H(\varphi)$. The instance `CategoryTheory.ShortComplex.homologyFunctor_linear` says that the homology functor is $R$-linear. The lemmas `CategoryTheory.ShortComplex.cyclesMap_smul` and `CategoryTheory.ShortComplex.opcyclesMap_smul` complete the family.

#### Homotopies of short complexes

Let $\varphi_1, \varphi_2 : S_1 \to S_2$. A homotopy `CategoryTheory.ShortComplex.Homotopy φ₁ φ₂` consists of four maps
$$h_0 : X_1 \to Y_1, \quad h_1 : X_2 \to Y_1, \quad h_2 : X_3 \to Y_2, \quad h_3 : X_3 \to Y_3,$$
where $S_1 = (X_1, X_2, X_3)$ and $S_2 = (Y_1, Y_2, Y_3)$. They satisfy $h_0 \circ f_2 = 0$ in Mathlib order (the field `CategoryTheory.ShortComplex.Homotopy.h₀_f` states `h₀ ≫ S₂.f = 0`), and `CategoryTheory.ShortComplex.Homotopy.g_h₃` states `S₁.g ≫ h₃ = 0`. The three equations are
$$\varphi_1^{(1)} = h_1 f_1 + h_0 + \varphi_2^{(1)}, \quad \varphi_1^{(2)} = h_2 g_1 + f_2 h_1 + \varphi_2^{(2)}, \quad \varphi_1^{(3)} = h_3 + g_2 h_2 + \varphi_2^{(3)},$$
in the usual order of composition. They are the fields `CategoryTheory.ShortComplex.Homotopy.comm₁`, `CategoryTheory.ShortComplex.Homotopy.comm₂` and `CategoryTheory.ShortComplex.Homotopy.comm₃`. The maps $h_1$ and $h_2$ are the usual homotopy of a complex of length three. The two extra maps $h_0$ and $h_3$ absorb the ends, where a short complex has no further object.

**Proposition.** If $\varphi_1$ and $\varphi_2$ are homotopic, then $H(\varphi_1) = H(\varphi_2)$.

*Proof.* By additivity it suffices to show that $\psi = \varphi_1 - \varphi_2$ induces zero when $\psi$ has the form of the three equations with $\varphi_2 = 0$. Let $z$ be a cycle of $S_1$, so $g_1 z = 0$. Then $\psi^{(2)} z = h_2 g_1 z + f_2 h_1 z = f_2 (h_1 z)$, which is a boundary of $S_2$. So $\psi$ induces zero on the left homology, and the left homology is the homology. $\square$

In Lean this is `CategoryTheory.ShortComplex.Homotopy.homologyMap_congr`. The variants `CategoryTheory.ShortComplex.Homotopy.leftHomologyMap_congr` and `CategoryTheory.ShortComplex.Homotopy.rightHomologyMap_congr` treat left and right homology. A null homotopic morphism is built from the four maps by `CategoryTheory.ShortComplex.nullHomotopic`, and `CategoryTheory.ShortComplex.homologyMap_nullHomotopic` says that it induces zero. The equivalence `CategoryTheory.ShortComplex.Homotopy.equivSubZero` identifies homotopies from $\varphi_1$ to $\varphi_2$ with homotopies from $\varphi_1 - \varphi_2$ to $0$.

The homotopies form the usual algebra. The constructions `CategoryTheory.ShortComplex.Homotopy.refl`, `CategoryTheory.ShortComplex.Homotopy.symm`, `CategoryTheory.ShortComplex.Homotopy.trans`, `CategoryTheory.ShortComplex.Homotopy.add`, `CategoryTheory.ShortComplex.Homotopy.compLeft` and `CategoryTheory.ShortComplex.Homotopy.compRight` exist, and a simp lemma gives each component, for example `CategoryTheory.ShortComplex.Homotopy.trans_h₁`. The constructions `CategoryTheory.ShortComplex.Homotopy.op` and `CategoryTheory.ShortComplex.Homotopy.unop` pass to the opposite category, where $h_0$ and $h_3$ change places. A `CategoryTheory.ShortComplex.HomotopyEquiv` is a pair of morphisms with homotopies to the identities in both orders.

#### Functors and homology

Let $F : C \to D$ be a functor between categories with zero morphisms that preserves zero morphisms. Then $F$ sends a short complex $S$ to a short complex `S.map F`. The question is when $H(F S) \cong F(H(S))$.

A left homology data $h$ of $S$ consists of a kernel $K$ of $g$ and a cokernel $H$ of the induced map $X_1 \to K$. The class `CategoryTheory.ShortComplex.LeftHomologyData.IsPreservedBy h F` says that $F$ preserves this kernel and this cokernel. Then `CategoryTheory.ShortComplex.LeftHomologyData.map` gives a left homology data of `S.map F`, with objects $F K$ and $F H$. The dual notions are `CategoryTheory.ShortComplex.RightHomologyData.IsPreservedBy` and `CategoryTheory.ShortComplex.RightHomologyData.map`.

The class `CategoryTheory.Functor.PreservesLeftHomologyOf F S` says that $F$ preserves every left homology data of $S$. The class `CategoryTheory.Functor.PreservesHomology F` says that $F$ preserves all kernels and all cokernels; the fields `CategoryTheory.Functor.PreservesHomology.preservesKernels` and `CategoryTheory.Functor.PreservesHomology.preservesCokernels` state this. Then $F$ preserves the left and right homology of every short complex. An exact functor preserves homology: this is the instance `CategoryTheory.Functor.preservesHomologyOfExact`, for a functor that preserves finite limits and finite colimits.

The name of each comparison isomorphism is the word map, then the name of the object, then the word Iso.

| Lean name | Statement |
|---|---|
| `CategoryTheory.ShortComplex.mapCyclesIso` | $Z(F S) \cong F(Z(S))$ |
| `CategoryTheory.ShortComplex.mapOpcyclesIso` | the same for opcycles |
| `CategoryTheory.ShortComplex.mapLeftHomologyIso` | the same for left homology |
| `CategoryTheory.ShortComplex.mapHomologyIso` | $H(F S) \cong F(H(S))$ |
| `CategoryTheory.ShortComplex.homologyFunctorIso` | the isomorphism of functors $H \circ F \cong F \circ H$ |

The lemmas `CategoryTheory.ShortComplex.mapHomologyIso_hom_naturality` and `CategoryTheory.ShortComplex.mapCyclesIso_hom_naturality` say that these isomorphisms are natural in $S$. The lemma `CategoryTheory.ShortComplex.homologyMap_mapNatTrans` treats a natural transformation $F \to G$. Two special cases avoid the full hypothesis. If $g = 0$, then $F$ preserves the left homology of $S$ as soon as it preserves the cokernel of $f$ (`CategoryTheory.Functor.preservesLeftHomology_of_zero_g`); `CategoryTheory.Functor.preservesLeftHomology_of_zero_f` is the case $f = 0$.

#### Exact functors

The module `Mathlib.Algebra.Homology.ShortComplex.ExactFunctor` characterizes exact functors. Let $F : C \to D$ be an additive functor between abelian categories. Then `CategoryTheory.Functor.exact_tfae` says that the following are equivalent.

1. $F$ sends short exact sequences to short exact sequences.
2. $F$ sends exact short complexes to exact short complexes.
3. $F$ preserves homology.
4. $F$ preserves finite limits and finite colimits.

The one sided forms are `CategoryTheory.Functor.preservesFiniteLimits_tfae` and `CategoryTheory.Functor.preservesFiniteColimits_tfae`. For example, `CategoryTheory.Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono` says that $F$ is left exact if and only if, for each short exact sequence $0 \to A \to B \to C \to 0$, the sequence $0 \to F A \to F B \to F C$ is exact. The lemma `CategoryTheory.Functor.preservesMonomorphisms_of_preserves_shortExact_left` extracts the preservation of monomorphisms. The direction from 4 to 3 is the instance of the last subsection. The direction from 2 to 4 uses that a kernel of $f$ is the same as an exact sequence $0 \to K \to X \to Y$ with a mono on the left.

#### Quasi-isomorphisms

Let $S_1$ and $S_2$ have homology. A morphism $\varphi : S_1 \to S_2$ is a quasi-isomorphism, `CategoryTheory.ShortComplex.QuasiIso φ`, if $H(\varphi)$ is an isomorphism. The lemma `CategoryTheory.ShortComplex.quasiIso_iff` states the definition, and `CategoryTheory.ShortComplex.QuasiIso.isIso` gives the instance. The forms `CategoryTheory.ShortComplex.quasiIso_iff_isIso_leftHomologyMap'` and `CategoryTheory.ShortComplex.quasiIso_iff_isIso_rightHomologyMap'` use explicit homology data.

The class has the two out of three property. An isomorphism is a quasi-isomorphism (`CategoryTheory.ShortComplex.quasiIso_of_isIso`), a composite of two quasi-isomorphisms is one (`CategoryTheory.ShortComplex.quasiIso_comp`), and `CategoryTheory.ShortComplex.quasiIso_of_comp_left` and `CategoryTheory.ShortComplex.quasiIso_of_comp_right` cancel one factor. These all follow from the functoriality of $H$.

**Proposition.** If $\varphi^{(1)}$ is an epimorphism, $\varphi^{(2)}$ is an isomorphism and $\varphi^{(3)}$ is a monomorphism, then $\varphi$ is a quasi-isomorphism.

*Proof sketch.* The cycles of $S_i$ are the kernel of $g_i$. Since $\varphi^{(3)}$ is mono, $g_2 \varphi^{(2)} x = 0$ if and only if $g_1 x = 0$, so $\varphi^{(2)}$ maps the cycles of $S_1$ isomorphically to those of $S_2$. Since $\varphi^{(1)}$ is epi, the image of $f_2$ is the image under $\varphi^{(2)}$ of the image of $f_1$. So the quotients agree. $\square$

This is `CategoryTheory.ShortComplex.quasiIso_of_epi_of_isIso_of_mono`. The module also relates quasi-isomorphisms to functors: `CategoryTheory.ShortComplex.quasiIso_map_iff_of_preservesLeftHomology` says that $F \varphi$ is a quasi-isomorphism when $\varphi$ is one and $F$ preserves left homology. For opposite categories, `CategoryTheory.ShortComplex.quasiIso_opMap_iff` says that $\varphi^{\mathrm{op}}$ is a quasi-isomorphism if and only if $\varphi$ is one.

#### Common errors

1. A homotopy of short complexes has four maps, not two. A proof that gives only $h_1$ and $h_2$ must set $h_0$ and $h_3$ and prove the side conditions `h₀ ≫ S₂.f = 0` and `S₁.g ≫ h₃ = 0`. The easy choice is often $h_0 = 0$ and $h_3 = 0$.
2. `CategoryTheory.ShortComplex.mapHomologyIso` needs the instance `CategoryTheory.Functor.PreservesLeftHomologyOf F S` and the instance that `S.map F` has homology. A missing instance error at this point usually means that Lean cannot see that $F$ preserves the kernel. For an exact functor, the instance comes from `CategoryTheory.Functor.preservesHomologyOfExact`.
3. `CategoryTheory.ShortComplex.QuasiIso` is a class on a morphism of short complexes. The class `QuasiIso` for maps of homological complexes is a different notion of Chapter 2. The two names do not unify.

### Exercises

1. (A) Use `CategoryTheory.ShortComplex.homologyMap_add` and `CategoryTheory.ShortComplex.homologyMap_neg` to prove $H(\varphi - \varphi') = H(\varphi) - H(\varphi')$.
2. (A) Show that the identity of $S$ is homotopic to $0$ when $S$ is $0 \to X \xrightarrow{1} X$, and conclude that $H(S) = 0$.
3. (B) Let $\varphi : S_1 \to S_2$ have $\varphi^{(1)}$ and $\varphi^{(3)}$ isomorphisms. Give an example in abelian groups where $\varphi$ is not a quasi-isomorphism.
4. (B) Prove that the forgetful functor from $R$-modules to abelian groups preserves homology, and find the instance that gives it.
5. (B) Show that a quasi-isomorphism between two short complexes with $f = 0$ and $g = 0$ is an isomorphism on $X_2$.
6. (C) Prove the direction from 1 to 4 of `CategoryTheory.Functor.exact_tfae`: a functor that preserves short exact sequences preserves kernels.

### Reference

<?reference?>
