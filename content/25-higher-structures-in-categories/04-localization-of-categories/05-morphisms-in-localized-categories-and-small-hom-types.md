---
title: Morphisms in localized categories and small hom types
kind: api
modules:
  - Mathlib.CategoryTheory.Localization.HomEquiv
  - Mathlib.CategoryTheory.Localization.LocallySmall
  - Mathlib.CategoryTheory.Localization.SmallHom
  - Mathlib.CategoryTheory.Localization.SmallShiftedHom
explains:
  E2: [CategoryTheory.Localization.homEquiv, CategoryTheory.LocalizerMorphism.homMap, CategoryTheory.MorphismProperty.locallySmall_of_hasLocalization, CategoryTheory.Localization.hasSmallLocalizedHom_iff, CategoryTheory.Localization.SmallHom.equiv_comp, CategoryTheory.Localization.SmallShiftedHom.comp, CategoryTheory.Localization.SmallShiftedHom.postcompEquiv]
  E1: auto
families: []
requires: [V24.C01, V24.C02, V25.C03]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Morphisms in localized categories and small hom types

### Overview

Section 1 shows that a localization of $C$ at $W$ is unique up to equivalence, so the type of morphisms $L(X) \to L(Y)$ does not depend on the choice of the localization functor $L$, up to a bijection. The four modules of this section make this bijection explicit and use it to solve a problem of universes. The constructed localization `W.Localization` has its morphisms in a large universe, because a morphism is a class of zigzags. In many cases a smaller model exists. The derived category of a category of modules is an example: its types of morphisms are small, but the construction does not show it.

The module `HomEquiv` gives the bijection `Localization.homEquiv` between morphisms in two localized categories, and its generalization `LocalizerMorphism.homMap` along a localizer morphism. The module `LocallySmall` relates the existence of a localization with small types of morphisms to the property that the localized category is locally small. The module `SmallHom` defines a type `SmallHom W X Y` in a chosen universe $w$ when the morphisms from $X$ to $Y$ in the localized category are $w$-small, and it transports the composition. The module `SmallShiftedHom` does the same for morphisms $X \to Y[m]$ in a category with a shift. This last construction is the base of the type `Abelian.Ext` of extensions in an abelian category, which Volume 26 treats.

### The library around it

#### The bijection between two localizations

Let $L_1 : C \to D_1$ and $L_2 : C \to D_2$ be two localization functors for the same class $W$. By the uniqueness of Section 1, there is an equivalence $G : D_1 \to D_2$ with an isomorphism $e : L_1 \circ G \cong L_2$. For objects $X$ and $Y$ of $C$, the map

$$f \mapsto e_X^{-1} \circ G(f) \circ e_Y$$

sends a morphism $L_1(X) \to L_1(Y)$ to a morphism $L_2(X) \to L_2(Y)$. This is `Localization.homEquiv W L₁ L₂`, an `Equiv` of the two types of morphisms. The value does not depend on the choice of $G$ and $e$. The lemma `Localization.homEquiv_eq` gives the formula for any such pair. The reason is that two lifts of $L_2$ along $L_1$ are isomorphic by a unique isomorphism compatible with $e$, so two choices give the same conjugate of $G(f)$.

The basic identities are simp lemmas or are used by simp:

| Lean name | Statement |
| --- | --- |
| `Localization.homEquiv_map` | the image of $L_1(f)$ is $L_2(f)$ |
| `Localization.homEquiv_id` | the image of an identity is an identity |
| `Localization.homEquiv_comp` | the image of $f \circ g$ is the composite of the images |
| `Localization.homEquiv_isoOfHom_inv` | the image of the formal inverse of $s \in W$ is the formal inverse of $s$ |
| `Localization.homEquiv_refl` | `homEquiv W L L` is the identity |
| `Localization.homEquiv_trans` | `homEquiv W L₂ L₃` after `homEquiv W L₁ L₂` is `homEquiv W L₁ L₃` |
| `Localization.homEquiv_symm_apply` | the inverse of `homEquiv W L₁ L₂` is `homEquiv W L₂ L₁` |

The construction comes from a more general map. Let $\Phi$ be a localizer morphism from $W_1$ on $C_1$ to $W_2$ on $C_2$, and let $L_1$ and $L_2$ be localizations at $W_1$ and $W_2$. The map `LocalizerMorphism.homMap Φ L₁ L₂` sends a morphism $L_1(X) \to L_1(Y)$ to a morphism $L_2(\Phi X) \to L_2(\Phi Y)$. It uses the localized functor $\bar\Phi$ of Section 4 and the isomorphism of the commutative square. The lemmas `LocalizerMorphism.homMap_map`, `LocalizerMorphism.homMap_id` and `LocalizerMorphism.homMap_comp` say that it is compatible with $L_1$, identities and composition. The lemma `LocalizerMorphism.homMap_apply` gives the formula for any commutative square, and `LocalizerMorphism.homMap_homMap` says that the map for a composite $\Phi \circ \Psi$ is the composite of the maps. With $\Phi$ the identity, `LocalizerMorphism.id_homMap` gives the case of `homEquiv`. The bijection `homEquiv` is then `homMap` of the identity localizer morphism, with inverse `homMap` in the other direction. The identity `homMap_homMap` with `id_homMap` proves that the two maps are inverse.

#### Locally small localizations

Section 1 introduced the class `MorphismProperty.HasLocalization`, which records a localization functor `W.Q'` whose target has morphisms in a chosen universe $w$. The module `LocallySmall` relates it to the class `LocallySmall` of the target.

The definition `MorphismProperty.hasLocalizationOfLocallySmall` produces an instance of `HasLocalization.{w} W` from any localization functor $L : C \to D$ with `LocallySmall.{w} D`. The proof shrinks the morphisms of $D$: the category `ShrinkHoms D` has the same objects as $D$ and morphisms in `Type w`, and `ShrinkHoms.equivalence` is an equivalence with $D$. The composite of $L$ and this equivalence is again a localization functor. This version needs the objects of $C$ and $D$ in the same universe. The variant `MorphismProperty.hasLocalizationOfLocallySmall'` removes this condition. It replaces $D$ by the category induced on the objects of $C$ by $L$, which is equivalent to $D$ because $L$ is essentially surjective. It is a definition, not an instance, so a user supplies it as a local instance.

In the other direction, `MorphismProperty.locallySmall_of_hasLocalization` says that the target of any localization functor for $W$ is locally $w$-small when `HasLocalization.{w} W` holds. The proof is short. The functor `Localization.uniq L W.Q' W` is an equivalence from $D$ to the target of `W.Q'`. An equivalence is faithful, so it injects each type of morphisms of $D$ into a type of morphisms of the small model, and a type that injects into a $w$-small type is $w$-small.

#### Small types of morphisms

The class `Localization.HasSmallLocalizedHom.{w} W X Y` says that the type of morphisms from $X$ to $Y$ in `W.Localization` is $w$-small. The definition uses the constructed localization, but `Localization.hasSmallLocalizedHom_iff` frees it from this choice: for any localization functor $L$, the class holds if and only if the type $L(X) \to L(Y)$ is $w$-small. The proof is one line. The bijection `homEquiv W W.Q L` carries smallness in both directions. Two consequences are useful. First, `Localization.hasSmallLocalizedHom_of_isLocalization` gives the class for the universe of the morphisms of any target $D$, so the class always holds in some universe. Second, `Localization.small_of_hasSmallLocalizedHom` gives the `Small` instance for any choice of $L$.

The class depends on $X$ and $Y$ only through their images in the localized category. The lemma `Localization.hasSmallLocalizedHom_iff_of_isos` changes $X$ and $Y$ by isomorphisms of $C$. The lemmas `Localization.hasSmallLocalizedHom_iff_target` and `Localization.hasSmallLocalizedHom_iff_source` change them along a morphism of $W$, which becomes an isomorphism after localization.

Under the class, `Localization.SmallHom.{w} W X Y` is the type `Shrink` of `W.Q.obj X ⟶ W.Q.obj Y`, a type in the universe $w$. For each localization functor $L$, the bijection `Localization.SmallHom.equiv W L` identifies it with $L(X) \to L(Y)$. It is the composite of `equivShrink` and `homEquiv`. The constructors and the composition are:

| Lean name | Meaning |
| --- | --- |
| `Localization.SmallHom.mk` | the image of a morphism $f : X \to Y$ of $C$ |
| `Localization.SmallHom.mkInv` | the formal inverse of a morphism $s : Y \to X$ in $W$ |
| `Localization.SmallHom.comp` | the composite of $\alpha : X \to Y$ and $\beta : Y \to Z$ |
| `Localization.SmallHom.chgUniv` | the bijection between the types for two universes |

The composition `Localization.SmallHom.comp` is defined with the constructed localization `W.Q`. The main lemma `Localization.SmallHom.equiv_comp` says that every `equiv W L` carries it to the composition in the target of $L$: $\mathrm{equiv}_L(\alpha \circ \beta) = \mathrm{equiv}_L(\alpha) \circ \mathrm{equiv}_L(\beta)$. The proof writes $\alpha$ and $\beta$ as images under `equivShrink` and then uses `homEquiv_comp`. The simp lemmas `Localization.SmallHom.equiv_mk` and `Localization.SmallHom.equiv_mkInv` compute the bijection on the constructors. All the algebraic identities follow by the same method: apply the injective map `equiv W W.Q` and simplify. This gives `Localization.SmallHom.mk_comp_mk`, `Localization.SmallHom.comp_assoc`, the unit laws `Localization.SmallHom.comp_mk_id` and `Localization.SmallHom.mk_id_comp`, and the inverse laws `Localization.SmallHom.mk_comp_mkInv` and `Localization.SmallHom.mkInv_comp_mk`.

A localizer morphism acts on these types. The map `LocalizerMorphism.smallHomMap` sends `SmallHom W₁ X Y` to `SmallHom W₂ (Φ X) (Φ Y)`, in a possibly different universe. The lemma `LocalizerMorphism.equiv_smallHomMap` computes it through any commutative square, and `LocalizerMorphism.smallHomMap_mk` and `LocalizerMorphism.smallHomMap_comp` give compatibility with the constructors and the composition. The primed form `LocalizerMorphism.smallHomMap'` allows objects isomorphic to $\Phi X$ and $\Phi Y$.

#### Small shifted morphisms

Let $C$ carry a shift by an additive monoid $M$, and let $W$ be compatible with the shift, which is the class `MorphismProperty.IsCompatibleWithShift`. The localized category then carries a shift, and a localization functor commutes with the shifts (Chapter 5 treats shifts). The predicate `Localization.HasSmallLocalizedShiftedHom.{w} W M X Y` asks that the morphisms $X[a] \to Y[b]$ in the localized category are $w$-small for all $a$ and $b$ in $M$. The lemma `Localization.hasSmallLocalizedShiftedHom_iff` restates it with any localization functor $L$ that commutes with the shifts.

The type `Localization.SmallShiftedHom.{w} W X Y m` is `SmallHom W X (Y⟦m⟧)`. It is a small model for the type `ShiftedHom (L.obj X) (L.obj Y) m` of morphisms $L(X) \to L(Y)[m]$, and `Localization.SmallShiftedHom.equiv W L` is the bijection. A morphism $f : X \to Y$ in degree $0$ gives `Localization.SmallShiftedHom.mk₀`, and a morphism of $W$ gives a formal inverse `Localization.SmallShiftedHom.mk₀Inv` in degree $0$. The composition

$$\mathrm{comp} : \mathrm{SmallShiftedHom}(X, Y, a) \times \mathrm{SmallShiftedHom}(Y, Z, b) \to \mathrm{SmallShiftedHom}(X, Z, c), \quad b + a = c,$$

is `Localization.SmallShiftedHom.comp`. For $f : X \to Y[a]$ and $g : Y \to Z[b]$, it composes $f$ with the shift $g[a] : Y[a] \to Z[b][a]$ and with the isomorphism $Z[b][a] \cong Z[c]$. The shift of $g$ uses `Localization.SmallHom.shift`, which is `smallHomMap` for the localizer morphism `MorphismProperty.shiftLocalizerMorphism`. The lemma `Localization.SmallShiftedHom.equiv_comp` says that `equiv W L` carries this composition to the composition of shifted morphisms, and `Localization.SmallShiftedHom.comp_assoc` gives associativity.

The unit laws are `Localization.SmallShiftedHom.comp_mk₀_id` and `Localization.SmallShiftedHom.mk₀_id_comp`. The laws `Localization.SmallShiftedHom.mk₀_comp_mk₀Inv` and `Localization.SmallShiftedHom.mk₀Inv_comp_mk₀` say that `mk₀Inv` is an inverse. From them, `Localization.SmallShiftedHom.postcompEquiv` gives a bijection $\mathrm{SmallShiftedHom}(X, Y, a) \cong \mathrm{SmallShiftedHom}(X, Z, a)$ for each morphism $s : Y \to Z$ in $W$. The proof is direct: composition with `mk₀ s` has inverse the composition with `mk₀Inv s`, by associativity and the inverse laws. The dual `Localization.SmallShiftedHom.precompEquiv` composes on the other side. For the derived category, these bijections say that $\mathrm{Ext}^n$ does not change when an object is replaced by a quasi-isomorphic one. The universe change `Localization.SmallShiftedHom.chgUniv` and the action `LocalizerMorphism.smallShiftedHomMap` of a localizer morphism that commutes with the shifts complete the API.

#### Common errors

1. A user proves an identity in `SmallHom W X Y` by unfolding `Shrink`. The intended method is to apply `(SmallHom.equiv W W.Q).injective` and simplify with `equiv_comp`, `equiv_mk` and `equiv_mkInv`, as the library does.
2. A user forgets the order of the degrees in `Localization.SmallShiftedHom.comp`. The hypothesis is `b + a = c`, with the degree of the second morphism first. In a commutative monoid such as $\mathbb{Z}$ this order is easy to miss, and a rewrite with `add_comm` is often needed.
3. A user expects `MorphismProperty.hasLocalizationOfLocallySmall` to fire by instance search. It is a definition, so a user must supply it by hand as a local instance.

### Exercises

1. (A) Prove that `Localization.homEquiv W L₁ L₂` sends $L_1(f)$ to $L_2(f)$ from the formula with $G$ and $e$, and deduce that it sends identities to identities.
2. (A) Show that `HasSmallLocalizedHom.{w} W X Y` holds when $W$ is the class of isomorphisms and $C$ is locally $w$-small.
3. (B) Use `Localization.hasSmallLocalizedHom_iff_target` to show that, for a reflective subcategory with reflector $r$ and $W$ the morphisms that $r$ inverts, the class `HasSmallLocalizedHom.{w} W X Y` holds when the morphisms $r(X) \to r(Y)$ form a $w$-small type.
4. (B) Prove `Localization.SmallHom.mk_comp_mkInv` from `equiv_comp`, `equiv_mk` and `equiv_mkInv`.
5. (B) Show that `Localization.SmallShiftedHom.postcompEquiv` for $s$ and for $s'$ compose to `postcompEquiv` for $s \circ s'$, when all the hypotheses hold.
6. (C) Let $\Phi$ be a localized equivalence. Show that `LocalizerMorphism.homMap Φ L₁ L₂` is a bijection, and deduce that `HasSmallLocalizedHom` for $X$ and $Y$ is equivalent to `HasSmallLocalizedHom` for $\Phi X$ and $\Phi Y$.

### Reference

<?reference?>
