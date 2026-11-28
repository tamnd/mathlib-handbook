---
title: Comma categories cut out by morphism properties, and relative representability
kind: api
modules:
  - Mathlib.CategoryTheory.MorphismProperty.Comma
  - Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
  - Mathlib.CategoryTheory.MorphismProperty.CommaSites
  - Mathlib.CategoryTheory.MorphismProperty.Representable
explains:
  E2: [CategoryTheory.MorphismProperty.Comma.forgetFullyFaithful, CategoryTheory.MorphismProperty.Over.mapPullbackAdj, CategoryTheory.MorphismProperty.Under.mapPushoutAdj, CategoryTheory.Functor.relativelyRepresentable.of_isIso, CategoryTheory.Functor.relativelyRepresentable.isMultiplicative, CategoryTheory.Functor.relativelyRepresentable.isStableUnderBaseChange, CategoryTheory.MorphismProperty.of_relative_map, CategoryTheory.MorphismProperty.relative_isStableUnderBaseChange]
  E1: auto
families: []
requires: [V24.C02, V24.C03, V24.C04, V24.C05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Comma categories cut out by morphism properties, and relative representability

### Overview

Algebraic geometry seldom works with the full category of schemes over a base $S$. It works with the schemes of finite presentation or the étale schemes over $S$. Each of these is a subcategory of the slice category $\mathrm{Over}(S)$, cut out by a property $P$ of the structure morphism $X \to S$. Sometimes the morphisms are also restricted by a second property $Q$. The first two modules give this construction for a general comma category, with the special cases `P.Over` and `P.Under`, and they lift pushforward and base change to these subcategories.

The third module puts a Grothendieck topology on `P.Over ⊤ S` from a precoverage on the ambient category. The fourth module defines relatively representable morphisms. A morphism $f : X \to Y$ in $D$ is representable relative to a functor $F : C \to D$ when each base change of $f$ along a morphism $F(a) \to Y$ is again in the image of $F$. With $F$ the Yoneda embedding, this is the classical notion of a representable morphism of presheaves.

The section uses the classes `RespectsIso` and `IsMultiplicative` of Section 1 and the stability under base change of Section 6. Comma categories, slices and pullbacks are in Chapters 2 and 4 of Volume 24.

### The library around it

#### The category `P.Comma L R Q W`

Let $L : A \to T$ and $R : B \to T$ be functors, and let $P$, $Q$, $W$ be properties of morphisms of $T$, $A$ and $B$. An object of `P.Comma L R Q W` is an object $(a, b, h : L(a) \to R(b))$ of the comma category with $P(h)$. A morphism $(a, b, h) \to (a', b', h')$ is a morphism $(u, v)$ of the comma category with $Q(u)$ and $W(v)$. The structures `MorphismProperty.Comma` and `Comma.Hom` add these proofs as fields. The identities and the composites exist only when $Q$ and $W$ contain the identities and are closed under composition, so the `Category` instance needs `Q.IsMultiplicative` and `W.IsMultiplicative`.

A morphism of `P.Comma L R Q W` has an underlying morphism `Comma.Hom.hom` in `Comma L R`. The simp lemmas `Comma.id_hom` and `Comma.comp_hom` compute it, and `Comma.Hom.ext'` says that two morphisms are equal when their underlying morphisms are equal. The functor `Comma.forget` to `Comma L R` is faithful. It reflects isomorphisms when $Q$ and $W$ respect isomorphisms. The constructions `Comma.isoFromComma` and `Comma.isoMk` build isomorphisms of the subcategory.

**Proposition.** The functor `Comma.forget L R P ⊤ ⊤` is fully faithful.

*Proof.* With $Q = W = \top$ the conditions on the morphisms are empty, so each morphism of `Comma L R` between objects of the subcategory lifts. This is `Comma.forgetFullyFaithful`. $\square$

So `P.Comma L R ⊤ ⊤` is the full subcategory of `Comma L R` on the objects whose structure morphism satisfies $P$. This full subcategory also has the form of an object property: `commaObj` is the property $P(h)$ of an object of `Comma L R`. The variants `overObj`, `underObj`, `costructuredArrowObj` and `structuredArrowObj` give the same property on `Over X`, `Under X`, `CostructuredArrow L X` and `StructuredArrow X R`. Each of them is `IsClosedUnderIsomorphisms` when $P$ respects isomorphisms.

The same data also gives a property of the morphisms of a slice category. A morphism of `Over X` satisfies `W.over` when its left component satisfies $W$, and a morphism of `Under X` satisfies `W.under` when its right component satisfies $W$. The lemma `over_eq_inverseImage` writes `W.over` as an inverse image along the forgetful functor. The instance `HasFactorization.over` says that factorizations in $T$ give factorizations in `Over S`.

Three kinds of functors connect the subcategories. For $P \le P'$, $Q \le Q'$ and $W \le W'$, `Comma.changeProp` is the inclusion of `P.Comma L R Q W` into `P'.Comma L R Q' W'`. It is faithful, and fully faithful when only $P$ changes (`Comma.fullyFaithfulChangeProp`). The functor `Comma.lift` factors a functor into `Comma L R` through the subcategory when its values satisfy the three properties. A natural transformation $l : L_1 \to L_2$ gives `Comma.mapLeft` from `P.Comma L₂ R Q W` to `P.Comma L₁ R Q W`, and $r : R_1 \to R_2$ gives `Comma.mapRight`. The coherences are `Comma.mapLeftId`, `Comma.mapLeftComp` and their analogues, and natural isomorphisms give the equivalences `Comma.mapLeftIso` and `Comma.mapRightIso`.

#### Arrows, slices and costructured arrows

The special cases are abbreviations, so the API of `P.Comma` applies to them.

| Lean name | Definition |
| --- | --- |
| `MorphismProperty.Arrow` | `P.Arrow Q W` is `P.Comma (𝟭 T) (𝟭 T) Q W`, the arrows that satisfy $P$, with squares whose sides satisfy $Q$ and $W$ |
| `MorphismProperty.Over` | `P.Over Q X` is `P.Comma (𝟭 T) (fromPUnit X) Q ⊤`, the objects $Y \to X$ that satisfy $P$, with morphisms over $X$ that satisfy $Q$ |
| `MorphismProperty.Under` | `P.Under Q X`, the objects $X \to Y$ that satisfy $P$, with morphisms under $X$ that satisfy $Q$ |
| `MorphismProperty.CostructuredArrow` | `P.CostructuredArrow Q F X`, the morphisms $F(a) \to X$ that satisfy $P$, with morphisms $a \to a'$ that satisfy $Q$ |

Each case has a faithful forgetful functor, such as `Over.forget`, to the ordinary category. It is full when the condition on the morphisms is $\top$. The constructors follow one pattern. `Over.mk Q f hf` is the object $f : Y \to X$ with `hf : P f`. `Over.homMk f w hf` is the morphism with left component `f`, the triangle `w` and `hf : Q f`. The last two arguments have default proofs. `Over.isoMk` builds an isomorphism from an isomorphism of the left objects, and `Over.Hom.ext` compares only the left components. The names `Under.mk`, `Under.homMk`, `CostructuredArrow.mk` and `CostructuredArrow.homMk` are the analogues. The functor `CostructuredArrow.toOver` sends $F(a) \to X$ to the same morphism in `P.Over ⊤ X`. It is faithful when $F$ is faithful and full when $F$ is full.

For example, in the category of schemes with $P$ the morphisms locally of finite presentation, `P.Over ⊤ S` is the category of $S$-schemes locally of finite presentation. In the category of sets with $P$ the injections, `P.Over ⊤ X` is a preorder, because a morphism between two injections into $X$ is unique when it exists.

#### Pushforward and base change

Let $f : X \to Y$ be a morphism of $T$. On the ordinary slices, composition with $f$ is a functor $\Sigma_f : \mathrm{Over}(X) \to \mathrm{Over}(Y)$, and base change is a functor $f^* : \mathrm{Over}(Y) \to \mathrm{Over}(X)$ with $\Sigma_f \dashv f^*$. The module `MorphismProperty.OverAdjunction` lifts this adjunction to the subcategories.

`Over.map Q hPf` is $\Sigma_f$ on `P.Over Q X`. It needs `P.IsStableUnderComposition` and a proof `hPf : P f`, so that $g \circ f$ satisfies $P$ when $g$ does. `Over.pullback P Q f` is $f^*$ on `P.Over Q Y`. It needs `P.HasPullbacksAlong f`, `P.IsStableUnderBaseChangeAlong f`, and `Q.IsStableUnderBaseChange`. The coherence isomorphisms are `Over.mapId`, `Over.mapComp`, `Over.pullbackComp` and `Over.pullbackCongr`. The isomorphism `Over.pullbackCompForgetIso` says that `Over.pullback` followed by `Over.forget` is the ordinary `Over.pullback f` after `Over.forget`. It is the identity, so the two agree by definition.

**Theorem.** Assume that $P$ is stable under composition, that $Q$ is stable under base change and has `Q.HasOfPostcompProperty Q`, that the pullbacks along $f$ of the elements of $P$ exist and satisfy $P$, and that $f$ satisfies $P$ and $Q$. Then `Over.map Q hPf ⊣ Over.pullback P Q f`.

*Proof sketch.* The counit at $A \to Y$ is the projection $X \times_Y A \to A$. It is a base change of $f$, so it satisfies $Q$. The unit at $a : A \to X$ is the morphism $A \to X \times_Y A$ with components $a$ and $1_A$. Its composite with the projection to $A$ is $1_A$. Both $1_A$ and the projection satisfy $Q$, so `HasOfPostcompProperty` gives $Q$ for the unit. The triangle identities hold because the forgetful functors are faithful. This is `Over.mapPullbackAdj`. $\square$

With $Q = \top$ the extra conditions on $Q$ are automatic. An instance then makes `Over.map ⊤ hPf` a left adjoint, and `isRightAdjoint_pullback` makes `Over.pullback P ⊤ f` a right adjoint. Dually, `Under.map Q hPf` is precomposition with $f$ and `Under.pushout P Q f` is cobase change. The adjunction `Under.mapPushoutAdj` is `Under.pushout P Q f ⊣ Under.map Q hPf`, under the dual hypotheses with `IsStableUnderCobaseChange` and `HasOfPrecompProperty`.

#### Topologies on `P.Over ⊤ S`

The module `MorphismProperty.CommaSites` is short. Let $K$ be a precoverage on $C$ that contains the isomorphisms and is stable under base change and composition. Assume $K \le$ `P.precoverage`, that is, each member of each $K$-cover satisfies $P$. Then `locallyCoverDense_forget_of_le` says that `Over.forget P ⊤ S` is locally cover dense for the topology `K.toGrothendieck.over S`. The lemma `toGrothendieck_comap_forget_eq_restrictedTopology` identifies the topology generated by the pulled back precoverage `K.comap` with the restricted topology `Functor.restrictedTopology`. Under more hypotheses on $C$ and $P$, the forgetful functor is continuous (`isContinuous_comap_forget`), and the topology is also the induced topology (`toGrothendieck_comap_forget_eq_inducedTopology`). Sites and induced topologies are the subject of Chapter 6.

#### Relatively representable morphisms

Let $F : C \to D$ be a functor. A morphism $f : X \to Y$ of $D$ is *relatively representable* with respect to $F$ when, for each object $a$ of $C$ and each $g : F(a) \to Y$, there is an object $b$ of $C$, a morphism $s : b \to a$ and a morphism $t : F(b) \to X$ such that the square with sides $t$, $F(s)$, $f$, $g$ is a pullback. The class of these morphisms is `Functor.relativelyRepresentable F`, a `MorphismProperty D`. For a presheaf morphism $f : G \to H$ on $C$, `yoneda.relativelyRepresentable f` is the classical condition: each fiber product $G \times_H h_a$ is representable.

For `hf : F.relativelyRepresentable f` and `g : F.obj a ⟶ Y`, the API makes a choice. `hf.pullback g` is the object $b$, `hf.snd g` is $s$, `hf.fst g` is $t$, and `hf.isPullback g` is the pullback square. When $F$ is full and the source of $f$ is $F(c)$, `hf.fst'` is a preimage of `hf.fst` under $F$. The universal property is phrased inside $C$: `lift`, `lift_fst`, `lift_snd` and `hom_ext`, with `Full F` and `Faithful F` as needed. The isomorphism `symmetryIso` compares the two ways to form the same fiber product, and `pullback₃` with `lift₃` gives triple fiber products inside $C$.

**Proposition.** The class `F.relativelyRepresentable` contains the isomorphisms, is closed under composition, and is stable under base change. In Lean these are `of_isIso`, the instance `isMultiplicative`, and the instance `isStableUnderBaseChange`. In particular it respects isomorphisms (`respectsIso`).

*Proof.* If $f$ is an isomorphism, the square with sides $g \circ f^{-1}$, $F(1_a)$, $f$, $g$ is a pullback, because two opposite sides are isomorphisms. For a composite $g' \circ f$ and $h : F(a) \to Z$, pull $g'$ back along $h$ to get $F(b)$, and then pull $f$ back along $F(b) \to Y$. The pasting lemma says that the outer rectangle is a pullback. For base change, let a pullback square exhibit $f'$ as a base change of $f$ along $g$, and let $h : F(a) \to Y'$. Represent the pullback of $f$ along $g \circ h$. The pasting lemma, used in the other direction, makes it a pullback of $f'$ along $h$. $\square$

The lemma `map` shows that $F(f)$ is relatively representable for each $f$ of $C$ when $F$ is full, $C$ has pullbacks and $F$ preserves them. For the Yoneda embedding this says that a morphism of representable presheaves is representable.

A property $P$ of morphisms of $C$ gives a property `P.relative F` of morphisms of $D$. A morphism $f$ satisfies it when $f$ is relatively representable and each represented base change $s : b \to a$ satisfies $P$. The abbreviation `P.presheaf` is `P.relative yoneda`. The projections are `relative.rep` and `relative.property`. When $F$ is fully faithful and $P$ respects isomorphisms, it suffices to check $P$ on one choice of base change (`relative.of_exists` and `relative_of_snd`), because any two choices differ by an isomorphism of $C$.

| Lean name | Statement |
| --- | --- |
| `of_relative_map` | $P$`.relative F (F.map f)` implies $P(f)$ |
| `relative_map` | if $P$ is stable under base change and $F$ is fully faithful and preserves pullbacks, $P(f)$ implies $P$`.relative F (F.map f)` |
| `relative_map_iff` | under these hypotheses, $P$`.relative F (F.map f)` $\leftrightarrow P(f)$ |
| `relative_isStableUnderBaseChange` | `P.relative F` is stable under base change |
| `relative_isStableUnderComposition` | if $F$ is fully faithful and $P$ is closed under composition, so is `P.relative F` |
| `presheaf_monomorphisms_le_monomorphisms` | a morphism in `(monomorphisms C).presheaf` is a monomorphism |

The proof of `of_relative_map` is one line: the square with sides $1$, $F(f)$, $F(f)$, $1$ is a pullback, so $f$ itself is a represented base change of $F(f)$ along the identity. For $P$ inside the monomorphisms, `presheaf_mono_of_le` shows that a morphism $h_X \to G$ in `P.presheaf` is a monomorphism.

The last part of the module is a criterion with the diagonal. Let $C$ have binary products and pullbacks, let $D$ have finite limits, and let $F$ be full and preserve binary products and pullbacks. Then `diag_iff` says that the diagonal $X \to X \times X$ is relatively representable if and only if every morphism $F(a) \to X$ is relatively representable. The two directions are `of_diag` and `diag_of_map_from_obj`. The idea is that the fiber product $F(a) \times_X F(a')$ is the base change of the diagonal of $X$ along $F(a) \times F(a') \to X \times X$, and that $F(a) \times F(a') = F(a \times a')$.

#### Common errors

1. `P.Over Q X` needs `Q.IsMultiplicative` before it is a category. Without this instance the category structure is not found. The usual choice is `Q = ⊤`.
2. `Over.map` takes the proof `hPf : P f`, not the morphism, as its explicit argument, while `Over.pullback` takes `P`, `Q` and the morphism `f` explicitly. The instances `HasPullbacksAlong` and `IsStableUnderBaseChangeAlong` for `f` must be available.
3. `Functor.relativelyRepresentable` is a `Prop`, and `hf.pullback g` is an object chosen from an existence statement. Another pullback square gives an isomorphic object, not an equal one. A statement that must not depend on the choice should use `relative.of_exists` or the square `isPullback`.

### Exercises

1. (A) Show that `P.Over ⊤ X` is equivalent to the poset of subsets of $X$ when $T$ is the category of sets and $P$ is the class of injections.
2. (A) Show that $F(f)$ is relatively representable for each isomorphism $f$ of $C$, without any hypothesis on $F$.
3. (B) Let $P$ be stable under composition and let $f : X \to Y$ satisfy $P$. Show that `Over.map ⊤ hPf` is faithful, and give an example where it is not full.
4. (B) Write the unit and the counit of `Under.pushout P Q f ⊣ Under.map Q hPf`, and say why the counit satisfies $Q$.
5. (B) Let $F$ be fully faithful and let $P$ be closed under composition. Prove that `P.relative F` is closed under composition by pasting two pullback squares.
6. (C) Let $C$ have binary products and pullbacks and let $F : C \to D$ be full and preserve them. Prove that if the diagonal of $X$ is relatively representable, then so is each morphism $F(a) \to X$.

### Reference

<?reference?>
