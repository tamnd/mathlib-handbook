---
title: Idempotent completion of functor categories and complexes
kind: api
modules:
  - Mathlib.CategoryTheory.Idempotents.Biproducts
  - Mathlib.CategoryTheory.Idempotents.FunctorCategories
  - Mathlib.CategoryTheory.Idempotents.FunctorExtension
  - Mathlib.CategoryTheory.Idempotents.HomologicalComplex
  - Mathlib.CategoryTheory.Idempotents.SimplicialObject
explains:
  E2: [CategoryTheory.Idempotents.Karoubi.decomposition, CategoryTheory.Idempotents.Karoubi.karoubi_hasFiniteBiproducts, CategoryTheory.Idempotents.functor_category_isIdempotentComplete, CategoryTheory.Idempotents.karoubiFunctorCategoryEmbedding, CategoryTheory.Idempotents.natTrans_eq, CategoryTheory.Idempotents.karoubiUniversal₁, CategoryTheory.Idempotents.karoubiUniversal₂, CategoryTheory.Idempotents.karoubiHomologicalComplexEquivalence, CategoryTheory.Idempotents.instIsIdempotentCompleteHomologicalComplex]
  E1: auto
families: []
requires: [V24.C01, V24.C02, V24.C03, V24.C08]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Idempotent completion of functor categories and complexes

### Overview

Section 2 built the Karoubi envelope $\mathrm{Kar}(C)$ of a category $C$. Its objects are pairs $(X, p)$ with $p$ an idempotent of $X$, and a morphism $(X, p) \to (Y, q)$ is a morphism $f : X \to Y$ with $q \circ f \circ p = f$. Section 2 proved that $\mathrm{Kar}(C)$ is idempotent complete and that $\iota : C \to \mathrm{Kar}(C)$ is an equivalence when $C$ is idempotent complete. This section collects the modules that make the envelope a working tool. They answer four questions. Does $\mathrm{Kar}(C)$ keep the biproducts of $C$? Is a category of functors idempotent complete when its target is? How does a functor extend from $C$ to $\mathrm{Kar}(C)$? How does the envelope interact with chain complexes and simplicial objects?

The answers are positive, and the proofs are short. Each one comes from one principle: an idempotent of a functor or of a complex is a family of idempotents, one at each object or in each degree, and these idempotents commute with the structure maps. So the splitting can be done one component at a time. The results are the base of the Dold-Kan correspondence in Volume 27, which is first proved for the Karoubi envelopes and then transported to the categories themselves.

In the text $g \circ f$ is the textbook composite, and Mathlib writes `f ≫ g`. For `P : Karoubi C` the underlying object is `P.X` and the idempotent is `P.p`. For a morphism `f : P ⟶ Q` the underlying morphism of $C$ is `f.f`.

### The library around it

#### Biproducts in the envelope

The module `Mathlib.CategoryTheory.Idempotents.Biproducts` works in a preadditive category $C$. The definition `Karoubi.complement P` is the object $(X, 1 - p)$ for $P = (X, p)$. The lemma `idem_of_id_sub_idem` of Section 2 shows that $1 - p$ is idempotent, and the simp lemmas `Karoubi.complement_X` and `Karoubi.complement_p` give the two fields.

**Proposition.** For each $P = (X, p)$ in $\mathrm{Kar}(C)$ there is an isomorphism $P \oplus \bar P \cong \iota X$, where $\bar P$ is the complement. This is `Karoubi.decomposition`.

*Proof sketch.* The morphism $p$ is a morphism $i_P : P \to \iota X$ and a morphism $e_P : \iota X \to P$. In Mathlib these are `Karoubi.decompId_i` and `Karoubi.decompId_p`. In the same way $1 - p$ gives $i_{\bar P}$ and $e_{\bar P}$. In $C$ the four composites are $e_P i_P = p^2 = p$, which is the identity of $P$, $e_{\bar P} i_{\bar P} = 1 - p$, the identity of $\bar P$, and $e_{\bar P} i_P = (1 - p) p = 0 = p (1 - p) = e_P i_{\bar P}$. Finally $i_P e_P + i_{\bar P} e_{\bar P} = p + (1 - p) = 1_X$. These are the equations of a biproduct bicone from Section 1, so $\iota X$ is a biproduct of $P$ and $\bar P$. $\square$

The instance `Karoubi.instHasBinaryBiproductComplement` records that this biproduct exists, even if $C$ has no biproducts. When $C$ has finite biproducts, the instance `Karoubi.karoubi_hasFiniteBiproducts` gives finite biproducts in $\mathrm{Kar}(C)$. The bicone is `Karoubi.Biproducts.bicone`. For a finite family $P_j = (X_j, p_j)$, its point is $\bigl(\bigoplus_j X_j, \bigoplus_j p_j\bigr)$, with the diagonal matrix of the $p_j$ as idempotent. Its inclusions and projections are the biproduct maps of $C$ composed with the $p_j$. Hence the Karoubi envelope of an additive category is additive, and it is the idempotent complete additive envelope when it is applied to `Mat_ C` of Section 1.

#### Functor categories

The module `Mathlib.CategoryTheory.Idempotents.FunctorCategories` treats $\mathrm{Kar}(\mathrm{Fun}(J, C))$. An object is a functor $F : J \to C$ with an idempotent natural transformation $p : F \to F$. The simp lemmas evaluate the Karoubi equations at an object $j$ of $J$.

| Lean name | Statement |
|---|---|
| `Idempotents.app_idem` | $p_j \circ p_j = p_j$ |
| `Idempotents.app_p_comp` | $f_j \circ p_j = f_j$ for a morphism $f : (F, p) \to (G, q)$ |
| `Idempotents.app_comp_p` | $q_j \circ f_j = f_j$ |
| `Idempotents.app_p_comm` | $f_j \circ p_j = q_j \circ f_j$ |

Each lemma has an `_assoc` form for rewriting inside a longer composite. The first three are simp lemmas, and `app_p_comm` is not, because it has no preferred direction.

**Theorem.** If $C$ is idempotent complete, then $\mathrm{Fun}(J, C)$ is idempotent complete. This is the instance `functor_category_isIdempotentComplete`.

*Proof sketch.* Let $p : F \to F$ be idempotent. For each $j$ choose a splitting $p_j = i_j \circ e_j$ in $C$, with $e_j \circ i_j = 1_{Y_j}$. For $\varphi : j \to j'$ put $Y(\varphi) = e_{j'} \circ F(\varphi) \circ i_j$. Then $Y$ is a functor. For composable $\varphi$ and $\psi$, the composite $Y(\psi) Y(\varphi)$ is $e F(\psi) p_{j'} F(\varphi) i$, and naturality of $p$ turns it into $e\, p\, F(\psi \varphi)\, i = e F(\psi\varphi) i$, since $e_{j''} p_{j''} = e_{j''}$. The families $i$ and $e$ are natural by a similar computation, and they split $p$. Mathlib takes the splittings from equalizers of $1$ and $p_j$, by the criterion `isIdempotentComplete_iff_hasEqualizer_of_id_and_idempotent` of Section 2. $\square$

For an arbitrary $C$ the module also gives the functor `karoubiFunctorCategoryEmbedding J C` from $\mathrm{Kar}(\mathrm{Fun}(J, C))$ to $\mathrm{Fun}(J, \mathrm{Kar}(C))$. It sends $(F, p)$ to the functor $j \mapsto (F j, p_j)$, and it is full and faithful by the instances `instFullKaroubiFunctorKaroubiFunctorCategoryEmbedding` and `instFaithfulKaroubiFunctorKaroubiFunctorCategoryEmbedding`. The theorem `toKaroubi_comp_karoubiFunctorCategoryEmbedding` says that $\iota$ followed by this embedding is the functor of composition with $\iota : C \to \mathrm{Kar}(C)$.

#### Extension of functors

The module `Mathlib.CategoryTheory.Idempotents.FunctorExtension` gives the universal property of the envelope. Its first result says that a natural transformation out of $\mathrm{Kar}(C)$ is fixed by its values on the objects $\iota X$.

**Lemma.** Let $F, G : \mathrm{Kar}(C) \to D$ and $\varphi : F \to G$. For $P = (X, p)$, $\varphi_P = G(e_P) \circ \varphi_{\iota X} \circ F(i_P)$. This is `natTrans_eq`.

*Proof.* By `Karoubi.decompId`, the identity of $P$ is $e_P \circ i_P$. Naturality of $\varphi$ for $e_P$ gives $\varphi_P \circ F(e_P) = G(e_P) \circ \varphi_{\iota X}$. Compose with $F(i_P)$ on the right and use $F(e_P) F(i_P) = F(1_P) = 1$. $\square$

There are three extension functors, and the names follow the source and target of the input.

| Lean name | Statement |
|---|---|
| `functorExtension₁ C D` | the functor $\mathrm{Fun}(C, \mathrm{Kar}(D)) \to \mathrm{Fun}(\mathrm{Kar}(C), \mathrm{Kar}(D))$ |
| `karoubiUniversal₁ C D` | the equivalence $\mathrm{Fun}(C, \mathrm{Kar}(D)) \simeq \mathrm{Fun}(\mathrm{Kar}(C), \mathrm{Kar}(D))$ |
| `functorExtension₂ C D` | the functor $\mathrm{Fun}(C, D) \to \mathrm{Fun}(\mathrm{Kar}(C), \mathrm{Kar}(D))$ |
| `karoubiUniversal₂ C D` | the equivalence $\mathrm{Fun}(C, D) \simeq \mathrm{Fun}(\mathrm{Kar}(C), \mathrm{Kar}(D))$, for $D$ idempotent complete |
| `functorExtension C D` | the functor $\mathrm{Fun}(C, D) \to \mathrm{Fun}(\mathrm{Kar}(C), D)$, for $D$ idempotent complete |
| `karoubiUniversal C D` | the equivalence $\mathrm{Fun}(C, D) \simeq \mathrm{Fun}(\mathrm{Kar}(C), D)$, from Section 2 |

The formula of the first extension is simple. For $F : C \to \mathrm{Kar}(D)$ and $P = (X, p)$, the object $F_1(P)$ has underlying object $(F X).X$ and idempotent $F(p).f$. These are the simp lemmas `FunctorExtension₁.obj_obj_X` and `FunctorExtension₁.obj_obj_p`. The second extension composes a functor $C \to D$ with $\iota_D$ and then applies the first. The unit and counit of `karoubiUniversal₁` are `functorExtension₁CompWhiskeringLeftToKaroubiIso` and `KaroubiUniversal₁.counitIso`. The isomorphism `functorExtension₁Comp` compares the extension of a composite with the composite of the extensions. The theorems `karoubiUniversal₂_functor_eq` and `karoubiUniversal_functor_eq` identify the functors of the equivalences, and instances record that `functorExtension₂ C D` and `functorExtension C D` are equivalences.

One result needs no completeness. The definition `whiskeringLeftObjToKaroubiFullyFaithful` says that composition with $\iota$, from $\mathrm{Fun}(\mathrm{Kar}(C), D)$ to $\mathrm{Fun}(C, D)$, is full and faithful for every $D$. The preimage of $\tau$ is given by the formula of `natTrans_eq`, and `whiskeringLeft_obj_preimage_app` states this formula in the idempotent complete case.

#### Chain complexes

The module `Mathlib.CategoryTheory.Idempotents.HomologicalComplex` works with a preadditive category $C$ and a complex shape $c$. An object of $\mathrm{Kar}(\mathrm{Ch}_c(C))$ is a complex $K$ with an idempotent chain map $p$. Its components $p_n$ are idempotents of $K_n$, and they commute with the differentials. The simp lemmas mirror those of functor categories: `Karoubi.HomologicalComplex.p_idem`, `Karoubi.HomologicalComplex.p_comp_d` and `Karoubi.HomologicalComplex.comp_p_d`, with the commutation `Karoubi.HomologicalComplex.p_comm_f`.

**Theorem.** There is an equivalence $\mathrm{Kar}(\mathrm{Ch}_c(C)) \simeq \mathrm{Ch}_c(\mathrm{Kar}(C))$. This is `karoubiHomologicalComplexEquivalence C c`.

*Proof sketch.* The functor sends $(K, p)$ to the complex with terms $(K_n, p_n)$ and differentials $d \circ p = p \circ d$. These are morphisms of $\mathrm{Kar}(C)$ because $p\, (d p)\, p = d p$. In the other direction, a complex of objects $(X_n, q_n)$ with differentials $d_n$ is a complex of $C$ with the same terms and differentials. The square $d \circ d = 0$ holds in $C$, because the zero morphism of $\mathrm{Kar}(C)$ is the zero of $C$. The family $q_n$ is a chain map, because $q\, d = d = d\, q$ for a morphism of $\mathrm{Kar}(C)$. So it is an idempotent of this complex. The two composites are the identity up to the obvious isomorphisms, and these are `KaroubiHomologicalComplexEquivalence.unitIso` and `KaroubiHomologicalComplexEquivalence.counitIso`. $\square$

The special cases `karoubiChainComplexEquivalence C α` and `karoubiCochainComplexEquivalence C α` use the shapes `ComplexShape.down α` and `ComplexShape.up α`. The instance `instIsIdempotentCompleteHomologicalComplex` says that $\mathrm{Ch}_c(C)$ is idempotent complete when $C$ is. Its proof is a chain of equivalences. The equivalence `toKaroubiEquivalence C` gives $\mathrm{Ch}_c(C) \simeq \mathrm{Ch}_c(\mathrm{Kar}(C))$, the theorem gives $\mathrm{Ch}_c(\mathrm{Kar}(C)) \simeq \mathrm{Kar}(\mathrm{Ch}_c(C))$, and the last category is idempotent complete. The lemma `isIdempotentComplete_iff_of_equivalence` transports the property.

#### Simplicial objects

The module `Mathlib.CategoryTheory.Idempotents.SimplicialObject` holds two instances. If $C$ is idempotent complete, then `SimplicialObject C` and `CosimplicialObject C` are idempotent complete. Both are functor categories, from $\Delta^{\mathrm{op}}$ and from $\Delta$, so the instances follow from `functor_category_isIdempotentComplete`. The Dold-Kan correspondence uses them. The equivalence `Preadditive.DoldKan.equivalence` is between the Karoubi envelopes of `SimplicialObject C` and `ChainComplex C ℕ`, and `Idempotents.DoldKan.equivalence` removes the envelopes when $C$ is idempotent complete, by the instances of this section.

#### Common errors

1. The embedding `karoubiFunctorCategoryEmbedding J C` is full and faithful, but it is not an equivalence in general. A functor $J \to \mathrm{Kar}(C)$ sends $\varphi$ to a morphism $f$ with $q f p = f$, and $f$ need not come from a functor $J \to C$. Only for an idempotent complete $C$ are both sides equivalent to $\mathrm{Fun}(J, C)$.
2. The three extension functors differ in their input. `functorExtension₁` takes functors into `Karoubi D`, `functorExtension₂` takes functors into `D` and returns functors into `Karoubi D`, and `functorExtension` returns functors into `D` and needs `IsIdempotentComplete D`.
3. A morphism of `Karoubi (HomologicalComplex C c)` has two layers. For `f : P ⟶ Q`, the chain map is `f.f`, and its component in degree `n` is `f.f.f n`. The idempotent in degree `n` is `P.p.f n`.

### Exercises

1. (A) Let $P = (X, p)$ in $\mathrm{Kar}(C)$ for a preadditive $C$. Show that the complement of the complement of $P$ is equal to $P$.
2. (A) Let $k$ be a field and $C$ the category with one object whose endomorphism ring is $k \times k$. Write the decomposition of $\iota X$ given by `Karoubi.decomposition` for the idempotent $(1, 0)$.
3. (B) Prove that the functor $j \mapsto (F j, p_j)$ is full: a natural transformation between two such functors is a morphism of $\mathrm{Kar}(\mathrm{Fun}(J, C))$.
4. (B) Let $D$ be idempotent complete. Show that a functor $\mathrm{Kar}(C) \to D$ is determined up to isomorphism by its composite with $\iota$, using `natTrans_eq`.
5. (B) Let $C$ be preadditive and let $c$ be a complex shape. Show that a complex $K$ in $C$ with an idempotent chain map $p$ gives a complex in $\mathrm{Kar}(C)$ whose differentials are $d \circ p$.
6. (C) Let $C$ be the category of free modules of finite rank over $\mathbb{Z} \times \mathbb{Z}$. Describe $\mathrm{Ch}(\mathrm{Kar}(C))$ as a category of complexes of projective modules, and show that $\mathrm{Ch}(C)$ is not idempotent complete.

### Reference

<?reference?>
