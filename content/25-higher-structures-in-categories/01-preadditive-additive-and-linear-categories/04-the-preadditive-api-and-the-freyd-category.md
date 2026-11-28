---
title: The preadditive API, its constructions and the Freyd category
kind: api
modules:
  - Mathlib.CategoryTheory.Preadditive.Basic
  - Mathlib.CategoryTheory.Preadditive.Opposite
  - Mathlib.CategoryTheory.Preadditive.FunctorCategory
  - Mathlib.CategoryTheory.Preadditive.Comma
  - Mathlib.CategoryTheory.Preadditive.EndoFunctor
  - Mathlib.CategoryTheory.Preadditive.EilenbergMoore
  - Mathlib.CategoryTheory.Preadditive.SingleObj
  - Mathlib.CategoryTheory.Preadditive.Transfer
  - Mathlib.CategoryTheory.Preadditive.Indization
  - Mathlib.CategoryTheory.Preadditive.CommGrp_
  - Mathlib.CategoryTheory.Preadditive.LiftToFinset
  - Mathlib.CategoryTheory.Preadditive.FreydCategory.Homotopy
  - Mathlib.CategoryTheory.Preadditive.FreydCategory.RightFreyd
explains:
  E2: [CategoryTheory.Preadditive.mono_iff_isZero_kernel, CategoryTheory.Preadditive.isLimitForkOfKernelFork, CategoryTheory.Preadditive.hasZeroObject_of_hasCoproduct, CategoryTheory.Preadditive.ofFullyFaithful, CategoryTheory.Preadditive.commGrpEquivalence, CategoryTheory.Arrow.RightHomotopy, CategoryTheory.Preadditive.RightFreyd, CategoryTheory.Preadditive.RightFreyd.Candidate.isColimitCokernelCofork]
  E1: auto
families: []
requires: [V05, V24.C02, V24.C04, V24.C06, V24.C07, V24.C08]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The preadditive API, its constructions and the Freyd category

### Overview

Volume 24, Chapter 8 defined a preadditive category: each group $\mathrm{Hom}(X, Y)$ is an abelian group, and composition is bilinear. This section goes through the API of the class `Preadditive`: the simp lemmas for sums and negatives under composition, the tests for monomorphisms and epimorphisms by the zero morphism, and the link between equalizers and kernels.

The second part lists the constructions that keep the preadditive structure: the opposite category, functor categories, comma and arrow categories, the categories of algebras and coalgebras, a ring seen as a category with one object, the category of ind-objects, and the transfer along a fully faithful functor. It also proves that in an additive category each object has exactly one structure of commutative group object. The last part treats the right Freyd category of a preadditive category $V$. It is a quotient of the arrow category of $V$ that adds cokernels to $V$ freely.

In the text, $g \circ f$ is the textbook composite, and Mathlib writes `f ≫ g`.

### The library around it

#### The hom groups and composition

The class `CategoryTheory.Preadditive` has the field `homGroup`, an instance `AddCommGroup (X ⟶ Y)`, and the two laws `Preadditive.add_comp` and `Preadditive.comp_add`. The maps of composition with a fixed morphism are group homomorphisms: `Preadditive.leftComp` and `Preadditive.rightComp` fix one side, and `Preadditive.compHom` is the bilinear map $(P \to Q) \to^{+} (Q \to R) \to^{+} (P \to R)$. The instance `Preadditive.preadditiveHasZeroMorphisms` gives the zero morphisms, so that `0 : X ⟶ Y` is the zero of the group.

The simp lemmas move the group operations out of a composite. Each lemma has a twin with the order of the factors changed, and a `_assoc` form for composites of three morphisms.

| Lean name | Statement |
|---|---|
| `Preadditive.sub_comp`, `Preadditive.comp_sub` | $g \circ (f - f') = g \circ f - g \circ f'$ and the twin |
| `Preadditive.neg_comp`, `Preadditive.comp_neg` | $g \circ (-f) = -(g \circ f)$ and the twin |
| `Preadditive.neg_comp_neg` | $(-g) \circ (-f) = g \circ f$ |
| `Preadditive.nsmul_comp`, `Preadditive.zsmul_comp` | $g \circ (n f) = n (g \circ f)$ for $n \in \mathbb{N}$ or $\mathbb{Z}$ |
| `Preadditive.sum_comp`, `Preadditive.comp_sum` | composition distributes over a finite sum $\sum_{j \in s}$ |
| `Preadditive.sum_comp'` | $h \circ \sum_j (g_j \circ f_j) = \sum_j h \circ g_j \circ f_j$ |

The endomorphisms of an object form a ring. The instance `Preadditive.instRingEnd` gives `Ring (End X)`, and `End.addEquiv` is the additive bijection between `End X` and `X ⟶ X`. The lemma `End.sum_asHom` moves a finite sum through this bijection. The group `X ⟶ Y` is a module over `End Y` by `Preadditive.moduleEndRight`, where an endomorphism acts by composition on the target side. A full subcategory and an induced category inherit the structure by the instances `Preadditive.fullSubcategory` and `Preadditive.inducedCategory`, and `InducedCategory.homAddEquiv` is the additive bijection of hom groups.

An isomorphism can be negated, and it can be multiplied by a unit of $\mathbb{Z}$. The instances `Preadditive.instNegIso` and `Preadditive.instSMulUnitsIntIso` give these operations, and `Preadditive.neg_iso_hom` and `Preadditive.smul_iso_hom` compute the forward maps.

#### Monomorphisms, kernels and equalizers

**Theorem (Tests by zero).** In a preadditive category, $f : Q \to R$ is a monomorphism if and only if $f \circ g = 0$ implies $g = 0$ for each $g : P \to Q$. If $f$ has a kernel, then $f$ is a monomorphism if and only if $\ker f$ is a zero object.

*Proof.* If $f$ is a monomorphism and $f \circ g = 0 = f \circ 0$, then $g = 0$. Conversely, if $f \circ g = f \circ h$, then $f \circ (g - h) = 0$ by bilinearity, so $g - h = 0$. For the second statement, let $\iota : K \to Q$ be the kernel. If $f$ is a monomorphism, then $\iota = 0$, so $1_K$ and $0$ both lift $\iota$ and $K$ is zero. If $K$ is zero and $f \circ g = 0$, then $g$ factors through $K$, so $g = 0$. ∎

The first statement is `Preadditive.mono_iff_cancel_zero`, and the second is `Preadditive.mono_iff_isZero_kernel`. The dual statements are `Preadditive.epi_iff_cancel_zero` and `Preadditive.epi_iff_isZero_cokernel`.

**Theorem (Equalizers are kernels).** Let $f, g : X \to Y$. A morphism $e : E \to X$ is an equalizer of $f$ and $g$ if and only if it is a kernel of $f - g$.

*Proof.* The condition $f \circ e = g \circ e$ is the condition $(f - g) \circ e = 0$, by bilinearity. So the forks on $(f, g)$ and the kernel forks on $f - g$ are the same data, and the universal properties agree. ∎

`Preadditive.forkOfKernelFork` and `Preadditive.kernelForkOfFork` convert the cones. `Preadditive.isLimitForkOfKernelFork` and `Preadditive.isLimitKernelForkOfFork` move the limit property. The existence results are `Preadditive.hasEqualizer_of_hasKernel`, `Preadditive.hasKernel_of_hasEqualizer` and `Preadditive.hasEqualizers_of_hasKernels`. The duals include `Preadditive.hasCoequalizers_of_hasCokernels`.

The theorem `Preadditive.hasZeroObject_of_hasCoproduct` says that the empty coproduct is a zero object. The empty coproduct $I$ is initial, so $\mathrm{Hom}(I, I)$ has one element, and $1_I = 0$. An object whose identity is zero is a zero object.

#### Constructions that keep the structure

**Opposites.** The instance `instPreadditiveOpposite` makes `Cᵒᵖ` preadditive with the same groups. The simp lemmas `op_add`, `op_neg`, `op_sub`, `op_zsmul`, `op_sum` and their `unop` versions say that `op` and `unop` are additive, and `opHom` and `unopHom` package them as group homomorphisms. The instances `Functor.op_additive`, `Functor.rightOp_additive`, `Functor.leftOp_additive` and `Functor.unop_additive` show that the opposites of an additive functor are additive.

**Functor categories.** For a preadditive $D$, the instance `functorCategoryPreadditive` makes `C ⥤ D` preadditive, with the operations taken objectwise. The simp lemmas `NatTrans.app_add`, `NatTrans.app_sub` and `NatTrans.app_sum` compute components. `NatTrans.appHom X` is the evaluation at $X$ as a group homomorphism.

**Comma and arrow categories.** Let $L : A \to T$ and $R : B \to T$ be additive functors between preadditive categories. The instance `instPreadditiveComma` makes `Comma L R` preadditive. The sum of two morphisms is the pair of sums, and its square commutes because $L$ and $R$ are additive. The projections are additive by `instAdditiveCommaFst` and `instAdditiveCommaSnd`. The special case $L = R = 1_T$ is `instPreadditiveArrow`, and simp lemmas such as `Arrow.Hom.add_left` compute the components.

**Algebras and coalgebras.** Let $F : C \to C$ be an additive endofunctor. A morphism of $F$-algebras $(X, a) \to (Y, b)$ is a morphism $u$ with $u \circ a = b \circ F(u)$. This condition is linear in $u$ because $F$ is additive. So the algebras form a preadditive category, by `Endofunctor.algebraPreadditive`, and the coalgebras also, by `Endofunctor.coalgebraPreadditive`. The same argument gives `Monad.algebraPreadditive` for the Eilenberg-Moore category of a monad whose functor is additive, and `Comonad.coalgebraPreadditive` for a comonad. The forgetful functors are additive, for example by `Monad.forget_additive`.

**Rings as categories.** For a ring $\alpha$, the category `SingleObj α` has one object, with $\alpha$ as its monoid of endomorphisms. The instance `instPreadditiveSingleObj` makes it preadditive. Composition is multiplication, so bilinearity is the distributive law of $\alpha$.

**Transfer.** Let $F : C \to D$ be fully faithful, with $D$ preadditive. Then $F$ gives a bijection $\mathrm{Hom}(X, Y) \cong \mathrm{Hom}(FX, FY)$, and the group structure on the right moves to the left. This is `Preadditive.ofFullyFaithful`. The lemma `Functor.FullyFaithful.additive_ofFullyFaithful` says that $F$ is additive for this structure.

**Ind-objects.** Let $C$ be a small preadditive category with finite colimits. The instance `instPreadditiveInd` makes `Ind C` preadditive. The proof is a transfer. The category `Ind C` is equivalent to the left exact functors $C^{\mathrm{op}} \to \mathrm{Ab}$, which form a preadditive category, so `Preadditive.ofFullyFaithful` gives the structure on `Ind C`.

**Finite subcoproducts.** A coproduct $\coprod_a f_a$ is the colimit of its finite subcoproducts $\coprod_{a \in S} f_a$. In a preadditive category, `CoproductsFromFiniteFiltered.finiteSubcoproductsCocone_ι_app_eq_sum` writes the leg at $S$ as the finite sum $\sum_{a \in S} \pi_a \circ \iota_a$ of a projection followed by an inclusion.

#### Group objects in an additive category

Let $C$ be preadditive with a cartesian monoidal structure, so that $X \otimes Y$ is the product $X \times Y$. The instance `Preadditive.instGrpObj` makes each object a group object, with the unit $0$, the multiplication $\mathrm{fst} + \mathrm{snd} : X \times X \to X$ and the inverse $-1_X$. The lemmas `Preadditive.one_def` and `Preadditive.mul_def` record these choices. The group is commutative when $C$ is braided. The functor `Preadditive.toCommGrp` sends an object to this group object.

**Theorem (Unique group structure).** The functor `Preadditive.toCommGrp C` is an equivalence $C \simeq \mathrm{CommGrp}(C)$, with the forgetful functor as inverse.

*Proof.* Let $(X, e, m)$ be a monoid object. The product $X \times X$ is a biproduct, with the inclusions $i_1 = (1, 0)$ and $i_2 = (0, 1)$. So $m$ is fixed by $m \circ i_1$ and $m \circ i_2$, and $m = (m \circ i_1) \circ \mathrm{fst} + (m \circ i_2) \circ \mathrm{snd}$. The unit laws, with $e = 0$ because the unit object is terminal and hence zero, give $m \circ i_1 = 1_X$ and $m \circ i_2 = 1_X$. Thus $m = \mathrm{fst} + \mathrm{snd}$, and each group object is the one of `Preadditive.toCommGrp`. Each morphism respects these multiplications by bilinearity. ∎

This is `Preadditive.commGrpEquivalence`. The additive structure of $C$ becomes the multiplicative structure of the group objects, which is the reason for the names `mul_def` and `one_def`.

#### Homotopies of arrows

Let $V$ be preadditive, and let $u : u_0 \to u_1$ and $v : v_0 \to v_1$ be objects of `Arrow V`. A morphism $f : u \to v$ is a commutative square with components $f_0 : u_0 \to v_0$ and $f_1 : u_1 \to v_1$. For two such morphisms $f, g$:

1. a *left homotopy* `Arrow.LeftHomotopy f g` is a morphism $h : u_1 \to v_0$ with $f_0 - g_0 = h \circ u$;
2. a *right homotopy* `Arrow.RightHomotopy f g` is a morphism $h : u_1 \to v_0$ with $f_1 - g_1 = v \circ h$.

The field `hom` holds $h$, and the field `comm` holds the equation. For a right homotopy, think of an arrow $v$ as a presentation of the object $\mathrm{coker}(v)$. Two morphisms of cokernels induced by $f_1$ and $g_1$ are equal exactly when $f_1 - g_1$ factors through $v$.

The two relations are congruences. The constructors `LeftHomotopy.refl`, `LeftHomotopy.symm` and `LeftHomotopy.trans` take $h = 0$, $-h$ and $h + k$, and `LeftHomotopy.comp` composes a homotopy with a morphism. The namespace `Arrow.RightHomotopy` has the same constructors. The relations themselves are `Arrow.leftHomotopic` and `Arrow.rightHomotopic`, and the instances `Arrow.leftHomotopy_congruence` and `Arrow.rightHomotopy_congruence` say that they are congruences.

#### The right Freyd category

The right Freyd category `Preadditive.RightFreyd V` is the quotient of `Arrow V` by the right homotopy relation. The instance `Preadditive.instRightFreyd` makes it preadditive, because the sum of two right homotopies is a right homotopy. The quotient functor `Preadditive.RightFreyd.quotient V` is full, essentially surjective and additive. The lemma `RightFreyd.quotient_map_eq_iff` says that two morphisms have the same image if and only if a right homotopy exists between them, and `RightFreyd.homotopyOfEq` chooses one.

If $V$ has a zero object, `RightFreyd.rightFunctor V` sends $X$ to the arrow $0 \to X$, and the composite `RightFreyd.functor V` with the quotient is full, faithful and additive. It is faithful because a right homotopy between two morphisms $(0 \to X) \to (0 \to Y)$ gives $f_1 - g_1 = 0 \circ h = 0$.

**Theorem (Cokernels in the Freyd category).** Let $V$ have binary biproducts, and let $f : u \to v$ be a morphism of `Arrow V`. Let $c(f)$ be the arrow $(v, f_1) : v_0 \oplus u_1 \to v_1$, and let $\pi : v \to c(f)$ be the square with components $\iota_1 : v_0 \to v_0 \oplus u_1$ and $1 : v_1 \to v_1$. Then the image of $\pi$ in the right Freyd category is a cokernel of the image of $f$. So `RightFreyd V` has cokernels.

*Proof.* First, $\pi \circ f$ is right homotopic to $0$. Its second component is $f_1$, and the morphism $h = \iota_2 : u_1 \to v_0 \oplus u_1$ gives $(v, f_1) \circ \iota_2 = f_1$. Next, let $g : v \to w$ with a right homotopy $k$ from $g \circ f$ to $0$, so $g_1 \circ f_1 = w \circ k$. Define $d : c(f) \to w$ with components $(g_0, k) : v_0 \oplus u_1 \to w_0$ and $g_1$. The square commutes by the square of $g$ and the equation of $k$. By construction $d \circ \pi = g$. Last, the image of $\pi$ is an epimorphism, because its second component is the identity. So the factorization is unique in the quotient. ∎

The objects of the proof are `Preadditive.RightFreyd.Candidate.cokernel` and `Preadditive.RightFreyd.Candidate.desc`, the colimit property of the cofork is `RightFreyd.Candidate.isColimitCokernelCofork`, and the instance `RightFreyd.instHasCokernels` collects them. The left homotopies are the dual tool, for a left Freyd category with kernels, which the library does not define.

#### Common errors

1. `Preadditive.ofFullyFaithful` is a definition, not an instance. If the category already has a preadditive instance, a second structure from this definition gives two different instances, and the lemmas of one do not apply to the other. Use it only through `letI` on a category with no structure, as the file on ind-objects does.
2. In `Arrow.RightHomotopy f g`, the field `hom` goes from the target of the source arrow to the source of the target arrow, $u_1 \to v_0$, and the equation is on the second components. The left homotopy uses the same type of `hom` and puts the equation on the first components. Check the field `comm` before a proof.
3. The preadditive instance on `Comma L R` needs `L.Additive` and `R.Additive`, and the one on `Monad.Algebra T` needs `(T : C ⥤ C).Additive`. Without these instances in the context, the search fails with no clear message.

### Exercises

1. (A) Prove `Preadditive.epi_iff_cancel_zero` from the dual argument of the theorem on tests by zero, and say where bilinearity enters.
2. (A) Let $\alpha$ and $\beta$ be rings. Show that an additive functor `SingleObj α ⥤ SingleObj β` is the same as a ring homomorphism $\alpha \to \beta$. Say which axiom of a functor gives $1 \mapsto 1$.
3. (B) Let $V$ be preadditive with a zero object. Show that an arrow $u : u_0 \to u_1$ is isomorphic in `RightFreyd V` to `(RightFreyd.functor V).obj u₁` when $u$ is zero. Then show that any arrow with $u_1 = 0$ gives a zero object of `RightFreyd V`.
4. (B) In the theorem on group objects, the proof used that the unit object of a cartesian monoidal category is zero. Prove that a terminal object of a preadditive category is a zero object.
5. (A) Let $F : C \to C$ be additive. Show that the forgetful functor from $F$-algebras to $C$ reflects isomorphisms. Then use the preadditive structure to show that an algebra $(X, a)$ is a zero object if $X$ is a zero object of $C$.
6. (C) Let $V$ be the category of finitely generated free modules over a ring $R$. Show that `RightFreyd V` is equivalent to the category of finitely presented $R$-modules. *Hint:* send an arrow to its cokernel, and use the description of right homotopies by factorization through $v$.

### Reference

<?reference?>
