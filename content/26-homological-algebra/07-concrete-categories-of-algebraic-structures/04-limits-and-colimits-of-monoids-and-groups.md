---
title: Limits and colimits of monoids and groups
kind: api
modules:
  - Mathlib.Algebra.Category.MonCat.Limits
  - Mathlib.Algebra.Category.MonCat.Colimits
  - Mathlib.Algebra.Category.MonCat.FilteredColimits
  - Mathlib.Algebra.Category.Grp.Limits
  - Mathlib.Algebra.Category.Grp.Colimits
  - Mathlib.Algebra.Category.Grp.FilteredColimits
  - Mathlib.Algebra.Category.Grp.LargeColimits
  - Mathlib.Algebra.Category.Grp.Kernels
  - Mathlib.Algebra.Category.Grp.Images
  - Mathlib.Algebra.Category.Grp.CartesianMonoidal
  - Mathlib.Algebra.Category.Grp.Subobject
explains:
  E2: [MonCat.HasLimits.limitConeIsLimit, GrpCat.limitConeIsLimit, GrpCat.hasLimit_iff_small_sections, MonCat.FilteredColimits.colimit_mul_mk_eq, MonCat.FilteredColimits.colimitCoconeIsColimit, AddCommGrpCat.Colimits.colimitCoconeIsColimit, AddCommGrpCat.hasColimit_iff_small_quot, AddCommGrpCat.cokernelIsoQuotient]
  E1: auto
families: []
requires: [V24.C04, V24.C07, V05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Limits and colimits of monoids and groups

### Overview

Section 1 of this chapter proves that limits of rings are computed on the underlying sets. The same argument works for monoids, commutative monoids, groups and commutative groups. This section describes the files that carry it out for these categories, and the files that build colimits. The colimits are of two kinds. A filtered colimit of monoids or groups is computed on the underlying sets, so the forgetful functor preserves it. A general colimit is a quotient of a free object, and it is much larger than the colimit of the sets.

The section also treats the concrete kernels, cokernels and images of abelian groups, the chosen binary products that make `GrpCat` a cartesian monoidal category, and the fact that `AddCommGrpCat` is well powered. These are the facts that the abelian structure of Section 1 rests on in practice: they identify the abstract kernel and cokernel with the subgroup and the quotient group of the textbook.

### The library around it

#### Limits of monoids and groups

Let $J$ be a category and $F \colon J \to \mathbf{Mon}$ a functor. The sections of $F$ are the families $(x_j)_j \in \prod_j F(j)$ with $F(u)(x_j) = x_{j'}$ for each arrow $u \colon j \to j'$. They form a submonoid `MonCat.sectionsSubmonoid F` of the product, because each $F(u)$ preserves $1$ and products. The limit cone `MonCat.HasLimits.limitCone F` has this submonoid as its point and the projections `MonCat.limitπMonoidHom` as its legs. The proof `MonCat.HasLimits.limitConeIsLimit` is the proof of Section 1: a cone $(M, \lambda_j)$ gives the map $m \mapsto (\lambda_j(m))_j$, which lands in the sections and is the unique factorization.

For groups the sections also contain inverses, because $F(u)(x_j^{-1}) = x_{j'}^{-1}$. This gives `GrpCat.sectionsSubgroup F`, the cone `GrpCat.limitCone` and the proof `GrpCat.limitConeIsLimit`. The commutative versions are `CommMonCat.limitCone`, `CommMonCat.limitConeIsLimit`, `CommGrpCat.limitCone` and `CommGrpCat.limitConeIsLimit`. Each name has an additive twin made by the additive translation of the library, such as `AddMonCat.hasLimitsOfSize` and `AddCommGrpCat.hasLimits`.

The files state the result as a family of instances with a fixed naming pattern. The table shows them for `GrpCat`; the names for `MonCat`, `CommMonCat` and `CommGrpCat` follow the same pattern.

| Lean name | Statement |
|---|---|
| `GrpCat.hasLimits` | `GrpCat` has all small limits |
| `GrpCat.hasLimitsOfSize` | limits indexed by categories in a universe $v$ with $v \le u$ |
| `GrpCat.forget_preservesLimits` | the forgetful functor to types preserves limits |
| `GrpCat.forget_createsLimitsOfShape` | the forgetful functor creates limits of each shape |
| `GrpCat.forget₂Mon_preservesLimits` | the functor to `MonCat` preserves limits |
| `CommGrpCat.forget₂Group_preservesLimits` | the functor to `GrpCat` preserves limits |
| `CommGrpCat.forget₂CommMon_preservesLimitsOfSize` | the functor to `CommMonCat` preserves limits |

A functor that creates limits lifts each limit cone downstairs to a unique limit cone upstairs. So the instance `GrpCat.forget_createsLimitsOfSize` contains both the existence of limits and the fact that the underlying set of a limit is the limit of the sets.

The size of the index category matters. If $J$ lives in a larger universe than the groups, the product $\prod_j F(j)$ can be too large to be a group in the universe of `GrpCat`. The theorem `GrpCat.hasLimit_iff_small_sections` gives the exact condition: $F$ has a limit if and only if the type of sections of the underlying functor is small. The direction from right to left is the construction above, done in a smaller copy of the sections. The direction from left to right follows because the forgetful functor preserves the limit, and the point of a limit in `GrpCat` is a small type. `CommGrpCat.hasLimit_iff_small_sections` is the commutative case.

#### Filtered colimits

A category $J$ is filtered if each finite diagram in $J$ has a cocone. The colimit of a functor $G \colon J \to \mathbf{Set}$ with $J$ filtered has a simple form: it is the disjoint union $\bigsqcup_j G(j)$ modulo the relation $(j, x) \sim (j', x')$ when $x$ and $x'$ have the same image in some $G(k)$. The file `Mathlib.Algebra.Category.MonCat.FilteredColimits` puts a monoid structure on this quotient. The type is `MonCat.FilteredColimits.M F`, and `MonCat.FilteredColimits.M.mk F ⟨j, x⟩` is the class of $x \in F(j)$.

To multiply the classes of $x \in F(j_1)$ and $y \in F(j_2)$, choose an object $k$ and arrows $f \colon j_1 \to k$ and $g \colon j_2 \to k$, and put
$$[x] \cdot [y] = [F(f)(x) \cdot F(g)(y)].$$
This is `MonCat.FilteredColimits.colimit_mul_mk_eq`. The value does not depend on the choice. Proof: two choices $(k, f, g)$ and $(k', f', g')$ have a common refinement, because $J$ is filtered: there is an object $s$ and arrows $\alpha \colon k \to s$, $\beta \colon k' \to s$ with $\alpha f = \beta f'$ and $\alpha g = \beta g'$. Each $F(\alpha)$ is a homomorphism, so both products have the same image $F(\alpha f)(x) \cdot F(\alpha g)(y)$ in $F(s)$. The library uses the lemma `CategoryTheory.IsFiltered.bowtie` for this step. The unit is the class of $1$ in any $F(j)$, by `MonCat.FilteredColimits.colimit_one_eq`. The monoid axioms hold because any three classes have representatives in one $F(k)$.

The cocone is `MonCat.FilteredColimits.colimitCocone`, and `MonCat.FilteredColimits.colimitCoconeIsColimit` proves the universal property. Its underlying cocone of sets is the colimit cocone of sets, so the instance `MonCat.FilteredColimits.forget_preservesFilteredColimits` follows. For groups the file `Mathlib.Algebra.Category.Grp.FilteredColimits` adds the inverse $[x]^{-1} = [x^{-1}]$, by `GrpCat.FilteredColimits.colimit_inv_mk_eq`, and proves `GrpCat.FilteredColimits.forget_preservesFilteredColimits`. There are versions for `CommMonCat` and `CommGrpCat`, such as `CommGrpCat.FilteredColimits.forget₂Group_preservesFilteredColimits`.

#### General colimits of monoids

A coproduct of two groups is their free product, which is not a quotient of the disjoint union. So general colimits need another construction. The file `Mathlib.Algebra.Category.MonCat.Colimits` builds the colimit of $F \colon J \to \mathbf{Mon}$ from the syntax of monoids. The inductive type `MonCat.Colimits.Prequotient F` has the constructors `MonCat.Colimits.Prequotient.of`, `MonCat.Colimits.Prequotient.one` and `MonCat.Colimits.Prequotient.mul`: its terms are formal words built from the elements of all the $F(j)$. The relation `MonCat.Colimits.Relation F` identifies two words by the monoid laws (the constructors `MonCat.Colimits.Relation.mul_assoc`, `MonCat.Colimits.Relation.one_mul` and `MonCat.Colimits.Relation.mul_one`), by the compatibility with the operations of each $F(j)$, and by the constructor `MonCat.Colimits.Relation.map`, which identifies $x \in F(j)$ with $F(u)(x) \in F(j')$. The quotient is `MonCat.Colimits.ColimitType F`, with the monoid structure `MonCat.Colimits.monoidColimitType`. The lemmas `MonCat.Colimits.quot_mul` and `MonCat.Colimits.quot_one` compute its operations on classes. The cocone is `MonCat.Colimits.colimitCocone`, and `MonCat.Colimits.colimitIsColimit` gives the universal property. The instance `MonCat.Colimits.hasColimits_monCat` records that `MonCat` has all small colimits.

#### Colimits of abelian groups

For abelian groups there is a smaller model. Let $F \colon J \to \mathbf{Ab}$. The direct sum $\bigoplus_j F(j)$ is the group of finitely supported families, and `AddCommGrpCat.Colimits.Relations F` is its subgroup generated by the elements $\iota_{j'}(F(u)(x)) - \iota_j(x)$. The quotient is
$$\operatorname{Quot}(F) = \Big(\bigoplus_{j} F(j)\Big) \Big/ \big\langle \iota_{j'}(F(u)\,x) - \iota_j(x) \big\rangle,$$
which is `AddCommGrpCat.Colimits.Quot F`. The map `AddCommGrpCat.Colimits.Quot.ι F j` sends $x$ to the class of $\iota_j(x)$. For any cocone $c$, the map `AddCommGrpCat.Colimits.Quot.desc F c` sends the class of $\sum_j \iota_j(x_j)$ to $\sum_j c_j(x_j)$. It is well defined because each $c_{j'} \circ F(u) = c_j$ kills the generators of the relations. This gives the cocone `AddCommGrpCat.Colimits.colimitCocone` and its proof `AddCommGrpCat.Colimits.colimitCoconeIsColimit`. The general form `AddCommGrpCat.Colimits.isColimit_of_bijective_desc` says that a cocone $c$ is a colimit when `Quot.desc F c` is bijective.

The quotient $\operatorname{Quot}(F)$ lives in the universe of $J$ and of the groups together. So the existence of the colimit in `AddCommGrpCat` at universe $w$ is a question of size. `AddCommGrpCat.hasColimit_of_small_quot` gives the colimit when $\operatorname{Quot}(F)$ is $w$-small. The file `Mathlib.Algebra.Category.Grp.LargeColimits` proves the converse, so that `AddCommGrpCat.hasColimit_iff_small_quot` is an equivalence, and `AddCommGrpCat.isColimit_iff_bijective_desc` characterizes all colimit cocones. The instance `AddCommGrpCat.hasColimitsOfSize` covers each $J$ in a universe below that of the groups.

A cokernel is the colimit of the pair $(f, 0)$, so the construction gives $\operatorname{coker} f \cong H / f(G)$. This is `AddCommGrpCat.cokernelIsoQuotient`. Proof: the arrow $0$ gives the relation $\iota_G(g) = \iota_H(0) = 0$, and the arrow $f$ gives the relation $\iota_G(g) = \iota_H(f(g))$. So the quotient is $(G \oplus H)/(G \oplus f(G)) \cong H/f(G)$.

#### Kernels, cokernels and images of abelian groups

The file `Mathlib.Algebra.Category.Grp.Kernels` gives the concrete kernel and cokernel as limit and colimit cones. `AddCommGrpCat.kernelCone f` is the fork on the subgroup $\ker f$, and `AddCommGrpCat.kernelIsLimit` proves that it is a kernel. `AddCommGrpCat.cokernelCocone f` is the cofork on $H/f(G)$, and `AddCommGrpCat.cokernelIsColimit` proves that it is a cokernel. The file `Mathlib.Algebra.Category.Grp.Images` factors $f$ through its range: `AddCommGrpCat.image f` is the range, `AddCommGrpCat.factorThruImage` and `AddCommGrpCat.image.ι` are the two factors, and `AddCommGrpCat.isImage` proves the universal property. `AddCommGrpCat.imageIsoRange` identifies the abstract image `image f` with the range. The file `Mathlib.Algebra.Category.Grp.Subobject` proves the instance `AddCommGrpCat.wellPowered_addCommGrp`: the subobjects of an abelian group form a small type, because they correspond to subgroups.

#### Chosen products

The file `Mathlib.Algebra.Category.Grp.CartesianMonoidal` makes `GrpCat` a cartesian monoidal category, with the product $G \times H$ as chosen product. The cone is `GrpCat.binaryProductLimitCone`, the instance is `GrpCat.cartesianMonoidalCategoryGrp`, and `GrpCat.tensorObj_eq` states that $G \otimes H$ is the group $G \times H$. The forgetful functor to types is braided monoidal, by `GrpCat.instBraidedForgetMonoidHomCarrier`, and `GrpCat.μ_forget_apply` states that its comparison map is the identity on pairs. The versions for `CommGrpCat` are `CommGrpCat.cartesianMonoidalCategory` and `CommGrpCat.tensorObj_eq`. The point of the chosen product is definitional: the tensor product is literally the product group, so lemmas about pairs apply without a transport along an isomorphism.

#### Common errors

1. The forgetful functor `forget GrpCat` preserves limits and filtered colimits, but not coproducts. Do not compute a coproduct of groups on the underlying sets: in `MonCat` it is the free product, built in `MonCat.Colimits.ColimitType`.
2. The colimit of a diagram of abelian groups exists only when `AddCommGrpCat.Colimits.Quot F` is small. A diagram indexed by a large category can fail this, so give the universe of $J$ explicitly or use `AddCommGrpCat.hasColimit_iff_small_quot`.
3. The abstract `cokernel f` and the group `H ⧸ (Hom.hom f).range` are isomorphic, not equal. Use `AddCommGrpCat.cokernelIsoQuotient` to pass from one to the other, and `AddCommGrpCat.imageIsoRange` for images.

### Exercises

1. (A) Describe the limit of the diagram $\mathbb{Z} \xrightarrow{2} \mathbb{Z}$, $\mathbb{Z} \xrightarrow{0} \mathbb{Z}$ (an equalizer) in $\mathbf{Ab}$ by the sections construction.
2. (A) Use the filtered colimit construction to show that $\operatorname{colim}(\mathbb{Z} \xrightarrow{2} \mathbb{Z} \xrightarrow{2} \mathbb{Z} \to \cdots) \cong \mathbb{Z}[1/2]$.
3. (B) Show that $\mathbb{Z}/2 * \mathbb{Z}/2$ is the coproduct in $\mathbf{Mon}$ of two copies of $\mathbb{Z}/2$, and that this coproduct is infinite.
4. (B) Prove from the description of $\operatorname{Quot}(F)$ that the colimit of a diagram of abelian groups with no arrows other than identities is the direct sum.
5. (B) Prove that a filtered colimit of groups in which each group is abelian is abelian, by the description of the product of classes.
6. (C) Prove that a filtered colimit of exact sequences of abelian groups is exact. Hint: each element of the colimit has a representative in one $F(k)$.

### Reference

<?reference?>
