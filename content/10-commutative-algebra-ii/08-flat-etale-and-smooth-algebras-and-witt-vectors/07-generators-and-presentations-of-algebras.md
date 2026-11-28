---
title: Generators and presentations of algebras
kind: api
modules:
  - Mathlib.RingTheory.Extension.Generators
  - Mathlib.RingTheory.Extension.Presentation.Basic
  - Mathlib.RingTheory.Extension.Presentation.Core
  - Mathlib.RingTheory.Extension.Presentation.Submersive
explains:
  E2: [Algebra.Generators, Algebra.Generators.comp, Algebra.Generators.Hom, Algebra.Presentation, Algebra.Presentation.dimension, Algebra.Presentation.finitePresentation_of_isFinite, Algebra.PreSubmersivePresentation.jacobian, Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian, Algebra.SubmersivePresentation, Algebra.Presentation.tensorModelOfHasCoeffsEquiv]
  E1: auto
families: []
requires: [V07, V09]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Generators and presentations of algebras

### Overview

Let $S$ be an $R$-algebra. A family of generators of $S$ is a family $(x_i)_{i \in \iota}$ of elements of $S$ such that the map $R[X_i : i \in \iota] \to S$, $X_i \mapsto x_i$, is surjective. A presentation adds a family $(f_j)_{j \in \sigma}$ of polynomials that generates the kernel of this map, so that
$$S \cong R[X_i : i \in \iota]/(f_j : j \in \sigma).$$
A submersive presentation is a finite presentation with an injective map $\sigma \to \iota$ such that the Jacobian determinant $\det(\partial f_j / \partial X_{i})$, taken over the selected variables, is a unit in $S$. This is the classical local form of a standard smooth algebra.

The four modules of this section give these three levels of data, the constructions on them (polynomial rings, localizations, composition, base change), the Jacobian and its behaviour under composition, and a descent result: a finite presentation over $R$ comes by base change from a finitely presented algebra over a finitely generated subring of $R$. The previous section gives the extension and the cotangent complex that each family of generators defines. Section 2 of this chapter uses submersive presentations to define standard smooth algebras.

### The library around it

#### Generators

The structure `Algebra.Generators R S ι` has a field `Algebra.Generators.val`, a map $\iota \to S$, and a set map `Algebra.Generators.σ'` that is a section of the map from the polynomial ring. The section is data, not a proof of surjectivity, so that the extension `Algebra.Generators.toExtension` has a section on the nose. The polynomial ring is `Algebra.Generators.Ring`, which unfolds to `MvPolynomial ι R`, and the kernel of the map to $S$ is `Algebra.Generators.ker`. The lemma `Algebra.Generators.ker_eq_ker_aeval_val` identifies it with the kernel of `MvPolynomial.aeval`.

| Constructor | Data |
| --- | --- |
| `Algebra.Generators.ofSurjective` | a family $x$ and a proof that $X_i \mapsto x_i$ is surjective |
| `Algebra.Generators.ofSet` | a set $s$ with `Algebra.adjoin R s = ⊤` |
| `Algebra.Generators.self` | all elements of $S$ |
| `Algebra.Generators.mvPolynomial` | the variables of $R[X_i]$ |
| `Algebra.Generators.localizationAway` | the element $1/r$ of $S = R[1/r]$, with one variable |
| `Algebra.Generators.naive` | the classes of the variables in $R[X_i]/I$ |
| `Algebra.Generators.comp` | generators of $S$ over $R$ and of $T$ over $S$, with index `ι' ⊕ ι` |
| `Algebra.Generators.baseChange` | the images in $T \otimes_R S$ |
| `Algebra.Generators.extend` | extra elements added to the family |
| `Algebra.Generators.reindex` | transport along an equivalence of index types |

The lemma `Algebra.Generators.finiteType` says that a finite family of generators makes $S$ of finite type, and `Algebra.FiniteType.iff_exists_generators` gives the converse with index `Fin n`.

A map of generators is a `Algebra.Generators.Hom P P'`. Here $P$ presents $S$ over $R$, $P'$ presents $S'$ over $R'$, and $S \to S'$ is given. The field `Algebra.Generators.Hom.val` assigns to each variable of $P$ a polynomial in the variables of $P'$, and the field `Algebra.Generators.Hom.aeval_val` asks that this polynomial maps to the image of $x_i$ in $S'$. The map `Algebra.Generators.Hom.toAlgHom` is the induced map of polynomial rings. A hom always exists: `Algebra.Generators.defaultHom` uses the section of $P'$. For a composition the two canonical homs are `Algebra.Generators.toComp`, from $P$ to the composite, and `Algebra.Generators.ofComp`, from the composite to $Q$. The map `Algebra.Generators.Hom.toExtensionHom` converts a hom of generators into a hom of extensions, and so gives the functoriality of the cotangent complex from the previous section.

#### Presentations and their dimension

The structure `Algebra.Presentation R S ι σ` extends `Algebra.Generators R S ι` with a field `Algebra.Presentation.relation : σ → P.Ring` and the field `Algebra.Presentation.span_range_relation_eq_ker`, which says that the relations span the kernel. The isomorphism `Algebra.Presentation.quotientEquiv` identifies $R[X_i]/(f_j)$ with $S$.

With finitely many relations the kernel is finitely generated, `Algebra.Presentation.fg_ker`. With finitely many variables and relations, `Algebra.Presentation.finitePresentation_of_isFinite` gives `Algebra.FinitePresentation R S`. Conversely, `Algebra.Presentation.exists_presentation_fin` extracts a presentation indexed by `Fin n` and `Fin m` from `Algebra.FinitePresentation R S`, and `Algebra.Presentation.ofFinitePresentation` is a fixed choice of it.

The dimension `Algebra.Presentation.dimension` is `Nat.card ι - Nat.card σ`, in natural numbers. It is meaningful only for finite presentations, and the expected value of a relative dimension only for complete intersections.

| Presentation | Variables, relations | Dimension |
| --- | --- | --- |
| `Algebra.Presentation.id` | none, none | $0$, by `Algebra.Presentation.id_dimension` |
| `Algebra.Presentation.mvPolynomial` | $\iota$, none | $\lvert\iota\rvert$, by `Algebra.Presentation.dimension_mvPolynomial` |
| `Algebra.Presentation.localizationAway` | one, one: $rX - 1$ | $0$, by `Algebra.Presentation.localizationAway_dimension_zero` |
| `Algebra.Presentation.naive` | $\sigma$, the given $v$ | $\lvert\sigma\rvert - \lvert\iota\rvert$ |
| `Algebra.Presentation.baseChange` | same index types | unchanged |
| `Algebra.Presentation.comp` | `ι' ⊕ ι`, `σ' ⊕ σ` | see below |

The lemma `Algebra.Generators.ker_localizationAway` states that the kernel for $S = R[1/r]$ is the ideal generated by `MvPolynomial.C r * MvPolynomial.X () - 1`.

#### Composition of presentations

Let $P$ present $S$ over $R$ with variables $X$ and relations $f_j$, and let $Q$ present $T$ over $S$ with variables $Y$ and relations $g_k$. The composite presentation `Algebra.Presentation.comp Q P` presents $T$ over $R$ in the variables $Y$ and $X$. For each $g_k$ the auxiliary definition `Algebra.Presentation.compRelationAux` lifts each coefficient of $g_k$ from $S$ to $R[X]$ by the section of $P$. This gives a polynomial $\tilde g_k \in R[X, Y]$.

**Proposition.** The kernel of $R[X, Y] \to T$ is generated by the $\tilde g_k$ and the $f_j$. In Lean this is `Algebra.Presentation.span_range_relation_eq_ker_comp`.

*Proof.* Let $J$ be the ideal generated by the $\tilde g_k$ and the $f_j$. Each generator maps to $0$ in $T$, so $J$ lies in the kernel. The quotient $R[X, Y]/(f_j)$ is $S[Y]$, because $R[X]/(f_j) = S$. In $S[Y]$ the image of $\tilde g_k$ is $g_k$. Thus $R[X, Y]/J \cong S[Y]/(g_k) \cong T$, and the map $R[X,Y]/J \to T$ is this isomorphism. So $J$ is the kernel. $\square$

The underlying generators agree with the composite generators, `Algebra.Presentation.toGenerators_comp`. If both presentations are pre-submersive, `Algebra.PreSubmersivePresentation.dimension_comp_eq_dimension_add_dimension` gives additivity of the dimension. The proof needs $\lvert\sigma\rvert \le \lvert\iota\rvert$, which `Algebra.PreSubmersivePresentation.card_relations_le_card_vars_of_isFinite` supplies. For arbitrary presentations the truncated subtraction can break additivity.

#### Jacobians and submersive presentations

The structure `Algebra.PreSubmersivePresentation R S ι σ` extends a presentation with an injective map `Algebra.PreSubmersivePresentation.map : σ → ι`. It selects for each relation $f_j$ a variable $X_{m(j)}$. The linear map `Algebra.PreSubmersivePresentation.differential` on $P^\sigma$ sends the basis vector $e_j$ to the vector $(\partial f_j / \partial X_{m(i)})_{i \in \sigma}$. The Jacobian `Algebra.PreSubmersivePresentation.jacobian` is the image in $S$ of its determinant. For a finite type with decidable equality, `Algebra.PreSubmersivePresentation.jacobiMatrix` is the matrix, and `Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det` connects the two.

The structure `Algebra.SubmersivePresentation R S ι σ` adds the field `Algebra.SubmersivePresentation.jacobian_isUnit`. The criterion `Algebra.PreSubmersivePresentation.isUnit_jacobian_iff_aevalDifferential_bijective` says that the Jacobian is a unit if and only if the differential, evaluated in $S$, is bijective. For a submersive presentation, `Algebra.SubmersivePresentation.aevalDifferentialEquiv` is this bijection as a linear equivalence, and `Algebra.SubmersivePresentation.basisDeriv` is the resulting basis of $S^\sigma$.

| Presentation | Jacobian |
| --- | --- |
| `Algebra.PreSubmersivePresentation.mvPolynomial` | $1$, by `Algebra.PreSubmersivePresentation.jacobian_mvPolynomial` |
| `Algebra.PreSubmersivePresentation.localizationAway` | $r$, by `Algebra.PreSubmersivePresentation.localizationAway_jacobian` |
| `Algebra.PreSubmersivePresentation.baseChange` | $1 \otimes J$, by `Algebra.PreSubmersivePresentation.baseChange_jacobian` |
| `Algebra.PreSubmersivePresentation.comp` | product, see below |

Since $r$ is a unit in $R[1/r]$, the localization presentation is submersive, `Algebra.SubmersivePresentation.localizationAway`. The constructions `Algebra.SubmersivePresentation.mvPolynomial`, `Algebra.SubmersivePresentation.baseChange`, `Algebra.SubmersivePresentation.comp` and `Algebra.SubmersivePresentation.reindex` complete the list.

**Proposition.** For pre-submersive presentations $P$ of $S$ over $R$ and $Q$ of $T$ over $S$, the Jacobian of the composite is the product $J_P \cdot J_Q$ in $T$. In Lean this is `Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian`, with the product written as a scalar action of $S$ on $T$.

*Proof.* Order the relations as the $\tilde g_k$ first, then the $f_j$, and order the selected variables in the same way. The relations $f_j$ contain only the variables $X$, so their derivatives with respect to the variables $Y$ vanish. Thus the Jacobian matrix is block triangular. Its diagonal blocks are the derivatives of the $\tilde g_k$ with respect to $Y$ and of the $f_j$ with respect to $X$. The first block, evaluated in $T$, is the Jacobian matrix of $Q$, because differentiation in $Y$ commutes with the map $R[X][Y] \to S[Y]$. The second block, evaluated in $S$, is the Jacobian matrix of $P$. The determinant of a block triangular matrix is the product of the determinants of the blocks. $\square$

So a composite of submersive presentations is submersive, since a product of units is a unit.

#### Descent of the coefficients

The relations of a presentation $P$ have finitely many coefficients when $\sigma$ is finite, `Algebra.Presentation.finite_coeffs`, where `Algebra.Presentation.coeffs` is the set of all coefficients. The subring `Algebra.Presentation.core` is the $\mathbb{Z}$-subalgebra of $R$ generated by them, and `Algebra.Presentation.Core` is its type. It is of finite type over $\mathbb{Z}$, and so Noetherian.

More generally, the class `Algebra.Presentation.HasCoeffs P R₀` says that all coefficients lie in the image of $R_0 \to R$. Then `Algebra.Presentation.relationOfHasCoeffs` lifts each relation to $R_0[X]$, and `Algebra.Presentation.ModelOfHasCoeffs R₀` is the quotient $S_0 = R_0[X]/(f_j^0)$. It is finitely presented over $R_0$ when the index types are finite. The equivalence `Algebra.Presentation.tensorModelOfHasCoeffsEquiv` identifies $R \otimes_{R_0} S_0$ with $S$ as $R$-algebras, because base change preserves presentations. For submersive presentations, `Algebra.SubmersivePresentation.HasCoeffs` also asks for the coefficients of polynomials $h_j$ with $\sum_j h_j f_j = \det \cdot \sigma(J^{-1}) - 1$, which `Algebra.SubmersivePresentation.jacobianRelations_spec` gives. They make the Jacobian of the model a unit. Under it and `FaithfulSMul R₀ R`, the model `Algebra.SubmersivePresentation.ofHasCoeffs` is again submersive. This is the step that reduces statements about smooth algebras to the case of a Noetherian base.

#### Common errors

1. `Algebra.Presentation.dimension` uses truncated subtraction. A presentation with more relations than variables has dimension $0$, and lemmas about the dimension of a composite need the pre-submersive bound $\lvert\sigma\rvert \le \lvert\iota\rvert$.
2. A `Algebra.SubmersivePresentation` asks that the Jacobian is a unit in $S$, not in the polynomial ring. The determinant in $R[X]$ is almost never a unit, so a proof must evaluate first, with `Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det`.
3. The variables of a composite are indexed by `ι' ⊕ ι`, with the variables of the upper presentation $Q$ on the left. A goal about the left injection refers to $Q$, and a goal about the right injection refers to $P$.

### Exercises

1. (A) Let $S = R[1/r]$. Use `Algebra.Generators.ker_localizationAway` to show that $S \cong R[X]/(rX - 1)$. Compute the Jacobian of this presentation and explain why it is submersive.
2. (A) Let $k$ be a field and $S = k[X]/(X^2)$, presented with one variable, the relation $X^2$, and the identity map on the one element index type. Compute the Jacobian and show that this presentation is not submersive.
3. (A) Give a presentation of $R$ over itself with one variable and two relations. Compute its dimension, and show that it has no pre-submersive structure.
4. (A) Let $P$ be a submersive presentation of $S$ over $R$ and let $T$ be an $R$-algebra. Use `Algebra.PreSubmersivePresentation.baseChange_jacobian` to show that the base change of $P$ to $T$ is submersive.
5. (B) Let $f \in R[X, Y]$ and $S = R[X, Y]/(f)$. Give a pre-submersive presentation with the map to the variable $Y$. Show that it is submersive if and only if the class of $\partial f / \partial Y$ is a unit in $S$. Then present $S[1/g]$ over $R$ with `Algebra.PreSubmersivePresentation.comp` and compute its Jacobian.
6. (B) Let $S = \mathbb{C}[X]/(X^2 - i)$. Compute `Algebra.Presentation.coeffs` and `Algebra.Presentation.core` for this presentation, describe the model $S_0$, and verify directly that $\mathbb{C} \otimes_{\mathbb{Z}[i]} S_0 \cong S$.

### Reference

<?reference?>
