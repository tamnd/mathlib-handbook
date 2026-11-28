---
title: Free bases, presentations and finitely presented groups
kind: api
modules:
  - Mathlib.GroupTheory.FreeGroup.IsFreeGroup
  - Mathlib.GroupTheory.FreeGroup.NielsenSchreier
  - Mathlib.GroupTheory.PresentedGroup
  - Mathlib.GroupTheory.Presentation
  - Mathlib.GroupTheory.FinitelyPresentedGroup
explains:
  E2: [FreeGroupBasis.ofUniqueLift, Subgroup.isFreeGroupOfIsFreeGroup, PresentedGroup.mk_eq_one_iff, PresentedGroup.toGroup, PresentedGroup.coprodPresentations, Group.Presentation.presentedGroupEquiv, Group.Presentation.isFinitelyPresented_iff_exists_finite_presentation, Group.IsFinitelyPresented.quotient]
  E1: auto
families: []
requires: [V01, V05.C01, V05.C02, V05.C03, V05.C04, V05.C05, V05.C06]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Free bases, presentations and finitely presented groups

### Overview

Section 2 builds one free group `FreeGroup α` for each type $\alpha$. Many groups are free without being of this form: a subgroup of a free group, or a group with an isomorphism to a free group. The module `Mathlib.GroupTheory.FreeGroup.IsFreeGroup` gives the notion of a free basis of a group $G$ and the predicate `IsFreeGroup G`. The module `Mathlib.GroupTheory.FreeGroup.NielsenSchreier` proves the theorem of Nielsen and Schreier: each subgroup of a free group is free.

A presentation $\langle S \mid R \rangle$ describes a group as the quotient of the free group on $S$ by the normal subgroup that the relators $R$ generate. The module `Mathlib.GroupTheory.PresentedGroup` builds this quotient from a set of relators. The module `Mathlib.GroupTheory.Presentation` packs a presentation of a given group $G$ as data, on top of the generating families `Group.Generators` of Chapter 4. The module `Mathlib.GroupTheory.FinitelyPresentedGroup` defines finitely presented groups and proves their closure properties. The section uses normal closures and quotients from Chapter 5.

### The library around it

#### Free bases

A free basis of $G$ indexed by $\iota$ is an isomorphism $G \cong F(\iota)$. The structure `FreeGroupBasis ι G` holds it as the field `FreeGroupBasis.repr`, with the constructor `FreeGroupBasis.ofRepr`. A basis is also a function $\iota \to G$ through the instance `FreeGroupBasis.instFunLike`: the value $b(i)$ is the preimage of the generator $\mathrm{of}\,i$, and `FreeGroupBasis.repr_apply_coe` says $\mathrm{repr}\,(b\,i) = \mathrm{of}\,i$. This function is injective (`FreeGroupBasis.injective`). The free group itself has the basis `FreeGroupBasis.ofFreeGroup`, and a basis moves along an isomorphism (`FreeGroupBasis.map`) and along a bijection of the index type (`FreeGroupBasis.reindex`).

The universal property of `FreeGroup ι` passes to each group with a basis. The equivalence `FreeGroupBasis.lift` sends a map $\iota \to H$ to a homomorphism $G \to H$, and `FreeGroupBasis.ext_hom` says that two homomorphisms that agree on a basis are equal. The converse holds as well: a map with the universal property is a basis.

**Bases from the universal property.** Let $X$ be a type and $\mathrm{of} : X \to G$ a map such that, for each group $H$ and each map $f : X \to H$, there is exactly one homomorphism $F : G \to H$ with $F \circ \mathrm{of} = f$. Then `FreeGroupBasis.ofUniqueLift` gives a basis of $G$ indexed by $X$.

*Proof sketch.* Take $H = F(X)$ and $f = \mathrm{of}_{F(X)}$: this gives a homomorphism $\psi : G \to F(X)$. The lift of $\mathrm{of}$ is a homomorphism $\chi : F(X) \to G$. The composite $\chi \circ \psi$ and the identity of $G$ both send $\mathrm{of}\,x$ to $\mathrm{of}\,x$, so they are equal by the uniqueness in the hypothesis. The composite $\psi \circ \chi$ is the identity of $F(X)$ by `FreeGroup.ext_hom`. So $\psi$ is an isomorphism. $\square$

The variant `FreeGroupBasis.ofLift` takes the universal property as an equivalence. Both hypotheses quantify over groups $H$ in the universe of $G$.

The class `IsFreeGroup G` says that a basis exists, with the field `IsFreeGroup.nonempty_basis`. A basis gives the class by `FreeGroupBasis.isFreeGroup`, and the class moves along isomorphisms (`IsFreeGroup.ofMulEquiv`). For a free group the library chooses a basis: its index type is `IsFreeGroup.Generators G`, the basis is `IsFreeGroup.basis`, and `IsFreeGroup.mulEquiv` and `IsFreeGroup.toFreeGroup` are the isomorphisms with `FreeGroup (IsFreeGroup.Generators G)`. The API of Section 2 comes back with the names `IsFreeGroup.of`, `IsFreeGroup.lift`, `IsFreeGroup.lift_of`, `IsFreeGroup.ext_hom` and `IsFreeGroup.unique_lift`. The theorems `IsFreeGroup.ofUniqueLift` and `IsFreeGroup.ofLift` are the forms of the criterion above for the class. The additive forms are `FreeAddGroupBasis` and `IsFreeAddGroup`, and `isFreeAddGroup_additive_iff` connects the two.

The chosen generating type is unique up to bijection: `Equiv.ofIsFreeGroupEquiv` turns an isomorphism of free groups into a bijection of their generating types, from the result `Equiv.ofFreeGroupEquiv` of Section 2.

#### The Nielsen-Schreier theorem

**Theorem.** Each subgroup of a free group is free. This is the instance `Subgroup.isFreeGroupOfIsFreeGroup`.

*Proof sketch.* The proof replaces the covering spaces of the topological proof by groupoids. A groupoid is free when its functors to groups are given freely by their values on a set of generating arrows, the class `IsFreeGroupoid`. Let the free group $G$ act on the cosets $G/H$. The action groupoid has the cosets as objects and an arrow $g : x \to g \cdot x$ for each $g$ and $x$, and it is free with the arrows of the generators (`IsFreeGroupoid.actionGroupoidIsFree`). The action is transitive, so the groupoid is connected, and the loops at the coset $H$ form a group isomorphic to the stabilizer, which is $H$. In a connected free groupoid, choose a spanning tree of the generating graph. Each generating arrow outside the tree gives one loop at the root: go along the tree, take the arrow, and go back along the tree. These loops form a free basis of the group of loops (`IsFreeGroupoid.SpanningTree.endIsFree`), and `IsFreeGroupoid.endIsFreeOfConnectedFree` states the result for connected groupoids. $\square$

The spanning tree argument also counts the basis: for a subgroup of index $n$ in a free group of rank $r$, the rank of the subgroup is $1 + n(r - 1)$. The library does not state this count.

#### Presented groups

Let $\alpha$ be a type and $R$ a set of elements of `FreeGroup α`. The type `PresentedGroup R` is the quotient of `FreeGroup α` by `Subgroup.normalClosure R`, with the group instance `instGroupPresentedGroup`. The quotient map is `PresentedGroup.mk R`, a surjective homomorphism (`PresentedGroup.mk_surjective`), and the generators are `PresentedGroup.of`. They generate the group (`PresentedGroup.closure_range_of`), and the lemma `PresentedGroup.generated_by` says that a subgroup with all generators is the whole group.

**The kernel.** For $x$ in the free group, $\mathrm{mk}\,x = 1$ exactly when $x$ is in the normal closure of $R$. This is `PresentedGroup.mk_eq_one_iff`.

*Proof.* The map $\mathrm{mk}$ is the quotient map by the normal subgroup $\overline{R}$, and its kernel is $\overline{R}$ by the first isomorphism theorem of Chapter 5. $\square$

Each relator becomes $1$ (`PresentedGroup.one_of_mem`), and two words that differ by a relator have the same image (`PresentedGroup.mk_eq_mk_of_mul_inv_mem` and `PresentedGroup.mk_eq_mk_of_inv_mul_mem`).

**The universal property.** Let $f : \alpha \to G$ be a map to a group such that the lift of $f$ to the free group sends each relator to $1$. Then `PresentedGroup.toGroup` is the homomorphism $\langle \alpha \mid R \rangle \to G$ with $\mathrm{of}\,a \mapsto f(a)$. It is unique.

*Proof.* The kernel of $\mathrm{lift}\,f$ is a normal subgroup that contains $R$, so it contains the normal closure $\overline{R}$ (`PresentedGroup.closure_rels_subset_ker`). So $\mathrm{lift}\,f$ factors through the quotient by $\overline{R}$. Uniqueness holds because the elements $\mathrm{of}\,a$ generate. $\square$

The computation rule is `PresentedGroup.toGroup.of`, and the uniqueness is `PresentedGroup.toGroup.unique`. The extensionality lemma `PresentedGroup.ext` compares two homomorphisms out of a presented group on the generators. A homomorphism of free groups that maps one set of relators into another induces `PresentedGroup.map`, and a bijection of generators gives the isomorphism `PresentedGroup.equivPresentedGroup`.

**Free products.** Let $R_1$ be relators on $\alpha$ and $R_2$ relators on $\beta$. Then $\langle \alpha \sqcup \beta \mid R_1 \cup R_2 \rangle$ is the free product $\langle \alpha \mid R_1 \rangle * \langle \beta \mid R_2 \rangle$ of Section 1. This is `PresentedGroup.coprodPresentations`.

*Proof sketch.* Send the generators from $\alpha$ to the left factor and those from $\beta$ to the right factor. The relators go to $1$ (`PresentedGroup.lift_toCoprod_eq_one`), so `PresentedGroup.toGroup` gives a homomorphism to the free product. In the other direction, `Monoid.Coprod.lift` combines the two maps of presented groups. Both composites are the identity on generators. $\square$

The additive forms have the prefix `PresentedAddGroup`.

#### Presentations as data

A presentation of a given group $G$ is a structure `Group.Presentation G ι`. It extends a generating family `Group.Generators G ι` with a set `Group.Presentation.rel` of words in `FreeGroup ι`, and the field `Group.Presentation.lift_ker_eq_normalClosure` says that the kernel of the surjection $F(\iota) \to G$ is the normal closure of the relators. The lemma `Group.Presentation.ker_lift` restates this field, and `Group.Presentation.lift_rel_eq_one` says that each relator maps to $1$. A surjection from a free group and a set of relators with the right kernel give a presentation by `Group.Presentation.ofFreeGroupHom`.

**The presented group of a presentation.** For a presentation $P$ of $G$, the group `PresentedGroup P.rel` is isomorphic to $G$. This is `Group.Presentation.presentedGroupEquiv`.

*Proof.* The presented group is the quotient of $F(\iota)$ by the normal closure of the relators, and this normal closure is the kernel of the surjection $F(\iota) \to G$. The first isomorphism theorem `QuotientGroup.quotientKerEquivOfSurjective` identifies this quotient with $G$. $\square$

#### Finitely presented groups

A normal subgroup $N$ is finitely normally generated when it is the normal closure of a finite set, `Subgroup.IsFinitelyNormallyGenerated`. A normal subgroup that is finitely generated as a group has this property (`Subgroup.IsFinitelyNormallyGenerated.of_FG`). The property passes to images under surjections (`Subgroup.IsFinitelyNormallyGenerated.map`) and to preimages under a surjection with a finitely normally generated kernel (`Subgroup.IsFinitelyNormallyGenerated.comap`).

The class `Group.IsFinitelyPresented G` says that there is $n$ and a surjection $\varphi : F(\mathrm{Fin}\,n) \to G$ with a finitely normally generated kernel. The unfolding lemma is `Group.isFinitelyPresented_iff`, and `Group.IsFinitelyPresented.exists_mulEquiv_presentedGroup` gives an isomorphism with a `PresentedGroup` of finitely many relators.

**Two forms of the definition.** A group is finitely presented exactly when it has a presentation with finitely many generators and finitely many relators. This is `Group.Presentation.isFinitelyPresented_iff_exists_finite_presentation`.

*Proof.* A surjection $\varphi : F(\mathrm{Fin}\,n) \to G$ and a finite set $S$ with $\ker \varphi = \overline{S}$ give a presentation by `Group.Presentation.ofFreeGroupHom`. Conversely, a finite presentation gives such a surjection and such a set, by `Group.Presentation.isFinitelyPresented`. $\square$

**Quotients.** Let $G$ be finitely presented and let $N$ be a normal subgroup that is finitely normally generated. Then $G/N$ is finitely presented. This is `Group.IsFinitelyPresented.quotient`.

*Proof.* Let $\varphi : F(\mathrm{Fin}\,n) \to G$ be a surjection with $\ker \varphi = \overline{S}$ for a finite $S$. Let $N = \overline{T}$ for a finite $T$, and choose a finite set $T'$ of preimages of $T$. The composite $F(\mathrm{Fin}\,n) \to G \to G/N$ is surjective, and its kernel is $\varphi^{-1}(N)$. This kernel is the normal closure of $S \cup T'$, by `Subgroup.IsFinitelyNormallyGenerated.comap`. $\square$

The theorem `Group.IsFinitelyPresented.of_surjective` is the form for a surjection with a finitely normally generated kernel, and `Group.IsFinitelyPresented.equiv` moves the class along an isomorphism. The instances give the standard examples.

| Lean name | Statement |
|---|---|
| `Group.IsFinitelyPresented.instFreeGroupOfFinite` | a free group of finite rank is finitely presented |
| `Group.IsFinitelyPresented.instPresentedGroupOfFiniteElemFreeGroup` | finitely many generators and relators give a finitely presented group |
| `Group.IsFinitelyPresented.instMultiplicativeInt` | $\mathbb{Z}$ is finitely presented |
| `Group.IsFinitelyPresented.instCoprod` | the free product of two finitely presented groups is finitely presented |
| `Group.IsFinitelyPresented.instOfFinite` | a finite group is finitely presented |

A finite group $G$ has the presentation with the elements of $G$ as generators and the multiplication table $g \cdot h = gh$ as relators.

#### Common errors

1. `PresentedGroup R` takes the relators as a set of elements of `FreeGroup α`, not as pairs of words. To impose $u = v$, put $u v^{-1}$ in the set.
2. `IsFreeGroup.Generators G` is a chosen index type, not a subset of $G$. Two different bases of one free group can have different elements. Only their cardinality is determined, by `Equiv.ofIsFreeGroupEquiv`.
3. `Group.IsFinitelyPresented` uses generators indexed by `Fin n`. A presentation with another finite index type gives the class by `Group.Presentation.isFinitelyPresented`, not by unfolding the definition.

### Exercises

1. (A) Show that the presented group $\langle a \mid a^n \rangle$ is cyclic of order $n$, with `PresentedGroup.toGroup` and `PresentedGroup.mk_eq_one_iff`.
2. (A) Prove that a group with a basis indexed by an empty type is trivial, with `FreeGroupBasis.repr`.
3. (B) Show that $\langle a, b \mid aba^{-1}b^{-1} \rangle$ is isomorphic to $\mathbb{Z}^2$.
4. (B) Use `Subgroup.isFreeGroupOfIsFreeGroup` to prove that each subgroup of `FreeGroup α` has no element of finite order other than $1$.
5. (B) Prove that the product of two finitely presented groups is finitely presented, with a presentation that adds commutators of the generators to the free product.
6. (C) Prove that the commutator subgroup of the free group on two generators is not finitely generated, with the action of the free group on the cosets, which are the points of $\mathbb{Z}^2$, and the spanning tree argument of the Nielsen-Schreier proof.

### Reference

<?reference?>
