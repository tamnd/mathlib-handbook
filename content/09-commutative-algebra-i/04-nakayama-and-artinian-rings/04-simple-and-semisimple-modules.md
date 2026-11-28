---
title: Simple and semisimple modules
kind: api
modules:
  - Mathlib.RingTheory.SimpleModule.Basic
  - Mathlib.RingTheory.SimpleModule.Rank
  - Mathlib.RingTheory.SimpleModule.InjectiveProjective
  - Mathlib.RingTheory.SimpleModule.Isotypic
  - Mathlib.RingTheory.SimpleModule.WedderburnArtin
  - Mathlib.RingTheory.SimpleModule.IsAlgClosed
explains:
  E2: [LinearMap.bijective_or_eq_zero, isSimpleModule_iff_quot_maximal, sSup_simples_eq_top_iff_isSemisimpleModule, IsSemisimpleRing.ideal_eq_span_idempotent, Module.projective_of_isSemisimpleRing, IsSimpleRing.isSemisimpleRing_iff_isArtinianRing, isSemisimpleRing_iff_pi_matrix_divisionRing]
  E1: auto
families: []
requires: [V07.C01, V09.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Simple and semisimple modules

### Overview

A module is simple when it is nonzero and has no submodules except $0$ and itself. A module is semisimple when every submodule has a complement, or equivalently when it is a sum of simple submodules. A ring is semisimple when it is a semisimple module over itself. Section 3 met these rings in the definition of a semiprimary ring: the quotient $R / J(R)$ of such a ring by its Jacobson radical is semisimple.

The modules of this section hold the theory of simple and semisimple modules over an arbitrary ring, not only a commutative one. They contain Schur's lemma, the density theorem of Jacobson, the isotypic components, and the theorem of Wedderburn and Artin: a semisimple ring is a finite product of matrix rings over division rings. The simple rings of Chapter 1, Section 4 appear here as the factors of that product.

### The library around it

**Simple modules.** The class `IsSimpleModule R M` says that the lattice `Submodule R M` is a simple order: it has exactly two elements, $\bot \neq \top$. So the API of simple orders applies directly, through `IsSimpleModule.toIsSimpleOrder`. A submodule $m$ is simple as a module exactly when it is an atom of the lattice of submodules, `isSimpleModule_iff_isAtom`, and the quotient $M / m$ is simple exactly when $m$ is a coatom, `isSimpleModule_iff_isCoatom`. Every nonzero element of a simple module generates it, `IsSimpleModule.span_singleton_eq_top`. So the map $R \to M$, $r \mapsto r x$ is surjective for $x \neq 0$, and its kernel is a maximal left ideal, `IsSimpleModule.ker_toSpanSingleton_isMaximal`. This gives the description
$$M \text{ simple} \iff M \cong R / I \text{ for a maximal left ideal } I,$$
which is `isSimpleModule_iff_quot_maximal`. For a commutative ring the annihilator of a simple module is a maximal ideal, `IsSimpleModule.annihilator_isMaximal`. The ring $R$ is simple as a module over itself exactly when it is a division ring, `isSimpleModule_self_iff_isUnit`. Over a division ring a module is simple exactly when it has dimension $1$: this is `isSimpleModule_iff_finrank_eq_one` in `Mathlib.RingTheory.SimpleModule.Rank`.

**Schur's lemma.** Let $f : M \to N$ be a linear map between simple modules. Its kernel is a submodule of $M$, so it is $0$ or $M$. Its range is a submodule of $N$, so it is $0$ or $N$. Hence $f$ is zero or bijective:
$$f = 0 \quad \text{or} \quad f \text{ is bijective}.$$
The library states the three halves separately as `LinearMap.injective_or_eq_zero`, `LinearMap.surjective_or_eq_zero` and `LinearMap.bijective_or_eq_zero`. Two consequences follow. A nonzero map between simple modules is an isomorphism, `LinearMap.linearEquiv_of_ne_zero`. The endomorphism ring of a simple module is a division ring, the instance `Module.End.instDivisionRing`.

**Semisimple modules.** The class `IsSemisimpleModule R M` asks that `Submodule R M` is a complemented lattice, and `isSemisimpleModule_iff` states this. The main characterization is
$$M \text{ semisimple} \iff \sum_{S \subseteq M \text{ simple}} S = M,$$
which is `sSup_simples_eq_top_iff_isSemisimpleModule`. In one direction, if the simple submodules do not span $M$, take a complement $C$ of their sum. A nonzero element of $C$ generates a cyclic submodule, and that submodule has a simple quotient. In a complemented lattice this quotient is isomorphic to a submodule of $C$, which is a simple submodule outside the sum. The other direction uses Zorn's lemma to find a maximal independent family of simple submodules. With independence one gets a decomposition $M \cong \bigoplus_i S_i$, `IsSemisimpleModule.exists_linearEquiv_dfinsupp`. The class passes to submodules, quotients and images (`IsSemisimpleModule.submodule`, `IsSemisimpleModule.quotient`, `IsSemisimpleModule.of_surjective`, `IsSemisimpleModule.range`), to sums of submodules (`IsSemisimpleModule.sup`), and to finite products and direct sums by instances. The extension and lifting properties, `IsSemisimpleModule.extension_property` and `IsSemisimpleModule.lifting_property`, say that every map out of a submodule extends and that every map into a quotient lifts. For a commutative ring the annihilator of a semisimple module is a radical ideal, `IsSemisimpleModule.annihilator_isRadical`. The density theorem of Jacobson is `jacobson_density`: an endomorphism of $M$ as a module over its endomorphism ring agrees on each finite set with the action of an element of $R$.

**Semisimple rings.** The predicate `IsSemisimpleRing R` is `IsSemisimpleModule R R`. Every module over a semisimple ring is semisimple, `IsSemisimpleRing.isSemisimpleModule`. Each left ideal of a semisimple ring is a direct summand, so it is generated by an idempotent:
$$I = R e, \quad e^2 = e,$$
which is `IsSemisimpleRing.ideal_eq_span_idempotent`. Every simple module over a semisimple ring is isomorphic to a left ideal, `IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule`. The class passes to quotients by `RingHom.isSemisimpleRing_of_surjective`, to finite products by instances, and to the opposite ring by `isSemisimpleRing_mulOpposite_iff`. The module `Mathlib.RingTheory.SimpleModule.InjectiveProjective` proves that every module over a semisimple ring is projective and injective: `Module.projective_of_isSemisimpleRing` and `Module.injective_of_isSemisimpleRing`. For projectivity, write $M$ as a quotient of a free module $F$; the kernel has a complement in $F$, so $M$ is a direct summand of $F$.

**Isotypic components.** Two simple modules have the same type when they are isomorphic. The module `Mathlib.RingTheory.SimpleModule.Isotypic` defines `IsIsotypicOfType R M S`: every simple submodule of $M$ is isomorphic to $S$. The predicate `IsIsotypic R M` says that $M$ is isotypic of some type. The isotypic component `isotypicComponent R M S` is the sum of the simple submodules isomorphic to $S$, and `isotypicComponents R M` is the set of these components. The components are independent, `sSupIndep_isotypicComponents`, and for a semisimple module they span $M$, `sSup_isotypicComponents`. A semisimple isotypic module is a direct sum of copies of one simple module, `IsIsotypic.linearEquiv_finsupp`. The fully invariant submodules, `Submodule.IsFullyInvariant`, are the submodules stable under every endomorphism; for a semisimple module they are exactly the sums of isotypic components, `isFullyInvariant_iff_sSup_isotypicComponents`. For the ring $R$ itself, a left ideal is fully invariant exactly when it is a two-sided ideal, `isFullyInvariant_iff_isTwoSided`.

**The theorem of Wedderburn and Artin.** The module `Mathlib.RingTheory.SimpleModule.WedderburnArtin` proves
$$R \text{ semisimple} \iff R \cong \prod_{i=1}^{n} M_{d_i}(D_i) \text{ for division rings } D_i,$$
which is `isSemisimpleRing_iff_pi_matrix_divisionRing`, with the existence half `IsSemisimpleRing.exists_ringEquiv_pi_matrix_divisionRing`. The proof splits $R$ into its isotypic components. Each component is a two-sided ideal and a ring, isotypic of one type $S_i$, so it is $S_i^{d_i}$ as a module. Its endomorphism ring is then $M_{d_i}(\operatorname{End}(S_i))$, and $\operatorname{End}(S_i)$ is a division ring by Schur's lemma. Finally the ring $R$ is the opposite of its own endomorphism ring as a left module, which explains the `MulOpposite` in the variants `IsSemisimpleRing.exists_ringEquiv_pi_matrix_end_mulOpposite` and `IsSimpleRing.exists_ringEquiv_matrix_end_mulOpposite`. For simple rings there is one factor: an Artinian simple ring is a matrix ring $M_n(D)$, `IsSimpleRing.exists_ringEquiv_matrix_divisionRing`. A simple ring is semisimple exactly when it is Artinian, `IsSimpleRing.isSemisimpleRing_iff_isArtinianRing`, and `isSimpleRing_isArtinianRing_iff` characterizes the Artinian simple rings as the nontrivial semisimple rings that are isotypic over themselves. The variants whose names contain algEquiv work over a base ring $R_0$ and give algebra isomorphisms. The module `Mathlib.RingTheory.SimpleModule.IsAlgClosed` specializes to a finite-dimensional algebra $A$ over an algebraically closed field $F$. Then each division ring $D_i$ is $F$ itself, so
$$A \cong \prod_{i} M_{d_i}(F),$$
which is `IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed`, and a simple such $A$ is a single matrix algebra, `IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed`.

#### Common errors

1. `IsSemisimpleRing R` is an abbreviation for `IsSemisimpleModule R R`. Many facts about semisimple rings are stated only for semisimple modules, so a search for such a fact should also look under `IsSemisimpleModule`.
2. The modules here are left modules. The ideals in `IsSemisimpleRing.ideal_eq_span_idempotent` and in the isotypic decomposition of $R$ are left ideals of type `Ideal R`, and they are two-sided only in special cases.
3. A simple ring in the sense of `IsSimpleRing` need not be semisimple: the Weyl algebra is simple and not Artinian. The theorem of Wedderburn and Artin for a simple ring needs the hypothesis `IsArtinianRing`.

### Exercises

1. (A) Prove that $\mathbb{Z}$ is not a semisimple $\mathbb{Z}$-module, and that $\mathbb{Z}/n$ is semisimple exactly when $n$ is squarefree.
2. (A) Use Schur's lemma to prove that the endomorphism ring of a simple module is a division ring, and find the instance of the library that states it.
3. (B) Let $K$ be a field and $V = K^n$. Prove that $V$ is a simple module over $M_n(K)$, and that $M_n(K)$ is isotypic as a module over itself, of type $V$.
4. (B) Prove that a quotient of a semisimple module is semisimple, using the complement of the kernel.
5. (B) Prove that a commutative semisimple ring is a finite product of fields, starting from `isSemisimpleRing_iff_pi_matrix_divisionRing`.
6. (C) Let $G$ be a finite group and $K$ an algebraically closed field whose characteristic does not divide $|G|$. Assume that $K[G]$ is semisimple. Prove that $|G| = \sum_i d_i^2$, where the $d_i$ are the sizes of the matrix factors of `IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed`.

### Reference

<?reference?>
