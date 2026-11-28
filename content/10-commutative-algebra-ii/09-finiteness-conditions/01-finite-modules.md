---
title: Finite modules and finitely generated submodules
kind: api
modules:
  - Mathlib.RingTheory.Finiteness.Defs
  - Mathlib.RingTheory.Finiteness.Basic
  - Mathlib.RingTheory.Finiteness.Bilinear
  - Mathlib.RingTheory.Finiteness.Cardinality
  - Mathlib.RingTheory.Finiteness.Cofinite
  - Mathlib.RingTheory.Finiteness.Descent
  - Mathlib.RingTheory.Finiteness.Finsupp
  - Mathlib.RingTheory.Finiteness.Ideal
  - Mathlib.RingTheory.Finiteness.Lattice
  - Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
  - Mathlib.RingTheory.Finiteness.Nilpotent
  - Mathlib.RingTheory.Finiteness.NilpotentKer
  - Mathlib.RingTheory.Finiteness.Prod
  - Mathlib.RingTheory.Finiteness.Projective
  - Mathlib.RingTheory.Finiteness.Quotient
  - Mathlib.RingTheory.Finiteness.Small
  - Mathlib.RingTheory.Finiteness.Subalgebra
  - Mathlib.RingTheory.FiniteLength
  - Mathlib.RingTheory.AlgebraTower
explains:
  E2: [Module.Finite, Submodule.FG, Module.Finite.trans, Module.Finite.of_exact, Ideal.exists_pow_le_of_le_radical_of_fg, Submodule.CoFG, isFiniteLength_iff_isNoetherian_isArtinian, Module.Basis.smulTower, Module.not_finite_of_infinite_basis]
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

## Finite modules and finitely generated submodules

### Overview

A module $M$ over a ring $R$ is finite when finitely many elements generate it. A submodule $N \subseteq M$ is finitely generated when it is the span of a finite set. These two conditions are the most common finiteness hypotheses of commutative algebra. Nakayama's lemma in Chapter 2, the integral extensions of Chapter 1 and the Noetherian rings of Volume 9 all use them.

The modules of this section hold the definitions, the closure properties under sums, quotients, products, extensions and towers of rings, and a set of smaller results: the finiteness of ideals and their powers, modules of finite length, cofinitely generated submodules, nilpotent endomorphisms of a finite module, and the descent of finiteness along a faithfully flat map. The module `Mathlib.RingTheory.AlgebraTower` adds the bases of a tower $R \to S \to A$. Section 2 of this chapter builds the finiteness conditions for algebras on this material.

### The library around it

#### The two definitions

The module `Mathlib.RingTheory.Finiteness.Defs` holds the definitions. For a submodule `N : Submodule R M`, the proposition `Submodule.FG N` says that there is a finite set $S$ with $N = \operatorname{span}_R S$. The lemma `Submodule.fg_def` states this with a `Set.Finite` set, and `Submodule.fg_iff_exists_fin_generating_family` with a family indexed by `Fin n`. For an ideal, `Ideal.FG` is the same notion. The class `Module.Finite R M` says that the top submodule of $M$ is finitely generated, and `Module.finite_def` is this equivalence. A user of the class usually takes a surjection from a free module: `Module.Finite.exists_fin` gives $n$ and $s : \mathrm{Fin}\ n \to M$ whose span is $M$.

The two notions are linked by `Module.Finite.iff_fg : Module.Finite R N ↔ N.FG` for a submodule $N$ seen as a module. So a lemma about `Submodule.FG` and a lemma about `Module.Finite` of a subtype say the same thing, and the library has both forms. Over $\mathbb{Z}$ and $\mathbb{N}$, `Module.Finite.iff_addGroup_fg` and `Module.Finite.iff_addMonoid_fg` connect the class to finitely generated groups and monoids.

The module also defines finite ring maps. A ring map $f : A \to B$ is finite, `RingHom.Finite f`, when $B$ is a finite $A$-module through $f$. The version for algebra maps is `AlgHom.Finite`, and `RingHom.finite_algebraMap` says that `algebraMap A B` is finite if and only if `Module.Finite A B`.

#### Closure properties

The module `Mathlib.RingTheory.Finiteness.Basic` proves that the two notions are stable under the usual constructions. Many of the results are instances, so that Lean finds them with no help.

| Lean name | Statement |
|---|---|
| `Submodule.fg_span` | the span of a finite set is finitely generated |
| `Submodule.FG.sup` | $N_1 + N_2$ is finitely generated if $N_1$ and $N_2$ are |
| `Submodule.FG.map` | the image of a finitely generated submodule is finitely generated |
| `Submodule.fg_iSup` | a finite supremum of finitely generated submodules is finitely generated |
| `Module.Finite.of_surjective` | a quotient of a finite module is finite |
| `Module.Finite.quotient` | $M/N$ is finite when $M$ is finite |
| `Module.Finite.pi` | a finite product of finite modules is finite |
| `Module.Finite.prod` | $M \times N$ is finite when $M$ and $N$ are |
| `Module.Finite.finsupp` | $\iota \to_0 V$ is finite for $\iota$ finite and $V$ finite |
| `Module.Finite.trans` | in a tower $R \to A \to M$, finite over finite is finite |
| `Module.Finite.of_restrictScalars_finite` | if $M$ is finite over $R$, then it is finite over $A$ |
| `RingHom.Finite.comp` | a composite of finite ring maps is finite |

The lemma `Submodule.fg_iff_compact` says that the finitely generated submodules are the compact elements of the lattice of submodules. This is the order form of the definition: $N$ is finitely generated if and only if every directed family whose supremum contains $N$ has a member that contains $N$. The lemma `Submodule.FG.stabilizes_of_iSup_eq` is the form for an increasing sequence.

**Proof of `Module.Finite.trans`.** Let $a_1, \dots, a_m$ generate $A$ as an $R$-module, and let $x_1, \dots, x_n$ generate $M$ as an $A$-module. Each $x \in M$ is $\sum_j b_jx_j$ with $b_j \in A$, and each $b_j$ is $\sum_i r_{ij}a_i$ with $r_{ij} \in R$. So $x = \sum_{i,j} r_{ij}\,(a_ix_j)$, and the $mn$ elements $a_ix_j$ generate $M$ over $R$. $\square$

The module `Mathlib.RingTheory.Finiteness.Prod` has `Submodule.FG.prod` and the instance `Module.Finite.prod`. The module `Mathlib.RingTheory.Finiteness.Lattice` has the instance `Submodule.finite_iSup` for a finite family of finite submodules. The module `Mathlib.RingTheory.Finiteness.Bilinear` has one result, `Submodule.FG.map₂`: the image of $p \times q$ under a bilinear map $f$ spans a finitely generated submodule when $p$ and $q$ are finitely generated.

#### Extensions and exact sequences

The module `Mathlib.RingTheory.Finiteness.Finsupp` proves that finiteness passes to extensions. The lemma `Module.Finite.of_exact` takes an exact sequence $M \xrightarrow{f} N \xrightarrow{g} P$ with $g$ surjective and $M$, $P$ finite, and concludes that $N$ is finite. The form with a submodule is `Module.Finite.of_submodule_quotient`: if $N$ and $M/N$ are finite, then $M$ is finite.

**Proof of `Module.Finite.of_exact`.** Let $y_1, \dots, y_k \in N$ map to generators of $P$, and let $x_1, \dots, x_l$ generate $M$. For $y \in N$, write $g(y) = \sum_i r_ig(y_i)$. Then $y - \sum_i r_iy_i$ is in the kernel of $g$, which is the image of $f$. So it is $f(\sum_j s_jx_j) = \sum_j s_jf(x_j)$. Thus the $y_i$ and the $f(x_j)$ generate $N$. $\square$

The same module has `Submodule.fg_ker_comp`, for the kernel of a composite, and the bijection `LinearMap.finsuppLinearMap_bijective_of_moduleFinite`: for a finite module $M$, a finitely supported family of linear maps $M \to N$ is the same as a linear map $M \to (\iota \to_0 N)$. The instances `MonoidAlgebra.moduleFinite` and `AddMonoidAlgebra.moduleFinite` say that the monoid algebra of a finite monoid is a finite module.

#### Ideals

The module `Mathlib.RingTheory.Finiteness.Ideal` treats finitely generated ideals. The products `Ideal.FG.mul` and the powers `Ideal.FG.pow` of finitely generated ideals are finitely generated, and so is the image `Ideal.FG.map` under a ring map. The main result is `Ideal.exists_pow_le_of_le_radical_of_fg`: if $I \subseteq \sqrt{J}$ and $I$ is finitely generated, then $I^n \subseteq J$ for some $n$.

**Proof.** Let $I = (x_1, \dots, x_k)$. Each $x_i$ is in $\sqrt J$, so $x_i^{m} \in J$ for one $m$ that works for all $i$. Put $n = k(m - 1) + 1$. The ideal $I^n$ is generated by the monomials $x_1^{e_1} \cdots x_k^{e_k}$ with $\sum_i e_i = n$. By the pigeonhole principle, some $e_i \ge m$, so each such monomial is in $J$. $\square$

In a Noetherian ring every ideal is finitely generated, so the result applies to $I = \sqrt J$ and gives `Ideal.exists_radical_pow_le_of_fg` in that case. The module `Mathlib.RingTheory.Finiteness.Subalgebra` has the same closure results for submodules of an algebra: `Submodule.FG.mul`, `Submodule.FG.pow`, and `Submodule.fg_of_isUnit`, which says that an invertible submodule is finitely generated. This last result is the reason why invertible fractional ideals are finitely generated in Chapter 4.

#### Finite modules and cardinality

The module `Mathlib.RingTheory.Finiteness.Cardinality` compares `Module.Finite` with the finiteness of the type. Over a finite ring, `Module.finite_iff_finite` says that a module is finite as a module if and only if it has finitely many elements. A basis of a finite module over a nontrivial ring is finite, `Module.Finite.finite_basis`, and `Module.not_finite_of_infinite_basis` is the contrapositive. The lemma `Module.Finite.exists_fin_quot_equiv` presents a finite module as a quotient $R^n / S$, and `Module.Finite.reprEquiv` is a chosen such presentation.

**Proof of `Module.not_finite_of_infinite_basis`.** Suppose that $M$ is finite with generators $x_1, \dots, x_n$, and let $(b_i)_{i \in \iota}$ be a basis. Each $x_j$ is a combination of finitely many $b_i$. So a finite set $F \subseteq \iota$ has all the $x_j$ in its span, and then $M = \operatorname{span}\{b_i : i \in F\}$. For $i \notin F$, the vector $b_i$ is then a combination of the $b_k$ with $k \in F$. This contradicts the linear independence, since $R$ is nontrivial. So $\iota = F$ is finite. $\square$

The module `Mathlib.RingTheory.Finiteness.Small` has universe results. If $R$ is $u$-small, then each finitely generated submodule is $u$-small, `Submodule.FG.small`, a finite module is $u$-small, `Module.Finite.small`, and the span of a $u$-small set is $u$-small. These results let a proof move a finite module into a smaller universe.

#### Cofinitely generated submodules

The module `Mathlib.RingTheory.Finiteness.Cofinite` defines `Submodule.CoFG`. A submodule $S \subseteq M$ is cofinitely generated when the quotient $M/S$ is a finite module. The definition is an abbreviation for `Module.Finite R (M ⧸ S)`. Every submodule of a finite module is cofinitely generated, `Submodule.CoFG.of_finite`. A submodule above a cofinitely generated one is again cofinitely generated, `Submodule.CoFG.of_le`. For a linear map $f$, the lemma `Submodule.range_fg_iff_ker_cofg` says that the image is finitely generated if and only if the kernel is cofinitely generated: this is the isomorphism $M/\ker f \cong \operatorname{im} f$. The intersection of two cofinitely generated submodules is cofinitely generated over a Noetherian ring, `Submodule.CoFG.inf`. A complement of a cofinitely generated submodule is finitely generated, `Submodule.CoFG.fg_of_isCompl`.

#### Nilpotence, projectivity and quotients

The module `Mathlib.RingTheory.Finiteness.Nilpotent` characterizes nilpotent endomorphisms of a finite module. An endomorphism $f$ of a finite module over a commutative ring is nilpotent if and only if every vector is killed by some power of $f$, `Module.End.isNilpotent_iff_of_finite`. The point is that one power works for the finitely many generators, and so for all vectors. The matrix forms are `Matrix.isNilpotent_iff`, `Matrix.isNilpotent_iff_forall_row` and `Matrix.isNilpotent_iff_forall_col`.

The module `Mathlib.RingTheory.Finiteness.Projective` has `Module.Finite.exists_comp_eq_id_of_projective`: a finite projective module is a direct summand of some $R^n$, with maps $g : M \to R^n$ and $f : R^n \to M$ such that $f \circ g = \mathrm{id}$. The module `Mathlib.RingTheory.Finiteness.NilpotentKer` has `Module.finite_of_surjective_of_ker_le_nilradical`: if $S \to T$ is a surjective $R$-algebra map with a finitely generated nilpotent kernel and $T$ is finite over $R$, then $S$ is finite over $R$.

The module `Mathlib.RingTheory.Finiteness.Quotient` has instances for a prime $P$ of $B$ over a prime $p$ of $A$. When $B$ is finite over $A$, the quotient $B/P$ is finite over $A/p$, `module_finite_of_liesOver`, and the same holds for finite type, `algebra_finiteType_of_liesOver`. The module `Mathlib.RingTheory.Finiteness.ModuleFinitePresentation` relates the finite presentation of a module and of an algebra: for an algebra $S$ that is a finite $R$-module, `Module.FinitePresentation.iff_finitePresentation_of_finite` says that $S$ is finitely presented as a module if and only if it is finitely presented as an algebra.

#### Descent along a faithfully flat map

The module `Mathlib.RingTheory.Finiteness.Descent` proves that finiteness descends along a faithfully flat algebra $R \to T$. If $T \otimes_R M$ is a finite $T$-module, then $M$ is a finite $R$-module, `Module.Finite.of_finite_tensorProduct_of_faithfullyFlat`. The same holds for ideals, `Ideal.FG.of_FG_map_of_faithfullyFlat`, and for algebras of finite type and of finite presentation, `Algebra.FiniteType.of_finiteType_tensorProduct_of_faithfullyFlat` and `Algebra.FinitePresentation.of_finitePresentation_tensorProduct_of_faithfullyFlat`. The idea for modules: take finitely many elements of $M$ whose images generate $T \otimes_R M$. The cokernel $C$ of the map from $R^n$ to $M$ then has $T \otimes_R C = 0$, so $C = 0$ by faithful flatness.

#### Modules of finite length

The module `Mathlib.RingTheory.FiniteLength` defines `IsFiniteLength R M` inductively: the zero module has finite length, and $M$ has finite length when a submodule $N$ with $M/N$ simple has finite length. So $M$ has finite length when it has a composition series, `isFiniteLength_iff_exists_compositionSeries`. The main result is `isFiniteLength_iff_isNoetherian_isArtinian`: a module has finite length if and only if it is Noetherian and Artinian.

**Proof sketch.** A module with a composition series of length $n$ has all its chains of submodules of length at most $n$, by the Jordan-Hölder theorem, so both chain conditions hold. Conversely, let $M$ be Noetherian and Artinian. By the Noetherian condition, every nonzero submodule $N$ has a maximal proper submodule $N'$, and $N/N'$ is simple. Start with $M_0 = M$ and choose $M_{i+1}$ maximal in $M_i$. The chain $M_0 \supsetneq M_1 \supsetneq \cdots$ must stop by the Artinian condition, and it stops only at $0$. This gives a composition series. $\square$

For a semisimple module, `IsSemisimpleModule.finite_tfae` gives five equivalent conditions: finite, Noetherian, Artinian, of finite length, and a finite direct sum of simple modules.

#### Bases in towers

The module `Mathlib.RingTheory.AlgebraTower` has the bases of a tower $R \to S \to A$. Given a basis $(b_i)$ of $S$ over $R$ and a basis $(c_j)$ of $A$ over $S$, the products $b_ic_j$ form a basis of $A$ over $R$. This is `Module.Basis.smulTower`, indexed by $\iota \times \iota'$, with `Module.Basis.smulTower_apply` for its vectors and `Module.Basis.smulTower_repr` for its coordinates. The version `Module.Basis.smulTower'` uses the index $\iota' \times \iota$. The underlying statement on independence is `linearIndependent_smul`.

**Proof of `Module.Basis.smulTower`.** The products span $A$ by the argument of `Module.Finite.trans`. For independence, suppose $\sum_{i,j} r_{ij}b_ic_j = 0$. Group the terms as $\sum_j \big(\sum_i r_{ij}b_i\big)c_j = 0$. The $c_j$ are independent over $S$, so $\sum_i r_{ij}b_i = 0$ for each $j$. The $b_i$ are independent over $R$, so each $r_{ij} = 0$. $\square$

The same module has `Module.Basis.algebraMapCoeffs`, which moves a basis over $R$ to a basis over $A$ when `algebraMap R A` is bijective, and the restriction maps `AlgHom.restrictDomain` and `AlgHom.extendScalars` for algebra maps out of a tower. The equivalence `algHomEquivSigma` splits an $R$-algebra map $C \to D$ into a map $B \to D$ and a $B$-algebra map $C \to D$.

#### Common errors

1. `Module.Finite R M` is about generation, not about the number of elements. The type $M$ can be infinite. For a finite type, use `Finite M`, and use `Module.finite_iff_finite` over a finite ring.
2. A submodule $N$ is not a module until it is coerced to a type. To use an instance such as `Module.Finite R N`, move between `Submodule.FG` and the class with `Module.Finite.iff_fg`.
3. A submodule of a finite module need not be finite. This needs a Noetherian hypothesis, as in Volume 9. Do not expect `Module.Finite R N` from `Module.Finite R M` alone.

### Exercises

1. (A) Prove that a quotient of a finitely generated ideal is finitely generated with `Ideal.FG.map`.
2. (A) Show that $\mathbb{Q}$ is not a finite $\mathbb{Z}$-module, but that every finitely generated submodule of $\mathbb{Q}$ is cyclic.
3. (B) Let $I = (x_1, \dots, x_k)$ with $x_i^2 = 0$ for all $i$. Find the smallest $n$ that the proof of `Ideal.exists_pow_le_of_le_radical_of_fg` gives with $I^n = 0$, and show that it is sharp for $k = 2$.
4. (B) Show that $\mathbb{Z}/p^n\mathbb{Z}$ has finite length $n$ as a $\mathbb{Z}$-module, and that $\mathbb{Z}$ has no finite length.
5. (B) Use `Module.Basis.smulTower` to show that $[L : K] = [L : F][F : K]$ for fields $K \subseteq F \subseteq L$.
6. (C) Let $M$ be finite over a commutative ring and $f : M \to M$ an endomorphism. Show that $f$ is nilpotent if and only if every $m \in M$ has $f^n(m) = 0$ for some $n$, and find a counterexample for a module that is not finite.

### Reference

<?reference?>
