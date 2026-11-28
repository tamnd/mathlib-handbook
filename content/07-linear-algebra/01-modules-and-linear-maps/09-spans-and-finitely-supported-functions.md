---
title: Spans, linear combinations and functions of finite support
kind: api
modules:
  - Mathlib.LinearAlgebra.Span.Basic
  - Mathlib.LinearAlgebra.Span.TensorProduct
  - Mathlib.LinearAlgebra.FiniteSpan
  - Mathlib.LinearAlgebra.Countable
  - Mathlib.LinearAlgebra.Finsupp.Defs
  - Mathlib.LinearAlgebra.Finsupp.LSum
  - Mathlib.LinearAlgebra.Finsupp.LinearCombination
  - Mathlib.LinearAlgebra.Finsupp.Pi
  - Mathlib.LinearAlgebra.Finsupp.Span
  - Mathlib.LinearAlgebra.Finsupp.SumProd
  - Mathlib.LinearAlgebra.Finsupp.Supported
  - Mathlib.LinearAlgebra.Finsupp.VectorSpace
  - Mathlib.LinearAlgebra.DFinsupp
explains:
  E2: [LinearMap.toSpanSingleton, LinearMap.map_span, LinearMap.ext_on, Finsupp.linearCombination, Finsupp.range_linearCombination, Finsupp.mem_span_iff_linearCombination, Finsupp.lsum, Finsupp.supported, Submodule.mem_iSup_iff_exists_dfinsupp, iSupIndep_iff_linearIndependent_of_ne_zero]
  E1: auto
families: []
requires: [V03, V04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Spans, linear combinations and functions of finite support

### Overview

Section 1 defines the span of a set $s$ as the smallest submodule that contains $s$. A second description is often more useful: the span is the set of the finite linear combinations $\sum_k c_k v_k$ with $v_k \in s$. Mathlib encodes a finite linear combination as a function of finite support $c : \alpha \to_0 R$, a coefficient for each index with only finitely many nonzero coefficients. The type `α →₀ M` of such functions is the free module on $\alpha$ when $M = R$, and the linear map $c \mapsto \sum_a c_a v_a$ is `Finsupp.linearCombination`.

This section describes three groups of files. The first group, `Mathlib.LinearAlgebra.Span.Basic` with its companions, collects the facts about spans and linear maps: images of spans, extensionality on a spanning set, and the span of one vector. The second group, the eight `Finsupp` files, gives the module structure of `α →₀ M`, its linear maps and its submodules, and the description of spans by linear combinations. The third, `Mathlib.LinearAlgebra.DFinsupp`, treats the dependent version `Π₀ i, M i` and uses it for sums of families of submodules and their independence. Chapter 2 builds bases on these files.

### The library around it

#### Spans and linear maps

The module `Mathlib.LinearAlgebra.Span.Basic` relates spans to linear maps. A linear map carries the span of a set onto the span of its image.

**Proposition (`LinearMap.map_span`).** For a linear map $f : M \to M_2$ and a set $s \subseteq M$, $f(\operatorname{span} s) = \operatorname{span} f(s)$.

*Proof.* The image $f(\operatorname{span} s)$ is a submodule that contains $f(s)$, so it contains $\operatorname{span} f(s)$. The preimage of $\operatorname{span} f(s)$ is a submodule that contains $s$, so it contains $\operatorname{span} s$. $\square$

The same fact read from right to left is `Submodule.span_image`, and `Submodule.map_span` is a copy in the namespace of submodules. The inequality `LinearMap.span_preimage_le` gives the weaker statement for preimages. The lemma `Submodule.apply_mem_span_image_of_mem_span` is the form for elements.

A linear map is determined by its values on a spanning set. The lemma `LinearMap.ext_on` says: if $\operatorname{span} s = M$ and $f = g$ on $s$, then $f = g$. Its proof applies the induction principle of the span to the set where $f$ and $g$ agree, a submodule. The lemmas `LinearMap.eqOn_span` and `LinearMap.eqOn_span_iff` give the local form, and `Submodule.linearMap_eq_iff_of_span_eq_top` the form with an equivalence.

The span of one vector $x$ is the line $R x$, with the notation `R ∙ x`. It is the range of a linear map from $R$.

**Definition (`LinearMap.toSpanSingleton`).** For $x \in M$, the map `LinearMap.toSpanSingleton R M x : R →ₗ[R] M` sends $c$ to $c \cdot x$.

The lemma `LinearMap.span_singleton_eq_range` says that $R x$ is its range, and `LinearMap.toSpanSingleton_apply` computes it. Over a domain, a nonzero $x$ in a torsion free module gives an injective map (`LinearMap.ker_toSpanSingleton`), so the line is isomorphic to $R$: this is `LinearEquiv.toSpanNonzeroSingleton`, and its inverse `LinearEquiv.coord` reads off the coefficient of $x$. Each map out of $R$ is of this form, since `LinearMap.smulRight_id` and `LinearMap.toSpanSingleton_eq_zero_iff` reduce the question to the image of $1$.

Over a field the lines control the order of submodules. The lemma `Submodule.covBy_span_singleton_sup` says that $s \subsetneq s + K x$ is a covering relation when $x \notin s$: there is no submodule strictly between them. A hyperplane is a coatom of the lattice, and `Submodule.isCoatom_iff_exists_notMem_isCompl_span_singleton` says that $s$ is a coatom if and only if some line $K x$ is a complement of $s$. The lemmas `Submodule.finite_span_isCompactElement` and `Submodule.singleton_span_isCompactElement` say that finitely generated submodules are compact elements of the lattice, the fact behind the use of the lemma of Zorn on submodules. The file also has the product of submodules `Submodule.prod` with its lattice lemmas `Submodule.prod_sup_prod` and `Submodule.prod_inf_prod`, and the comparison `AddSubgroup.toIntSubmodule_closure` between the subgroup generated by a set and its $\mathbb{Z}$-span.

Three small modules sit next to this one. `Mathlib.LinearAlgebra.Span.TensorProduct` compares the $A$-span of an $R$-submodule $p$ with the base change $A \otimes_R p$: the map `Submodule.tensorToSpan` is surjective, and `Submodule.tensorEquivSpan` is an equivalence when $A$ is flat over $R$ and $R \to A$ is an epimorphism of rings. `Mathlib.LinearAlgebra.FiniteSpan` proves `LinearEquiv.isOfFinOrder_of_finite_of_span_eq_top_of_mapsTo`: a linear automorphism that permutes a finite spanning set has finite order, because it is determined by a permutation of that set. `Mathlib.LinearAlgebra.Countable` proves that a finite module over a countable ring is countable (`Countable.of_moduleFinite`), and `Uncountable.of_moduleFinite` says that the ring is uncountable when a finite module over it is uncountable.

#### The module of functions of finite support

The type `α →₀ M` is a module with the pointwise operations, and the module `Mathlib.LinearAlgebra.Finsupp.Defs` gives its linear structure maps. They follow a naming pattern: the letter l in front of a name of the `Finsupp` API marks the linear version.

| Lean name | Statement |
|---|---|
| `Finsupp.lsingle a` | the linear map $m \mapsto$ the function $a \mapsto m$, zero elsewhere |
| `Finsupp.lapply a` | the evaluation $f \mapsto f(a)$ |
| `Finsupp.lmapDomain M R g` | the push forward along $g : \alpha \to \alpha'$, summing the fibres |
| `Finsupp.lcomapDomain` | the pull back along an injective map |
| `Finsupp.mapRange.linearMap` | applies a linear map to each value |
| `Finsupp.linearEquivFunOnFinite` | `α →₀ M` is `α → M` when $\alpha$ is finite |
| `Finsupp.curryLinearEquiv` | $(\alpha \times \beta \to_0 M) \simeq (\alpha \to_0 \beta \to_0 M)$ |
| `Finsupp.sumFinsuppLEquivProdFinsupp` | $(\alpha \sqcup \beta \to_0 M) \simeq (\alpha \to_0 M) \times (\beta \to_0 M)$ |
| `Finsupp.sigmaFinsuppLEquivPiFinsupp` | the same for a finite sigma type |

The extensionality lemma `Finsupp.lhom_ext` says that two linear maps out of `α →₀ M` agree when they agree on each single function `Finsupp.single a b`. The universal property comes from `Mathlib.LinearAlgebra.Finsupp.LSum`.

**Proposition (`Finsupp.lsum`).** A family of linear maps $f_a : M \to N$, one for each $a \in \alpha$, gives one linear map $\alpha \to_0 M \to N$, $g \mapsto \sum_a f_a(g(a))$. This is a linear equivalence between the families and the maps.

*Proof sketch.* The sum is finite because $g$ has finite support. The inverse sends $F$ to the family $F \circ \mathrm{lsingle}_a$. The two composites are identities by `Finsupp.lhom_ext` and by the decomposition of $g$ as the finite sum of its single functions. $\square$

For $M = R$, a linear map out of $\alpha \to_0 R$ is the same as a function $\alpha \to N$: this is `Finsupp.lift`, the statement that $\alpha \to_0 R$ is the free module on $\alpha$. The equivalences `Finsupp.lcongr` and `Finsupp.domLCongr` transport along equivalences of the index type and of the values. The map `LinearMap.splittingOfFinsuppSurjective` is a section of a surjection onto a free module $\alpha \to_0 R$, the proof that free modules are projective. The ring isomorphism `Module.End.ringEquivEndFinsupp` and `Submodule.mulLeftMap` are more special tools.

#### Linear combinations

The module `Mathlib.LinearAlgebra.Finsupp.LinearCombination` defines the map that every later file uses.

**Definition (`Finsupp.linearCombination`).** For a family $v : \alpha \to M$, the map `Finsupp.linearCombination R v : (α →₀ R) →ₗ[R] M` sends $c$ to $\sum_a c_a \, v_a$.

The lemma `Finsupp.linearCombination_single` computes it on a single function, $c \cdot v_a$, and `Finsupp.linearCombination_apply` writes it as a `Finsupp.sum`. The theorem that ties it to spans is short.

**Theorem (`Finsupp.range_linearCombination`).** The range of `Finsupp.linearCombination R v` is the span of the range of $v$.

*Proof.* The range is a submodule. It contains each $v_a$, the image of the single function at $a$ with value $1$, so it contains the span. Each value $\sum_a c_a v_a$ is a finite sum of multiples of vectors of the range of $v$, so it lies in the span. $\square$

Applied to the inclusion of a set, it gives `Finsupp.mem_span_iff_linearCombination`: $x \in \operatorname{span} s$ if and only if $x$ is the linear combination of the elements of $s$ with some coefficients of finite support. The lemmas `Submodule.mem_span_set`, `Finsupp.mem_span_range_iff_exists_finsupp`, `Submodule.mem_span_finset` and `Submodule.mem_span_iff_exists_finset_subset` restate this with other encodings of the coefficients, the last ones with a `Finset` and an ordinary function. For a finite index type, `Fintype.linearCombination R v` takes coefficients in `α → R`, and `Finsupp.linearCombination_eq_fintype_linearCombination` compares the two maps. The lemma `Finsupp.linearCombination_comp` says how the map changes when the family is precomposed, and `Finsupp.linearCombination_linearCombination` says that a combination of combinations is a combination. The map `Span.repr` chooses coefficients for each vector of a span.

#### Supports and submodules

The module `Mathlib.LinearAlgebra.Finsupp.Supported` defines `Finsupp.supported M R s`, the submodule of the functions with support in $s$ (`Finsupp.mem_supported`). It is the span of the single functions at the points of $s$ (`Finsupp.supported_eq_span_single`), it is isomorphic to `s →₀ M` (`Finsupp.supportedEquivFinsupp`), and the map `Finsupp.restrictDom` restricts a function to $s$. The operation $s \mapsto$ `Finsupp.supported M R s` is a lattice homomorphism: `Finsupp.supported_union`, `Finsupp.supported_inter` and `Finsupp.supported_iUnion` hold, and `Finsupp.disjoint_supported_supported` says that disjoint sets give disjoint submodules. Linear independence uses these lemmas: a family is independent on a set $s$ when the linear combination map is injective on `Finsupp.supported R R s`.

The module `Mathlib.LinearAlgebra.Finsupp.Span` adds `Finsupp.iSup_lsingle_range`, the statement that the copies of $M$ at the points of $\alpha$ span `α →₀ M`, and `Finsupp.span_single_eq_top`. The module `Mathlib.LinearAlgebra.Finsupp.Pi` compares functions of finite support with all functions: `Finsupp.lcoeFun` is the linear inclusion, `Finsupp.submodule` is the submodule of functions with values in a family of submodules, and `FunOnFinite.linearMap` pushes functions on a finite type forward. The module `Mathlib.LinearAlgebra.Finsupp.VectorSpace` gives the bases: `Finsupp.basisSingleOne` is the standard basis of $\alpha \to_0 R$, `Finsupp.basis` combines bases of $M$ into a basis of $\alpha \to_0 M$, and `Module.Free.finsupp` records that `ι →₀ M` is free when $M$ is free.

#### Dependent functions and sums of submodules

The type `Π₀ i, M i` holds the dependent functions of finite support, and it is the direct sum $\bigoplus_i M_i$. The module `Mathlib.LinearAlgebra.DFinsupp` gives the same API as for `Finsupp`, with the same names in the namespace `DFinsupp`: `DFinsupp.lsingle`, `DFinsupp.lapply`, `DFinsupp.lsum`, `DFinsupp.lhom_ext`, `DFinsupp.mapRange.linearMap` and `DFinsupp.linearEquivFunOnFintype`. The map `DFinsupp.coprodMap` is the form of `DFinsupp.lsum` for a target without a commuting action.

The main use is the description of a sum of submodules. Let $(p_i)_{i \in \iota}$ be a family of submodules of $N$.

**Proposition (`Submodule.mem_iSup_iff_exists_dfinsupp`).** An element $x$ lies in $\sum_i p_i$ if and only if $x = \sum_i x_i$ for a family $x_i \in p_i$ with only finitely many nonzero terms.

*Proof sketch.* The set of such sums is the range of the map $\bigoplus_i p_i \to N$ that sums the inclusions, so it is a submodule (`Submodule.iSup_eq_range_dfinsupp_lsum`). It contains each $p_i$, and it lies in each submodule that contains all $p_i$. So it is the supremum. $\square$

The form `Submodule.mem_iSup_iff_exists_finsupp` uses a nondependent function, and `Submodule.mem_iSup_finset_iff_exists_sum` treats a finite set of indices. The family is independent, `iSupIndep p`, when each $p_i$ meets the sum of the others only in $0$. The library proves that this means that the summing map is injective (`iSupIndep_iff_dfinsupp_lsum_injective`), or that a finite sum $\sum_i v_i = 0$ with $v_i \in p_i$ forces all $v_i = 0$ (`iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero`). An independent family that spans $N$ gives an equivalence $\bigoplus_i p_i \simeq N$, `iSupIndep.linearEquiv`.

**Proposition (`iSupIndep_iff_linearIndependent_of_ne_zero`).** Let $R$ be a domain, let $N$ be torsion free, and let $v_i \neq 0$ for each $i$. The lines $R v_i$ are independent if and only if the family $v$ is linearly independent.

The proof compares the two criteria above: a relation $\sum_i c_i v_i = 0$ is a vanishing sum of vectors of the lines. The direction from the lines to the family is `iSupIndep.linearIndependent`.

#### Common errors

1. `Finsupp.linearCombination R v` takes the ring $R$ as an explicit argument, and its domain is `α →₀ R`, not `α → R`. For a finite index type and an ordinary function of coefficients, use `Fintype.linearCombination`.
2. The linear maps of `Finsupp` and of `DFinsupp` have the same short names. A proof about `Π₀ i, M i` that uses `Finsupp.lsum` fails with a type mismatch; the open namespace decides which one Lean picks.
3. `iSupIndep p` is independence of submodules. It does not say that a family of vectors is linearly independent. The bridge is `iSupIndep_iff_linearIndependent_of_ne_zero`, and it needs the vectors to be nonzero.

### Exercises

1. (A) Show that $f(\operatorname{span}\{x, y\}) = \operatorname{span}\{f x, f y\}$ for a linear map $f$, with `LinearMap.map_span`.
2. (A) Compute `Finsupp.linearCombination ℚ v c` for $v = (e_1, e_1 + e_2)$ in $\mathbb{Q}^2$ and $c$ the function with $c(0) = 2$, $c(1) = -1$.
3. (B) Prove that `Finsupp.supported M R s ⊓ Finsupp.supported M R t` is `Finsupp.supported M R (s ∩ t)`.
4. (B) Show that two linear maps $\mathbb{Q}^2 \to \mathbb{Q}$ that agree on $(1, 1)$ and $(1, -1)$ are equal, with `LinearMap.ext_on`.
5. (B) Show that the three lines spanned by $(1, 0)$, $(0, 1)$ and $(1, 1)$ in $\mathbb{Q}^2$ are not independent, although any two of them are.
6. (C) Prove that a finitely generated module over a countable ring is countable, by writing it as the image of $R^n$.

### Reference

<?reference?>
