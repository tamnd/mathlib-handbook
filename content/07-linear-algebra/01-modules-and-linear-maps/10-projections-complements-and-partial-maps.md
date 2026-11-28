---
title: Projections, complements and partially defined linear maps
kind: api
modules:
  - Mathlib.LinearAlgebra.Projection
  - Mathlib.LinearAlgebra.FixedSubmodule
  - Mathlib.LinearAlgebra.LinearPMap
explains:
  E2: [Submodule.prodEquivOfIsCompl, Submodule.projectionOnto, Submodule.projection, Submodule.quotientEquivOfIsCompl, Submodule.isComplEquivProj, LinearMap.IsProj, LinearMap.isIdempotentElem_iff_eq_projection_range_ker, LinearMap.ofIsCompl, LinearMap.fixedSubmodule, LinearPMap]
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

## Projections, complements and partially defined linear maps

### Overview

Two submodules $p$ and $q$ of a module $E$ are *complements* when $p \cap q = 0$ and $p + q = E$. In the lattice of submodules this is the order relation `IsCompl p q`, and the library uses that general predicate. A complement gives a decomposition $E \cong p \times q$, a projection of $E$ onto $p$ along $q$, and an isomorphism $E / p \cong q$. Conversely, an idempotent linear endomorphism $f$, one with $f \circ f = f$, splits $E$ into its range and its kernel. The module `Mathlib.LinearAlgebra.Projection` states these facts in Lean.

This section also describes two smaller topics that use the same tools. The module `Mathlib.LinearAlgebra.FixedSubmodule` defines the submodule of the fixed vectors of an endomorphism. The module `Mathlib.LinearAlgebra.LinearPMap` defines *partially defined* linear maps: a submodule of $E$, the domain, with a linear map from it to $F$. Partial maps order by extension, and that order is the frame for the proofs by the lemma of Zorn that extend a linear map step by step. The topological versions, with closed operators and topological complements, are in volume 14.

Over a field each submodule has a complement, so each section of this file applies to all subspaces of a vector space. Over a general ring a complement need not exist: the submodule $2\mathbb{Z}$ of $\mathbb{Z}$ has none. Most statements here take a proof of `IsCompl p q` as an argument and need a ring, not a semiring, because the proofs subtract vectors.

### The library around it

#### Complements and decompositions

Let $R$ be a ring and let $p$, $q$ be submodules of $E$ with `h : IsCompl p q`. The sum map $p \times q \to E$, $(x, y) \mapsto x + y$, is injective because $p \cap q = 0$ and surjective because $p + q = E$.

**Definition (`Submodule.prodEquivOfIsCompl`).** The linear equivalence `Submodule.prodEquivOfIsCompl p q h : (p × q) ≃ₗ[R] E` is the sum map.

The lemma `Submodule.coe_prodEquivOfIsCompl` says that its underlying map is `p.subtype.coprod q.subtype`, with `LinearMap.coprod` from Section 8. Read pointwise, the equivalence says that each $x \in E$ is $u + v$ with unique $u \in p$ and $v \in q$: this is `Submodule.existsUnique_add_of_isCompl`. The lemma `Submodule.prodComm_trans_prodEquivOfIsCompl` says that the order of $p$ and $q$ is a matter of a swap.

The first component of the inverse equivalence is the projection.

**Definition (`Submodule.projectionOnto`).** `Submodule.projectionOnto p q h : E →ₗ[R] p` sends $u + v$ to $u$, for $u \in p$ and $v \in q$.

The projection is the identity on $p$ (`Submodule.projectionOnto_apply_left`) and zero on $q$ (`Submodule.projectionOnto_apply_right`), and these two properties determine it. Its kernel is $q$ (`Submodule.ker_projectionOnto`) and it is surjective (`Submodule.range_projectionOnto`). The projection lands in the subtype $p$. For the endomorphism of $E$ use `Submodule.projection p q h : E →ₗ[R] E`, its composite with the inclusion. This version can be compared with other endomorphisms, and it is idempotent (`Submodule.isIdempotentElem_projection`). The sum of the two projections is the identity (`Submodule.projection_add_projection_eq_id`), so `Submodule.projection_eq_id_sub_projection` gives one from the other. The lemma `Submodule.projection_eq_self_iff` says that $x$ is fixed by the projection if and only if $x \in p$.

The library also has `LinearMap.linearProjOfIsCompl`, a projection onto the image of an injective map $i : F \to E$, with target $F$. It exists for definitional control over the type of the target; its kernel is $q$ by `LinearMap.ker_linearProjOfIsCompl`.

A complement of $p$ is isomorphic to the quotient by $p$.

**Proposition (`Submodule.quotientEquivOfIsCompl`).** If `IsCompl p q`, then $E / p \cong q$.

*Proof.* The projection of $E$ onto $q$ along $p$ is surjective and has kernel $p$. The first isomorphism theorem gives the equivalence. In Lean the forward map is `Submodule.liftQ` applied to that projection (`Submodule.toLinearMap_quotientEquivOfIsCompl`), and the inverse is $q \to E \to E / p$ (`Submodule.toLinearMap_symm_quotientEquivOfIsCompl`). $\square$

The data of a complement is the same as the data of a projection.

**Proposition (`Submodule.isComplEquivProj`).** The complements $q$ of $p$ correspond one to one to the linear maps $f : E \to p$ with $f(x) = x$ for $x \in p$. The correspondence sends $q$ to the projection along $q$, and $f$ to its kernel.

The equivalence `Submodule.isIdempotentElemEquiv` gives the same correspondence with the idempotent endomorphisms of $E$ whose range is $p$. A consequence is `LinearMap.surjective_comp_subtype_of_isComplemented`: when $p$ has a complement, each linear map $p \to M$ extends to $E$.

Maps out of $E$ can be glued from maps out of $p$ and $q$.

**Definition (`LinearMap.ofIsCompl`).** For $\varphi : p \to F$ and $\psi : q \to F$, the map `LinearMap.ofIsCompl h φ ψ : E →ₗ[R] F` sends $u + v$ to $\varphi(u) + \psi(v)$.

It is characterised by `LinearMap.ofIsCompl_apply_left` and `LinearMap.ofIsCompl_apply_right`, and it is unique by `LinearMap.ofIsCompl_eq`. Its range is $\varphi(p) + \psi(q)$ (`LinearMap.range_ofIsCompl`). Over a commutative ring, `LinearMap.ofIsComplProdEquiv` is the linear equivalence $\operatorname{Hom}(p, F) \times \operatorname{Hom}(q, F) \simeq \operatorname{Hom}(E, F)$. In the other direction, `LinearMap.equivProdOfSurjectiveOfIsCompl` says that two surjections $f : E \to F$ and $g : E \to G$ with complementary kernels give $E \cong F \times G$.

#### Idempotents and the predicate `LinearMap.IsProj`

The predicate `LinearMap.IsProj p f` says that $f : M \to M$ maps $M$ into $p$ and fixes each element of $p$. It accepts any type of functions with a coercion, so it applies also to continuous linear maps and to matrices. The fields are `LinearMap.IsProj.map_mem` and `LinearMap.IsProj.map_id`, and `LinearMap.IsProj.mem_iff_map_id` says that $p$ is the set of fixed points. The lemma `LinearMap.isProj_iff_isIdempotentElem` says that $f$ is a projection onto some submodule if and only if $f$ is idempotent, and `LinearMap.isProj_range_iff_isIdempotentElem` fixes the submodule as the range of $f$.

**Theorem (`LinearMap.isIdempotentElem_iff_eq_projection_range_ker`).** An endomorphism $T$ of a module over a ring is idempotent if and only if its range and its kernel are complements and $T$ is the projection onto the range along the kernel.

*Proof.* Let $T^2 = T$. Each $x$ is $T x + (x - T x)$, with $T x$ in the range and $T(x - T x) = 0$. If $y = T z$ is in the kernel, then $y = T z = T^2 z = T y = 0$. So range and kernel are complements, and $T$ agrees with the projection on both of them. The converse holds because each projection is idempotent. $\square$

The lemma `LinearMap.IsIdempotentElem.isCompl` is the first half of the theorem. With it, `LinearMap.IsIdempotentElem.ker_eq_range_one_sub` and `LinearMap.IsIdempotentElem.range_eq_ker_one_sub` relate $T$ and $1 - T$, and `LinearMap.IsIdempotentElem.ext` says that two idempotents with the same range and the same kernel are equal. The lemma `LinearMap.IsIdempotentElem.commute_iff` says that an idempotent $f$ commutes with $T$ if and only if the range and the kernel of $f$ are invariant under $T$. Invariant submodules are the topic of Chapter 5.

#### Fixed vectors of an endomorphism

The module `Mathlib.LinearAlgebra.FixedSubmodule` is short. The submodule `LinearMap.fixedSubmodule f` holds the vectors $v$ with $f v = v$ (`LinearMap.mem_fixedSubmodule_iff`). It is the kernel of $f - \mathrm{id}$ (`LinearMap.fixedSubmodule_eq_ker`), it is the whole module only for the identity (`LinearMap.fixedSubmodule_eq_top_iff`), and a vector fixed by $f$ and by $g$ is fixed by $f \circ g$ (`LinearMap.fixedSubmodule_inf_fixedSubmodule_le_comp`).

For a linear automorphism $e$ the file looks at the action on quotients. The map `LinearEquiv.reduce W` is a group homomorphism from the stabilizer of a submodule $W$ to the automorphisms of $V / W$. An automorphism stabilizes its own fixed submodule (`LinearEquiv.mem_stabilizer_fixedSubmodule`), so it induces `LinearEquiv.fixedReduce e` on $V$ modulo the fixed vectors. The lemma `LinearEquiv.fixedReduce_eq_one` says that this induced map is the identity if and only if $e v - v$ is fixed for each $v$. In that case $e - 1$ has square zero, and $e$ is a transvection in the wide sense. The lemma `LinearEquiv.fixedReduce_eq_smul_iff` treats the case where the induced map is a scalar.

#### Partially defined linear maps

A term `f : E →ₗ.[R] F` of type `LinearPMap R E F` has a submodule `LinearPMap.domain f` of $E$ and a linear map `f.toFun : f.domain →ₗ[R] F`. The coercion applies $f$ to elements of the subtype, so `f x` needs `x : f.domain`. The order `f ≤ g` says that $g$ extends $f$: the domain of $f$ is in the domain of $g$, and the two maps agree there. The lemma `LinearPMap.exists_of_le` unfolds this order. Partial maps form a semilattice under `⊓`, where the meet is defined on the set `LinearPMap.eqLocus f g` where the two maps agree, with least element `LinearPMap.bot`.

The basic constructions are these.

| Lean name | Domain | Value |
|---|---|---|
| `LinearMap.toPMap f p` | $p$ | $f$ restricted to $p$ |
| `LinearPMap.mkSpanSingleton x y h` | $K x$ | $c x \mapsto c y$, over a division ring, for $x \neq 0$ |
| `LinearPMap.sup f g h` | $f.\mathrm{domain} + g.\mathrm{domain}$ | $u + v \mapsto f u + g v$ |
| `LinearPMap.supSpanSingleton f x y hx` | $f.\mathrm{domain} + K x$ | $u + c x \mapsto f u + c y$ |
| `LinearPMap.sSup c hc` | union of a directed family | the common extension |
| `LinearPMap.domRestrict f p` | $f.\mathrm{domain} \cap p$ | $f$ |

The sum `LinearPMap.sup` needs a proof that $f$ and $g$ agree on the intersection of the domains; `LinearPMap.sup_h_of_disjoint` gives it when the domains meet only in $0$. The lemma `LinearPMap.sup_apply` computes the result, and `LinearPMap.left_le_sup` and `LinearPMap.right_le_sup` say that it extends both maps. The supremum `LinearPMap.sSup` of a directed set has the union as domain (`LinearPMap.domain_sSup`) and is the least upper bound by `LinearPMap.le_sSup` and `LinearPMap.sSup_le`. These are the two steps of the usual extension proof: `LinearPMap.supSpanSingleton` extends a map by one vector outside its domain, and `LinearPMap.sSup` gives an upper bound to each chain, so the lemma of Zorn gives a maximal extension, which must be defined everywhere. The Hahn and Banach theorem in volume 14 follows this plan.

A partial map is also a submodule of $E \times F$, its graph `LinearPMap.graph f`, with membership `LinearPMap.mem_graph_iff`. The order of partial maps is the inclusion of graphs (`LinearPMap.le_graph_iff`), and the first projection of the graph is the domain (`LinearPMap.graph_map_fst_eq_domain`). Conversely, `Submodule.toLinearPMap g` turns a submodule $g \subseteq E \times F$ into a partial map. If $g$ has no element of the form $(0, y)$ with $y \neq 0$, its graph is $g$ again (`Submodule.toLinearPMap_graph_eq`). The inverse of an injective partial map, `LinearPMap.inverse`, is defined as the partial map of the swapped graph (`LinearPMap.inverse_graph`). The kernel `LinearPMap.ker` and the range follow the API of linear maps, with `LinearPMap.ker_eq_bot` for injectivity.

#### Common errors

1. `Submodule.projectionOnto p q h` has target the subtype $p$, and `Submodule.projection p q h` has target $E$. Statements such as `IsIdempotentElem` or $P + Q = \mathrm{id}$ need the second one.
2. A complement is an explicit proof argument `h : IsCompl p q`. Over a field, obtain one with `Submodule.exists_isCompl`; over a general ring, a submodule may have no complement, and there is no instance to find one.
3. For `f : E →ₗ.[R] F`, the expression `f x` with `x : E` does not typecheck. Give an element of the subtype, as `f ⟨x, hx⟩` with `hx : x ∈ f.domain`.

### Exercises

1. (A) Let $p$ and $q$ be the two coordinate axes of $\mathbb{Q}^2$. Compute `Submodule.projection p q h (3, 5)`.
2. (A) Show that `LinearMap.fixedSubmodule (-LinearMap.id)` on a $\mathbb{Q}$-vector space is $0$.
3. (B) Let $T$ be idempotent. Prove that $1 - T$ is idempotent and that its range is the kernel of $T$.
4. (B) Give two different complements of the line $\mathbb{Q}(1, 0)$ in $\mathbb{Q}^2$, and check that the two projections onto the line differ.
5. (B) Prove that the partial map `LinearPMap.supSpanSingleton f x y hx` sends $x$ to $y$.
6. (C) With `LinearPMap.sSup`, `LinearPMap.supSpanSingleton` and the lemma of Zorn, prove that each linear map from a subspace of a vector space to $F$ extends to the whole space.

### Reference

<?reference?>
