---
title: Bundled continuous maps and the compact-open topology
kind: api
modules:
  - Mathlib.Topology.ContinuousMap.Defs
  - Mathlib.Topology.ContinuousMap.Basic
  - Mathlib.Topology.CompactOpen
  - Mathlib.Topology.ContinuousMap.Compact
  - Mathlib.Topology.ContinuousMap.SecondCountableSpace
  - Mathlib.Topology.ContinuousMap.Sigma
  - Mathlib.Topology.ContinuousMap.T0Sierpinski
  - Mathlib.Topology.ContinuousMap.Interval
  - Mathlib.Topology.ContinuousMap.LocallyConstant
  - Mathlib.Topology.ContinuousMap.CocompactMap
explains:
  E2: [ContinuousMap.isOpen_setOfPred_mapsTo, ContinuousMap.tendsto_compactOpen_iff_forall, ContinuousMap.instContinuousEvalOfLocallyCompactPair, Homeomorph.curry, ContinuousMap.liftCover, ContinuousMap.dist_le, CocompactMap.isCompact_preimage]
  E1: auto
families: []
requires: [V01, V04, V13.C01, V13.C02, V13.C03, V13.C04, V13.C05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Bundled continuous maps and the compact-open topology

### Overview

A continuous map is a function together with a proof that it is continuous. Chapter 1 keeps the two apart: it states `Continuous f` for a bare function `f`. This section puts them together. The structure `ContinuousMap X Y`, written `C(X, Y)`, holds a function and a proof of its continuity. A term of `C(X, Y)` is then one object. It can be an element of a set, a point of a space, or the value of another map.

The section has three parts. The first part gives the structure, its coercion to functions, and the basic maps: the identity, the composition, the constants, the restrictions and the maps into products and out of sums. The second part puts a topology on `C(X, Y)`, the compact-open topology, and studies evaluation, currying and convergence. The third part treats a compact space $X$ and a metric space $Y$. There `C(X, Y)` has the supremum metric, and it is the same space as the bounded continuous functions of Section 3.

The section uses compact sets and local compactness from Chapter 5, and the separation axioms from Chapter 4.

### The library around it

#### The structure and its coercion

The module `Mathlib.Topology.ContinuousMap.Defs` defines the structure `ContinuousMap` with the fields `toFun` and `continuous_toFun`, and the notation `C(X, Y)`. The structure is an instance of `FunLike`, so a term `f : C(X, Y)` is applied to a point as `f x`. The coercion `⇑f` is the simp normal form: the rule `ContinuousMap.toFun_eq_coe` rewrites `f.toFun` to `⇑f`, and `ContinuousMap.coe_mk` evaluates the coercion of an explicit structure. Two maps are equal when they agree at each point (`ContinuousMap.ext`), and the coercion is injective (`ContinuousMap.coe_injective`).

Many bundled maps are continuous: homeomorphisms, continuous linear maps, isometries. The class `ContinuousMapClass F X Y` says that each term of a type `F` with a coercion to functions is continuous. The rule `ContinuousMapClass.map_continuous` gives the continuity, and each such term gives a term of `C(X, Y)` by the coercion `ContinuousMap.ofClass`. Thus a lemma about `C(X, Y)` applies to each class of continuous bundled maps.

The basic maps are `ContinuousMap.id`, `ContinuousMap.const`, `ContinuousMap.comp` and `ContinuousMap.restrict s`, which restricts a map to a subtype $s$. Their values are simp rules, for example `ContinuousMap.comp_apply`: $(f \circ g)(a) = f(g(a))$. The map `ContinuousMap.copy` replaces the function by an equal function, to fix its definitional form. The map `ContinuousMap.mkD f g` is `f` when `f` is continuous and the default `g` otherwise (`ContinuousMap.mkD_of_continuous`).

The module `Mathlib.Topology.ContinuousMap.Basic` gives the maps of products and sums. The maps `ContinuousMap.fst`, `ContinuousMap.snd`, `ContinuousMap.prodMk` and `ContinuousMap.prodMap` treat products, and `ContinuousMap.prodEquiv` is the bijection $C(X, Y_1 \times Y_2) \simeq C(X, Y_1) \times C(X, Y_2)$. For a family of spaces, `ContinuousMap.pi` and `ContinuousMap.piEquiv` treat maps into a product, and `ContinuousMap.sigma` and `ContinuousMap.sigmaEquiv` treat maps out of a disjoint union. A homeomorphism $X \cong X'$ and a homeomorphism $Y \cong Y'$ give a bijection `Homeomorph.continuousMapCongr`.

Maps can be glued. Let $(S_i)$ be a family of sets that covers $X$ in the sense that each point has some $S_i$ as a neighbourhood. Let $\varphi_i \in C(S_i, Y)$ agree on the overlaps. Then `ContinuousMap.liftCover` is the map $f \in C(X, Y)$ with $f = \varphi_i$ on $S_i$. The map is well defined because of the agreement. It is continuous because, near each point $x$, it is equal to the continuous map $\varphi_i$ on the neighbourhood $S_i$ of $x$. The rule `ContinuousMap.liftCover_restrict` says that its restriction to $S_i$ is $\varphi_i$. A quotient map $f$ also lets a map descend: if $g$ factors through $f$, then `Topology.IsQuotientMap.lift` gives the continuous map on the quotient.

#### The compact-open topology

The module `Mathlib.Topology.CompactOpen` puts the compact-open topology on `C(X, Y)`, as the instance `ContinuousMap.compactOpen`. For a compact set $K \subseteq X$ and an open set $U \subseteq Y$, let

$$[K, U] = \{ f \in C(X, Y) \mid f(K) \subseteq U \}.$$

The sets $[K, U]$ form a subbasis of the topology (`ContinuousMap.compactOpen_eq`). In Lean, $f(K) \subseteq U$ is written `Set.MapsTo f K U`, and the rule `ContinuousMap.isOpen_setOfPred_mapsTo` says that $[K, U]$ is open. When $U$ is clopen, $[K, U]$ is clopen (`ContinuousMap.isClopen_setOfPred_mapsTo`). When $X$ is discrete, each compact set is finite, and the topology is the topology of pointwise convergence: `ContinuousMap.homeoFnOfDiscrete` is a homeomorphism $C(X, Y) \cong (X \to Y)$.

Convergence in this topology is uniform convergence on compact sets, in the language of restrictions:

**Theorem.** A family $F_i$ tends to $f$ in `C(X, Y)` along a filter $l$ if and only if, for each compact set $K \subseteq X$, the restrictions $F_i|_K$ tend to $f|_K$ in `C(K, Y)`.

This is `ContinuousMap.tendsto_compactOpen_iff_forall`. The proof uses the form `ContinuousMap.compactOpen_eq_iInf_induced`: the compact-open topology is the infimum over the compact sets $K$ of the topologies induced by the restriction maps to `C(K, Y)`. A limit in an infimum of induced topologies is a limit in each of them. When $X$ is weakly locally compact and $Y$ is Hausdorff, a family converges if and only if its restriction to each compact set converges (`ContinuousMap.exists_tendsto_compactOpen_iff_forall`).

The main fact about the compact-open topology is the continuity of evaluation.

**Theorem.** If $X$ is locally compact, the map $C(X, Y) \times X \to Y$, $(f, x) \mapsto f(x)$, is continuous.

*Proof.* Let $f(x) \in U$ with $U$ open. The set $f^{-1}(U)$ is an open neighbourhood of $x$. Since $X$ is locally compact, it contains a compact neighbourhood $K$ of $x$. Then $[K, U] \times K$ is a neighbourhood of $(f, x)$, and each pair $(g, y)$ in it has $g(y) \in U$. $\square$

The library states this with the class `ContinuousEval`, and the instance is `ContinuousMap.instContinuousEvalOfLocallyCompactPair`. The class `LocallyCompactPair X Y` is the weak form of local compactness that the proof uses. For each fixed point the evaluation is continuous with no hypothesis (`ContinuousMap.instContinuousEvalConst`). With the same hypothesis on the middle space, composition is jointly continuous (`Continuous.compCM`). Composition on one side is always continuous (`ContinuousMap.continuous_postcomp`, `ContinuousMap.continuous_precomp`), and post-composition with an embedding is an embedding (`ContinuousMap.isEmbedding_postcomp`).

The topology passes the separation axioms from $Y$ to `C(X, Y)`: the instances `ContinuousMap.instT0Space`, `ContinuousMap.instT2Space` and `ContinuousMap.instRegularSpace`. If $X$ is locally compact and both spaces are second countable, then `C(X, Y)` is second countable (`ContinuousMap.instSecondCountableTopology`, in `Mathlib.Topology.ContinuousMap.SecondCountableSpace`).

#### Currying

A map $g \in C(X \times Y, Z)$ gives a map $x \mapsto g(x, \cdot)$ from $X$ to `C(Y, Z)`. This is `ContinuousMap.curry`, and it is continuous for the compact-open topology with no hypothesis. The converse `ContinuousMap.uncurry` needs the continuity of evaluation, so it needs $Y$ locally compact. When $X$ and $Y$ are both locally compact, the two maps are inverse homeomorphisms:

$$C(X \times Y, Z) \cong C(X, C(Y, Z)).$$

This is `Homeomorph.curry`. The map `ContinuousMap.coev`, $y \mapsto (x \mapsto (y, x))$, is the unit of this adjunction, and it is continuous (`ContinuousMap.continuous_coev`). A consequence of the same idea: let $f : X_0 \to X$ be a quotient map and let $Y$ be locally compact. If $g \circ (f \times \mathrm{id}_Y)$ is continuous, then $g$ is continuous on $X \times Y$ (`Topology.IsQuotientMap.continuous_lift_prod_left`).

#### Small modules

The module `Mathlib.Topology.ContinuousMap.Sigma` treats maps from a connected space into a disjoint union. Such a map lands in one summand, so `ContinuousMap.sigmaCodHomeomorph` is a homeomorphism $C(X, \Sigma_i Y_i) \cong \Sigma_i C(X, Y_i)$ for a connected space $X$.

The module `Mathlib.Topology.ContinuousMap.T0Sierpinski` sends a point $x$ to the family of the propositions $x \in U$, one for each open set $U$. The target is a product of copies of the Sierpinski space `Prop`. The map `TopologicalSpace.productOfMemOpens` is continuous, and it is an embedding when $X$ is $T_0$ (`TopologicalSpace.productOfMemOpens_isEmbedding`). So each $T_0$ space is a subspace of a power of the Sierpinski space.

The module `Mathlib.Topology.ContinuousMap.Interval` works on closed intervals of a linear order. The map `ContinuousMap.projIccCM` is the projection of the line onto $[a, b]$, and `ContinuousMap.IccExtendCM` extends a map on $[a, b]$ by constants (`ContinuousMap.IccExtendCM_of_mem`). The map `ContinuousMap.concat` joins a map on $[a, b]$ and a map on $[b, c]$ that agree at $b$ into one map on $[a, c]$, as in the concatenation of paths.

The module `Mathlib.Topology.ContinuousMap.LocallyConstant` sees a locally constant function as a continuous map. The maps `LocallyConstant.toContinuousMapMonoidHom`, `LocallyConstant.toContinuousMapLinearMap` and `LocallyConstant.toContinuousMapAlgHom` respect the algebraic structure. On a totally separated space the locally constant functions separate the points (`LocallyConstant.separatesPoints_range_toContinuousMapAlgHom`), which is the hypothesis of the Stone-Weierstrass theorem of Section 2.

#### Cocompact maps

The module `Mathlib.Topology.ContinuousMap.CocompactMap` defines the structure `CocompactMap X Y` of continuous maps that tend to the cocompact filter `Filter.cocompact Y` along `Filter.cocompact X`. In words, $f(x)$ leaves each compact set of $Y$ when $x$ leaves each compact set of $X$. The class `CocompactMapClass` and the maps `CocompactMap.id` and `CocompactMap.comp` follow the pattern of `ContinuousMapClass`.

**Proposition.** If $Y$ is Hausdorff and $f$ is a cocompact map, then $f^{-1}(K)$ is compact for each compact set $K \subseteq Y$.

*Proof sketch.* The set $K$ is closed, since $Y$ is Hausdorff. The complement of $K$ is in the cocompact filter of $Y$, so the complement of $f^{-1}(K)$ is in the cocompact filter of $X$. Thus $f^{-1}(K)$ is contained in a compact set. It is closed, as the preimage of a closed set, so it is compact. $\square$

This is `CocompactMap.isCompact_preimage`. The converse holds with no hypothesis (`CocompactMap.tendsto_of_forall_preimage`). So, between Hausdorff spaces, the cocompact maps are the proper maps.

#### The supremum metric on a compact space

The module `Mathlib.Topology.ContinuousMap.Compact` treats a compact space $X$ and a metric space $Y$. Each continuous map $X \to Y$ is then bounded, so `C(X, Y)` and the bounded continuous functions `X →ᵇ Y` of Section 3 are the same set. The bijection is `ContinuousMap.equivBoundedOfCompact`, and it is an isometry (`ContinuousMap.isometryEquivBoundedOfCompact`). The instance `ContinuousMap.instMetricSpace` gives `C(X, Y)` the supremum distance

$$d(f, g) = \sup_{x \in X} d(f(x), g(x)).$$

The instance keeps the uniform structure of `C(X, Y)`, so its topology is the compact-open topology (`ContinuousMap.isUniformInducing_equivBoundedOfCompact`). The rules for the distance are the rules for a supremum:

| Lean name | Statement |
|---|---|
| `ContinuousMap.dist_apply_le_dist` | $d(f(x), g(x)) \le d(f, g)$ |
| `ContinuousMap.dist_le` | for $C \ge 0$: $d(f, g) \le C \iff \forall x,\ d(f(x), g(x)) \le C$ |
| `ContinuousMap.dist_lt_iff` | for $C > 0$: $d(f, g) < C \iff \forall x,\ d(f(x), g(x)) < C$ |
| `ContinuousMap.norm_eq_iSup_norm` | $\lVert f \rVert = \sup_x \lVert f(x) \rVert$ |
| `ContinuousMap.norm_coe_le_norm` | $\lVert f(x) \rVert \le \lVert f \rVert$ |

The proof of `ContinuousMap.dist_le` is short. The distance is the supremum of the numbers $d(f(x), g(x))$, and a supremum is at most $C$ if and only if each term is at most $C$. The condition $C \ge 0$ covers the case of an empty space, where the supremum is $0$. The strict form needs $C > 0$ for the same reason, and it also uses the compactness: the supremum is attained, so it is less than $C$ when each term is.

When the target is a normed group, ring or algebra, `C(X, Y)` is one too, with the supremum norm: `ContinuousMap.instNormedAddCommGroup`, `ContinuousMap.instNormedRing`, `ContinuousMap.normedSpace`, `ContinuousMap.instNormedAlgebra`, and `ContinuousMap.instCStarRing` for a C*-ring. A series of maps on a locally compact space is summable when its restrictions to each compact set are summable in norm (`ContinuousMap.summable_of_locally_summable_norm`). This is the Weierstrass M-test on compact sets.

#### Common errors

1. Writing `f.toFun x` in a statement. The simp normal form is `f x` with the coercion `⇑f`, and the simp rules of the library do not fire on `f.toFun`. Use `ContinuousMap.toFun_eq_coe` to rewrite.
2. Expecting the topology of pointwise convergence on `C(X, Y)`. The topology is the compact-open topology, and it agrees with pointwise convergence only when the compact sets of $X$ are finite, for example when $X$ is discrete.
3. Looking for the supremum norm on `C(X, E)` for a space $X$ that is not compact. The instance needs `CompactSpace X`. For a general space, use the bounded continuous functions `X →ᵇ E` of Section 3.

### Exercises

1. (A) Prove that `ContinuousMap.comp` is associative and that `ContinuousMap.id` is a unit for it, with `ContinuousMap.ext`.
2. (A) Let $X$ be discrete. Show that each function $X \to Y$ is continuous, and describe the compact sets of $X$.
3. (B) Show that the evaluation map $C(\mathbb{Q}, \mathbb{R}) \times \mathbb{Q} \to \mathbb{R}$ is not continuous at the zero map and a point $q$. Use that each compact subset of $\mathbb{Q}$ has empty interior.
4. (B) Let $X$ be compact and $Y$ a metric space. Show that a sequence of `C(X, Y)` converges in the supremum metric if and only if it converges uniformly.
5. (B) Prove that a map from a connected space into a disjoint union $\Sigma_i Y_i$ lands in one summand.
6. (C) Prove `Homeomorph.curry` on paper for locally compact Hausdorff spaces $X$ and $Y$: show that `ContinuousMap.uncurry` is continuous.

### Reference

<?reference?>
