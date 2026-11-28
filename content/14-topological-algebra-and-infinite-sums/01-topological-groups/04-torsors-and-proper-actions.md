---
title: Torsors, proper actions and asymptotic cones
kind: api
modules:
  - Mathlib.Topology.Algebra.Group.Torsor
  - Mathlib.Topology.Algebra.Group.AddTorsor
  - Mathlib.Topology.Algebra.ProperAction.Basic
  - Mathlib.Topology.Algebra.ProperAction.CompactlyGenerated
  - Mathlib.Topology.Algebra.ProperAction.Torsor
  - Mathlib.Topology.Algebra.ProperAction.AddTorsor
  - Mathlib.Topology.Algebra.ProperConstSMul
  - Mathlib.Topology.Algebra.Constructions.DomMulAct
  - Mathlib.Topology.Algebra.AsymptoticCone
explains:
  E2: [IsTopologicalAddTorsor, Homeomorph.vaddConst, ProperSMul, properSMul_iff, t2Space_quotient_mulAction_of_properSMul, properlyDiscontinuousSMul_iff_properSMul, ProperConstSMul, DomMulAct.mkHomeomorph, asymptoticCone, mem_asymptoticCone_iff]
  E1: auto
families: []
requires: [V05, V13.C01, V13.C04, V13.C05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Torsors, proper actions and asymptotic cones

### Overview

A group can act on a space in many ways. This section collects the parts of the library that study a continuous action of a topological group $G$ on a topological space $X$. The first part treats torsors. A torsor is a space on which $G$ acts freely and transitively, such as an affine space over a vector space. The second part treats proper actions. An action is proper when the map $(g, x) \mapsto (g \cdot x, x)$ is a proper map, and then the orbit space is Hausdorff. The third part treats the weaker condition that each single map $x \mapsto c \cdot x$ is proper.

The section ends with two smaller topics. The type copy `Mᵈᵐᵃ` lets a monoid act on functions through their domain, and it gets the topology of `M`. The asymptotic cone of a subset of an affine space records the directions in which the subset goes to infinity.

### The library around it

#### Topological torsors

An additive torsor `AddTorsor V P` has an action `v +ᵥ p` of the group `V` on `P` and a subtraction `p -ᵥ q : V`. The class `IsTopologicalAddTorsor P` says that both operations are continuous. Its fields are the continuity of `+ᵥ` (as a `ContinuousVAdd V P` instance) and `IsTopologicalAddTorsor.continuous_vsub`. The multiplicative form is `IsTopologicalTorsor`, with the division `p /ₛ q` and the field `IsTopologicalTorsor.continuous_sdiv`. The module `Mathlib.Topology.Algebra.Group.AddTorsor` has no live declarations of its own; the additive results come from `Mathlib.Topology.Algebra.Group.Torsor` by `to_additive`.

A topological additive group is a torsor over itself, by the instance `instIsTopologicalAddTorsor`. Products and Pi types of torsors are torsors. The class also gives facts about the group: if `V` acts on a nonempty `P` as a topological torsor, then `IsTopologicalAddTorsor.to_isTopologicalAddGroup` says that `V` is a topological group.

| Lean name | Statement |
|---|---|
| `Continuous.vsub` | if $f$ and $g$ are continuous, then $x \mapsto f(x) -_v g(x)$ is continuous |
| `Filter.Tendsto.vsub` | the same fact for limits along a filter |
| `Continuous.sdiv` | the multiplicative form of `Continuous.vsub` |
| `Homeomorph.vaddConst` | for $p \in P$, the map $v \mapsto v +_v p$ is a homeomorphism $V \simeq P$ |
| `Homeomorph.constVSub` | for $p \in P$, the map $q \mapsto p -_v q$ is a homeomorphism $P \simeq V$ |
| `Homeomorph.pointReflection` | the reflection $q \mapsto (x -_v q) +_v x$ through $x$ is a homeomorphism |
| `Homeomorph.smulConst` | the multiplicative form of `Homeomorph.vaddConst` |
| `Homeomorph.constSDiv` | the multiplicative form of `Homeomorph.constVSub` |

The homeomorphism `Homeomorph.vaddConst p` transports each topological property of `V` to `P`. This is how the library proves that a torsor is regular and $T_0$ when `V` is a topological group: it uses `IsTopologicalAddTorsor.regularSpace` and `IsTopologicalAddTorsor.t0Space`. A typical proof about an affine space $P$ picks a base point $p$, moves the problem to $V$ with `Homeomorph.vaddConst p`, and solves it there.

#### Proper actions

Let $G$ act on $X$. The class `ProperSMul G X` asks that the map

$$G \times X \to X \times X, \qquad (g, x) \mapsto (g \cdot x, x)$$

is a proper map in the sense of `IsProperMap`. The definition is `properSMul_iff`, and the field is `ProperSMul.isProperMap_smul_pair`. A proper map is continuous, so a proper action is continuous: this is the instance `ProperSMul.toContinuousSMul`. The additive form is `ProperVAdd`, and each result below has a `VAdd` twin.

The main use of the class is the orbit space. The lemma `t2Space_quotient_mulAction_of_properSMul` says that the quotient of $X$ by the orbit relation `MulAction.orbitRel G X` is Hausdorff. The proof is short. The orbit relation is the image of the proper map above, and a proper map has a closed image. The quotient map of a group action is open. A space whose quotient map is open and whose relation is closed has a Hausdorff quotient. The lemma `t2Space_of_properSMul_of_t1Group` gives the second consequence: if $G$ is $T_1$ and acts properly, then $X$ is Hausdorff.

The library has these instances and constructors.

1. A topological group acts properly on itself by left and right translation (`instProperSMulOfIsTopologicalGroup` and `instProperSMulMulOppositeOfIsTopologicalGroup`).
2. A closed subgroup of a group that acts properly also acts properly (`instProperSMulSubtypeMemSubgroupOfIsClosedCoe`).
3. A proper action pulls back along a closed embedding that respects the action (`properSMul_of_isClosedEmbedding`).
4. A topological torsor action is proper, by `instProperSMul` and `instProperVAdd` in `Mathlib.Topology.Algebra.ProperAction.Torsor`. The file `Mathlib.Topology.Algebra.ProperAction.AddTorsor` has no live declarations of its own.

The last fact gives a second proof that $G/H$ is Hausdorff for a closed subgroup $H$: the subgroup $H$ acts properly on $G$, so the orbit space is $T_2$. The library states the result as the instance `QuotientGroup.instT2Space`.

A test with filters is often easier than the definition. The lemma `properSMul_iff_continuousSMul_ultrafilter_tendsto` says that the action is proper if and only if it is continuous and, for each ultrafilter $\mathcal{U}$ on $G \times X$ whose image under $(g, x) \mapsto (g \cdot x, x)$ converges, the first coordinate converges too. On a compact set the lemma `ProperSMul.isCompact_setOfPred_inter_nonempty` gives the usual finiteness property: for compact $K$ and $L$, the set $\{g \mid g K \cap L \ne \emptyset\}$ is compact.

#### Discrete groups and compactly generated spaces

For a discrete group the classical notion is a properly discontinuous action: for compact $K$ and $L$, only finitely many $g$ satisfy $g K \cap L \ne \emptyset$. The module `Mathlib.Topology.Algebra.ProperAction.CompactlyGenerated` compares the two notions. The lemma `properlyDiscontinuousSMul_iff_properSMul` says that `ProperlyDiscontinuousSMul G X` and `ProperSMul G X` are equivalent when $G$ is discrete, $X$ is Hausdorff, each $x \mapsto g \cdot x$ is continuous, and $X \times X$ is a `CompactlyCoherentSpace`. A locally compact Hausdorff space satisfies the last condition. The lemma `MulAction.properSMul_iff_isCompact_setOfPred_inter_nonempty` is the general form for a continuous action: under the same condition on $X \times X$, the action is proper if and only if the set of $g$ with $g K \cap L \ne \emptyset$ is compact for each pair of compact sets.

#### Proper scalar maps

The class `ProperConstSMul M X` is weaker. It only asks that each map $x \mapsto c \cdot x$ is proper, and $M$ needs no topology. The field is `ProperConstSMul.isProperMap_smul`. The practical form is `IsCompact.preimage_smul`: the preimage of a compact set under $x \mapsto c \cdot x$ is compact.

The instances cover the usual cases. A group action with continuous scalar maps has the property, because each $x \mapsto c \cdot x$ is a homeomorphism (`instProperConstSMulOfContinuousConstSMul`). An action on a compact Hausdorff space with continuous scalar maps has it too, because each map from a compact space to a Hausdorff space is proper. Products and Pi types keep the property (`instProperConstSMulProd` and `instProperConstSMulForall`).

#### Action on the domain

The type `Mᵈᵐᵃ` (the structure `DomMulAct M`) is a copy of `M` that acts on functions $f : \alpha \to \beta$ by $(c \cdot f)(a) = f(m \cdot a)$, where $m$ is the element of `M` behind $c$, that is `DomMulAct.mk.symm c`. The module `Mathlib.Topology.Algebra.Constructions.DomMulAct` gives `Mᵈᵐᵃ` the topology of `M`. The main declaration is `DomMulAct.mkHomeomorph : M ≃ₜ Mᵈᵐᵃ`, and the simp lemma `DomMulAct.coe_mkHomeomorph` says that its function is `DomMulAct.mk`. The module transfers each separation and countability axiom by an instance, for example `DomMulAct.instT2Space`, `DomMulAct.instLocallyCompactSpace` and `DomMulAct.instSecondCountableTopology`. It also states the embedding facts `DomMulAct.isEmbedding_mk`, `DomMulAct.isOpenEmbedding_mk` and `DomMulAct.isClosedEmbedding_mk`, and the neighbourhood identity `DomMulAct.map_mk_nhds`.

#### Asymptotic cones

Let $k$ be an ordered field and let $P$ be an affine space over a topological vector space $V$. The filter `AffineSpace.asymptoticNhds k P v` describes the points that go to infinity in the direction $v$. The lemma `AffineSpace.asymptoticNhds_eq_smul_vadd` gives the formula

$$\operatorname{asymptoticNhds}_k(v) = \mathrm{atTop} \cdot \mathcal{N}(v) +_v \{p\},$$

for each base point $p$. In words, a set is in the filter if it contains all the points $t w +_v p$ with $t$ large and $w$ near $v$. The asymptotic cone `asymptoticCone k s` is the set of directions $v$ such that $s$ meets this filter frequently. This is the content of `mem_asymptoticCone_iff`. In $\mathbb{R}^n$ the cone is the set of the limits of $t_n x_n$ with $t_n \to 0^+$ and $x_n \in s$.

| Lean name | Statement |
|---|---|
| `zero_mem_asymptoticCone` | $0$ is in the cone of a nonempty set |
| `asymptoticCone_nonempty` | the cone is nonempty if and only if $s$ is nonempty |
| `smul_mem_asymptoticCone` | the cone is closed under multiplication by $c \ge 0$ |
| `isClosed_asymptoticCone` | the cone is closed |
| `asymptoticCone_closure` | $s$ and its closure have the same cone |
| `asymptoticCone_union` | the cone of $s \cup t$ is the union of the cones |
| `asymptoticCone_mono` | the cone is monotone in $s$ |
| `asymptoticCone_submodule` | the cone of a subspace is its closure |
| `Convex.asymptoticCone` | the cone of a convex set is convex |

The main theorem for convex sets is `Convex.smul_vadd_mem_of_isClosed_of_mem_asymptoticCone`. If $s$ is closed and convex, $v$ is in its cone, $p \in s$ and $c \ge 0$, then $c v +_v p \in s$. So for a closed convex set the cone is the set of directions of the half lines inside $s$, and these half lines can start at each point of $s$. The lemma `StarConvex.smul_vadd_mem_of_isClosed_of_mem_asymptoticCone` gives the same result for a star convex set and its centre.

#### Common errors

1. `ProperSMul G X` needs a topology on `G`, and `ProperConstSMul M X` does not. A search for `ProperSMul` on a discrete monoid without a `TopologicalSpace` instance fails, and `ProperConstSMul` is then the right class.
2. `t2Space_quotient_mulAction_of_properSMul` is about `Quotient (MulAction.orbitRel G X)`, not about a `QuotientGroup` type. For a group modulo a subgroup, use `QuotientGroup.instT2Space` or rewrite with the orbit relation first.
3. `asymptoticCone k s` takes the field `k` as an explicit argument. Without it, Lean cannot find `k` from `s`, and the elaborator reports a stuck typeclass problem.

### Exercises

1. (A) Use `Homeomorph.vaddConst` to show that an affine space over a connected topological group is connected.
2. (A) Prove that the asymptotic cone of a bounded set in $\mathbb{R}^2$ is $\{0\}$, and find the cone of the parabola $\{(x, y) \mid y \ge x^2\}$.
3. (B) Show that the action of $\mathbb{Z}$ on $\mathbb{R}$ by translation satisfies `ProperSMul`, and deduce that the orbit space is Hausdorff with `t2Space_quotient_mulAction_of_properSMul`.
4. (B) Give an action of $\mathbb{R}$ on $\mathbb{R}^2$ that is continuous but not proper, and explain which condition of `properSMul_iff` fails.
5. (C) Prove that a closed convex set in $\mathbb{R}^n$ is bounded if and only if its asymptotic cone is $\{0\}$, using `Convex.smul_vadd_mem_of_isClosed_of_mem_asymptoticCone`.

### Reference

<?reference?>
