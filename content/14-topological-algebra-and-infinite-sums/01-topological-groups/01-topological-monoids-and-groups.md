---
title: Topological monoids and groups
kind: theory
modules:
  - Mathlib.Topology.Algebra.Monoid.Defs
  - Mathlib.Topology.Algebra.Monoid
  - Mathlib.Topology.Algebra.Group.Defs
  - Mathlib.Topology.Algebra.Group.ContinuousInv
  - Mathlib.Topology.Algebra.Group.ContinuousDiv
  - Mathlib.Topology.Algebra.Group.ZPow
  - Mathlib.Topology.Algebra.Group.Units
  - Mathlib.Topology.Algebra.ConstMulAction
  - Mathlib.Topology.Algebra.MulAction
  - Mathlib.Topology.Algebra.Constructions
  - Mathlib.Topology.Algebra.Semigroup
explains:
  E3: [ContinuousMul, IsTopologicalGroup]
  E2: [ContinuousAdd, SeparatelyContinuousMul, ContinuousInv, ContinuousNeg, IsTopologicalAddGroup, ContinuousDiv, continuous_mul, Continuous.mul, Filter.Tendsto.mul, Continuous.inv, Filter.Tendsto.inv, Continuous.div', continuous_pow, Continuous.zpow, Homeomorph.inv, Homeomorph.mulLeft, Homeomorph.mulRight, isOpenMap_mul_left, Prod.continuousMul, Prod.instIsTopologicalGroup, Pi.isTopologicalGroup, Units.instTopologicalSpaceUnits, Units.isEmbedding_embedProduct, Units.topology_eq_inf, Units.isEmbedding_val_mk', Units.instIsTopologicalGroupOfContinuousMul, isTopologicalGroup_of_discreteTopology, ContinuousConstSMul, ContinuousSMul]
  E1: auto
families: []
requires: [V05, V13.C01, V13.C02, V13.C04]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Topological monoids and groups

### Overview

A topological group is a group with a topology in which the multiplication $(x, y) \mapsto xy$ and the inversion $x \mapsto x^{-1}$ are continuous. Mathlib splits the definition into the classes `ContinuousMul`, `ContinuousInv` and `IsTopologicalGroup`. This section proves that translations are homeomorphisms, that products of topological groups are topological groups, and that the units of a topological monoid form a topological group for a suitable topology. A counterexample, the Sorgenfrey line, shows that a continuous multiplication does not give a continuous inversion.

### Definitions

**Definition (Topological monoid).** Let $M$ be a monoid with a topology. The multiplication is continuous if the map $M \times M \to M$, $(x, y) \mapsto xy$, is continuous for the product topology. A topological monoid is a monoid with a continuous multiplication.

**Definition (Topological group).** Let $G$ be a group with a topology. The group $G$ is a topological group if the multiplication $G \times G \to G$ and the inversion $G \to G$, $x \mapsto x^{-1}$, are continuous.

The additive forms are the same with $x + y$ and $-x$. A topological additive group is an additive group with continuous addition and negation.

::: mathlib
`ContinuousMul` · `Mathlib.Topology.Algebra.Monoid.Defs`

A class with one field: `continuous_mul : Continuous fun p : M × M => p.1 * p.2`. It needs only `[TopologicalSpace M] [Mul M]`, so it applies to monoids, groups, rings and also to structures with no unit. The additive twin is `ContinuousAdd`. Use `Continuous.mul` to prove that `fun x => f x * g x` is continuous from the continuity of `f` and `g`, and `Filter.Tendsto.mul` for limits. The weaker class `SeparatelyContinuousMul` asks only that each map $x \mapsto ax$ and $x \mapsto xa$ is continuous.

<?decl ContinuousMul?>
:::

::: mathlib
`IsTopologicalGroup` · `Mathlib.Topology.Algebra.Group.Defs`

A class that extends `ContinuousMul G` and `ContinuousInv G`, for `[TopologicalSpace G] [Group G]`. The additive form is `IsTopologicalAddGroup`, which extends `ContinuousAdd` and `ContinuousNeg`. To build an instance, give the two parts: `IsTopologicalGroup.mk` takes them as instance arguments. The lemma `Continuous.inv` gives the continuity of `fun x => (f x)⁻¹`, and `Continuous.div'` that of `fun x => f x / g x`.

<?decl IsTopologicalGroup?>
:::

Mathlib keeps the two conditions apart because some structures have only one of them. A topological monoid has no inversion. A topological field, in Chapter 2, has an inversion that is continuous only away from $0$. The class `ContinuousDiv` says that $(x, y) \mapsto x / y$ is continuous; a topological group has it by an instance.

**Remark (Common errors).** A learner often asks only that each translation $x \mapsto ax$ is continuous. This is the class `SeparatelyContinuousMul`, and it is weaker than `ContinuousMul`: continuity in each variable does not give continuity on the product. A second error is to forget the topology of $G \times G$. The multiplication must be continuous for the product topology, not for a finer topology.

### Theorems and proofs

**Theorem (Translations).** Let $G$ be a topological group and $a \in G$. The left translation $L_a : x \mapsto ax$, the right translation $R_a : x \mapsto xa$ and the inversion $x \mapsto x^{-1}$ are homeomorphisms of $G$. In particular $aU$ and $Ua$ are open for each open $U$.

*Proof.* The map $L_a$ is the composite of $x \mapsto (a, x)$, which is continuous into $G \times G$, and of the multiplication. So $L_a$ is continuous. Its inverse is $L_{a^{-1}}$, since $a^{-1}(ax) = x$ and $a(a^{-1}x) = x$. The inverse is continuous for the same reason, so $L_a$ is a homeomorphism. The same argument works for $R_a$, with $x \mapsto (x, a)$. The inversion is continuous by hypothesis and is its own inverse, since $(x^{-1})^{-1} = x$. A homeomorphism maps open sets to open sets, so $aU = L_a(U)$ and $Ua = R_a(U)$ are open. $\square$

The proof of continuity of $L_a$ uses only that $x \mapsto ax$ is continuous for each fixed $a$. So the theorem holds in a group with `SeparatelyContinuousMul`, and Mathlib states it with this class.

::: mathlib
`Homeomorph.mulLeft` · `Mathlib.Topology.Algebra.Group.Basic`

`Homeomorph.mulLeft a : G ≃ₜ G` for a group with `SeparatelyContinuousMul G`. A homeomorphism `G ≃ₜ G` is a bundled structure that holds the map, its inverse and the two continuity proofs. The twins are `Homeomorph.mulRight` and `Homeomorph.inv`. The lemma `isOpenMap_mul_left` states that $x \mapsto ax$ is an open map.

<?decl Homeomorph.mulLeft?>
:::

**Corollary (Homogeneity).** For $x, y$ in a topological group $G$ there is a homeomorphism of $G$ that maps $x$ to $y$. The neighbourhoods of $x$ are the sets $xN$ with $N$ a neighbourhood of $1$.

*Proof.* The left translation $L_{yx^{-1}}$ maps $x$ to $y$. A homeomorphism $h$ maps the neighbourhoods of a point $p$ onto the neighbourhoods of $h(p)$. Apply this to $L_x$ and $p = 1$. $\square$

So a property of the neighbourhoods of $1$ holds at each point. Section 2 uses this fact all the time.

**Theorem (Products).** Let $(G_i)_{i \in I}$ be a family of topological groups. The product $\prod_i G_i$, with the product topology and the componentwise operations, is a topological group. The same holds for topological monoids.

*Proof.* Let $p_i$ be the projection onto $G_i$. A map into a product is continuous if and only if each composite with a projection is continuous (Volume 13, Chapter 1). The composite of the multiplication with $p_i$ is $(x, y) \mapsto x_i y_i$. It is the multiplication of $G_i$ composed with $(x, y) \mapsto (x_i, y_i)$, so it is continuous. In the same way $p_i(x^{-1}) = x_i^{-1}$ is continuous in $x$. $\square$

::: mathlib
`Prod.instIsTopologicalGroup` · `Mathlib.Topology.Algebra.Group.Basic`

The instance for `G × H`. For a family the instance is `Pi.isTopologicalGroup`, and for monoids `Prod.continuousMul` and `Pi.continuousMul`. These instances fire automatically, so `ℝ × ℝ` and `Fin n → ℝ` are topological groups with no extra work.

<?decl Prod.instIsTopologicalGroup?>
:::

**Theorem (Units of a topological monoid).** Let $M$ be a topological monoid and $M^\times$ its group of units. Give $M^\times$ the topology induced by the map $j : M^\times \to M \times M$, $j(u) = (u, u^{-1})$. Then $M^\times$ is a topological group, and the maps $u \mapsto u$ and $u \mapsto u^{-1}$ from $M^\times$ to $M$ are continuous.

*Proof.* The topology on $M^\times$ is the coarsest one for which $\alpha(u) = u$ and $\beta(u) = u^{-1}$ are continuous into $M$. So a map $f : X \to M^\times$ is continuous if and only if $\alpha \circ f$ and $\beta \circ f$ are continuous. For the multiplication $m(u, v) = uv$ on $M^\times \times M^\times$, $\alpha(uv) = \alpha(u)\alpha(v)$ is continuous, as a product of continuous maps into the topological monoid $M$. Also $\beta(uv) = v^{-1}u^{-1} = \beta(v)\beta(u)$ is continuous for the same reason. For the inversion, $\alpha(u^{-1}) = \beta(u)$ and $\beta(u^{-1}) = \alpha(u)$ are continuous. $\square$

The second factor is needed. The topology induced by $\alpha$ alone can make the inversion discontinuous, and the next part gives an example. When the inversion of $M$ is already continuous on $M^\times$ for the subspace topology, the two topologies agree.

::: mathlib
`Units.instTopologicalSpaceUnits` · `Mathlib.Topology.Algebra.Constructions`

The topology on `Mˣ`, induced by `Units.embedProduct M : Mˣ →* M × Mᵐᵒᵖ`. The second factor is the opposite monoid, so that `embedProduct` is a monoid hom. `Units.isEmbedding_embedProduct` states that it is an embedding, `Units.topology_eq_inf` writes the topology as the infimum of the two induced topologies, and `Units.isEmbedding_val_mk'` gives a criterion for the subspace topology to be the same. The instance `Units.instIsTopologicalGroupOfContinuousMul` makes `Mˣ` a topological group when `M` has `ContinuousMul`.

<?decl Units.instTopologicalSpaceUnits?>
:::

### Examples

**Example (The circle).** Let $S^1 = \{z \in \mathbb{C} : |z| = 1\}$ with the multiplication of $\mathbb{C}$ and the subspace topology. The multiplication $(z, w) \mapsto zw$ is the restriction of a polynomial map $\mathbb{R}^4 \to \mathbb{R}^2$, so it is continuous. On $S^1$ the inverse is $z^{-1} = \bar z$, the restriction of a linear map. So $S^1$ is a topological group. Section 3 builds the same group as the quotient $\mathbb{R}/\mathbb{Z}$.

**Example (The general linear group).** Let $M = M_n(\mathbb{R})$ with the topology of $\mathbb{R}^{n^2}$. Each entry of $AB$ is a polynomial in the entries of $A$ and $B$, so $M$ is a topological monoid. Its unit group is $GL_n(\mathbb{R})$. By Cramer's rule, $A^{-1} = \operatorname{adj}(A)/\det A$, whose entries are polynomials in the entries of $A$ divided by $\det A \ne 0$. So the inversion is continuous on $GL_n(\mathbb{R})$ for the subspace topology. Therefore the topology of the theorem on units is the subspace topology of $GL_n(\mathbb{R}) \subseteq \mathbb{R}^{n^2}$, and $GL_n(\mathbb{R})$ is a topological group. In Mathlib it is `Matrix.GeneralLinearGroup n ℝ`, an abbreviation for the units of `Matrix n n ℝ`, so it receives the topology of the theorem.

**Counterexample (The Sorgenfrey line).** Let $\mathbb{R}_\ell$ be $\mathbb{R}$ with the topology generated by the intervals $[a, b)$, the Sorgenfrey line of Volume 13, Chapter 1. The addition is continuous. Let $x_0 + y_0 \in [c, d)$, and let $\delta = (d - x_0 - y_0)/2$. For $x \in [x_0, x_0 + \delta)$ and $y \in [y_0, y_0 + \delta)$, $x_0 + y_0 \le x + y < d$, so $x + y \in [c, d)$. The negation is not continuous: the preimage of the open set $[0, 1)$ under $x \mapsto -x$ is $(-1, 0]$, which contains no set $[0, \varepsilon)$, so it is not open. Thus $(\mathbb{R}_\ell, +)$ is a topological monoid in which each element is invertible, but it is not a topological group.

The units theorem repairs this. Each element of $(\mathbb{R}, +)$ is an additive unit. The topology of the theorem is induced by $x \mapsto (x, -x)$ into $\mathbb{R}_\ell \times \mathbb{R}_\ell$. The preimage of the open set $[x_0, x_0 + 1) \times [-x_0, -x_0 + 1)$ is $\{x : x \ge x_0 \text{ and } -x \ge -x_0\} = \{x_0\}$. So each point is open, and the topology on the units is discrete. This topology makes negation continuous, at the price of a finer topology.

### The library around it

The classes form a small hierarchy. `SeparatelyContinuousMul` is below `ContinuousMul`, and `IsTopologicalGroup` extends `ContinuousMul` and `ContinuousInv`. Each lemma has an additive twin, made by the attribute `to_additive`: `Continuous.add` for `Continuous.mul`, `Homeomorph.addLeft` for `Homeomorph.mulLeft`, `IsTopologicalAddGroup` for `IsTopologicalGroup`. The lemmas `Continuous.mul`, `Filter.Tendsto.mul`, `Continuous.inv` and `Continuous.zpow` have forms for each kind of continuity (`ContinuousAt`, `ContinuousOn`). The power $x \mapsto x^n$ is continuous by induction on $n$ (`continuous_pow`). The prime in `Continuous.div'` separates the group form from the form `Continuous.div` for division in a field, which needs a nonzero denominator.

Actions have their own classes. `ContinuousConstSMul Γ X` says that each map $x \mapsto \gamma \cdot x$ is continuous, and `ContinuousSMul M X` says that $(m, x) \mapsto m \cdot x$ is continuous on $M \times X$. A topological monoid acts continuously on itself by multiplication. A group with the discrete topology is a topological group, `isTopologicalGroup_of_discreteTopology`.

### Exercises

1. (A) Show that $(\mathbb{Q}, +)$ and $(\mathbb{Q}^\times, \cdot)$, with the topologies induced by $\mathbb{R}$, are topological groups.
2. (A) Let $G$ be a topological group and $U \subseteq G$ open. Show that $AU$ is open for each subset $A \subseteq G$. *Hint:* $AU = \bigcup_{a \in A} aU$.
3. (A) Show that in a topological group the map $(x, y) \mapsto x^{-1}y$ is continuous, and that conversely a group in which this map is continuous is a topological group. *Hint:* $x^{-1} = x^{-1} \cdot 1$ and $xy = (x^{-1})^{-1} y$.
4. (B) Show that the subspace topology on $(\mathbb{R}_{>0}, \cdot) \subseteq \mathbb{R}$ agrees with the topology of the units theorem for the monoid $(\mathbb{R}, \cdot)$.
5. (B) Let $M$ be the monoid $(\mathbb{R}_\ell, +)$ of the counterexample. Show that the identity map from $\mathbb{R}_\ell$ with the discrete topology to $\mathbb{R}_\ell$ is continuous and is not a homeomorphism.
6. (B) Show that the group of upper triangular real $2 \times 2$ matrices with positive diagonal is a topological group for the subspace topology of $\mathbb{R}^4$, and that it is homeomorphic to $\mathbb{R}_{>0}^2 \times \mathbb{R}$.
7. (C) Let $G$ be a group with a topology in which multiplication is separately continuous, and suppose $G$ is a compact Hausdorff space. The theorem of Ellis states that $G$ is then a topological group. Prove the easier statement: if multiplication is jointly continuous and $G$ is compact Hausdorff, then the inversion is continuous. *Hint:* the graph of the inversion is the closed set $\{(x, y) : xy = 1\}$, and a map into a compact Hausdorff space with closed graph is continuous.

### Notes and history

Topological groups appear in the work of Lie on continuous groups of transformations in the late nineteenth century. Hilbert's fifth problem of 1900 asked when a locally Euclidean topological group is a Lie group, and Gleason, Montgomery and Zippin solved it in 1952. Ellis proved in 1957 that a locally compact Hausdorff group with separately continuous multiplication is a topological group.

### Reference

<?reference?>
