---
title: Quotients, homomorphisms and the circle
kind: theory
modules:
  - Mathlib.Topology.Algebra.Group.Quotient
  - Mathlib.Topology.Algebra.ContinuousMonoidHom
  - Mathlib.Topology.Algebra.Group.GroupTopology
  - Mathlib.Topology.Algebra.Group.CompactOpen
  - Mathlib.Topology.Algebra.Group.OpenMapping
  - Mathlib.Topology.Algebra.Group.Extension
  - Mathlib.Topology.Algebra.Group.TopologicalAbelianization
  - Mathlib.Topology.Algebra.PontryaginDual
  - Mathlib.Topology.Instances.AddCircle.Defs
  - Mathlib.Topology.Instances.AddCircle.Real
  - Mathlib.Topology.Instances.AddCircle.DenseSubgroup
  - Mathlib.Topology.Instances.ZMultiples
  - Mathlib.Topology.Instances.Int
  - Mathlib.Topology.Instances.Discrete
  - Mathlib.Topology.Instances.Nat
  - Mathlib.Topology.Instances.PNat
explains:
  E3: [QuotientGroup.isOpenMap_coe, ContinuousMonoidHom, AddCircle]
  E2: [QuotientGroup.isOpenQuotientMap_mk, QuotientGroup.t1Space_iff, QuotientGroup.discreteTopology_iff, QuotientGroup.instIsTopologicalGroup, QuotientGroup.instT3Space, QuotientGroup.instTopologicalSpace, ContinuousAddMonoidHom, ContinuousMonoidHom.toMonoidHom, ContinuousMonoidHom.comp, ContinuousMulEquiv, ContinuousMulEquiv.toHomeomorph, ContinuousMonoidHom.instIsTopologicalGroup, GroupTopology, GroupTopology.coinduced, MonoidHom.isOpenMap_of_sigmaCompact, PontryaginDual, AddCircle.coe_eq_zero_iff, AddCircle.equivIco, AddCircle.compactSpace, UnitAddCircle, AddCircle.dense_addSubgroup_iff_ne_zmultiples, AddCircle.denseRange_zsmul_coe_iff, dense_addSubgroupClosure_pair_iff, Int.isClosedEmbedding_coe_real]
  E1: auto
families: []
requires: [V05, V13.C01, V13.C04, V13.C05]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Quotients, homomorphisms and the circle

### Overview

For a subgroup $H$ of a topological group $G$, the coset space $G/H$ has the quotient topology. This section proves that the quotient map is open, that $G/H$ is a topological group when $H$ is normal, and that $G/H$ is Hausdorff if and only if $H$ is closed. The main example is the circle $\mathbb{R}/\mathbb{Z}$. The section classifies the subgroups of $\mathbb{R}$, proves Kronecker's theorem on the multiples of $\alpha$ modulo $1$, and introduces bundled continuous homomorphisms.

### Definitions

**Definition (Quotient topology).** Let $H \le G$ and let $\pi : G \to G/H$, $\pi(x) = xH$. The quotient topology on $G/H$ is the finest topology for which $\pi$ is continuous: $W \subseteq G/H$ is open if and only if $\pi^{-1}(W)$ is open in $G$.

**Definition (Continuous homomorphism).** A continuous homomorphism of topological groups is a group homomorphism $f : G \to K$ that is a continuous map. An isomorphism of topological groups is a group isomorphism that is a homeomorphism.

**Definition (The circle).** For a real number $p > 0$, the additive circle of period $p$ is the quotient group $\mathbb{R}/p\mathbb{Z}$ with the quotient topology.

::: mathlib
`AddCircle` · `Mathlib.Topology.Instances.AddCircle.Defs`

`AddCircle p` is an abbreviation for `𝕜 ⧸ AddSubgroup.zmultiples p`, for a commutative additive group `𝕜` and `p : 𝕜`; the main case is `𝕜 = ℝ`. Many results need an order on `𝕜` as well. Because it is an abbreviation, it receives the quotient topology and the topological group structure of `QuotientAddGroup` with no new instances. `UnitAddCircle` is `AddCircle (1 : ℝ)`. The lemma `AddCircle.coe_eq_zero_iff` describes the kernel, and `AddCircle.equivIco p a` is the bijection with the interval $[a, a + p)$. The multiplicative unit circle in `ℂ` is `Circle`, in another volume, and `AddCircle.homeomorphCircle` connects the two.

<?decl AddCircle?>
:::

### Theorems and proofs

**Theorem (The quotient map is open).** For $H \le G$ the map $\pi : G \to G/H$ is open. If $H$ is normal, then $G/H$ is a topological group.

*Proof.* Let $U \subseteq G$ be open. Then $\pi^{-1}(\pi(U)) = UH = \bigcup_{h \in H} Uh$, a union of open sets. So $\pi(U)$ is open by the definition of the quotient topology. Now let $H$ be normal and let $m'$ be the multiplication of $G/H$. Then $m' \circ (\pi \times \pi) = \pi \circ m$, which is continuous. The map $\pi \times \pi$ is open and surjective, because $\pi$ is, so it is a quotient map. Therefore $m'$ is continuous. In the same way the inversion $\iota'$ satisfies $\iota' \circ \pi = \pi \circ \iota$, and $\pi$ is a quotient map, so $\iota'$ is continuous. $\square$

::: mathlib
`QuotientGroup.isOpenMap_coe` · `Mathlib.Topology.Algebra.Group.Quotient`

`IsOpenMap (QuotientGroup.mk : G → G ⧸ N)`. It needs only `SeparatelyContinuousMul G`, since the proof uses only translations. The topology on `G ⧸ N` is `QuotientGroup.instTopologicalSpace`, the coinduced topology. The instance `QuotientGroup.instIsTopologicalGroup` needs `[N.Normal]`. The combined statement `QuotientGroup.isOpenQuotientMap_mk` says that `mk` is an open quotient map.

<?decl QuotientGroup.isOpenMap_coe?>
:::

**Theorem (Separation of quotients).** Let $H \le G$. (a) $G/H$ is $T_1$ if and only if $H$ is closed. (b) If $H$ is closed, then $G/H$ is Hausdorff. (c) $G/H$ is discrete if and only if $H$ is open.

*Proof.* (a) The points of $G/H$ are the cosets $xH$. The set $\{xH\}$ is closed if and only if $\pi^{-1}(\{xH\}) = xH$ is closed, and $xH$ is closed if and only if $H$ is, by translation. (b) Let $R = \{(x, y) \in G \times G : x^{-1}y \in H\}$. It is the preimage of the closed set $H$ under the continuous map $(x, y) \mapsto x^{-1}y$, so it is closed. Let $\Delta$ be the diagonal of $G/H \times G/H$. Then $(\pi \times \pi)^{-1}(\Delta) = R$. Since $\pi \times \pi$ is surjective, the complement of $\Delta$ is $(\pi \times \pi)((G \times G) \setminus R)$. This is the image of an open set under an open map, so it is open. A space with a closed diagonal is Hausdorff (Volume 13, Chapter 4). (c) The point $\{H\}$ is open if and only if $H = \pi^{-1}(\{H\})$ is open, and then each point is open by translation. $\square$

::: mathlib
`QuotientGroup.t1Space_iff` · `Mathlib.Topology.Algebra.Group.Quotient`

`T1Space (G ⧸ N) ↔ IsClosed (N : Set G)`, and `QuotientGroup.discreteTopology_iff` gives part (c). For a closed normal subgroup the instance `QuotientGroup.instT3Space` takes `[IsClosed (N : Set G)]` as an instance argument. The Hausdorff instance for any closed subgroup, `QuotientGroup.instT2Space`, lives in the module `Mathlib.Topology.Algebra.ProperAction.Basic`.

<?decl QuotientGroup.t1Space_iff?>
:::

**Theorem (The circle).** The group $\mathbb{R}/\mathbb{Z}$ is a compact Hausdorff topological group. The map $\varphi(t + \mathbb{Z}) = e^{2\pi i t}$ is an isomorphism of topological groups from $\mathbb{R}/\mathbb{Z}$ onto the unit circle $S^1 \subseteq \mathbb{C}$.

*Proof.* The subgroup $\mathbb{Z}$ is closed (Section 2), so $\mathbb{R}/\mathbb{Z}$ is a Hausdorff topological group. Each coset $t + \mathbb{Z}$ meets $[0, 1]$, so $\pi$ maps the compact set $[0, 1]$ onto $\mathbb{R}/\mathbb{Z}$, which is therefore compact. The map $e(t) = e^{2\pi i t}$ is a continuous homomorphism from $\mathbb{R}$ onto $S^1$ with kernel $\mathbb{Z}$. So $\varphi$ is a well defined bijective homomorphism, and it is continuous because $\varphi \circ \pi = e$ and $\pi$ is a quotient map. A continuous bijection from a compact space to a Hausdorff space is a homeomorphism (Volume 13, Chapter 5). $\square$

The subgroup $\mathbb{Z}$ has the discrete topology, and its inclusion into $\mathbb{R}$ is a closed embedding, `Int.isClosedEmbedding_coe_real`.

**Theorem (Subgroups of $\mathbb{R}$).** Each subgroup $H$ of $\mathbb{R}$ is either cyclic, $H = a\mathbb{Z}$ with $a \ge 0$, or dense.

*Proof.* Let $H \ne \{0\}$. Then $H$ has a positive element, since $-h \in H$ for $h \in H$. Let $a = \inf (H \cap (0, \infty))$. First let $a > 0$. If $a \notin H$, there are $h_1 > h_2$ in $H \cap (a, 2a)$, and $0 < h_1 - h_2 < a$ with $h_1 - h_2 \in H$, a contradiction. So $a \in H$. For $h \in H$ let $n = \lfloor h/a \rfloor$. Then $h - na \in H \cap [0, a)$, so $h - na = 0$, and $H = a\mathbb{Z}$. Now let $a = 0$, and let $x \in \mathbb{R}$ and $\varepsilon > 0$. There is $h \in H$ with $0 < h < \varepsilon$. For $n = \lfloor x/h \rfloor$, $nh \in H$ and $|x - nh| < h < \varepsilon$. So $H$ is dense. $\square$

**Corollary (Kronecker).** Let $a, b \in \mathbb{R}$ with $b \ne 0$. The group $a\mathbb{Z} + b\mathbb{Z}$ is dense in $\mathbb{R}$ if and only if $a/b$ is irrational. The multiples $n\alpha + \mathbb{Z}$, $n \in \mathbb{Z}$, are dense in $\mathbb{R}/\mathbb{Z}$ if and only if $\alpha$ is irrational.

*Proof.* If $a/b = m/n$ with $m, n \in \mathbb{Z}$ and $n \ne 0$, then $a = m(b/n)$ and $b = n(b/n)$, so $a\mathbb{Z} + b\mathbb{Z} \subseteq (b/n)\mathbb{Z}$, which is not dense. Conversely, if $a\mathbb{Z} + b\mathbb{Z}$ is not dense, it is $c\mathbb{Z}$ with $c > 0$ by the theorem. Then $a = mc$ and $b = nc$ with $n \ne 0$, and $a/b = m/n$. For the second part, a set $S \subseteq \mathbb{R}/\mathbb{Z}$ is dense if and only if $\pi^{-1}(S)$ is dense. This holds because $\pi$ is continuous, open and surjective: a nonempty open $W$ meets $S$ if and only if the nonempty open set $\pi^{-1}(W)$ meets $\pi^{-1}(S)$. Apply this with $\pi^{-1}(S) = \alpha\mathbb{Z} + \mathbb{Z}$, and use the first part with $a = \alpha$ and $b = 1$. $\square$

::: mathlib
`AddCircle.denseRange_zsmul_coe_iff` · `Mathlib.Topology.Instances.AddCircle.DenseSubgroup`

`DenseRange (fun n : ℤ => n • (a : AddCircle p)) ↔ Irrational (a / p)`. The real form is `dense_addSubgroupClosure_pair_iff`: `Dense (AddSubgroup.closure {a, b}) ↔ Irrational (a / b)`. The general form `AddCircle.dense_addSubgroup_iff_ne_zmultiples` states that a subgroup of the circle is dense if and only if it is not generated by an element of finite order. The dichotomy for subgroups of an archimedean group is `AddSubgroup.dense_or_isCyclic`, in another module. Compactness is the instance `AddCircle.compactSpace`, which needs `[Fact (0 < p)]`.

<?decl AddCircle.denseRange_zsmul_coe_iff?>
:::

::: mathlib
`ContinuousMonoidHom` · `Mathlib.Topology.Algebra.ContinuousMonoidHom`

`A →ₜ* B` is the type of continuous monoid homomorphisms, a structure that extends `A →* B` with a field `continuous_toFun`. The additive form is `ContinuousAddMonoidHom`, written `A →ₜ+ B`. Use `ContinuousMonoidHom.toMonoidHom` to forget the continuity and `ContinuousMonoidHom.comp` to compose. An isomorphism of topological groups is `ContinuousMulEquiv`, written `G ≃ₜ* H`, and `ContinuousMulEquiv.toHomeomorph` gives the homeomorphism. When the target is a commutative topological group, the compact open topology makes `A →ₜ* B` a topological group, by `ContinuousMonoidHom.instIsTopologicalGroup`.

<?decl ContinuousMonoidHom?>
:::

**Theorem (Open mapping).** Let $f : G \to K$ be a continuous surjective homomorphism, where $G$ is a $\sigma$-compact topological group and $K$ is a Hausdorff topological group that is a Baire space. Then $f$ is open.

The proof uses the Baire category theorem and this section does not give it. Mathlib has it as `MonoidHom.isOpenMap_of_sigmaCompact`. With the theorem, a continuous bijective homomorphism between such groups is an isomorphism of topological groups.

### Examples

**Example (The quotient $\mathbb{R}/\mathbb{Q}$).** The subgroup $\mathbb{Q}$ is dense in $\mathbb{R}$. Let $W \subseteq \mathbb{R}/\mathbb{Q}$ be open and nonempty. Then $\pi^{-1}(W)$ is open, nonempty and a union of cosets $x + \mathbb{Q}$. An open nonempty set $U$ satisfies $U + \mathbb{Q} = \mathbb{R}$, because for $y \in \mathbb{R}$ the set $y - U$ is open and meets $\mathbb{Q}$. So $\pi^{-1}(W) = \mathbb{R}$, and $W$ is the whole quotient. The quotient topology is indiscrete. This is the extreme case of part (a): $\mathbb{Q}$ is not closed, and the quotient is not $T_1$.

**Example (The torus and orbits on it).** The torus $\mathbb{T}^2 = \mathbb{R}^2/\mathbb{Z}^2$ is a compact Hausdorff group, as a product of two circles. The image of the line $t \mapsto (t, \alpha t)$ is a subgroup, the image of a one parameter group. When $\alpha$ is irrational, its closure contains the points $(0, n\alpha + \mathbb{Z})$ for $n \in \mathbb{Z}$, since $(n, n\alpha) \equiv (0, n\alpha)$ modulo $\mathbb{Z}^2$. By Kronecker these are dense in $\{0\} \times \mathbb{R}/\mathbb{Z}$. The closure is a closed subgroup that contains this circle and the image of the line, so it contains each point $(t, \alpha t + s)$, and it is the whole torus.

**Counterexample (A continuous bijection that is not open).** Let $\mathbb{R}_d$ be $\mathbb{R}$ with the discrete topology. The identity $\mathbb{R}_d \to \mathbb{R}$ is a continuous bijective homomorphism, and it is not a homeomorphism, since $\{0\}$ is open in $\mathbb{R}_d$ and not in $\mathbb{R}$. The group $\mathbb{R}_d$ is not $\sigma$-compact: a compact subset of a discrete space is finite, and a countable union of finite sets is countable. So the open mapping theorem needs the hypothesis of $\sigma$-compactness.

**Remark (Common errors).** A learner often assumes that $G/H$ is Hausdorff for each subgroup $H$. It is Hausdorff only for closed $H$, as $\mathbb{R}/\mathbb{Q}$ shows. A second error is to treat the quotient map $\pi$ as a closed map. It is open, and in general not closed: the image of the closed set $\{n + 1/n : n \ge 2\}$ in $\mathbb{R}/\mathbb{Z}$ is $\{1/n + \mathbb{Z}\}$, which has the limit $0 + \mathbb{Z}$ outside it. In Lean, many results on `AddCircle p` need the instance `[Fact (0 < p)]`.

### The library around it

Quotients are in `Mathlib.Topology.Algebra.Group.Quotient`, continuous homomorphisms in `Mathlib.Topology.Algebra.ContinuousMonoidHom`, and the compact open topology on them in `Mathlib.Topology.Algebra.Group.CompactOpen`. The circle has three modules under `Mathlib.Topology.Instances.AddCircle`: the definitions, the real case with compactness, and the dense subgroups. The modules `Mathlib.Topology.Instances.Int`, `Mathlib.Topology.Instances.Nat` and `Mathlib.Topology.Instances.ZMultiples` give the discrete subgroups $\mathbb{Z}$, $\mathbb{N}$ and $p\mathbb{Z}$ of $\mathbb{R}$.

### Exercises

1. (A) Show that $\mathbb{R}/2\pi\mathbb{Z}$ and $\mathbb{R}/\mathbb{Z}$ are isomorphic topological groups.
2. (A) Show that $\mathbb{R}/\mathbb{Z}$ is connected and that its only open subgroup is itself.
3. (A) Show that the image of $\sqrt 2\,\mathbb{Z}$ in $\mathbb{R}/\mathbb{Z}$ is dense, and that the image of $\tfrac{3}{7}\mathbb{Z}$ has $7$ elements.
4. (B) Let $f : G \to K$ be a continuous homomorphism. Show that $\ker f$ is closed if $K$ is Hausdorff, and that $G/\ker f \to K$ is a continuous bijective homomorphism onto $f(G)$.
5. (C) Let $\Lambda$ be a discrete subgroup of $\mathbb{R}^n$. Show that $\Lambda$ is generated by at most $n$ linearly independent vectors. *Hint:* induct on $n$; choose a nonzero $v \in \Lambda$ of least norm and project along $\mathbb{R}v$. The theorem on subgroups of $\mathbb{R}$ is the case $n = 1$.
6. (B) Find the closed subgroups of $\mathbb{R}/\mathbb{Z}$. *Hint:* their preimages are closed subgroups of $\mathbb{R}$ that contain $\mathbb{Z}$.
7. (B) Show that $2^n$ has decimal expansions that start with each finite string of digits. *Hint:* $\log_{10} 2$ is irrational; apply Kronecker to the fractional parts of $n \log_{10} 2$.

### Notes and history

Mathlib has the group topologies on a group as a complete lattice, `GroupTopology`, and `GroupTopology.coinduced` is the finest one that makes a given map continuous. The theorem on dense orbits modulo $1$ is due to Kronecker in 1884. Pontryagin's duality theorem of 1934 describes a locally compact abelian group through its continuous homomorphisms into the circle. Mathlib defines the dual group as `PontryaginDual`.

### Reference

<?reference?>
