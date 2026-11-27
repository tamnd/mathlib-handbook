---
title: Neighbourhoods of the identity and subgroups
kind: theory
modules:
  - Mathlib.Topology.Algebra.Group.Basic
  - Mathlib.Topology.Algebra.Group.Neighborhood
  - Mathlib.Topology.Algebra.Group.Pointwise
  - Mathlib.Topology.Algebra.Group.Subgroup
  - Mathlib.Topology.Algebra.Group.ClosedSubgroup
  - Mathlib.Topology.Algebra.OpenSubgroup
  - Mathlib.Topology.Algebra.Group.SubmonoidClosure
  - Mathlib.Topology.Algebra.Group.Compact
  - Mathlib.Topology.Algebra.ClopenNhdofOne
  - Mathlib.Topology.Algebra.Group.DiscontinuousSubgroup
explains:
  E3: [OpenSubgroup, Subgroup.topologicalClosure, IsTopologicalGroup.t2Space_iff_one_closed]
  E2: [exists_nhds_split_inv, exists_closed_nhds_one_inv_eq_mul_subset, inv_mem_nhds_one, map_mul_left_nhds_one, mem_closure_iff_nhds_one, IsTopologicalGroup.t1Space, IsTopologicalGroup.t2Space_of_one_sep, IsTopologicalGroup.regularSpace, Subgroup.isClosed_topologicalClosure, Subgroup.is_normal_topologicalClosure, Subgroup.connectedComponentOfOne, mul_mem_connectedComponent_one, OpenSubgroup.isOpen, OpenSubgroup.isClosed, Subgroup.isOpen_of_mem_nhds, Subgroup.isClosed_of_isOpen, Subgroup.isOpen_mono, Subgroup.isOpen_of_isClosed_of_finiteIndex, continuous_of_continuousAt_one, compact_open_separated_mul_right, IsClosed.mul_left_of_isCompact]
  E1: auto
families: []
requires: [V05, V13.C01, V13.C02, V13.C04, V13.C05, V13.C06]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Neighbourhoods of the identity and subgroups

### Overview

By Section 1, the neighbourhoods of $x$ in a topological group $G$ are the sets $xN$ with $N$ a neighbourhood of $1$, so the filter $\mathcal{N}(1)$ determines the topology. Each neighbourhood of $1$ contains the square of a smaller one, and from this fact the section gets three results: a topological group is regular, it is Hausdorff as soon as $\{1\}$ is closed, and a homomorphism that is continuous at $1$ is continuous. It then studies closures of subgroups, open subgroups and the identity component.

### Definitions

**Definition (Symmetric set).** A subset $V$ of a group is symmetric if $V^{-1} = V$, where $V^{-1} = \{v^{-1} : v \in V\}$. For subsets $A, B$ write $AB = \{ab : a \in A, b \in B\}$.

**Definition (Open subgroup).** An open subgroup of a topological group $G$ is a subgroup $H \le G$ that is an open subset of $G$.

**Definition (Identity component).** The identity component $G_0$ of a topological group $G$ is the connected component of $G$ that contains $1$.

::: mathlib
`OpenSubgroup` · `Mathlib.Topology.Algebra.OpenSubgroup`

A structure that extends `Subgroup G` with the field `isOpen'`. A term `U : OpenSubgroup G` coerces to a subgroup and to a set. The lemmas `OpenSubgroup.isOpen` and `OpenSubgroup.isClosed` give the two properties. It is bundled because open subgroups form a lattice, and because the neighbourhood bases of profinite and $p$-adic groups are families of open subgroups. To prove that a plain subgroup is open, use `Subgroup.isOpen_of_mem_nhds`: it is enough that the subgroup is a neighbourhood of one point.

<?decl OpenSubgroup?>
:::

### Theorems and proofs

**Lemma (Splitting).** Let $U$ be a neighbourhood of $1$ in a topological group $G$. There is an open symmetric neighbourhood $V$ of $1$ with $VV \subseteq U$.

*Proof.* The multiplication $m$ is continuous at $(1, 1)$ and $m(1, 1) = 1$. So $m^{-1}(U)$ is a neighbourhood of $(1, 1)$ in $G \times G$, and it contains a product $W_1 \times W_2$ of open neighbourhoods of $1$. Let $W = W_1 \cap W_2$ and $V = W \cap W^{-1}$. The set $W^{-1}$ is open because inversion is a homeomorphism, and it contains $1$. So $V$ is an open neighbourhood of $1$. It is symmetric, since $(W \cap W^{-1})^{-1} = W^{-1} \cap W$. For $v, w \in V$, $(v, w) \in W_1 \times W_2$, so $vw \in U$. $\square$

**Lemma (Closure).** Let $A \subseteq G$ and let $V$ be a symmetric neighbourhood of $1$. Then $\overline{A} \subseteq AV$. In particular $\overline{V} \subseteq VV$.

*Proof.* Let $x \in \overline{A}$. The set $xV$ is a neighbourhood of $x$, so it meets $A$: there are $v \in V$ and $a \in A$ with $xv = a$. Then $x = av^{-1}$, and $v^{-1} \in V$ because $V$ is symmetric. So $x \in AV$. $\square$

**Theorem (Regularity).** In a topological group the closed neighbourhoods of $1$ form a basis of $\mathcal{N}(1)$. So each topological group is a regular space.

*Proof.* Let $U$ be a neighbourhood of $1$. The splitting lemma gives a symmetric open $V \ni 1$ with $VV \subseteq U$. By the closure lemma, $\overline{V} \subseteq VV \subseteq U$, and $\overline{V}$ is a closed neighbourhood of $1$. By the homogeneity of Section 1, the sets $x\overline{V}$ form a basis of closed neighbourhoods at each point $x$. A space in which each point has a basis of closed neighbourhoods is regular (Volume 13, Chapter 4). $\square$

**Theorem (Separation).** For a topological group $G$ the following are equivalent: (a) $G$ is Hausdorff; (b) $\{1\}$ is closed; (c) $G$ is $T_0$.

*Proof.* (a) implies (b), since points are closed in a Hausdorff space, and (b) implies (c), since then each point is closed by homogeneity. Assume (c). First, for $x \ne 1$ there is a neighbourhood of $1$ that does not contain $x$. By $T_0$ there is either such a set, or an open $U \ni x$ with $1 \notin U$. In the second case the set $U^{-1}x$ is open, it contains $x^{-1}x = 1$, and it does not contain $x$: if $x = u^{-1}x$ then $u = 1 \in U$. Now let $x \ne y$. Choose a neighbourhood $U$ of $1$ with $x^{-1}y \notin U$, and a symmetric $V$ with $VV \subseteq U$. If $xv = yw$ with $v, w \in V$, then $x^{-1}y = vw^{-1} \in VV \subseteq U$, a contradiction. So $xV$ and $yV$ are disjoint neighbourhoods of $x$ and $y$. $\square$

With regularity, a $T_0$ topological group is $T_3$.

::: mathlib
`IsTopologicalGroup.t2Space_iff_one_closed` · `Mathlib.Topology.Algebra.Group.Pointwise`

`T2Space G ↔ IsClosed {1}` for `[IsTopologicalGroup G]`. The criterion `IsTopologicalGroup.t2Space_of_one_sep` takes the hypothesis of the proof above: each `x ≠ 1` has a neighbourhood of `1` that misses it. Regularity is an instance, `IsTopologicalGroup.regularSpace`, so Lean finds `RegularSpace G` with no help. `IsTopologicalGroup.t1Space` needs only `ContinuousMul` and `IsClosed {1}`.

<?decl IsTopologicalGroup.t2Space_iff_one_closed?>
:::

::: mathlib
`exists_closed_nhds_one_inv_eq_mul_subset` · `Mathlib.Topology.Algebra.Group.Pointwise`

The splitting lemma together with the closure lemma: for `U ∈ 𝓝 1` there is `V ∈ 𝓝 1` with `IsClosed V`, `V⁻¹ = V` and `V * V ⊆ U`. The plain form is `exists_nhds_split_inv`, which gives `v / w ∈ U` for `v, w ∈ V`. The lemma `map_mul_left_nhds_one` states `map (x * ·) (𝓝 1) = 𝓝 x`, the filter form of homogeneity, and `mem_closure_iff_nhds_one` describes the closure through $\mathcal{N}(1)$.

<?decl exists_closed_nhds_one_inv_eq_mul_subset?>
:::

**Proposition (Continuity at the identity).** Let $f : G \to H$ be a homomorphism of topological groups that is continuous at $1$. Then $f$ is continuous.

*Proof.* Let $x \in G$. For $y \in G$, $f(y) = f(x) f(x^{-1}y)$. So $f = L_{f(x)} \circ f \circ L_{x^{-1}}$. The map $L_{x^{-1}}$ is continuous and sends $x$ to $1$, $f$ is continuous at $1$, and $L_{f(x)}$ is continuous. So $f$ is continuous at $x$. $\square$

In Mathlib this is `continuous_of_continuousAt_one`, stated for any class of monoid homomorphisms.

**Proposition (Compact sets).** Let $K \subseteq U \subseteq G$ with $K$ compact and $U$ open. There is a neighbourhood $V$ of $1$ with $KV \subseteq U$.

*Proof.* For $k \in K$ the set $k^{-1}U$ is a neighbourhood of $1$. Choose an open neighbourhood $W_k$ of $1$ with $W_k W_k \subseteq k^{-1}U$. The open sets $kW_k$ cover $K$, so finitely many $k_1 W_{k_1}, \dots, k_n W_{k_n}$ cover it. Let $V = W_{k_1} \cap \dots \cap W_{k_n}$. For $k \in K$ choose $i$ with $k \in k_i W_{k_i}$. Then $kV \subseteq k_i W_{k_i} W_{k_i} \subseteq U$. $\square$

This is `compact_open_separated_mul_right`. Chapter 2 uses it to show that a compact Hausdorff division ring is finite. A related result, `IsClosed.mul_left_of_isCompact`, states that $KF$ is closed when $K$ is compact and $F$ is closed.

**Theorem (Closure of a subgroup).** Let $H$ be a subgroup of $G$. Then $\overline{H}$ is a subgroup, and it is normal if $H$ is normal.

*Proof.* Let $f(x, y) = xy^{-1}$. It is continuous, and $f(H \times H) \subseteq H$. A continuous map sends the closure of a set into the closure of its image, and $\overline{H \times H} = \overline{H} \times \overline{H}$. So $f(\overline{H} \times \overline{H}) \subseteq \overline{H}$. Also $1 \in H \subseteq \overline{H}$. A nonempty subset closed under $xy^{-1}$ is a subgroup. If $H$ is normal, then for $g \in G$ the conjugation $c_g(x) = gxg^{-1}$ is a homeomorphism with $c_g(H) = H$. A homeomorphism maps closures to closures, so $c_g(\overline{H}) = \overline{H}$. $\square$

::: mathlib
`Subgroup.topologicalClosure` · `Mathlib.Topology.Algebra.Group.Subgroup`

`H.topologicalClosure : Subgroup G`, with carrier `closure (H : Set G)`. The lemmas `Subgroup.isClosed_topologicalClosure` and `Subgroup.is_normal_topologicalClosure` give the two parts of the theorem. Chapter 2 has `Subring.topologicalClosure` and `Submodule.topologicalClosure` of the same form.

<?decl Subgroup.topologicalClosure?>
:::

**Theorem (Open subgroups).** Let $H$ be a subgroup of $G$. (a) If $H$ contains a neighbourhood of one of its points, then $H$ is open. (b) If $H$ is open, then $H$ is closed. (c) If $H$ is open and $H \le K$, then $K$ is open. (d) If $H$ is closed and has finite index, then $H$ is open.

*Proof.* (a) Let $N \subseteq H$ be a neighbourhood of $h_0 \in H$. For $h \in H$ the set $hh_0^{-1}N$ is a neighbourhood of $h$ and lies in $H$. So $H$ is a neighbourhood of each of its points. (b) The complement $G \setminus H$ is the union of the cosets $gH$ with $g \notin H$. Each coset is open, as the image of $H$ under a translation. So the complement is open. (c) $K$ contains the neighbourhood $H$ of $1$, so (a) applies. (d) The complement is a finite union of cosets $gH$, each closed. So it is closed, and $H$ is open. $\square$

**Corollary (Connected groups).** Let $G$ be a connected topological group and $U$ a neighbourhood of $1$. Then $U$ generates $G$.

*Proof.* The subgroup $\langle U\rangle$ contains $U$, so it is open by (a) and closed by (b). It is not empty. A connected space has no clopen subset except $\emptyset$ and itself. So $\langle U\rangle = G$. $\square$

**Theorem (Identity component).** $G_0$ is a closed normal subgroup of $G$.

*Proof.* A connected component is closed (Volume 13, Chapter 6). The product $G_0 \times G_0$ is connected, and $f(x, y) = xy^{-1}$ maps it onto a connected set that contains $1$. So $f(G_0 \times G_0) \subseteq G_0$, and $G_0$ is a subgroup. For $g \in G$ the homeomorphism $c_g$ maps $G_0$ onto a connected set that contains $c_g(1) = 1$, so $c_g(G_0) \subseteq G_0$. $\square$

In Mathlib the subgroup is `Subgroup.connectedComponentOfOne`, and `mul_mem_connectedComponent_one` gives the closure under products.

### Examples

**Example (Subgroups of the real line).** In $(\mathbb{R}, +)$ the subgroup $\mathbb{Z}$ is closed: its complement is the union of the open intervals $(n, n + 1)$. It is not open, so part (d) of the theorem needs finite index. The subgroup $\mathbb{Q}$ is neither open nor closed, and $\overline{\mathbb{Q}} = \mathbb{R}$. The group $\mathbb{R}$ is connected, so its only open subgroup is $\mathbb{R}$, and by the corollary each interval $(-\varepsilon, \varepsilon)$ generates $\mathbb{R}$. Indeed each $x \in \mathbb{R}$ is a sum of $n$ copies of $x/n$, and $|x/n| < \varepsilon$ for large $n$.

**Example (A Cantor group).** Let $G = (\mathbb{Z}/2)^{\mathbb{N}}$ with the product of discrete topologies. For $n \ge 0$ let $H_n = \{x : x_0 = \dots = x_{n-1} = 0\}$. Each $H_n$ is an open subgroup of index $2^n$, so it is clopen. The sets $H_n$ form a basis of $\mathcal{N}(0)$. For $x \ne 0$, choose $n$ with $x_{n-1} \ne 0$. Then $x \notin H_n$, so the clopen set $H_n$ separates $0$ and $x$. So $G_0 = \{0\}$, and $G$ is totally disconnected.

**Counterexample (A group that is not Hausdorff).** Let $G = \mathbb{R}^2$ with the topology whose open sets are the sets $U \times \mathbb{R}$, $U \subseteq \mathbb{R}$ open. This is the topology induced by the first projection, which is a homomorphism, so addition and negation are continuous. The closure of $\{0\}$ is $\{0\} \times \mathbb{R}$, which is a closed subgroup by the theorem on closures. Two points $(0, 0)$ and $(0, 1)$ have the same neighbourhoods. So $G$ is not $T_0$ and not Hausdorff, but it is regular, as the theorem says. Section 3 shows that the quotient by $\overline{\{0\}}$ is Hausdorff.

**Remark (Common errors).** A learner often believes that a closed subgroup is open, or that a subgroup with nonempty interior can fail to be open. The example $\mathbb{Z} \subseteq \mathbb{R}$ shows the first error, and part (a) of the theorem refutes the second. A second error is to use the splitting lemma without symmetry. The closure lemma needs $v^{-1} \in V$. In Lean, the lemma `exists_nhds_split_inv` gives $v / w \in U$, not $vw \in U$, so check which form a proof needs.

### The library around it

Most lemmas of this section live in `Mathlib.Topology.Algebra.Group.Pointwise` and `Mathlib.Topology.Algebra.Group.Neighborhood`, stated with the pointwise products `s * t` and `s⁻¹` of sets. Open subgroups have their own module, `Mathlib.Topology.Algebra.OpenSubgroup`, and closed subgroups are bundled as `ClosedSubgroup` in `Mathlib.Topology.Algebra.Group.ClosedSubgroup`. Each lemma has an additive twin, for example `AddSubgroup.topologicalClosure`.

### Exercises

1. (A) Show that each subgroup of $\mathbb{R}$ that contains an interval $(-\varepsilon, \varepsilon)$ is $\mathbb{R}$.
2. (A) Let $H$ be a subgroup of a topological group with nonempty interior. Show that $H$ is clopen.
3. (A) Show that a discrete topological group is Hausdorff and that each subgroup of it is clopen.
4. (B) Let $A \subseteq G$. Show that $\overline{A} = \bigcap_{V} AV$, where $V$ runs through the neighbourhoods of $1$. *Hint:* for the inclusion from right to left, use the neighbourhood $xV^{-1}$ of $x$.
5. (B) Let $K$ be compact and $F$ closed in a topological group. Show that $KF$ is closed. *Hint:* let $x \notin KF$; apply the compact set proposition to $K^{-1}x$ and the open set $G \setminus F$.
6. (B) Show that the closure $N = \overline{\{1\}}$ is a closed normal subgroup, and that $N$ is contained in each open set that contains $1$.
7. (C) Let $G$ be a locally compact totally disconnected Hausdorff group. Show that each neighbourhood of $1$ contains a compact open subgroup. *Hint:* use a compact open neighbourhood $K$ of $1$ (a fact on totally disconnected locally compact spaces), the compact set proposition for $K \subseteq K$, and the subgroup generated by a symmetric $V$ with $KV \subseteq K$.

### Notes and history

The facts of this section are in Chapter III of Bourbaki's "Topologie générale". The result of Exercise 7 is van Dantzig's theorem. In Mathlib the module `Mathlib.Topology.Algebra.ClopenNhdofOne` proves that each closed subgroup of a profinite group is the intersection of the open subgroups that contain it (`ProfiniteGrp.closedSubgroup_eq_sInf_open`).

### Reference

<?reference?>
