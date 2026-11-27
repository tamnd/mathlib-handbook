---
title: Nonarchimedean groups and valued fields
kind: theory
modules:
  - Mathlib.Topology.Algebra.Nonarchimedean.Basic
  - Mathlib.Topology.Algebra.Nonarchimedean.Bases
  - Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
  - Mathlib.Topology.Algebra.Nonarchimedean.Completion
  - Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected
  - Mathlib.Topology.Algebra.Valued.ValuationTopology
  - Mathlib.Topology.Algebra.Valued.ValuedField
  - Mathlib.Topology.Algebra.Valued.NormedValued
  - Mathlib.Topology.Algebra.WithZeroTopology
explains:
  E3: [NonarchimedeanAddGroup, Ideal.adicTopology, Valued, Valued.locally_const, Valued.valuedCompletion]
  E2: [NonarchimedeanRing, NonarchimedeanRing.mul_subset, NonarchimedeanAddGroup.nonarchimedean_of_emb, NonarchimedeanAddGroup.prod_subset, NonarchimedeanAddGroup.exists_openAddSubgroup_separating, NonarchimedeanAddGroup.instTotallySeparated, instNonarchimedeanAddGroupCompletion, RingSubgroupsBasis, RingSubgroupsBasis.topology, RingSubgroupsBasis.hasBasis_nhds_zero, Ideal.hasBasis_nhds_zero_adic, Ideal.nonarchimedean, IsAdic, isAdic_iff, Valued.v, Valued.mk', Valued.mem_nhds_zero, Valued.isClopen_ball, Valued.isOpen_sphere, Valued.isClopen_integer, Valued.discreteTopology_of_forall_map_eq_one, Valuation.subgroups_basis, Valued.continuous_valuation, Valued.extension_extends, Valued.continuous_extension, Valued.completable, ValuedRing.separated, NormedField.toValued, WithZeroTopology.isOpen_iff, WithZeroTopology.nhds_of_ne_zero, WithZeroTopology.hasBasis_nhds_zero]
  E1: auto
families: []
requires: [V06, V13, V14.C01, V14.C02, V14.C03, V14.C05]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Nonarchimedean groups and valued fields

### Overview

The $p$-adic absolute value satisfies the strong triangle inequality $|x + y|_p \le \max(|x|_p, |y|_p)$. As a result, the ball $\{x : |x|_p < r\}$ is an additive subgroup, every point of a ball is a centre of it, and every ball is both open and closed. This section studies the topologies with this property. A nonarchimedean group is a topological group in which every neighbourhood of $0$ contains an open subgroup. The main sources of such groups are the $I$-adic topology of a commutative ring and the topology of a valuation.

### Definitions

A topological additive group $G$ is *nonarchimedean* when every neighbourhood of $0$ contains an open subgroup. A topological ring is *nonarchimedean* when its additive group is.

Let $R$ be a commutative ring and $I$ an ideal. The *$I$-adic topology* on $R$ is the topology in which the neighbourhoods of $x$ are the sets that contain $x + I^n$ for some $n$. A topology on $R$ is *$I$-adic* when it is this topology.

Let $\Gamma_0$ be a linearly ordered commutative group with a zero adjoined, such as $\{0\} \cup \{\gamma^k : k \in \mathbb{Z}\}$ or $[0, \infty)$ under multiplication. A *valuation* $v : R \to \Gamma_0$ satisfies $v(0) = 0$, $v(1) = 1$, $v(xy) = v(x)v(y)$ and $v(x + y) \le \max(v(x), v(y))$. Its *topology* is the group topology on $R$ in which a set is a neighbourhood of $0$ when it contains a ball $\{x : v(x) < \gamma\}$ for some $\gamma \ne 0$ in the value group. A ring with this topology is a *valued ring*. The set $\Gamma_0$ carries the topology in which a set $U$ is open when $0 \notin U$ or $U$ contains an interval $\{\delta : \delta < \gamma\}$ with $\gamma \ne 0$; every nonzero point is isolated.

::: mathlib
`NonarchimedeanAddGroup` · `Mathlib.Topology.Algebra.Nonarchimedean.Basic`

The class `NonarchimedeanAddGroup G`, which extends `IsTopologicalAddGroup G` with the field `is_nonarchimedean : ∀ U ∈ 𝓝 0, ∃ V : OpenAddSubgroup G, (V : Set G) ⊆ U`. The class `NonarchimedeanRing R` is the same condition for a ring. The multiplicative form is `NonarchimedeanGroup`.

<?decl NonarchimedeanAddGroup?>
<?decl NonarchimedeanRing?>
:::

::: mathlib
`Ideal.adicTopology` · `Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology`

The definition `Ideal.adicTopology I : TopologicalSpace R`, built from the basis `Ideal.adic_basis` of submodules. The predicate `IsAdic I` says that the given topology on `R` is this topology, and `isAdic_iff` tests it by `(∀ n, IsOpen (I ^ n)) ∧ ∀ s ∈ 𝓝 0, ∃ n, (I ^ n : Set R) ⊆ s`.

<?decl Ideal.adicTopology?>
<?decl isAdic_iff?>
:::

::: mathlib
`Valued` · `Mathlib.Topology.Algebra.Valued.ValuationTopology`

The class `Valued R Γ₀` holds a valuation `Valued.v : Valuation R Γ₀`, a uniform structure and the field `is_topological_valuation`, which says that the neighbourhoods of `0` are the sets that contain a ball `{x | v.restrict x < γ}`. The map `v.restrict` takes values in the value group of `v`, the part of `Γ₀` that `v` reaches. The constructor `Valued.mk'` builds the instance from a valuation. The topology on `Γ₀` is `WithZeroTopology`, with the test `WithZeroTopology.isOpen_iff`.

<?decl Valued?>
<?decl Valued.mk'?>
<?decl WithZeroTopology.isOpen_iff?>
:::

### Theorems and proofs

**Theorem (Nonarchimedean groups are totally separated).** Let $G$ be a Hausdorff nonarchimedean group and $a \ne b$ in $G$. Then there is a set that is open and closed, contains $a$ and does not contain $b$. So $G$ is totally separated, and in particular totally disconnected.

*Proof.* Since $G$ is Hausdorff, there is a neighbourhood $U$ of $0$ with $b - a \notin U$. Choose an open subgroup $V \subseteq U$. The coset $a + V$ is open, since translation is a homeomorphism. Its complement is the union of the other cosets of $V$, each of them open, so $a + V$ is also closed. It contains $a$ and does not contain $b$, because $b - a \notin V$. A set $C$ that is open and closed separates $G$ into $C$ and $G \setminus C$, so the connected component of $a$ lies in $C$, and it does not contain $b$. $\square$

::: mathlib
`NonarchimedeanAddGroup.instTotallySeparated` · `Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected`

The instance `TotallySeparatedSpace G` for a Hausdorff nonarchimedean group. The step of the proof is `NonarchimedeanAddGroup.exists_openAddSubgroup_separating`, with the conclusion `∃ V, Disjoint (a +ᵥ ↑V) (b +ᵥ ↑V)`.

<?decl NonarchimedeanAddGroup.instTotallySeparated?>
<?decl NonarchimedeanAddGroup.exists_openAddSubgroup_separating?>
:::

**Theorem (The adic topology is nonarchimedean).** Let $I$ be an ideal of a commutative ring $R$. Then the $I$-adic topology makes $R$ a nonarchimedean topological ring, and each $I^n$ is an open subgroup.

*Proof.* The sets $I^n$ are additive subgroups and they decrease, so they form a filter basis at $0$, and the sets $x + I^n$ define a group topology on $(R, +)$ by the criterion of Chapter 1. Multiplication is continuous at $(x, y)$: from $(x + a)(y + b) - xy = xb + ay + ab$ and $a, b \in I^n$, the difference lies in $I^n$, since $I^n$ is an ideal. Each $I^n$ is a neighbourhood of every one of its points, so it is open, and every neighbourhood of $0$ contains some $I^n$. $\square$

::: mathlib
`Ideal.nonarchimedean` · `Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology`

The statement `NonarchimedeanRing R` for the topology `Ideal.adicTopology I`. The neighbourhoods of $0$ are given by `Ideal.hasBasis_nhds_zero_adic`. The general device behind it is `RingSubgroupsBasis` of `Mathlib.Topology.Algebra.Nonarchimedean.Bases`: a family of additive subgroups with the conditions of the proof defines a ring topology, by `RingSubgroupsBasis.topology`.

<?decl Ideal.nonarchimedean?>
<?decl RingSubgroupsBasis.topology?>
:::

**Theorem (Balls and spheres of a valuation).** Let $R$ be a valued ring and $\gamma \ne 0$ in the value group. Then the ball $B_\gamma = \{x : v(x) < \gamma\}$ is an open and closed subgroup, and the sphere $S_\gamma = \{x : v(x) = \gamma\}$ is open. So $R$ is a nonarchimedean ring, and $v$ is locally constant on $R \setminus \{0\}$.

*Proof.* The ball is a subgroup: $v(0) = 0 < \gamma$, $v(-x) = v(x)$, and $v(x + y) \le \max(v(x), v(y)) < \gamma$. It is a neighbourhood of $0$, so the subgroup $B_\gamma$ is open: for $x \in B_\gamma$, the set $x + B_\gamma = B_\gamma$ is a neighbourhood of $x$. An open subgroup is closed. For the sphere, let $v(x) = \gamma$ and $v(y - x) < \gamma$. Then $v(y) \le \max(v(x), v(y - x)) = \gamma$, and $\gamma = v(x) \le \max(v(y), v(x - y))$ forces $v(y) \ge \gamma$. So $x + B_\gamma \subseteq S_\gamma$, and $S_\gamma$ is open. Every $x$ with $v(x) \ne 0$ lies in the open set $S_{v(x)}$, on which $v$ is constant. $\square$

::: mathlib
`Valued.locally_const` · `Mathlib.Topology.Algebra.Valued.ValuationTopology`

The statement `v x ≠ 0 → {y | v y = v x} ∈ 𝓝 x`. The other facts of the theorem are `Valued.isClopen_ball`, `Valued.isOpen_sphere` and `Valued.isClopen_integer`, the last for the ring of integers $\{x : v(x) \le 1\}$. The criterion of neighbourhoods is `Valued.mem_nhds_zero`, and `Valued.continuous_valuation` gives the continuity of $v$ into $\Gamma_0$ on a division ring.

<?decl Valued.locally_const?>
<?decl Valued.isClopen_ball?>
<?decl Valued.continuous_valuation?>
:::

**Theorem (Extension to the completion).** Let $K$ be a valued field and $\hat K$ its completion. Then $v$ extends to a continuous valuation $\hat v : \hat K \to \Gamma_0$, and $\hat K$ is a valued field with $\hat v$.

*Proof.* Let $(x_n)$ be a Cauchy sequence in $K$ with limit $\xi \in \hat K$. The proof for Cauchy filters is the same. If $x_n \to 0$, set $\hat v(\xi) = 0$. Otherwise there is $\gamma \ne 0$ such that $v(x_n) \ge \gamma$ for infinitely many $n$. Since the sequence is Cauchy, $v(x_n - x_m) < \gamma$ for $n, m \ge N$. For such $n, m$ with $v(x_n) \ge \gamma$, the sphere argument of the previous proof gives $v(x_m) = v(x_n)$. So $v(x_n)$ is constant for $n \ge N$, and $\hat v(\xi)$ is this value. It does not depend on the sequence, since two sequences with the same limit have differences that tend to $0$. The rules of a valuation pass to the limit, as each holds for the terms. Continuity of $\hat v$ follows because $\hat v$ is constant on the closure of each sphere $S_\gamma$ with $\gamma \ne 0$. The fact that $\hat K$ is a field is the theorem of Chapter 3 on completions of fields: the valuation topology satisfies its condition, since a Cauchy filter that does not tend to $0$ has its valuations bounded below. $\square$

::: mathlib
`Valued.valuedCompletion` · `Mathlib.Topology.Algebra.Valued.ValuedField`

The instance `Valued (UniformSpace.Completion K) Γ₀` for a valued field `K`. The extension is `Valued.extension`, with `Valued.extension_extends` and `Valued.continuous_extension`. The condition of Chapter 3 is `Valued.completable : CompletableTopField K`, and `ValuedRing.separated` gives the Hausdorff property.

<?decl Valued.valuedCompletion?>
<?decl Valued.completable?>
<?decl Valued.continuous_extension?>
:::

### Examples

**Example (The p-adic topology on the integers).** On $\mathbb{Z}$ the $(p)$-adic topology has the neighbourhoods $x + p^n \mathbb{Z}$. It is Hausdorff, because $\bigcap_n p^n \mathbb{Z} = 0$, and it is the topology of the valuation $v(x) = p^{-\operatorname{ord}_p x}$. The sequence $1, 1 + p, 1 + p + p^2, \dots$ is Cauchy and has no limit in $\mathbb{Z}$; the completion is the ring $\mathbb{Z}_p$ of $p$-adic integers, `PadicInt p` of `Mathlib.NumberTheory.Padics.PadicIntegers`. The group $\mathbb{Z}_p$ is totally separated, as is every nonarchimedean Hausdorff group, but it is compact.

**Example (Ultrametric normed fields).** A normed field whose distance is ultrametric is a valued field with values in $[0, \infty)$. This applies to $\mathbb{Q}_p$. Conversely, a valued field whose value group embeds in $(0, \infty)$ carries a norm.

::: mathlib
`NormedField.toValued` · `Mathlib.Topology.Algebra.Valued.NormedValued`

The definition `[NormedField K] [IsUltrametricDist K] → Valued K ℝ≥0`. It is a definition and not an instance, to avoid two uniform structures on one field. The converse is `Valued.toNormedField`, under `Valued.v.RankOne`.

<?decl NormedField.toValued?>
<?decl Valued.toNormedField?>
:::

**Example (A counterexample: groups that are not nonarchimedean).** The real line is not nonarchimedean. An open subgroup of $\mathbb{R}$ contains an interval $(-\varepsilon, \varepsilon)$ and so all of $\mathbb{R}$, and the neighbourhood $(-1, 1)$ of $0$ contains no open subgroup. A second counterexample concerns the adic topology: for the ideal $I = R$, every $I^n$ equals $R$, and the $I$-adic topology is the indiscrete topology, which is nonarchimedean and not Hausdorff. The $I$-adic topology is Hausdorff exactly when $\bigcap_n I^n = 0$.

**Remark (Common errors).** The class `Valued` holds data: a uniform structure and a valuation. On a field that already has a topology, such as `ℚ_[p]` or `ℝ`, an instance from `Valued.mk'` gives a second topology, and lemmas about the two do not match. Use `NormedField.toValued` or the instance of the library for the field, and build `Valued.mk'` only on a type synonym such as `WithVal v` of `Mathlib.Topology.Algebra.Valued.WithVal`. A second error is to compare valuations in `Γ₀` when the lemmas are stated with `v.restrict`, which takes values in the value group of `v`.

### The library around it

The modules `Nonarchimedean.Basic`, `Bases` and `AdicTopology` treat nonarchimedean groups and rings, their bases of subgroups, and the adic topology. The lemmas `NonarchimedeanAddGroup.nonarchimedean_of_emb` and `NonarchimedeanAddGroup.prod_subset` show that the class passes to open embeddings and products, and `instNonarchimedeanAddGroupCompletion` that it passes to completions. The modules `Valued.ValuationTopology` and `Valued.ValuedField` treat valued rings and fields and their completions. Further modules treat the synonym `WithVal` and the locally compact valued fields (`Valued.LocallyCompact`).

### Exercises

1. (A) Show that in a nonarchimedean group every open subgroup is closed, and every coset of it is open and closed.
2. (A) Show that the $3$-adic sequence $\sum_{k < n} 3^k$ is Cauchy in $\mathbb{Z}$ and that its limit $\xi$ in $\mathbb{Z}_3$ satisfies $2\xi = -1$.
3. (A) Let $v$ be a valuation and $v(x) \ne v(y)$. Show that $v(x + y) = \max(v(x), v(y))$.
4. (B) Show that a nonarchimedean ring $R$ has, for every open subgroup $U$, an open subgroup $V$ with $V \cdot V \subseteq U$.
5. (B) Show that the $I$-adic topology on $R$ is Hausdorff exactly when $\bigcap_n I^n = 0$.
6. (B) Show that the trivial valuation, with $v(x) = 1$ for $x \ne 0$, gives the discrete topology. *Hint:* the ball $\{x : v(x) < 1\}$ is $\{0\}$.
7. (B) Show that $\mathbb{Z}_p$ has no connected subset with more than one point, and that it is not discrete.
8. (C) Let $K$ be a valued field and $\hat K$ its completion. Show that the value group of $\hat v$ equals the value group of $v$. *Hint:* use that $\hat v$ is locally constant away from $0$ and that $K$ is dense in $\hat K$.

### Notes and history

Hensel introduced the $p$-adic numbers in 1897, and Kürschák defined absolute values on fields in 1913. Krull extended the theory to valuations with values in ordered groups in 1932. His intersection theorem says that $\bigcap_n I^n = 0$ for a proper ideal $I$ of a Noetherian local ring, so the $I$-adic topology of such a ring is Hausdorff.

### Reference

<?reference?>
