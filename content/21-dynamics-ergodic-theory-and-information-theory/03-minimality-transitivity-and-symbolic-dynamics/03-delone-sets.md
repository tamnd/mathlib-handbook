---
title: Delone sets
kind: theory
modules:
  - Mathlib.Analysis.AperiodicOrder.Delone.Basic
explains:
  E3: [Delone.DeloneSet, Delone.DeloneSet.packingRadius, Delone.DeloneSet.coveringRadius, Delone.DeloneSet.subset_ball_singleton, Delone.DeloneSet.mapBilipschitz, Delone.DeloneSet.mapIsometry]
  E2: [Delone.DeloneSet.packingRadius_pos, Delone.DeloneSet.coveringRadius_pos, Delone.DeloneSet.isSeparated_packingRadius, Delone.DeloneSet.isCover_coveringRadius, Delone.DeloneSet.packingRadius_lt_dist_of_mem_ne, Delone.DeloneSet.exists_dist_le_coveringRadius, Delone.DeloneSet.nonempty, Delone.DeloneSet.ext, Delone.DeloneSet.copy, Delone.DeloneSet.mapBilipschitz_carrier, Delone.DeloneSet.mapBilipschitz_packingRadius, Delone.DeloneSet.mapBilipschitz_coveringRadius, Delone.DeloneSet.mapBilipschitz_refl, Delone.DeloneSet.mapBilipschitz_trans, Delone.DeloneSet.mapIsometry_apply_carrier, Delone.DeloneSet.mapIsometry_symm, Delone.DeloneSet.mapIsometry_trans]
  E1: auto
families: []
requires: [V04, V13, V18]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Delone sets

### Overview

A Delone set is a set of points spread evenly through a metric space: no two points are too close, and no point of the space is too far from the set. The integer lattice and the vertices of a Penrose tiling are examples, and the atoms of a crystal or a quasicrystal the physical model. They are the objects of the theory of aperiodic order. This section defines Delone sets as Mathlib does, with a chosen packing radius and covering radius, proves that they exist, that they have uniform density in $\mathbb{R}^n$, and that bilipschitz maps carry them to Delone sets. Metric spaces come from Volume 13, Chapter 3, Zorn's lemma from Volume 4 and Lebesgue measure from Volume 18.

### Definitions

**Definition (Separated set, cover).** Let $X$ be a metric space, $D \subseteq X$ and $r, R > 0$. The set $D$ is *$r$-separated* if $d(x, y) > r$ for all distinct $x, y \in D$. It is an *$R$-cover* of $X$ if every $x \in X$ has some $y \in D$ with $d(x, y) \le R$.

**Definition (Delone set).** A *Delone set* in $X$ is a set $D$ with numbers $r, R > 0$, its *packing radius* and *covering radius*, such that $D$ is $r$-separated and an $R$-cover of $X$.

A set that is $r$-separated for some $r > 0$ is *uniformly discrete*, and an $R$-cover for some $R$ is *relatively dense*; a Delone set has both properties.

::: mathlib
`Delone.DeloneSet` · `Mathlib.Analysis.AperiodicOrder.Delone.Basic`

`DeloneSet X` for `[MetricSpace X]` is a structure with `carrier : Set X`, `packingRadius : ℝ≥0`, `packingRadius_pos`, `isSeparated_packingRadius : Metric.IsSeparated packingRadius carrier`, `coveringRadius : ℝ≥0`, `coveringRadius_pos` and `isCover_coveringRadius : Metric.IsCover coveringRadius univ carrier`. `ext` says that two Delone sets are equal when the carriers and both radii agree, and `copy` replaces the fields by equal ones.

<?decl Delone.DeloneSet?>
:::

Two conventions matter. The packing radius is a strict lower bound for the distances, not half the minimal distance as for sphere packings. And the radii are data: the same carrier with a smaller packing radius is a different term of `DeloneSet X`.

::: mathlib
`Delone.DeloneSet.packingRadius` · `Mathlib.Analysis.AperiodicOrder.Delone.Basic`

`packingRadius_lt_dist_of_mem_ne : x ∈ D → y ∈ D → x ≠ y → ↑D.packingRadius < dist x y`, and on the other side `exists_dist_le_coveringRadius : ∃ y ∈ D, dist x y ≤ ↑D.coveringRadius` for every `x : X`. With `[Nonempty X]`, `D.nonempty` says that the carrier is nonempty.

<?decl Delone.DeloneSet.packingRadius?>
:::

### Theorems and proofs

**Proposition (Small balls).** For a Delone set $D$ with packing radius $r$, every open ball of radius $r/2$ contains at most one point of $D$.

*Proof.* If $x, y \in D$ lie in the ball of radius $r/2$ about $z$, then $d(x, y) \le d(x, z) + d(z, y) < r$, so $x = y$ by separation. $\square$

::: mathlib
`Delone.DeloneSet.subset_ball_singleton` · `Mathlib.Analysis.AperiodicOrder.Delone.Basic`

`∃ r > 0, ∀ {x y z}, x ∈ D → y ∈ D → x ∈ ball z r → y ∈ ball z r → x = y`. The proof takes half the packing radius.

<?decl Delone.DeloneSet.subset_ball_singleton?>
:::

**Theorem (Existence).** Let $X$ be a nonempty metric space and $\varepsilon > 0$. Every maximal $\varepsilon$-separated subset of $X$ is an $\varepsilon$-cover, and such a set exists. So $X$ has a Delone set with packing radius and covering radius $\varepsilon$.

*Proof.* The union of a chain of $\varepsilon$-separated sets is $\varepsilon$-separated, since two distinct points of the union lie in one member of the chain. Zorn's lemma gives a maximal $\varepsilon$-separated set $N$. Let $x \in X$. If $d(x, y) > \varepsilon$ for all $y \in N$, then $x \notin N$ and $N \cup \{x\}$ is $\varepsilon$-separated, against maximality. So some $y \in N$ has $d(x, y) \le \varepsilon$. $\square$

::: mathlib
`Metric.IsCover.of_maximal_isSeparated` · `Mathlib.Topology.MetricSpace.Cover`

`Maximal (fun N ↦ N ⊆ s ∧ IsSeparated ε N) N → IsCover ε s N`, the first step of the proof, in a pseudo-extended metric space and relative to a set `s`. Zorn's lemma for sets is `zorn_subset`. The index of this edition has no declaration that builds a `DeloneSet` from it.

<?decl Metric.IsCover.of_maximal_isSeparated?>
:::

**Theorem (Uniform density).** Let $D$ be a Delone set in $\mathbb{R}^n$ with the Euclidean metric, packing radius $r$ and covering radius $R$, and let $N(\rho)$ be the number of points of $D$ in the closed ball $\bar B(0, \rho)$. Then
$$\Big(\frac{\rho - R}{R}\Big)^n \le N(\rho) \le \Big(\frac{2\rho}{r} + 1\Big)^n \qquad (\rho \ge R).$$

*Proof.* Let $\lambda$ be Lebesgue measure, with $\lambda(\bar B(z, s)) = c_n s^n$. For the upper bound, the open balls $B(d, r/2)$, $d \in D \cap \bar B(0, \rho)$, are disjoint by the proposition (a common point $z$ would put both centres in $B(z, r/2)$), and they lie in $B(0, \rho + r/2)$. So $N(\rho) c_n (r/2)^n \le c_n (\rho + r/2)^n$. For the lower bound, let $x \in \bar B(0, \rho - R)$. Some $d \in D$ has $|x - d| \le R$, so $|d| \le \rho$. Thus the balls $\bar B(d, R)$, $d \in D \cap \bar B(0, \rho)$, cover $\bar B(0, \rho - R)$, and $c_n(\rho - R)^n \le N(\rho)\, c_n R^n$. $\square$

So the number of points in a ball of radius $\rho$ grows like $\rho^n$, as for a lattice. The index of this edition has no declaration for these bounds.

**Theorem (Bilipschitz images).** Let $f : X \to Y$ be a bijection of metric spaces with $d(x, x') \le K_1\, d(f(x), f(x'))$ and $d(f(x), f(x')) \le K_2\, d(x, x')$ for constants $K_1, K_2 > 0$. If $D$ is a Delone set in $X$ with radii $r$ and $R$, then $f(D)$ is a Delone set in $Y$ with radii $r/K_1$ and $K_2 R$. For an isometry, both radii are kept, and $D \mapsto f(D)$ is a bijection between the Delone sets of $X$ and of $Y$.

*Proof.* For distinct $x, x' \in D$, $d(f(x), f(x')) \ge d(x, x')/K_1 > r/K_1$. For $y \in Y$, write $y = f(x)$ and take $z \in D$ with $d(x, z) \le R$; then $d(y, f(z)) \le K_2 R$. An isometry has $K_1 = K_2 = 1$, and its inverse is an isometry, which gives the inverse map on Delone sets. $\square$

::: mathlib
`Delone.DeloneSet.mapBilipschitz` · `Mathlib.Analysis.AperiodicOrder.Delone.Basic`

`mapBilipschitz f K₁ K₂ hK₁ hK₂ hf₁ hf₂ D` for `f : X ≃ Y`, `AntilipschitzWith K₁ f` and `LipschitzWith K₂ f`. The lemmas `mapBilipschitz_carrier`, `mapBilipschitz_packingRadius : ... = D.packingRadius / K₁` and `mapBilipschitz_coveringRadius : ... = K₂ * D.coveringRadius` give its fields, and `mapBilipschitz_refl` and `mapBilipschitz_trans` its behaviour under the identity and composition.

<?decl Delone.DeloneSet.mapBilipschitz?>
:::

::: mathlib
`Delone.DeloneSet.mapIsometry` · `Mathlib.Analysis.AperiodicOrder.Delone.Basic`

`mapIsometry (f : X ≃ᵢ Y) : DeloneSet X ≃ DeloneSet Y`, an equivalence of types, with `mapIsometry_symm : (mapIsometry f).symm = mapIsometry f.symm`, `mapIsometry_trans` and `mapIsometry_apply_carrier`.

<?decl Delone.DeloneSet.mapIsometry?>
:::

### Examples

**Example (The integer lattice).** In $\mathbb{R}^n$ with the Euclidean metric, distinct points of $\mathbb{Z}^n$ have distance at least $1$. So every $r < 1$ is a packing radius in the sense of Mathlib, but $r = 1$ is not, because the inequality is strict. Every $x \in \mathbb{R}^n$ is within $\sqrt n/2$ of $\mathbb{Z}^n$: round each coordinate to a nearest integer, with an error at most $1/2$ in each coordinate. The point $(1/2, \ldots, 1/2)$ has distance exactly $\sqrt n/2$ from $\mathbb{Z}^n$, so $\sqrt n/2$ is the least covering radius. For an invertible matrix $A$, the lattice $A\mathbb{Z}^n$ is the image under the bilipschitz map $x \mapsto Ax$, with $K_1 = \|A^{-1}\|$ and $K_2 = \|A\|$; so it is a Delone set with radii $r/\|A^{-1}\|$ and $\|A\|\sqrt n/2$.

**Example (A Penrose-type set).** A Penrose rhombus tiling covers the plane by two rhombi with sides of length $1$, a thick one with angles $72$ and $108$ degrees and a thin one with angles $36$ and $144$ degrees, placed edge to edge by matching rules. Its vertex set $D$ is a Delone set. Each point of the plane lies in a tile, so it is within the diameter of a tile of a vertex: this gives a covering radius. There are finitely many ways, up to rotation and translation, in which tiles meet at a vertex, and in each of them distinct vertices have a positive distance; the least of these is a packing radius. No translation maps $D$ onto itself, so $D$ is a Delone set without any periodicity. The index of this edition has no declaration for Penrose tilings or for cut and project sets.

### The library around it

The module is the start of a theory of aperiodic order. In that theory a Delone set $D$ in $\mathbb{R}^n$ defines a dynamical system: $\mathbb{R}^n$ acts on the closure of the set of translates $D - t$ in a suitable topology, the hull of $D$. Its minimality and ergodicity, in the sense of Section 1 and Chapter 6, describe the order of $D$. The index of this edition has no declaration for the hull.

Common errors of a learner:

- The packing radius is a strict bound and is not half the minimal distance; read the definition before using a formula from the literature.
- Two `DeloneSet` terms with the same carrier need not be equal; compare `carrier` when only the set matters.
- `mapBilipschitz` takes an equivalence `X ≃ Y`, not only a map, since the covering property needs surjectivity.

### Exercises

1. (A) Show that $\mathbb{Z}$ is a Delone set in $\mathbb{R}$ and find the least covering radius. Show that $\{n^2 : n \in \mathbb{Z}\}$ is not relatively dense.
2. (A) Show that a finite set is a Delone set of $\mathbb{R}^n$ only if $n = 0$, and that every finite metric space is a Delone set of itself.
3. (B) Show that the set $\{n + \frac{1}{2}\sin n : n \in \mathbb{Z}\}$ is a Delone set in $\mathbb{R}$ and give radii for it.
4. (B) Let $D$ be a Delone set in $\mathbb{R}^n$, $n \ge 1$, with packing radius $r$ and covering radius $R$. Show that $r < 2R$. Hint: for $x \in D$ and $\eta > 0$, the cover at a point $z$ with $|z - x| = R + \eta$ gives $d \in D \setminus \{x\}$ with $|d - x| \le 2R + \eta$; only finitely many points of $D$ lie near $x$.
5. (B) Show that the union of two Delone sets with packing radius $r$ need not be uniformly discrete, and that it is relatively dense.
6. (C) Let $\alpha > 0$ be irrational. Show that $D = \{n + \lfloor n\alpha \rfloor : n \in \mathbb{Z}\}$ is a Delone set in $\mathbb{R}$ with $D + t \neq D$ for every $t \neq 0$. Hint: the gaps between consecutive points take two values, and the frequency of the larger gap is the fractional part of $\alpha$.

### Notes and history

The name honours Boris Delone, also written Delaunay, who studied such point systems in the geometry of crystals. Penrose described his aperiodic tilings in 1974, and de Bruijn showed in 1981 that they arise by projection from $\mathbb{Z}^5$.

### Reference

<?reference?>
