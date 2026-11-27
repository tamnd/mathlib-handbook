---
title: Paths and path connectedness
kind: theory
modules:
  - Mathlib.Topology.Path
  - Mathlib.Topology.Connected.PathConnected
  - Mathlib.Topology.Connected.LocallyPathConnected
explains:
  E3: [Path, IsPathConnected, PathConnectedSpace]
  E2: [Path.refl, Path.symm, Path.trans, Path.map, Joined, JoinedIn, pathComponent, IsPathConnected.isConnected, PathConnectedSpace.connectedSpace, IsPathConnected.image, IsPathConnected.union, isPathConnected_iff_pathConnectedSpace, IsOpen.isConnected_iff_isPathConnected, LocallyPathConnectedSpace]
  E1: auto
families: []
requires: [V13.C01, V13.C02, V13.C05]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Paths and path connectedness

### Overview

A path from $x$ to $y$ is a continuous map $\gamma : [0, 1] \to X$ with $\gamma(0) = x$ and $\gamma(1) = y$. A set is path connected if each two of its points are joined by a path in it. This is a stronger and more concrete property than connectedness. This section proves that path connected sets are connected, that the two notions agree for open subsets of $\mathbb{R}^n$, and that they differ for the topologist's sine curve.

### Definitions

**Definition (Path).** Let $I = [0, 1]$. A path from $x$ to $y$ in $X$ is a continuous map $\gamma : I \to X$ with $\gamma(0) = x$ and $\gamma(1) = y$. The constant path at $x$ is $t \mapsto x$. The reverse of $\gamma$ is $t \mapsto \gamma(1 - t)$. If $\gamma$ goes from $x$ to $y$ and $\delta$ from $y$ to $z$, the concatenation $\gamma \cdot \delta$ is $\gamma(2t)$ for $t \le 1/2$ and $\delta(2t - 1)$ for $t \ge 1/2$.

The concatenation is continuous by the pasting lemma for the two closed halves of $I$, since both formulas give $y$ at $t = 1/2$.

::: mathlib
`Path` · `Mathlib.Topology.Path`

`Path x y` is a structure: a continuous map from `unitInterval` with the fields `source'` and `target'`. The constant path is `Path.refl x`, the reverse is `Path.symm`, and the concatenation is `Path.trans`. `Path.map` composes a path with a continuous map.

<?decl Path?>
:::

**Definition (Path connected).** Two points are joined if there is a path between them. A set $S$ is path connected if it is nonempty and each two points of $S$ are joined by a path with values in $S$. The path component of $x$ is the set of points joined to $x$.

::: mathlib
`IsPathConnected` · `Mathlib.Topology.Connected.PathConnected`

`IsPathConnected F` says that there is `x ∈ F` such that each `y ∈ F` satisfies `JoinedIn F x y`: a path from `x` to `y` stays in `F`. Joining to one point suffices, since paths can be reversed and concatenated. `Joined x y` is the relation on the whole space, and `pathComponent x` its class.

<?decl IsPathConnected?>
:::

::: mathlib
`PathConnectedSpace` · `Mathlib.Topology.Connected.PathConnected`

The class of nonempty spaces in which each two points are joined. `isPathConnected_iff_pathConnectedSpace` relates it to the set notion through the subtype.

<?decl PathConnectedSpace?>
:::

### Theorems and proofs

**Theorem (Path connected implies connected).** A path connected set is connected.

*Proof.* Let $S$ be path connected and $x \in S$. For each $y \in S$ choose a path $\gamma_y$ from $x$ to $y$ in $S$. The image $\gamma_y(I)$ is connected, since $I$ is connected (Section 1) and $\gamma_y$ is continuous. All these images contain $x$, and their union is $S$. By the union rule of Section 1, $S$ is connected. $\square$

::: mathlib
`IsPathConnected.isConnected` · `Mathlib.Topology.Connected.PathConnected`

The theorem. The instance `PathConnectedSpace.connectedSpace` is the space version.

<?decl IsPathConnected.isConnected?>
:::

**Theorem (Images and unions).** The image of a path connected set under a continuous map is path connected. The union of two path connected sets with a common point is path connected.

*Proof.* If $\gamma$ joins $x$ to $y$ in $S$, then $f \circ \gamma$ joins $f(x)$ to $f(y)$ in $f(S)$. For the union of $S$ and $T$ with $z \in S \cap T$, join each point of $S \cup T$ to $z$ inside $S$ or inside $T$. $\square$

::: mathlib
`IsPathConnected.image` · `Mathlib.Topology.Connected.PathConnected`

The image rule. `IsPathConnected.union` is the union rule.

<?decl IsPathConnected.image?>
:::

**Theorem (Open connected sets).** Let $U$ be an open connected subset of $\mathbb{R}^n$. Then $U$ is path connected.

*Proof.* Fix $x \in U$, and let $P$ be the set of points of $U$ joined to $x$ in $U$. Then $x \in P$.

$P$ is open. Let $y \in P$, and choose $r > 0$ with $B(y, r) \subseteq U$. For $z \in B(y, r)$, the segment $t \mapsto (1 - t) y + t z$ is a path from $y$ to $z$ in the ball, since balls are convex. Concatenate it with a path from $x$ to $y$. So $B(y, r) \subseteq P$.

$U \setminus P$ is open. Let $y \in U \setminus P$ and $B(y, r) \subseteq U$. If some $z \in B(y, r)$ were in $P$, a path from $x$ to $z$ and the segment from $z$ to $y$ would join $x$ to $y$. So $B(y, r) \subseteq U \setminus P$.

$U$ is connected, so $P$ is clopen in $U$ and nonempty, so $P = U$. $\square$

The proof used only one property of $\mathbb{R}^n$: each point has arbitrarily small path connected neighbourhoods. Spaces with this property are called locally path connected, and the theorem holds for open sets in each of them.

::: mathlib
`IsOpen.isConnected_iff_isPathConnected` · `Mathlib.Topology.Connected.LocallyPathConnected`

The theorem in a locally path connected space. The class `LocallyPathConnectedSpace` asks that each neighbourhood filter has a basis of path connected sets. Normed spaces over `ℝ` are instances.

<?decl IsOpen.isConnected_iff_isPathConnected?>
:::

**Theorem (Topologist's sine curve).** Let $A = \{(t, \sin(1/t)) : 0 < t \le 1\}$ and $B = \{0\} \times [-1, 1]$ in $\mathbb{R}^2$. The set $S = A \cup B$ is connected and not path connected.

*Proof.* $A$ is the image of $(0, 1]$ under a continuous map, so it is connected. Each point $(0, y)$ of $B$ is a limit of points of $A$: choose $s \in [-\pi/2, \pi/2]$ with $\sin s = y$, and let $t_k = 1/(s + 2\pi k)$. Then $(t_k, \sin(1/t_k)) = (t_k, y) \to (0, y)$. So $A \subseteq S \subseteq \overline{A}$, and $S$ is connected by the closure rule of Section 1.

Suppose a path $\gamma = (\gamma_1, \gamma_2)$ in $S$ goes from $(0, 0)$ to $(1, \sin 1)$. The set $\{u : \gamma_1(u) = 0\}$ is closed and contains $0$; let $u_0$ be its largest element. Then $u_0 < 1$, and $\gamma(u) \in A$ for $u > u_0$. By continuity at $u_0$, there is $\delta > 0$ with $|\gamma_2(u) - \gamma_2(u_0)| < 1/2$ for $u \in [u_0, u_0 + \delta]$. Let $a = \gamma_1(u_0 + \delta) > 0$. By the intermediate value theorem, $\gamma_1$ takes each value in $[0, a]$ on $[u_0, u_0 + \delta]$. Choose $k$ large with $1/(2\pi k + \pi/2)$ and $1/(2\pi k - \pi/2)$ both in $(0, a)$. At these values of $\gamma_1$ the second coordinate $\gamma_2$ is $1$ and $-1$. These two values differ by $2$, so both cannot be within $1/2$ of $\gamma_2(u_0)$. This is a contradiction. $\square$

### Examples

**Example (Convex sets).** A convex subset $C$ of a real vector space with a norm is path connected when nonempty: the segment $t \mapsto (1 - t) x + t y$ joins $x$ to $y$ in $C$. So balls, half spaces and $\mathbb{R}^n$ are path connected. Mathlib proves this as `Convex.isPathConnected`.

**Example (Spheres).** For $n \ge 2$ the sphere $S^{n-1} \subseteq \mathbb{R}^n$ is path connected. The map $x \mapsto x / \|x\|$ is continuous on $\mathbb{R}^n \setminus \{0\}$, and $\mathbb{R}^n \setminus \{0\}$ is path connected for $n \ge 2$: two points not on a line through $0$ are joined by a segment, and two other points are joined through a third point off that line. The image of a path connected set is path connected.

**Counterexample (Components and path components).** In the topologist's sine curve, the path components are $A$ and $B$, and there is one component. So path components need not be closed: the closure of $A$ is all of $S$.

### The library around it

Paths and their operations are in `Mathlib.Topology.Path`. The relations `Joined` and `JoinedIn`, path components and path connected sets are in `Mathlib.Topology.Connected.PathConnected`. Local path connectedness is in `Mathlib.Topology.Connected.LocallyPathConnected`. Homotopies of paths and the fundamental group build on `Path` in the volume on algebraic topology.

The reference table at the end of the section lists the declarations of the modules.

### Exercises

1. (A) Show that the relation "joined" is an equivalence relation.
2. (A) Show that a product of two path connected spaces is path connected.
3. (A) Show that the path component of a point lies in its connected component.
4. (B) Show that $\mathbb{R}^2$ minus a countable set is path connected.
5. (B) Show that an open subset of $\mathbb{R}^n$ has open path components, and that these are its components.
6. (B) Show that the closure of the graph of $t \mapsto t \sin(1/t)$ on $(0, 1]$ is path connected.
7. (C) Show that no continuous injective map sends $\mathbb{R}^2$ into $\mathbb{R}$.

### Notes and history

Paths were used long before the general definition, in complex analysis and in the work of Weierstrass on domains. The topologist's sine curve appears in many textbooks as the standard example of a connected set that is not path connected. Mathlib chose the unit interval as the domain of paths, with concatenation at $1/2$, which is the standard convention of homotopy theory.

### Reference

<?reference?>
