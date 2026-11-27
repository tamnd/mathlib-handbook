---
title: Extreme points and the theorem of Krein and Milman
kind: theory
modules:
  - Mathlib.Analysis.Convex.Extreme
  - Mathlib.Analysis.Convex.Exposed
  - Mathlib.Analysis.Convex.KreinMilman
  - Mathlib.Analysis.Convex.Intrinsic
explains:
  E3: [IsExtreme, Set.extremePoints, IsExposed, Set.exposedPoints, closure_convexHull_extremePoints, IsCompact.extremePoints_nonempty, intrinsicInterior, Set.Nonempty.intrinsicInterior]
  E2: [mem_extremePoints, IsExtreme.trans, isExtreme_sInter, IsExtreme.extremePoints_eq, extremePoints_convexHull_subset, Convex.mem_extremePoints_iff_convex_sdiff, IsExposed.isExtreme]
  E1: auto
families: []
requires: [V07, V13, V16.C05, V22.C02, V22.C06, V22.C07]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Extreme points and the theorem of Krein and Milman

### Overview

A square is the convex hull of its four corners, and a disc is the convex hull of its boundary circle. In both cases the set is the hull of the points that do not lie inside a segment of the set. These are the extreme points. The theorem of Krein and Milman says that this holds for every compact convex set in a locally convex Hausdorff space, up to a closure. The section proves the theorem of Minkowski in $\mathbb{R}^d$, where no closure is necessary, and sketches the general proof.

### Definitions

Let $E$ be a real vector space and $A \subseteq E$. The open segment $]x, y[$ is the set of $(1 - t)x + ty$ with $0 < t < 1$.

**Definition (extreme subset).** A set $B \subseteq A$ is an *extreme subset* of $A$ if for all $x, y \in A$ and $z \in B$ with $z \in\, ]x, y[$, both $x$ and $y$ lie in $B$.

**Definition (extreme point).** A point $x \in A$ is an *extreme point* of $A$ if $\{x\}$ is an extreme subset of $A$. Equivalently, $x \in\, ]x_1, x_2[$ with $x_1, x_2 \in A$ forces $x_1 = x_2 = x$. The set of extreme points is $\mathrm{ext}(A)$.

**Definition (exposed subset).** Let $E$ be a topological vector space. A set $B \subseteq A$ is an *exposed subset* of $A$ if $B$ is empty or there is a continuous linear functional $\ell$ with $B = \{x \in A : \ell(y) \le \ell(x) \text{ for all } y \in A\}$. A point $x$ is an *exposed point* if some $\ell$ attains its maximum on $A$ at $x$ and only at $x$.

**Definition (intrinsic interior).** Let $E$ be a topological vector space. The *intrinsic interior* of $A$ is the interior of $A$ as a subset of its affine span $\mathrm{aff}(A)$, with the subspace topology.

### Theorems and proofs

**Lemma (extreme sets).** Let $A \subseteq E$.

1. If $B$ is extreme in $A$ and $C$ is extreme in $B$, then $C$ is extreme in $A$.
2. A nonempty intersection of extreme subsets of $A$ is extreme in $A$.
3. If $B$ is extreme in $A$, then $\mathrm{ext}(B) = B \cap \mathrm{ext}(A)$.

*Proof.* (1) Let $x, y \in A$ and $z \in C$ with $z \in\, ]x, y[$. Since $C \subseteq B$ and $B$ is extreme, $x, y \in B$. Since $C$ is extreme in $B$, $x, y \in C$. (2) is immediate from the definition. (3) Apply (1) with $C = \{x\}$ for one inclusion. For the other, a point of $B$ that is extreme in $A$ is extreme in the smaller set $B$. $\square$

For convex $A$ and $x \in A$, $x \in \mathrm{ext}(A)$ if and only if $A \setminus \{x\}$ is convex: a segment of $A \setminus \{x\}$ cannot pass through an extreme point $x$, and conversely $x \in\, ]x_1, x_2[$ with $x_1, x_2 \ne x$ breaks the convexity of $A \setminus \{x\}$. By Chapter 7, Section 1, this is also $x \notin \mathrm{conv}(A \setminus \{x\})$.

**Lemma (extreme points of a hull).** $\mathrm{ext}(\mathrm{conv}(A)) \subseteq A$.

*Proof.* Let $x \in \mathrm{conv}(A) \setminus A$. Then $A \subseteq \mathrm{conv}(A) \setminus \{x\}$. If $x$ were extreme in $\mathrm{conv}(A)$, the remark above would make $\mathrm{conv}(A) \setminus \{x\}$ a convex set that contains $A$, so it would contain $\mathrm{conv}(A)$ and therefore $x$. $\square$

**Lemma (exposed is extreme).** An exposed subset is extreme. In particular an exposed point is extreme.

*Proof.* Let $B = \{x \in A : \ell(x) = M\}$ where $M = \max_A \ell$. Let $x, y \in A$ and $z = (1 - t)x + ty \in B$ with $0 < t < 1$. Then $M = (1 - t)\ell(x) + t\ell(y)$ with $\ell(x), \ell(y) \le M$, so $\ell(x) = \ell(y) = M$ and $x, y \in B$. $\square$

**Theorem (Krein-Milman lemma in $\mathbb{R}^d$).** A nonempty compact set $K \subseteq \mathbb{R}^d$ has an extreme point.

*Proof.* The Euclidean norm attains a maximum on $K$ at some $x$. Suppose $x = (1 - t)x_1 + tx_2$ with $x_1, x_2 \in K$ and $0 < t < 1$. Then $\|x\| \le (1 - t)\|x_1\| + t\|x_2\| \le \|x\|$, so $\|x_1\| = \|x_2\| = \|x\|$ with equality in the triangle inequality. The Euclidean norm is strictly convex, so $x_1 = x_2 = x$. $\square$

**Theorem (Minkowski).** Let $K \subseteq \mathbb{R}^d$ be compact and convex. Then $K = \mathrm{conv}(\mathrm{ext}(K))$.

*Proof.* The inclusion $\supseteq$ holds because $K$ is convex. For $\subseteq$, induct on the dimension $m$ of $\mathrm{aff}(K)$. If $K$ is empty or $m = 0$, then $K$ has at most one point and the claim is clear. Let $m \ge 1$. Work in $\mathrm{aff}(K)$, identified with $\mathbb{R}^m$ by an affine map. There $K$ has a nonempty interior, its intrinsic interior, whose closure is $K$.

Let $x \in K$ be on the boundary. Since $x$ is not in the open convex set $\mathrm{int}(K)$, the geometric form of Hahn-Banach (Volume 16, Chapter 5) gives a linear $\ell$ with $\ell(a) < \ell(x)$ on $\mathrm{int}(K)$. By continuity $\ell \le \ell(x)$ on $K$. So $F = \{y \in K : \ell(y) = \ell(x)\}$ is an exposed subset of $K$, compact and convex, and it lies in a hyperplane, so $\dim \mathrm{aff}(F) < m$. By induction $x \in \mathrm{conv}(\mathrm{ext}(F))$, and $\mathrm{ext}(F) = F \cap \mathrm{ext}(K)$ by the lemma on extreme sets.

Let $x$ be an interior point. Take any line $L$ through $x$ in $\mathrm{aff}(K)$. Then $K \cap L$ is a compact segment $[y, z]$, and its endpoints lie on the boundary of $K$. By the previous case $y, z \in \mathrm{conv}(\mathrm{ext}(K))$, so $x$ is there too. $\square$

**Theorem (Krein-Milman).** Let $E$ be a Hausdorff locally convex real topological vector space and $K \subseteq E$ compact and convex. Then $K = \overline{\mathrm{conv}}(\mathrm{ext}(K))$, the closure of the hull of the extreme points.

Sketch of the Mathlib proof. Zorn's lemma gives a minimal nonempty closed extreme subset $T$ of a nonempty compact set. If $T$ had two points $x \ne y$, a separating functional would expose a smaller closed extreme subset of $T$ that misses $y$, and by transitivity this subset would be extreme in the original set. So $T$ is a single extreme point. For the theorem, if $x \in K$ were outside the closed convex set $C = \overline{\mathrm{conv}}(\mathrm{ext}(K))$, a functional $\ell$ would separate $x$ from $C$. The set $F$ where $\ell$ is maximal on $K$ is compact, nonempty and exposed, and it misses $C$ because $\max_K \ell \ge \ell(x) > \sup_C \ell$. By the lemma $F$ has an extreme point. It is extreme in $K$, so it lies in $C$, which is absurd.

### Examples

**Example (a square and a disc).** Let $Q = [0,1]^2$. A point with $0 < u < 1$ lies inside a horizontal segment of $Q$, and the same holds for $v$, so $\mathrm{ext}(Q) \subseteq \{0,1\}^2$. Each corner is exposed: for $(1,1)$ take $\ell(u,v) = u + v$. So $\mathrm{ext}(Q)$ is the four corners, and $Q$ is their hull. For the closed unit disc $D$, every point $p$ with $\|p\| = 1$ is exposed by $\ell(q) = \langle p, q \rangle$, and no point with $\|p\| < 1$ is extreme.

**Counterexample (extreme but not exposed).** Let $S$ be the hull of the disc of radius $1$ at $(0,0)$ and the square $[0, 2] \times [-1, 1]$. The point $(0, 1)$ is extreme: it is on the circle and is not inside any segment of $S$. A functional that attains its maximum on $S$ at $(0,1)$ must be a positive multiple of $v$, because the circle has the tangent $v = 1$ there. That functional is maximal on the whole edge from $(0,1)$ to $(2,1)$. So $(0,1)$ is not exposed.

### The library around it

::: mathlib
`IsExtreme` · `Mathlib.Analysis.Convex.Extreme`

`Set.extremePoints 𝕜 A` is defined by `mem_extremePoints`. The lemma on extreme sets is `IsExtreme.trans`, `isExtreme_sInter` and `IsExtreme.extremePoints_eq`. `Convex.mem_extremePoints_iff_convex_sdiff` is the remark after it, and `extremePoints_convexHull_subset` is the lemma on hulls.

<?decl IsExtreme?>
:::

::: mathlib
`IsExposed` · `Mathlib.Analysis.Convex.Exposed`

`IsExposed 𝕜 A B` says `B.Nonempty → ∃ l : StrongDual 𝕜 E, B = { x ∈ A | ∀ y ∈ A, l y ≤ l x }`. `IsExposed.isExtreme` is the lemma that exposed implies extreme, and `Set.exposedPoints` is the set of exposed points.

<?decl IsExposed?>
:::

::: mathlib
`IsCompact.extremePoints_nonempty` · `Mathlib.Analysis.Convex.KreinMilman`

The Krein-Milman lemma: in a Hausdorff locally convex space, a nonempty compact set has an extreme point.

<?decl IsCompact.extremePoints_nonempty?>
:::

::: mathlib
`closure_convexHull_extremePoints` · `Mathlib.Analysis.Convex.KreinMilman`

The theorem: `closure (convexHull ℝ (s.extremePoints ℝ)) = s` for `s` compact and convex.

<?decl closure_convexHull_extremePoints?>
:::

The docstring of the file states that the theorem of Minkowski is not in Mathlib, and the index has no declaration for it.

::: mathlib
`intrinsicInterior` · `Mathlib.Analysis.Convex.Intrinsic`

`intrinsicInterior 𝕜 s` is the interior of `s` inside `affineSpan 𝕜 s`. `Set.Nonempty.intrinsicInterior` says that a nonempty convex set in finite dimension has a nonempty intrinsic interior, the fact that starts the induction for Minkowski.

<?decl Set.Nonempty.intrinsicInterior?>
:::

### Exercises

1. (A) Find the extreme points and the exposed points of the triangle with vertices $(0,0)$, $(1,0)$, $(0,1)$, and of the half-plane $\{v \ge 0\}$.
2. (A) Show that an extreme point of $A$ that lies in a convex subset $B \subseteq A$ is extreme in $B$.
3. (B) Show that $\mathrm{ext}(A \times B) = \mathrm{ext}(A) \times \mathrm{ext}(B)$ for any sets $A$ and $B$.
4. (B) Show that the extreme points of the closed unit ball of $\ell^1$ in $\mathbb{R}^d$ are the points $\pm e_i$.
5. (B) Show that the closed unit ball of the space $c_0$ of real sequences that tend to $0$, with the sup norm, has no extreme points. Explain why this does not contradict Krein-Milman.
6. (C) Show that in Minkowski's theorem each point of $K \subseteq \mathbb{R}^d$ is a convex combination of at most $d + 1$ extreme points. Hint: combine with Caratheodory from Chapter 7.

### Notes and history

Minkowski proved the finite-dimensional theorem in his work on convex bodies, published after his death in 1911. Krein and Milman proved the general theorem in 1940. The Mathlib files on extreme and exposed sets name Yaël Dillies and Bhavik Mehta as authors, the file on Krein-Milman names Yaël Dillies, and the file on the intrinsic interior names Paul Reichert and Yaël Dillies.

### Reference

<?reference?>
