---
title: Omega-limit sets
kind: theory
modules:
  - Mathlib.Dynamics.OmegaLimit
explains:
  E3: [omegaLimit, isClosed_omegaLimit, mem_omegaLimit_iff_frequently, nonempty_omegaLimit, Flow.isInvariant_omegaLimit, eventually_closure_subset_of_isOpen_of_omegaLimit_subset]
  E2: [omegaLimit_def, mem_omegaLimit_iff_frequently₂, mem_omegaLimit_singleton_iff_mapClusterPt, nonempty_omegaLimit_of_isCompact_absorbing, eventually_mapsTo_of_isOpen_of_omegaLimit_subset, Flow.omegaLimit_image_eq, Flow.omegaLimit_omegaLimit, mapsTo_omegaLimit, omegaLimit_mono_left, omegaLimit_mono_right, omegaLimit_union, omegaLimit_subset_of_tendsto]
  E1: auto
families: []
requires: [V13, V21.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Omega-limit sets

### Overview

The $\omega$-limit set of a point collects the places that its orbit visits again and again in the far future. This section defines it for a filter of times and a set of starting points, as Mathlib does, and proves its four basic properties on a compact space: it is closed, nonempty, invariant, and it absorbs the orbit. For a flow of $\mathbb{R}$ it is also connected, a fact that the index does not have. The flows are those of Section 1, and the filters and compactness come from Volume 13, Chapters 2 and 5.

### Definitions

**Definition ($\omega$-limit set).** Let $f$ be a filter on a set $\tau$ of times, $X$ a set, $Y$ a topological space, $\phi : \tau \times X \to Y$ and $S \subseteq X$. The *$\omega$-limit set* of $S$ is
$$\omega_f(\phi, S) = \bigcap_{u \in f} \overline{\phi(u \times S)},$$
where $\phi(u \times S) = \{\phi_t(x) : t \in u,\ x \in S\}$.

The main case is a flow of $\mathbb{R}$ or $\mathbb{N}$, the filter $f$ of the sets that contain some $[T, \infty)$, and $S = \{x\}$. Then
$$\omega(x) = \bigcap_{T} \overline{\{\phi_t(x) : t \ge T\}}.$$
For the filter at $-\infty$ the same formula gives the *$\alpha$-limit set*, the past of the orbit.

::: mathlib
`omegaLimit` · `Mathlib.Dynamics.OmegaLimit`

`omegaLimit f ϕ s` for `f : Filter τ`, `ϕ : τ → α → β` and `s : Set α`, with `[TopologicalSpace β]` and no structure on `τ` or `α`. `omegaLimit_def` unfolds it to `⋂ u ∈ f, closure (image2 ϕ u s)`. The notation `ω f ϕ s` is the general set, `ω⁺ ϕ s` the case `f = atTop` and `ω⁻ ϕ s` the case `f = atBot`, which is the $\alpha$-limit set.

<?decl omegaLimit?>
:::

### Theorems and proofs

**Theorem (Closed, and the characterization).** The set $\omega_f(\phi, S)$ is closed. A point $y$ lies in it if and only if, for every neighbourhood $N$ of $y$, the set of times $t$ with $\phi_t(S) \cap N \neq \emptyset$ meets every member of $f$. For $f$ the filter at $\infty$ on $\mathbb{N}$, $S = \{x\}$ and a metric space $Y$, this says that $y = \lim \phi_{t_k}(x)$ for some $t_k \to \infty$.

*Proof.* The set is an intersection of closures, so it is closed. Let $y \in \omega_f(\phi, S)$, $N$ a neighbourhood of $y$ and $u \in f$. Then $y \in \overline{\phi(u \times S)}$, so $N$ meets $\phi(u \times S)$, and some $t \in u$ has $\phi_t(S) \cap N \neq \emptyset$. Conversely, suppose the condition, and let $u \in f$ and $N$ a neighbourhood of $y$. Some $t \in u$ has $\phi_t(S)$ meeting $N$, so $N$ meets $\phi(u \times S)$, and $y \in \overline{\phi(u \times S)}$. For a metric space, take $N$ the ball of radius $1/k$ and $u = \{t \ge t_{k-1} + 1\}$ to choose $t_k$. $\square$

::: mathlib
`mem_omegaLimit_iff_frequently` · `Mathlib.Dynamics.OmegaLimit`

`y ∈ omegaLimit f ϕ s ↔ ∀ n ∈ 𝓝 y, ∃ᶠ t in f, (s ∩ ϕ t ⁻¹' n).Nonempty`. The form with images is `mem_omegaLimit_iff_frequently₂`, and the one for a point is `mem_omegaLimit_singleton_iff_mapClusterPt`, with `MapClusterPt` of Volume 13, Chapter 2. Closedness is `isClosed_omegaLimit`.

<?decl mem_omegaLimit_iff_frequently?>
:::

**Theorem (Nonempty).** Let $Y$ be compact, $f$ a proper filter (one that does not contain $\emptyset$) and $S$ nonempty. Then $\omega_f(\phi, S)$ is nonempty. The same holds if $Y$ is any space and $\overline{\phi(v \times S)}$ lies in a compact set $K$ for some $v \in f$.

*Proof.* The sets $C_u = \overline{\phi(u \times S)}$, $u \in f$, are closed and nonempty, since $u \neq \emptyset$ and $S \neq \emptyset$. They are directed downward: $C_{u \cap u'} \subseteq C_u \cap C_{u'}$ and $u \cap u' \in f$. So every finite intersection contains some $C_u$ and is nonempty, and compactness of $Y$ gives a point in all of them. For the second claim, apply the same argument to the closed sets $C_{u \cap v} \subseteq K$, whose intersection is $\omega_f(\phi, S)$ by monotonicity in $u$. $\square$

::: mathlib
`nonempty_omegaLimit` · `Mathlib.Dynamics.OmegaLimit`

`[CompactSpace β] [f.NeBot] → s.Nonempty → (omegaLimit f ϕ s).Nonempty`. The version with a compact absorbing set `c` is `nonempty_omegaLimit_of_isCompact_absorbing`, with the hypothesis `∃ v ∈ f, closure (image2 ϕ v s) ⊆ c`.

<?decl nonempty_omegaLimit?>
:::

**Theorem (Absorption).** Let $Y$ be compact and $V$ an open set with $\omega_f(\phi, S) \subseteq V$. Then there is $u \in f$ with $\overline{\phi(u \times S)} \subseteq V$; in particular $\phi_t(S) \subseteq V$ for all $t \in u$.

*Proof.* The sets $C_u \setminus V$ are closed subsets of the compact $Y$, directed downward as before, and their intersection is $\omega_f(\phi, S) \setminus V = \emptyset$. By compactness some finite intersection is empty, and it contains a member of the family. So $C_u \subseteq V$ for some $u \in f$. $\square$

::: mathlib
`eventually_closure_subset_of_isOpen_of_omegaLimit_subset` · `Mathlib.Dynamics.OmegaLimit`

`[CompactSpace β] → IsOpen v → omegaLimit f ϕ s ⊆ v → ∃ u ∈ f, closure (image2 ϕ u s) ⊆ v`. The form with `∀ᶠ t in f, MapsTo (ϕ t) s v` is `eventually_mapsTo_of_isOpen_of_omegaLimit_subset`. Variants replace `CompactSpace` by a compact absorbing set.

<?decl eventually_closure_subset_of_isOpen_of_omegaLimit_subset?>
:::

**Theorem (Invariance).** Let $\phi$ be a flow of a monoid $\tau$ on $X$, with $Y = X$, and suppose that $r \mapsto t + r$ tends to $f$ along $f$ for every $t$, as for the filter at $\infty$ on $\mathbb{N}$ or $\mathbb{R}$. Then $\omega_f(\phi, S)$ is invariant.

*Proof.* Let $y \in \omega_f(\phi, S)$, $t \in \tau$, and $N$ a neighbourhood of $\phi_t(y)$. Since $\phi_t$ is continuous, $\phi_t^{-1}(N)$ is a neighbourhood of $y$. Let $u \in f$. By hypothesis $u' = \{r : t + r \in u\}$ lies in $f$. By the characterization, some $r \in u'$ has $\phi_r(S)$ meeting $\phi_t^{-1}(N)$, so $\phi_{t + r}(S) = \phi_t(\phi_r(S))$ meets $N$, with $t + r \in u$. By the characterization again, $\phi_t(y) \in \omega_f(\phi, S)$. $\square$

For a flow of a group, Part 3 of the theorem on invariant sets of Section 1 then gives $\phi_t(\omega) = \omega$.

::: mathlib
`Flow.isInvariant_omegaLimit` · `Mathlib.Dynamics.OmegaLimit`

`(∀ t, Tendsto (t + ·) f f) → IsInvariant ϕ (omegaLimit f ϕ s)`. Related results: `Flow.omegaLimit_image_eq`, for a commutative group, says that `ω(ϕ t '' s) = ω(s)`, and `Flow.omegaLimit_omegaLimit` says that `ω(ω(s)) ⊆ ω(s)`.

<?decl Flow.isInvariant_omegaLimit?>
:::

**Theorem (Connectedness).** Let $\phi$ be a flow of $\mathbb{R}$ on a compact Hausdorff space $X$ and $x \in X$. Then $\omega(x)$ is a nonempty compact connected invariant set.

*Proof.* It is nonempty, closed in a compact space, so compact, and invariant by the theorems above. Suppose $\omega(x) = A \cup B$ with $A$, $B$ disjoint, closed and nonempty. A compact Hausdorff space is normal (Volume 13, Chapter 5), so there are disjoint open sets $U \supseteq A$ and $V \supseteq B$. By absorption there is $T$ with $\phi_t(x) \in U \cup V$ for all $t \ge T$. The set $O = \{\phi_t(x) : t \ge T\}$ is connected, as the image of $[T, \infty)$ under the continuous map $t \mapsto \phi_t(x)$. Take $a \in A$. By the characterization, some $t \ge T$ has $\phi_t(x) \in U$, so $O$ meets $U$; in the same way $O$ meets $V$. Then $O \cap U$ and $O \cap V$ split the connected set $O$ into two disjoint nonempty open parts, a contradiction. $\square$

The index of this edition has no declaration for the connectedness of $\omega$-limit sets. The proof uses the connectedness of $[T, \infty)$, so it fails for flows of $\mathbb{N}$: a point of minimal period $2$ has an $\omega$-limit set of two points.

### Examples

**Example (Linear flows on the line).** For $\phi_t(x) = e^{at}x$ with $a < 0$, $\omega(x) = \{0\}$ for every $x$, and the $\alpha$-limit set of $x \neq 0$ is empty, since $|e^{at}x| \to \infty$ as $t \to -\infty$. For $a > 0$ the roles swap. So the nonempty theorem needs compactness.

**Example (A limit cycle).** In polar coordinates on $\mathbb{R}^2$, consider $r' = r(1 - r^2)$, $\theta' = 1$. For $u = r^2$ the first equation becomes the logistic equation $u' = 2u(1 - u)$, with solution
$$u(t) = \frac{1}{1 + (1/u_0 - 1)e^{-2t}}, \qquad u_0 = r_0^2 > 0.$$
So $r(t) \to 1$ and $\theta(t) = \theta_0 + t$. For $r_0 > 0$ the $\omega$-limit set is the unit circle: for an angle $\theta$, the times $t_k = \theta - \theta_0 + 2\pi k$ give $\phi_{t_k}(x) \to (\cos\theta, \sin\theta)$. The forward orbit stays in the compact disc of radius $\max(r_0, 1)$, which is the absorbing set of the nonempty theorem. For $0 < r_0 < 1$ the $\alpha$-limit set of $x$ is the origin.

**Example (Rotations).** For the rotation $x \mapsto x + p/q$ of $\mathbb{R}/\mathbb{Z}$, every point is periodic and $\omega(x)$ is its orbit of $q$ points. For an irrational rotation, $\omega(x)$ is the whole circle, by the minimality proved in Chapter 3, Section 1.

### The library around it

The definition takes a set $S$ and a function $\phi$ with no flow axioms, so the results serve for semiflows and for the $\omega$-limit set of a whole set of initial points.

Common errors of a learner:

- `ω⁺ ϕ s` needs `ϕ : τ → α → β` with an order on `τ`; for a flow, write `ω⁺ ϕ.toFun s`.
- The $\omega$-limit set of `{x}` is not the closure of the orbit: in the limit cycle with $r_0 \neq 1$, $x \notin \omega(x)$.
- Invariance needs the hypothesis `∀ t, Tendsto (t + ·) f f`, which holds for `atTop` on `ℕ` and `ℝ` but fails for `atBot` on `ℕ`.

### Exercises

1. (A) Show that $\omega(x) = \{x\}$ for a fixed point $x$, and that $\omega(x)$ is the orbit of $x$ for a periodic point of a flow of $\mathbb{N}$.
2. (A) Show that $\omega_f(\phi, S_1 \cup S_2) = \omega_f(\phi, S_1) \cup \omega_f(\phi, S_2)$. Hint: for $\supseteq$ use monotonicity; for $\subseteq$, a point outside both has neighbourhoods $N_1$, $N_2$ and sets $u_1$, $u_2 \in f$ that witness it.
3. (B) For a flow of $\mathbb{R}$, show that $\omega(x) \subseteq \overline{\{\phi_t(x) : t \ge 0\}}$ and $\omega(\phi_s(x)) = \omega(x)$ for every $s$.
4. (B) For the flow of $\mathbb{N}$ generated by $x \mapsto x^2$ on $[0, 1]$, compute $\omega(x)$ for every $x$.
5. (B) Show that if $\omega(x) = \{p\}$ for a flow of $\mathbb{R}$ on a compact Hausdorff space, then $\phi_t(x) \to p$ and $p$ is a fixed point.
6. (C) On the torus $\mathbb{R}^2/\mathbb{Z}^2$, find a flow of $\mathbb{R}$ and a point whose $\omega$-limit set is the whole torus. Hint: a linear flow with an irrational slope; first show that its orbit meets the circle $\{0\} \times \mathbb{R}/\mathbb{Z}$ in an orbit of an irrational rotation.

### Notes and history

The terms $\omega$-limit set and $\alpha$-limit set are due to Birkhoff, after the last and the first letters of the Greek alphabet. The Poincaré-Bendixson theorem, which says that a nonempty compact $\omega$-limit set of a planar flow without fixed points is a periodic orbit, has no declaration in the index of this edition.

### Reference

<?reference?>
