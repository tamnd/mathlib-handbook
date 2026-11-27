---
title: The extension theorem of Tietze
kind: theory
modules:
  - Mathlib.Topology.TietzeExtension
explains:
  E3: [TietzeExtension, ContinuousMap.exists_restrict_eq]
  E2: [BoundedContinuousFunction.tietze_extension_step, BoundedContinuousFunction.exists_norm_eq_domRestrict_eq_of_closed, BoundedContinuousFunction.exists_extension_norm_eq_of_isClosedEmbedding, ContinuousMap.exists_extension, ContinuousMap.exists_forall_mem_restrict_eq, Real.instTietzeExtension, Pi.instTietzeExtension, TietzeExtension.of_homeo, ContinuousMap.restrict]
  E1: auto
families: []
requires: [V13.C03, V13.C04, V13.C05]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The extension theorem of Tietze

### Overview

Let $A$ be a closed subset of a normal space $X$. The theorem of Tietze says that each continuous $f : A \to \mathbb{R}$ is the restriction of a continuous $F : X \to \mathbb{R}$. If $f$ is bounded, $F$ can have the same bound. The lemma of Urysohn is the special case where $A$ is the union of two disjoint closed sets and $f$ takes the values $0$ and $1$. The proof approximates $f$ by Urysohn functions and sums a uniformly convergent series.

### Definitions

**Definition (Restriction, extension).** For $F : X \to Y$ and $A \subseteq X$, the restriction $F|_A : A \to Y$ is $F$ on $A$. An extension of $f : A \to Y$ is a map $F : X \to Y$ with $F|_A = f$.

**Definition (Tietze extension property).** A space $Y$ has the Tietze extension property if for each normal space $X$, each closed $A \subseteq X$ and each continuous $f : A \to Y$, there is a continuous extension $F : X \to Y$.

The theorem of Tietze says that $\mathbb{R}$ and $[a, b]$ have this property. The property passes to products and to homeomorphic spaces, so $\mathbb{R}^n$ has it too.

::: mathlib
`TietzeExtension` · `Mathlib.Topology.TietzeExtension`

A class on the target space `Y`, with the extension property for closed embeddings into normal spaces. Instances include `Real.instTietzeExtension`, `unitInterval`, `ℝ≥0`, `ℂ`, the open and closed unit balls, and `Pi.instTietzeExtension` for products. `TietzeExtension.of_homeo` transfers it along a homeomorphism.

<?decl TietzeExtension?>
:::

::: mathlib
`ContinuousMap.restrict` · `Mathlib.Topology.ContinuousMap.Basic`

The restriction of `f : C(X, Y)` to a set `s`, as an element of `C(s, Y)`.

<?decl ContinuousMap.restrict?>
:::

### Theorems and proofs

**Theorem (Approximation step).** Let $X$ be normal, $A$ closed, $c > 0$ and $g : A \to [-c, c]$ continuous. There is a continuous $h : X \to [-c/3, c/3]$ with $|g(a) - h(a)| \le 2c/3$ for all $a \in A$.

*Proof.* Let $A_- = \{a \in A : g(a) \le -c/3\}$ and $A_+ = \{a \in A : g(a) \ge c/3\}$. They are closed in $A$, since $g$ is continuous, so closed in $X$, since $A$ is closed. They are disjoint. By the lemma of Urysohn there is a continuous $u : X \to [0, 1]$ with $u = 0$ on $A_-$ and $u = 1$ on $A_+$. Let $h = (2u - 1) c / 3$, with values in $[-c/3, c/3]$.

Check the bound at $a \in A$. If $a \in A_-$, then $h(a) = -c/3$ and $g(a) \in [-c, -c/3]$, so $|g(a) - h(a)| \le 2c/3$. The case $a \in A_+$ is the same with the signs reversed. Otherwise $g(a) \in (-c/3, c/3)$ and $h(a) \in [-c/3, c/3]$, so $|g(a) - h(a)| < 2c/3$. $\square$

::: mathlib
`BoundedContinuousFunction.tietze_extension_step` · `Mathlib.Topology.TietzeExtension`

The step for a bounded continuous `f` on `X` and a closed embedding `e : X → Y` into a normal space: a `g` with `‖g‖ ≤ ‖f‖ / 3` and `dist (g ∘ e) f ≤ 2 / 3 * ‖f‖`.

<?decl BoundedContinuousFunction.tietze_extension_step?>
:::

**Theorem (Tietze, bounded case).** Let $X$ be normal, $A$ closed and $f : A \to [-1, 1]$ continuous. There is a continuous $F : X \to [-1, 1]$ with $F|_A = f$.

*Proof.* Set $f_0 = f$. Suppose $f_n : A \to \mathbb{R}$ is continuous with $|f_n| \le (2/3)^n$. Apply the step with $c = (2/3)^n$. This gives a continuous $h_n : X \to \mathbb{R}$ with $|h_n| \le \frac13 (2/3)^n$ and $|f_n - h_n| \le (2/3)^{n+1}$ on $A$. Set $f_{n+1} = f_n - h_n|_A$.

The series $F = \sum_n h_n$ converges uniformly on $X$, since $\sum_n \frac13 (2/3)^n = 1$. A uniform limit of continuous functions is continuous (Chapter 3), so $F$ is continuous, and $|F| \le 1$. On $A$, the partial sums satisfy $\sum_{k < n} h_k = f_0 - f_n$ by induction, and $f_n \to 0$ uniformly. So $F = f$ on $A$. $\square$

::: mathlib
`BoundedContinuousFunction.exists_norm_eq_domRestrict_eq_of_closed` · `Mathlib.Topology.TietzeExtension`

The bounded case for a closed set: an extension `g` with `‖g‖ = ‖f‖`. The version for a closed embedding is `BoundedContinuousFunction.exists_extension_norm_eq_of_isClosedEmbedding`.

<?decl BoundedContinuousFunction.exists_norm_eq_domRestrict_eq_of_closed?>
:::

**Theorem (Tietze).** Let $X$ be normal, $A$ closed and $f : A \to \mathbb{R}$ continuous. There is a continuous $F : X \to \mathbb{R}$ with $F|_A = f$.

*Proof.* The map $\phi(t) = t / (1 + |t|)$ is a homeomorphism from $\mathbb{R}$ to $(-1, 1)$. By the bounded case, $\phi \circ f$ has a continuous extension $G : X \to [-1, 1]$. The extension may take the values $\pm 1$, which are not in the image of $\phi$.

The set $Z = G^{-1}(\{-1, 1\})$ is closed and disjoint from $A$, since $G = \phi \circ f$ has values in $(-1, 1)$ on $A$. By the lemma of Urysohn there is a continuous $u : X \to [0, 1]$ with $u = 1$ on $A$ and $u = 0$ on $Z$. Then $H = u G$ is continuous, $H = G$ on $A$, and $|H(x)| < 1$ for all $x$: on $Z$, $H(x) = 0$, and off $Z$, $|H(x)| \le |G(x)| < 1$. So $F = \phi^{-1} \circ H$ is continuous and $F|_A = \phi^{-1} \circ \phi \circ f = f$. $\square$

::: mathlib
`ContinuousMap.exists_restrict_eq` · `Mathlib.Topology.TietzeExtension`

The theorem for each `TietzeExtension` target `Y`: for `s` closed in a normal space and `f : C(s, Y)`, some `g : C(X, Y)` has `g.restrict s = f`. With `Y = ℝ` it is the theorem above. `ContinuousMap.exists_forall_mem_restrict_eq` keeps the values in a set with the property, such as an interval.

<?decl ContinuousMap.exists_restrict_eq?>
:::

### Examples

**Example (Vector valued maps).** A continuous $f : A \to \mathbb{R}^n$ extends, since each coordinate extends. A map $f : A \to [0, 1]^n$ extends to $X \to [0, 1]^n$ in the same way, by the bounded case for each coordinate.

**Example (Extension from the integers).** Let $A = \mathbb{Z} \subseteq \mathbb{R}$, a closed set, and let $f : \mathbb{Z} \to \mathbb{R}$ be any function. Each function on $\mathbb{Z}$ is continuous, since $\mathbb{Z}$ is discrete. Here the extension is explicit: on each interval $[n, n + 1]$, let $F$ be the affine map with $F(n) = f(n)$ and $F(n + 1) = f(n + 1)$. The theorem of Tietze gives the same conclusion for each closed discrete subset of each normal space, where no such formula exists. If $f$ is bounded by $1$, the bounded case keeps the bound, and the affine map keeps it too.

**Counterexample (The circle).** The circle $S^1$ does not have the Tietze extension property. Let $X$ be the closed disc and $A = S^1$, and $f$ the identity of $S^1$. An extension $F : X \to S^1$ would be a retraction of the disc onto its boundary, and no such retraction exists, by the theorem of Brouwer on fixed points. So the theorem of Tietze needs targets such as $\mathbb{R}$, intervals and their products.

**Counterexample (Closedness is needed).** Let $A = (0, 1]$ in $X = [0, 1]$, and $f(t) = \sin(1/t)$. The function is continuous and bounded on $A$. No continuous extension exists, since $f$ has no limit at $0$.

### The library around it

The whole theory is in `Mathlib.Topology.TietzeExtension`. The file proves the bounded case with `BoundedContinuousFunction`, with closed embeddings in place of closed subsets, and then builds the class `TietzeExtension` with instances for `ℝ`, intervals, products and retracts. The step function uses `exists_continuous_zero_one_of_isClosed` of Section 1 and the completeness of the space of bounded continuous functions.

The reference table at the end of the section lists the declarations of the modules.

### Exercises

1. (A) Show that the theorem of Tietze implies the lemma of Urysohn.
2. (A) Show that $[a, b]$ has the Tietze extension property, using the bounded case and an affine map.
3. (B) Show that a $T_1$ space in which each continuous real function on each closed set extends is normal.
4. (B) Show that each retract of $\mathbb{R}^n$ has the Tietze extension property.
5. (B) Let $X$ be a metric space and $A$ closed. Give a direct proof of the bounded case with the formula $F(x) = \inf_{a \in A} (f(a) + d(x, a))$ for a Lipschitz $f$ with constant $1$.
6. (B) Let $A$ be closed in a normal space $X$ and $f : A \to \mathbb{R}$ continuous with $f > 0$. Show that $f$ has an extension $F : X \to \mathbb{R}$ with $F > 0$.
7. (B) Show that the open interval $(0, 1)$ has the Tietze extension property.

### Notes and history

Tietze proved the theorem for metric spaces in 1915. Urysohn extended it to normal spaces in 1925, with his lemma. The approximation by thirds is the standard proof since then. Dugundji (1951) proved that for metric spaces $X$, maps to each locally convex vector space extend, and the extension can be chosen linear in $f$.

### Reference

<?reference?>
