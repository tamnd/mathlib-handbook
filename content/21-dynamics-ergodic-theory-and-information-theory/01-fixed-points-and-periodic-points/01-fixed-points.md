---
title: Fixed points of maps
kind: theory
modules:
  - Mathlib.Dynamics.FixedPoints.Defs
  - Mathlib.Dynamics.FixedPoints.Basic
  - Mathlib.Dynamics.FixedPoints.Topology
  - Mathlib.Dynamics.FixedPoints.Support
  - Mathlib.Dynamics.FixedPoints.Prufer
explains:
  E3: [Function.fixedPoints, isFixedPt_of_tendsto_iterate, isClosed_fixedPoints, Function.bijOn_fixedPoints_comp, Function.fixedSupport, Function.HasCompactFixedSupport, smul_eq_self_of_preimage_zpow_eq_self]
  E2: [Function.mem_fixedPoints_iff, Function.IsFixedPt.iterate, Function.IsFixedPt.comp, Function.IsFixedPt.map, Function.Semiconj.mapsTo_fixedPoints, Function.invOn_fixedPoints_comp, Function.Commute.left_bijOn_fixedPoints_comp, Function.HasCompactFixedSupport.comp, vadd_eq_self_of_preimage_zsmul_eq_self]
  E1: auto
families: []
requires: [V04, V05, V13]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Fixed points of maps

### Overview

A discrete dynamical system is a set $X$ with a map $f : X \to X$. The map moves a point $x$ to $f(x)$, then to $f(f(x))$, and so on. The simplest behaviour is a point that does not move. This section defines iterates and fixed points, shows how fixed points move under maps between systems, proves that a limit of iterates is a fixed point, and proves Banach's contraction principle. It ends with the fixed support of a map and a lemma on Prüfer subgroups.

### Definitions

**Definition (Iterate).** Let $f : X \to X$. The iterates of $f$ are $f^{[0]} = \mathrm{id}$ and $f^{[n+1]} = f^{[n]} \circ f$. By induction on $n$, $f^{[m+n]} = f^{[m]} \circ f^{[n]}$. The sequence $(f^{[n]}(x))_{n \ge 0}$ is the forward orbit of $x$.

::: mathlib
`Nat.iterate` · `Mathlib.Logic.Function.Iterate`

The iterate `Nat.iterate f n` is written `f^[n]`. The recursion is `f^[n+1] = f^[n] ∘ f`, so `f^[n.succ] x = f^[n] (f x)` holds by definition (`Function.iterate_succ_apply`), and the form `f (f^[n] x)` is the lemma `Function.iterate_succ_apply'`. The law of addition is `Function.iterate_add_apply`.

<?decl Function.iterate_add_apply?>
:::

**Definition (Fixed point).** A point $x$ is a *fixed point* of $f$ if $f(x) = x$. The set of fixed points is $\mathrm{Fix}(f)$.

**Definition (Semiconjugacy).** Let $f_a : \alpha \to \alpha$, $f_b : \beta \to \beta$ and $g : \alpha \to \beta$. The map $g$ *semiconjugates* $f_a$ to $f_b$ if $g \circ f_a = f_b \circ g$. Two maps $f, g : \alpha \to \alpha$ *commute* if $f \circ g = g \circ f$. A bijective semiconjugacy is a *conjugacy*: it renames the points and keeps the dynamics.

::: mathlib
`Function.fixedPoints` · `Mathlib.Dynamics.FixedPoints.Defs`

The predicate `Function.IsFixedPt f x` is defined in `Mathlib.Logic.Function.Defs` as `f x = x`, and `Function.fixedPoints f` is `{x | IsFixedPt f x}`; `Function.mem_fixedPoints_iff` unfolds membership. In `Mathlib.Logic.Function.Conjugate`, `Function.Semiconj g fa fb` is `∀ x, g (fa x) = fb (g x)` and `Function.Commute f g` is `Semiconj f g g`.

<?decl Function.fixedPoints?>
:::

**Definition (Fixed support).** Let $X$ be a topological space and $f : X \to X$. The *fixed support* of $f$ is the closure of the set of points that $f$ moves: $\operatorname{supp}(f) = \overline{X \setminus \mathrm{Fix}(f)}$. The map $f$ has *compact fixed support* if this set is compact.

::: mathlib
`Function.fixedSupport` · `Mathlib.Dynamics.FixedPoints.Support`

`Function.fixedSupport f = closure (fixedPoints f)ᶜ`, and `Function.HasCompactFixedSupport f` says that it is compact.

<?decl Function.HasCompactFixedSupport?>
:::

### Theorems and proofs

**Proposition (Fixed points and composition).** Let $f, g : X \to X$. If $f(x) = x$, then $f^{[n]}(x) = x$ for each $n$. If $f(x) = x$ and $g(x) = x$, then $f(g(x)) = x$. If $g \circ f_a = f_b \circ g$ and $f_a(x) = x$, then $f_b(g(x)) = g(x)$.

*Proof.* For the first claim use induction: $f^{[n+1]}(x) = f^{[n]}(f(x)) = f^{[n]}(x) = x$. For the second, $f(g(x)) = f(x) = x$. For the third, $f_b(g(x)) = g(f_a(x)) = g(x)$. $\square$

**Theorem (Fixed points of $f \circ g$ and $g \circ f$).** Let $f : \alpha \to \beta$ and $g : \beta \to \alpha$. Then $g$ is a bijection from $\mathrm{Fix}(f \circ g)$ onto $\mathrm{Fix}(g \circ f)$, with inverse $f$.

*Proof.* Let $f(g(y)) = y$. Apply $g$: $g(f(g(y))) = g(y)$, so $g(y) \in \mathrm{Fix}(g \circ f)$. In the same way $f$ maps $\mathrm{Fix}(g \circ f)$ into $\mathrm{Fix}(f \circ g)$. The equations $f(g(y)) = y$ on the first set and $g(f(x)) = x$ on the second set say that the two restrictions are inverse to each other. $\square$

::: mathlib
`Function.bijOn_fixedPoints_comp` · `Mathlib.Dynamics.FixedPoints.Basic`

`Set.BijOn g (fixedPoints (f ∘ g)) (fixedPoints (g ∘ f))`, with `Function.invOn_fixedPoints_comp` for the inverse. If `f` and `g` commute, `Function.Commute.left_bijOn_fixedPoints_comp` says that `f` permutes `fixedPoints (f ∘ g)`. The proposition is `IsFixedPt.iterate`, `IsFixedPt.comp` and `IsFixedPt.map`, with the set form `Function.Semiconj.mapsTo_fixedPoints`.

<?decl Function.bijOn_fixedPoints_comp?>
:::

**Theorem (Limits of iterates).** Let $X$ be a Hausdorff space and $f : X \to X$. If $f^{[n]}(x) \to y$ and $f$ is continuous at $y$, then $f(y) = y$.

*Proof.* Put $x_n = f^{[n]}(x)$. The shifted sequence $x_{n+1}$ tends to $y$. Since $x_{n+1} = f(x_n)$ and $f$ is continuous at $y$, it also tends to $f(y)$. In a Hausdorff space a sequence has at most one limit, so $f(y) = y$. $\square$

**Theorem (The fixed point set is closed).** If $X$ is Hausdorff and $f$ is continuous, then $\mathrm{Fix}(f)$ is closed.

*Proof.* Let $f(x) \neq x$. Choose disjoint open sets $U \ni f(x)$ and $V \ni x$. The open set $W = V \cap f^{-1}(U)$ contains $x$. For $z \in W$, $f(z) \in U$ and $z \in V$, so $f(z) \neq z$. So the complement of $\mathrm{Fix}(f)$ is open. $\square$

::: mathlib
`isFixedPt_of_tendsto_iterate` · `Mathlib.Dynamics.FixedPoints.Topology`

`[T2Space α] → Tendsto (fun n ↦ f^[n] x) atTop (𝓝 y) → ContinuousAt f y → IsFixedPt f y`. Continuity is needed at the limit only. The second theorem is `isClosed_fixedPoints : Continuous f → IsClosed (fixedPoints f)`.

<?decl isFixedPt_of_tendsto_iterate?>
:::

**Theorem (Banach contraction principle).** Let $(X, d)$ be a nonempty complete metric space and $f : X \to X$ with $d(f(x), f(y)) \le K\, d(x, y)$ for all $x, y$, for a constant $0 \le K < 1$. Then $f$ has exactly one fixed point $p$. For each $x$, $f^{[n]}(x) \to p$ and
$$d(f^{[n]}(x), p) \le \frac{K^n}{1 - K}\, d(x, f(x)).$$

*Proof.* Fix $x$ and put $x_n = f^{[n]}(x)$. Then $d(x_{n+1}, x_{n+2}) = d(f(x_n), f(x_{n+1})) \le K\, d(x_n, x_{n+1})$, so by induction $d(x_n, x_{n+1}) \le K^n d(x_0, x_1)$. For $m > n$ the triangle inequality gives
$$d(x_n, x_m) \le \sum_{k=n}^{m-1} K^k d(x_0, x_1) \le \frac{K^n}{1 - K}\, d(x_0, x_1).$$
The right side tends to $0$, so $(x_n)$ is a Cauchy sequence, with a limit $p$ by completeness. The map $f$ is Lipschitz, hence continuous, and a metric space is Hausdorff, so the theorem on limits of iterates gives $f(p) = p$. Let $m \to \infty$ in the display to get the bound. If also $f(q) = q$, then $d(p, q) = d(f(p), f(q)) \le K\, d(p, q)$, so $(1 - K)\, d(p, q) \le 0$ and $p = q$. $\square$

::: mathlib
`ContractingWith.fixedPoint` · `Mathlib.Topology.MetricSpace.Contracting`

`ContractingWith K f` is `K < 1 ∧ LipschitzWith K f` with `K : ℝ≥0`. Under `[Nonempty α] [CompleteSpace α]`, `ContractingWith.fixedPoint f hf` is the fixed point, with `fixedPoint_isFixedPt`, `fixedPoint_unique`, `tendsto_iterate_fixedPoint` and the bound `apriori_dist_iterate_fixedPoint_le`.

<?decl ContractingWith.tendsto_iterate_fixedPoint?>
:::

**Proposition (Fixed support of a composition).** If $f$ and $g$ have compact fixed support, so does $f \circ g$.

*Proof.* If $f(g(x)) \neq x$, then $g(x) \neq x$ or $f(x) \neq x$, because otherwise $f(g(x)) = f(x) = x$. So the closure of the set that $f \circ g$ moves lies in the compact set $\operatorname{supp}(f) \cup \operatorname{supp}(g)$. A closed subset of a compact set is compact. $\square$

**Lemma (Prüfer).** Let $G$ be a commutative group, $n \in \mathbb{Z}$, and $s \subseteq G$ with $\{x : x^n \in s\} = s$. If $g^{n^j} = 1$ for some $j \ge 0$, then $g s = s$.

*Proof.* Use induction on $j$. If $j = 0$, then $g = 1$. Suppose the claim for $j$, and let $g^{n^{j+1}} = 1$. Then $(g^n)^{n^j} = 1$, so $g^n s = s$. For $x \in G$, by commutativity,
$$x \in g s \iff (g^{-1}x)^n \in s \iff x^n \in g^n s = s \iff x \in s. \qquad \square$$

::: mathlib
`smul_eq_self_of_preimage_zpow_eq_self` · `Mathlib.Dynamics.FixedPoints.Prufer`

`(fun x ↦ x ^ n) ⁻¹' s = s → g ^ n ^ j = 1 → g • s = s` in a `CommGroup`, with `n : ℤ`. The additive form `vadd_eq_self_of_preimage_zsmul_eq_self` serves the circle `AddCircle`, where the elements with $n^j g = 0$ form the Prüfer subgroup when $n$ is prime. Chapter 6 uses it for the ergodicity of $x \mapsto nx$. The composition result is `HasCompactFixedSupport.comp`.

<?decl smul_eq_self_of_preimage_zpow_eq_self?>
:::

### Examples

**Example (The cosine).** The map $\cos$ sends $[0, 1]$ into $[\cos 1, 1] \subseteq [0, 1]$. By the mean value theorem, $|\cos x - \cos y| \le (\sin 1)\, |x - y|$ there, and $\sin 1 \approx 0.8415$. The contraction principle gives a unique solution of $\cos p = p$ in $[0, 1]$. From $x_0 = 1$ the iterates are $0.5403$, $0.8576$, $0.6543$, $0.7935$, $0.7014$, and they converge to $p \approx 0.7391$. With $K = 0.8415$ and $d(x_0, x_1) = 0.4597$, the bound guarantees an error below $10^{-4}$ for $n \ge 60$.

**Counterexample (A strict contraction without a fixed point).** Let $X = [1, \infty)$ and $f(x) = x + 1/x$. Then $f(x) - f(y) = (x - y)(1 - 1/(xy))$, so $|f(x) - f(y)| < |x - y|$ for $x \neq y$, and $X$ is complete. But $f(x) > x$ for each $x$. The constant $K$ must be uniform.

**Example (Doubling on the circle).** Let $G = \mathbb{R}/\mathbb{Z}$ and $n = 2$, in additive notation. Let $s$ satisfy $\{x : 2x \in s\} = s$. The elements with $2^j g = 0$ are the dyadic points $k/2^j$, so the Prüfer lemma gives $s + k/2^j = s$. If $s$ is closed and contains a point $s_0$, then it contains the dense set of the points $s_0 + k/2^j$, so $s = G$. The set $\{0\}$ fails the condition, since $\{x : 2x = 0\} = \{0, 1/2\}$.

### The library around it

The fixed points of a monotone map of a complete lattice (`OrderHom.lfp`, Knaster-Tarski) are in `Mathlib.Order.FixedPoints` and Volume 4, Chapter 4. The files of this section add lemmas for permutations such as `IsFixedPt.perm_zpow`.

Common errors of a learner:

- `f^[n+1] x` unfolds to `f^[n] (f x)`, not to `f (f^[n] x)`.
- `isFixedPt_of_tendsto_iterate` needs a Hausdorff space. Without it a sequence can have two limits (Exercise 3).

### Exercises

1. (A) Show that $\mathrm{Fix}(f) \cap \mathrm{Fix}(g) \subseteq \mathrm{Fix}(f \circ g)$, and give an example where the inclusion is strict.
2. (A) Let $f$ be injective. Show that $f(x)$ is a fixed point of $f$ if and only if $x$ is.
3. (B) Let $X$ be the indiscrete space on two points and $f$ the swap. Show that $f^{[n]}(x)$ converges to each point, and that the theorem on limits of iterates fails.
4. (B) Let $f$ be a map of a complete metric space such that $f^{[k]}$ is a contraction for some $k \ge 1$. Show that $f$ has a unique fixed point. Hint: $f(p)$ is a fixed point of $f^{[k]}$ when $p$ is one.
5. (B) Use the contraction principle on $C([0, 1/2])$ with the sup norm to solve $u(t) = 1 + \int_0^t u(s)\, ds$. Identify the solution.
6. (C) Let $X$ be a compact metric space and $d(f(x), f(y)) < d(x, y)$ for $x \neq y$. Show that $f$ has a unique fixed point. Hint: $x \mapsto d(x, f(x))$ attains its minimum.

### Notes and history

Banach proved the contraction principle in his thesis, published in 1922 in Fundamenta Mathematicae. The method of successive approximations is older: Picard used it for differential equations. Exercise 6 is a theorem of Edelstein. The Prüfer groups $\mathbb{Z}[1/p]/\mathbb{Z}$ carry the name of Heinz Prüfer.

### Reference

<?reference?>
