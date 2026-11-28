---
title: The fundamental group of the circle
kind: theory
modules:
  - Mathlib.Topology.Covering.AddCircle
  - Mathlib.Topology.Covering.FundamentalGroupCircle
explains:
  E3: [AddCircle.isAddQuotientCoveringMap_coe, AddCircle.zsmulLoop, AddCircle.windingNumber, AddCircle.windingNumberIso, AddCircle.windingNumber_eq_div]
  E2: [AddCircle.isCoveringMap_coe, AddCircle.isLocalHomeomorph_coe, AddCircle.zsmulLoop_apply, AddCircle.windingNumber_zsmulLoop, AddCircle.isAddQuotientCoveringMap_zsmul, AddCircle.isAddQuotientCoveringMap_nsmul, AddCircle.isAddQuotientCoveringMap_zsmul_of_ne_zero, AddCircle.isAddQuotientCoveringMap_nsmul_of_ne_zero]
  E1: auto
families: []
requires: [V05.C01, V05.C05, V13.C01, V13.C06, V14.C01, V27.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The fundamental group of the circle

### Overview

The fundamental group of the circle is the group of integers. The isomorphism counts how many times a loop winds around the circle, with a sign for the direction. This is the first computation of a nontrivial fundamental group, and it shows that the circle is not contractible. The proof uses the covering map $\mathbb{R} \to S^1$ of the previous section. A loop in the circle lifts to a path in $\mathbb{R}$, and the lift ends at a point that differs from its start by an integer multiple of the period. That integer is the *winding number*.

Mathlib models the circle as the quotient group $\mathbb{R}/p\mathbb{Z}$ for a period $p > 0$, the type `AddCircle p`. This section proves that the quotient map is a covering map, defines the winding number through the lift of a loop, and proves that it gives an isomorphism $\pi_1(\mathbb{R}/p\mathbb{Z}, x) \cong \mathbb{Z}$. It checks the computation by hand on the loop that goes twice around, and it treats the coverings $z \mapsto nz$ of the circle by itself.

### Definitions

Fix a real number $p > 0$. Write $C_p = \mathbb{R}/p\mathbb{Z}$ with the quotient topology, and $\pi : \mathbb{R} \to C_p$ for the quotient map. For $p = 1$ the map $s \mapsto (\cos 2\pi s, \sin 2\pi s)$ induces a homeomorphism from $C_1$ to the unit circle $S^1 \subseteq \mathbb{R}^2$, so $C_p$ is a circle.

**Definition (The loop that winds $n$ times).** For $x \in \mathbb{R}$ and $n \in \mathbb{Z}$, the loop $\omega_n$ at $\pi(x)$ is $\omega_n(t) = \pi(n t p + x)$.

At $t = 0$ it gives $\pi(x)$, and at $t = 1$ it gives $\pi(np + x) = \pi(x)$, since $np \in p\mathbb{Z}$. So $\omega_n$ is a loop at $\pi(x)$. For $n = 0$ it is the constant loop.

**Definition (Winding number).** Let $\gamma$ be a loop in $C_p$ and $f : I \to \mathbb{R}$ a continuous lift, so that $\pi \circ f = \gamma$. The *winding number* of $\gamma$ is
$$w(\gamma) = \frac{f(1) - f(0)}{p}.$$

The proposition below shows that $w(\gamma)$ is an integer, that it does not depend on the lift $f$, and that a lift exists. Mathlib defines the winding number on the fundamental group through the isomorphism of the main theorem and proves the formula above as a theorem.

### Theorems and proofs

**Theorem (The covering of the circle).** The map $\pi : \mathbb{R} \to C_p$ is a quotient covering map for the group $p\mathbb{Z}$ acting by translation. In particular it is a covering map and a local homeomorphism.

*Proof.* The map $\pi$ is a quotient map by the definition of the quotient topology. The group $p\mathbb{Z}$ acts on $\mathbb{R}$ by the homeomorphisms $s \mapsto s + np$. By the definition of the quotient group, $\pi(a) = \pi(b)$ exactly when $a - b \in p\mathbb{Z}$, that is, when $a$ lies in the orbit of $b$. For $s \in \mathbb{R}$ let $U = (s - p/3, s + p/3)$. If $(U + np) \cap U \neq \emptyset$, then two points of $U$ differ by $np$, so $\lvert np \rvert < 2p/3$, and $n = 0$. So $\pi$ satisfies the definition of a quotient covering map. The theorem on quotients of the previous section shows that it is a covering map, and every covering map is a local homeomorphism. $\square$

**Proposition (The winding number is a well defined integer).** Let $\gamma$ be a loop at $\pi(x)$. Every point $e \in \pi^{-1}(\pi(x))$ is the start of exactly one lift of $\gamma$. For every continuous lift $f$ of $\gamma$, the number $(f(1) - f(0))/p$ is an integer, and it is the same for all lifts. Path homotopic loops have the same winding number.

*Proof.* The first claim is path lifting. Since $\pi(f(1)) = \gamma(1) = \gamma(0) = \pi(f(0))$, the difference $f(1) - f(0)$ lies in $p\mathbb{Z}$. Let $f$ and $g$ be two lifts. The map $f - g$ is continuous on $I$, and $\pi(f(t)) = \pi(g(t))$ gives $f(t) - g(t) \in p\mathbb{Z}$ for each $t$. A continuous map from the connected space $I$ into the discrete set $p\mathbb{Z}$ is constant, so $f - g = c$ for a constant $c$. Then $f(1) - f(0) = g(1) - g(0)$. For path homotopic loops $\gamma_0 \simeq \gamma_1$, the lifts that start at the same point $e$ end at the same point, by the corollary on homotopic paths of the previous section. So the two winding numbers agree. $\square$

So $w$ is a well defined map $\pi_1(C_p, \pi(x)) \to \mathbb{Z}$.

**Proposition (The winding number of $\omega_n$).** For every $n \in \mathbb{Z}$, $w(\omega_n) = n$.

*Proof.* The map $f(t) = ntp + x$ is continuous and satisfies $\pi \circ f = \omega_n$. So $w(\omega_n) = (np + x - x)/p = n$. $\square$

**Theorem (The fundamental group of the circle).** For every $x \in \mathbb{R}$, the winding number is a group isomorphism
$$w : \pi_1(C_p, \pi(x)) \to \mathbb{Z},$$
with inverse $n \mapsto [\omega_n]$.

*Proof.* The space $\mathbb{R}$ is convex, so it is simply connected, and the theorem on the fundamental group of a quotient from the previous section applies to $\pi$ with $G = p\mathbb{Z}$. It gives a bijection from $\pi_1(C_p, \pi(x))$ to $p\mathbb{Z}$ that sends $[\gamma]$ to $\Gamma(1) - \Gamma(0)$, where $\Gamma$ is the lift with $\Gamma(0) = x$. Dividing by $p$ gives $w$. Because $p\mathbb{Z}$ is commutative, the order of the product does not matter. The steps are short enough to check directly.

*Homomorphism.* Let $\Gamma$ and $\Delta$ be the lifts of $\gamma$ and $\delta$ with $\Gamma(0) = \Delta(0) = x$. The path $\Delta' = \Delta + (\Gamma(1) - x)$ is a lift of $\delta$, because the translation by an element of $p\mathbb{Z}$ commutes with $\pi$, and it starts at $\Gamma(1)$. So $\Gamma \cdot \Delta'$ is the lift of $\gamma \cdot \delta$, and it ends at $\Delta(1) + \Gamma(1) - x$. Thus $w(\gamma \cdot \delta) = w(\gamma) + w(\delta)$.

*Injectivity.* Let $w(\gamma) = 0$. Then the lift $\Gamma$ with $\Gamma(0) = x$ ends at $x$, so it is a loop in $\mathbb{R}$. The straight-line homotopy $K(s, t) = (1 - s)\Gamma(t) + s x$ fixes $t = 0$ and $t = 1$, so it is a path homotopy from $\Gamma$ to the constant loop. Then $\pi \circ K$ is a path homotopy from $\gamma$ to the constant loop.

*Surjectivity.* By the previous proposition, $w([\omega_n]) = n$. So $n \mapsto [\omega_n]$ is a right inverse of the bijection $w$, and hence its inverse. $\square$

**Corollary (The circle is not contractible).** The circle is not simply connected, and so it is not contractible.

*Proof.* The class $[\omega_1]$ has winding number $1 \neq 0$, so it is not the class of the constant loop. A contractible space is simply connected by the first chapter. $\square$

**Proposition (The coverings $z \mapsto nz$).** For $n \neq 0$, the map $\mu_n : C_p \to C_p$, $y \mapsto ny$, is a quotient covering map for its kernel, which has $\lvert n \rvert$ elements. It sends $[\omega_k]$ to $[\omega_{nk}]$, so it induces multiplication by $n$ on $\mathbb{Z}$.

*Proof.* The kernel is the set of $\pi(s)$ with $ns \in p\mathbb{Z}$, that is, $s \in (p/n)\mathbb{Z}$. Modulo $p\mathbb{Z}$ these are the $\lvert n \rvert$ points $\pi(jp/n)$ for $0 \le j < \lvert n \rvert$. The map $\mu_n$ is surjective and continuous. It is open: for open $V \subseteq C_p$, $\mu_n(V) = \pi(n\,\pi^{-1}(V))$, and $\pi$ and $s \mapsto ns$ are open maps. So $\mu_n$ is a quotient map. Two points have the same image exactly when they differ by an element of the kernel. For $y = \pi(s)$ let $U = \pi((s - \varepsilon, s + \varepsilon))$ with $\varepsilon = p/(3\lvert n \rvert)$. If $U$ meets its translate by $\pi(jp/n)$, then $(j + mn)p/n$ has absolute value less than $2\varepsilon$ for some $m \in \mathbb{Z}$, so $\lvert j + mn \rvert < 2/3$, $j + mn = 0$, and $\pi(jp/n) = \pi(-mp)$ is the unit. For the loops, $\mu_n(\omega_k(t)) = \pi(nktp + nx)$, which is $\omega_{nk}$ at the base point $\pi(nx)$. $\square$

### Examples

**Example (The loop that goes twice around).** Take $p = 1$ and $x = 0$, and let $\omega_1(t) = \pi(t)$ be the loop that goes once around. Compute the lift of $\omega_1 \cdot \omega_1$ that starts at $0$. For $t \le 1/2$ the loop is $\omega_1(2t) = \pi(2t)$, with lift $2t$. At $t = 1/2$ this lift is at $1$. For $t \ge 1/2$ the loop is $\omega_1(2t - 1) = \pi(2t - 1)$, and the lift that starts at $1$ is $(2t - 1) + 1 = 2t$. So the lift of $\omega_1 \cdot \omega_1$ is $t \mapsto 2t$, which ends at $2$, and $w(\omega_1 \cdot \omega_1) = 2$. The lift $2t$ is also the lift of $\omega_2$, and in fact $\omega_1 \cdot \omega_1 = \omega_2$ as maps, since $\pi(2t) = \pi(2t - 1)$. Check one value: at $t = 3/4$ the loop is at $\pi(3/2) = \pi(1/2)$, the point opposite to the base point.

**Example (A loop that goes halfway and back).** Take $p = 1$, $x = 0$ and $\gamma(t) = \pi(2t(1 - t))$. The lift $f(t) = 2t(1 - t)$ has $f(0) = f(1) = 0$, and $f(1/2) = 1/2$. So the loop runs to the opposite point and returns, and $w(\gamma) = 0$. The straight-line homotopy $(1 - s) f(t)$ in $\mathbb{R}$, followed by $\pi$, contracts $\gamma$ to the constant loop. The winding number counts the net number of turns, not the length of the path.

**Example (The reversed loop).** The reverse of $\omega_1$ is $t \mapsto \pi(1 - t) = \pi(-t)$, which is $\omega_{-1}$. Its lift $-t$ ends at $-1$, so its winding number is $-1$, the inverse of $1$ in $\mathbb{Z}$.

**Remark (The winding number needs a lift).** The loop $\omega_1$ and the constant loop both have the same values at $t = 0$ and $t = 1$, and no point of $C_p$ distinguishes them. The difference appears only in the lift: $t$ against $0$. A formula that reads $\gamma(1) - \gamma(0)$ in the group $C_p$ gives $0$ for every loop. The covering map is what turns the group $C_p$, where every loop returns to its start, into $\mathbb{R}$, where the end point records the number of turns.

### The library around it

::: mathlib
`AddCircle.isAddQuotientCoveringMap_coe` · `Mathlib.Topology.Covering.AddCircle`

For a topological additive group `𝕜` and `p : 𝕜` with `[DiscreteTopology (zmultiples p)]`, the coercion `𝕜 → AddCircle p` is an `IsAddQuotientCoveringMap` for `zmultiples p`. The consequences `AddCircle.isCoveringMap_coe` and `AddCircle.isLocalHomeomorph_coe` follow. The type `AddCircle p` is the quotient `𝕜 ⧸ zmultiples p`.

<?decl AddCircle.isAddQuotientCoveringMap_coe?>
:::

::: mathlib
`AddCircle.zsmulLoop` · `Mathlib.Topology.Covering.FundamentalGroupCircle`

`AddCircle.zsmulLoop p x n : Path (x : AddCircle p) x` is the loop `t ↦ n • (t * p) + x`, the loop $\omega_n$; its value is `AddCircle.zsmulLoop_apply`. Here `x : ℝ`, coerced to the circle.

<?decl AddCircle.zsmulLoop?>
:::

::: mathlib
`AddCircle.windingNumberIso` · `Mathlib.Topology.Covering.FundamentalGroupCircle`

Under `[Fact (0 < p)]`, `windingNumberIso x : FundamentalGroup (AddCircle p) x ≃* Multiplicative ℤ` for every point `x` of the circle. It is built from `IsAddQuotientCoveringMap.fundamentalGroupEquiv` for the coercion, with the lift `equivIco p 0 x` of the base point, then the inverse of `MulOpposite.opMulEquiv`, then `AddSubgroup.zmultiplesEquivInt`. The value group is `Multiplicative ℤ` because the fundamental group is written multiplicatively. The module imports the contractibility of convex sets, which gives the simple connectivity of `ℝ`.

<?decl AddCircle.windingNumberIso?>
:::

::: mathlib
`AddCircle.windingNumber` · `Mathlib.Topology.Covering.FundamentalGroupCircle`

`windingNumber γ : ℤ` is `(windingNumberIso x γ).toAdd`, for `γ : FundamentalGroup (AddCircle p) x`. `AddCircle.windingNumber_zsmulLoop` states that the class of `zsmulLoop p x n` has winding number `n`.

<?decl AddCircle.windingNumber?>
:::

::: mathlib
`AddCircle.windingNumber_eq_div` · `Mathlib.Topology.Covering.FundamentalGroupCircle`

For `γ : Path x x` and any `f : C(I, ℝ)` with `(↑) ∘ f = γ`, the cast of `windingNumber (.of (.mk γ))` to `ℝ` is `(f 1 - f 0) / p`. The lift `f` need not start at a chosen point; this is the independence of the lift in the proposition above.

<?decl AddCircle.windingNumber_eq_div?>
:::

The coverings of the circle by itself are `AddCircle.isAddQuotientCoveringMap_zsmul` and `AddCircle.isAddQuotientCoveringMap_nsmul`, for `n` a unit in `𝕜`, and the versions `AddCircle.isAddQuotientCoveringMap_zsmul_of_ne_zero` and `AddCircle.isAddQuotientCoveringMap_nsmul_of_ne_zero` for `[Algebra ℚ 𝕜]`. For the unit circle in `ℂ`, `Circle.isCoveringMap_exp` gives the covering by the exponential map, and `AddCircle.homeomorphCircle'` identifies `AddCircle (2 * π)` with `Circle`.

```lean
example (p : ℝ) [Fact (0 < p)] (x : ℝ) (n : ℤ) :
    AddCircle.windingNumber (x := (x : AddCircle p))
      (.of (.mk (AddCircle.zsmulLoop p x n))) = n :=
  AddCircle.windingNumber_zsmulLoop x n
```

The index of this edition has no declaration for the Brouwer fixed point theorem, and none for the statement that the circle is not a retract of the disk. Exercise 6 proves the second statement on paper.

Common errors of a learner: The circle in this module is `AddCircle p`, not the unit circle `Circle` of `ℂ`; a statement on `Circle` needs the homeomorphism. The winding number takes a class in the fundamental group, so a path must be wrapped as `.of (.mk γ)`. The instance `Fact (0 < p)` is needed for the isomorphism. The isomorphism goes to `Multiplicative ℤ`, so the product of classes becomes the sum of winding numbers only after `toAdd`.

### Exercises

1. (A) For $p = 1$ and $x = 0$, compute the winding number of $\gamma(t) = \pi(3t^2)$. *Hint:* Use the lift $3t^2$.
2. (A) Show that $\omega_m \cdot \omega_n$ is path homotopic to $\omega_{m+n}$. *Hint:* Compare winding numbers and use injectivity.
3. (B) Show that two loops at the same point of $C_p$ are path homotopic if and only if their lifts from a common start point have the same end point. *Hint:* One direction is the main theorem; the other is the proposition on homotopic loops.
4. (B) Show that every continuous map $f : C_p \to \mathbb{R}$ induces the trivial map on $\pi_1$, and deduce that $f$ is not a homotopy equivalence. *Hint:* $\mathbb{R}$ is simply connected.
5. (B) Compute $\pi_1$ of the torus $C_p \times C_p$ and of the cylinder $C_p \times \mathbb{R}$. *Hint:* Use the product formula of the first chapter.
6. (C) Show that no continuous map $r : D \to S^1$ from the closed unit disk restricts to the identity on $S^1$. *Hint:* The inclusion $i$ of $S^1$ into the convex set $D$ induces the zero map on $\pi_1$, while $r \circ i = \mathrm{id}$.
7. (C) Show that a loop $\gamma$ at $\pi(x)$ with $\gamma(t) \neq \pi(x + p/2)$ for all $t$ has winding number $0$. *Hint:* The lift from $x$ stays in the interval $(x - p/2, x + p/2)$ by the intermediate value theorem.

### Notes and history

Poincaré introduced the fundamental group in 1895. The computation $\pi_1(S^1) \cong \mathbb{Z}$ through the covering by the real line is the standard first example in textbooks of algebraic topology, and the no-retraction theorem of Exercise 6 gives the Brouwer fixed point theorem in dimension 2. The Mathlib source records the isomorphism as the theorem that the fundamental group of the circle is $\mathbb{Z}$.

The Mathlib Author of `Topology.Covering.AddCircle` is Junyan Xu. The Mathlib Author of `Topology.Covering.FundamentalGroupCircle` is Ruize Chen.

### Reference

<?reference?>
