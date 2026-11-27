---
title: Norming functionals and the double dual
kind: theory
modules:
  - Mathlib.Analysis.Normed.Module.HahnBanach
  - Mathlib.Analysis.Normed.Module.DoubleDual
  - Mathlib.Analysis.LocallyConvex.SeparatingDual
  - Mathlib.Analysis.Normed.Module.WeakDual
explains:
  E3: [exists_dual_vector, NormedSpace.inclusionInDoubleDualLi, NormedSpace.norm_le_dual_bound]
  E2: [exists_dual_vector', exists_dual_vector'', NormedSpace.double_dual_bound, NormedSpace.inclusionInDoubleDual, SeparatingDual, instSeparatingDual, SeparatingDual.exists_separating_of_ne, WeakDual.isCompact_closedBall]
  E1: auto
families: []
requires: [V07, V13, V16.C01, V16.C02, V16.C04]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Norming functionals and the double dual

### Overview

The extension theorem of Section 1 gives a normed space many bounded functionals. This section takes the consequences for the norm. Each vector $x$ has a functional $g$ of norm $1$ with $g(x) = \|x\|$. So the dual separates the points, the norm of $x$ is the largest value of $|f(x)|$ on the unit ball of the dual, and the canonical map of $E$ into its double dual is an isometry. The same argument computes the closure of a subspace from the functionals that vanish on it. The section ends with the theorem that a weakly bounded set is bounded, which joins the double dual and the uniform boundedness principle of Chapter 4. Over $\mathbb{R}$ and $\mathbb{C}$ all these results are in Mathlib with a field `𝕜` with `RCLike 𝕜`.

### Definitions

In this section $\mathbb{K}$ is $\mathbb{R}$ or $\mathbb{C}$ and $E^*$ is the space of bounded linear functionals on a normed space $E$ over $\mathbb{K}$, with the operator norm of Chapter 2. It is a Banach space by Chapter 4, Section 1, because $\mathbb{K}$ is complete.

**Definition (norming functional).** A *norming functional* for a vector $x$ of a normed space $E$ is a functional $g \in E^*$ with $\|g\| \le 1$ and $g(x) = \|x\|$.

**Definition (double dual).** The *double dual* of $E$ is $E^{**} = (E^*)^*$. The *canonical map* $J : E \to E^{**}$ is $J(x)(f) = f(x)$.

**Definition (separating dual).** A topological vector space $E$ over $\mathbb{K}$ has a *separating dual* if for each $x \ne 0$ there is a continuous linear functional $f$ with $f(x) \ne 0$.

::: mathlib
`SeparatingDual` · `Mathlib.Analysis.LocallyConvex.SeparatingDual`

`SeparatingDual R V` is a class with one field: each nonzero `x : V` has some `f : StrongDual R V` with `f x ≠ 0`. The ring and the space have only a topology, so the class applies to any topological module. The instance `instSeparatingDual` gives it for each normed space over an `RCLike` field, and another instance gives it for each real locally convex space with the $T_1$ property.

<?decl SeparatingDual?>
:::

**Definition (annihilator).** For a subspace $M$ of $E$ the *annihilator* is $M^\perp = \{f \in E^* : f(m) = 0 \text{ for all } m \in M\}$. For a set $N \subseteq E^*$ the *preannihilator* is ${}^\perp N = \{x \in E : f(x) = 0 \text{ for all } f \in N\}$.

**Definition (weakly bounded).** A subset $S$ of $E$ is *weakly bounded* if $\sup_{x \in S} |f(x)| < \infty$ for each $f \in E^*$.

### Theorems and proofs

**Theorem (norming functional).** Let $E$ be a normed space over $\mathbb{K}$ and $x \in E$ with $x \ne 0$. There is $g \in E^*$ with $\|g\| = 1$ and $g(x) = \|x\|$.

*Proof.* Let $M = \mathbb{K}x$ and define $f(tx) = t\|x\|$ on $M$. The map is well defined and linear because $x \ne 0$, and $|f(tx)| = |t|\,\|x\| = \|tx\|$, so $\|f\| = 1$. The theorem of Section 1 in its normed form extends $f$ to $g \in E^*$ with $\|g\| = \|f\| = 1$, and $g(x) = f(x) = \|x\|$. $\square$

::: mathlib
`exists_dual_vector` · `Mathlib.Analysis.Normed.Module.HahnBanach`

`exists_dual_vector 𝕜 x h : ∃ g : StrongDual 𝕜 E, ‖g‖ = 1 ∧ g x = ‖x‖` with `h : ‖x‖ ≠ 0`, over an `RCLike` field and a seminormed space. The proof is the proof of the text: it extends `(‖x‖ : 𝕜) • coord` from `span 𝕜 {x}` with `exists_extension_norm_eq`. The variant `exists_dual_vector'` assumes `Nontrivial E` and allows `x = 0`, with a functional of norm `1` that gives `0`. The variant `exists_dual_vector''` drops all hypotheses and gives `‖g‖ ≤ 1`, which is the norming functional of the definition.

<?decl exists_dual_vector?>
:::

**Corollary (the dual separates points).** If $x \ne y$ in a normed space $E$, there is $f \in E^*$ with $f(x) \ne f(y)$.

*Proof.* Apply the theorem to $x - y \ne 0$. It gives $f$ with $f(x) - f(y) = f(x - y) = \|x - y\| \ne 0$. $\square$

In Mathlib this is `SeparatingDual.exists_separating_of_ne` together with the instance `instSeparatingDual`.

**Corollary (the norm from the dual).** For each $x \in E$,
$$\|x\| = \max\{|f(x)| : f \in E^*, \|f\| \le 1\}.$$
Also, if $M \ge 0$ and $|f(x)| \le M\|f\|$ for each $f \in E^*$, then $\|x\| \le M$.

*Proof.* For $\|f\| \le 1$, $|f(x)| \le \|f\|\,\|x\| \le \|x\|$. A norming functional $g$ for $x$ has $\|g\| \le 1$ and $|g(x)| = \|x\|$, so the bound is attained and the maximum exists. For the second statement apply the hypothesis to $g$: $\|x\| = |g(x)| \le M\|g\| \le M$. $\square$

::: mathlib
`NormedSpace.norm_le_dual_bound` · `Mathlib.Analysis.Normed.Module.DoubleDual`

`norm_le_dual_bound 𝕜 x hM h : ‖x‖ ≤ M` with `hM : 0 ≤ M` and `h : ∀ f : StrongDual 𝕜 E, ‖f x‖ ≤ M * ‖f‖`. It is the second statement of the corollary. The first statement, with a maximum, has no separate name in the index of this edition. It follows from `exists_dual_vector''` and `le_opNorm`.

<?decl NormedSpace.norm_le_dual_bound?>
:::

**Theorem (the canonical map is an isometry).** The map $J : E \to E^{**}$ is linear and $\|J(x)\| = \|x\|$ for each $x \in E$.

*Proof.* Linearity in $x$ is linearity of each $f$. For fixed $x$, the map $f \mapsto f(x)$ is linear on $E^*$ and $|f(x)| \le \|x\|\,\|f\|$, so $J(x) \in E^{**}$ and $\|J(x)\| \le \|x\|$. A norming functional $g$ for $x$ has $\|g\| \le 1$ and $g(x) = \|x\|$, so $\|x\| = |J(x)(g)| \le \|J(x)\|\,\|g\| \le \|J(x)\|$. $\square$

::: mathlib
`NormedSpace.inclusionInDoubleDualLi` · `Mathlib.Analysis.Normed.Module.DoubleDual`

`inclusionInDoubleDualLi 𝕜 : E →ₗᵢ[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E)` is $J$ as a linear isometry. It is built from `inclusionInDoubleDual 𝕜 E : E →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E)`, which exists over any nontrivially normed field and has the bound `double_dual_bound`. The proof of `norm_map'` is the proof of the text: `le_antisymm` of `double_dual_bound` and the lower bound from `exists_dual_vector''` with `unit_le_opNorm`. The isometry needs the field `RCLike`, because over a general field the theorem of Hahn-Banach can fail.

<?decl NormedSpace.inclusionInDoubleDualLi?>
:::

Since $E^{**}$ is a Banach space, the closure of $J(E)$ in $E^{**}$ is a completion of $E$. This gives a second construction of the completion of Chapter 4, Section 1. A Banach space $E$ is *reflexive* if $J$ is onto.

**Theorem (distance to a closed subspace).** Let $M$ be a closed subspace of $E$ and $x_0 \notin M$, with $d = \inf_{m \in M} \|x_0 - m\| > 0$. There is $g \in E^*$ with $g|_M = 0$, $\|g\| = 1$ and $g(x_0) = d$.

*Proof.* Each vector of $N = M + \mathbb{K}x_0$ has a unique form $m + tx_0$, because $x_0 \notin M$. Define $f(m + tx_0) = td$, a linear functional on $N$ that vanishes on $M$. For $t \ne 0$,
$$\|m + tx_0\| = |t|\,\|x_0 + t^{-1}m\| = |t|\,\|x_0 - (-t^{-1}m)\| \ge |t|\,d = |f(m + tx_0)|,$$
and for $t = 0$ both sides of $|f| \le \|\cdot\|$ hold trivially. So $\|f\| \le 1$. For the other bound pick $m_n \in M$ with $\|x_0 - m_n\| \to d$. Then $f(x_0 - m_n) = d$, so $\|f\| \ge d / \|x_0 - m_n\| \to 1$. Thus $\|f\| = 1$. The normed form of Section 1 extends $f$ to $g \in E^*$ with $\|g\| = 1$. $\square$

**Corollary (closure of a subspace).** For a subspace $M$ of $E$, the closure of $M$ is ${}^\perp(M^\perp)$. In particular $M$ is dense if and only if the only $f \in E^*$ that vanishes on $M$ is $f = 0$.

*Proof.* Each $f \in M^\perp$ is continuous and vanishes on $M$, so it vanishes on $\overline{M}$. Thus $\overline{M} \subseteq {}^\perp(M^\perp)$. Conversely let $x_0 \notin \overline{M}$. The closure is a closed subspace and $d(x_0, \overline{M}) > 0$, since the complement of $\overline{M}$ is open. The theorem gives $g$ that vanishes on $\overline{M}$, so $g \in M^\perp$, with $g(x_0) = d > 0$. Hence $x_0 \notin {}^\perp(M^\perp)$. For the second statement, $M$ is dense if and only if ${}^\perp(M^\perp) = E$. If $M^\perp = \{0\}$ this holds. If $f \ne 0$ is in $M^\perp$, then ${}^\perp(M^\perp) \subseteq \ker f \ne E$. $\square$

**Theorem (weakly bounded sets are bounded).** Let $E$ be a normed space and $S \subseteq E$ weakly bounded. Then $S$ is bounded in norm.

*Proof.* The family $\{J(x) : x \in S\}$ consists of bounded linear functionals on $E^*$, which is a Banach space. For each $f \in E^*$ the set $\{J(x)(f) : x \in S\} = \{f(x) : x \in S\}$ is bounded by hypothesis. The uniform boundedness principle of Chapter 4, Section 2, gives $\sup_{x \in S}\|J(x)\| < \infty$. Since $J$ is an isometry, $\sup_{x \in S}\|x\| < \infty$. $\square$

The same argument, without the double dual, shows that a subset of $E^*$ that is bounded at each point of a Banach space $E$ is bounded in norm. Mathlib states this second form as `WeakDual.isBounded_iff_isVonNBounded` for the weak-* topology on the dual of a complete space.

### Examples

**Example (norming functionals in $\ell^1$).** Let $x \in \ell^1$ and define $g(y) = \sum_n \overline{\operatorname{sgn}(x_n)}\, y_n$, where $\operatorname{sgn}(z) = z/|z|$ for $z \ne 0$ and $\operatorname{sgn}(0) = 0$. Then $|g(y)| \le \|y\|_1$, so $\|g\| \le 1$, and $g(x) = \sum_n |x_n| = \|x\|_1$. Here the norming functional is given by an element of $\ell^\infty$, and no extension theorem is needed. If some $x_n = 0$, the coefficient at $n$ can be any number of modulus at most $1$, so the norming functional is not unique.

**Example (non-unique norming functional).** In $\mathbb{R}^2$ with $\|(a, b)\|_\infty = \max(|a|, |b|)$ let $x = (1, 1)$. Each $g_t(a, b) = ta + (1 - t)b$ with $t \in [0, 1]$ has $\|g_t\| = |t| + |1 - t| = 1$ and $g_t(x) = 1 = \|x\|_\infty$. The norming functional is unique at a point exactly when the unit ball has one supporting line there, and $x$ is a corner of the square.

**Example (the double dual of a finite dimensional space).** Let $E$ be a finite dimensional normed space. Then $\dim E^* = \dim E$, since each linear functional on $E$ is bounded by Chapter 3, and so $\dim E^{**} = \dim E$. The map $J$ is injective because it is an isometry, so it is onto, and $E$ is reflexive. The norm on $E^{**}$ that $J$ carries back to $E$ is the norm of $E$, by the theorem on the canonical map.

### The library around it

The norm consequences are in `Mathlib.Analysis.Normed.Module.HahnBanach` and `Mathlib.Analysis.Normed.Module.DoubleDual`, over a field with `RCLike 𝕜`. The class `SeparatingDual` of `Mathlib.Analysis.LocallyConvex.SeparatingDual` records the corollary that the dual separates points, for use in places where only that corollary matters, such as the statement that `E →L[𝕜] F` is nontrivial when `E` and `F` are.

The theorem of Banach-Alaoglu says that the closed unit ball of $E^*$ is compact for the weak-* topology, the topology of pointwise convergence on $E$. Mathlib has the type `WeakDual 𝕜 E` with this topology, and `WeakDual.isCompact_closedBall` states that the preimage of a closed ball of `StrongDual 𝕜 E` is compact in `WeakDual 𝕜 E`. The more general `WeakDual.isCompact_polar` states that the polar of a neighbourhood of `0` is weak-* compact. Both rest on `WeakDual.isCompact_of_bounded_of_closed`: a weak-* closed set that is bounded in norm is weak-* compact.

::: mathlib
`WeakDual.isCompact_closedBall` · `Mathlib.Analysis.Normed.Module.WeakDual`

`WeakDual.isCompact_closedBall x' r : IsCompact (toStrongDual ⁻¹' closedBall x' r)` over a nontrivially normed field with `ProperSpace 𝕜`. The map `WeakDual.toStrongDual` is the identity on the underlying functionals, and the statement takes the ball in the norm topology and asks for compactness in the weak-* topology.

<?decl WeakDual.isCompact_closedBall?>
:::

Common errors with these statements:

- The functional of `exists_dual_vector` takes the value `(‖x‖ : 𝕜)`, a coercion of a real number into `𝕜`. Over `ℂ` a rewrite with this equation needs `RCLike.ofReal` lemmas, or `norm_cast`.
- `inclusionInDoubleDual` exists over any nontrivially normed field, but it is an isometry only through `inclusionInDoubleDualLi`, which needs `RCLike 𝕜`.

### Exercises

1. (A) Let $x = (3, -4) \in \mathbb{R}^2$ with the norm $\|\cdot\|_1$. Find all norming functionals for $x$.
2. (A) Show that a normed space $E \ne \{0\}$ has $E^* \ne \{0\}$, and that $E^*$ has dimension at least the dimension of $E$ when $E$ is finite dimensional.
3. (B) Let $M$ be a closed subspace of $E$ and $x_0 \notin M$. Show that $M + \mathbb{K}x_0$ is closed. Hint: use the functional of the theorem on the distance to a closed subspace.
4. (B) Show that the polynomials are dense in $C[0, 1]$ if and only if each bounded functional that vanishes on all monomials $t^n$ is zero. Do not use the theorem of Weierstrass.
5. (B) Let $f_1, \dots, f_n \in E^*$ and $f \in E^*$ with $\bigcap_i \ker f_i \subseteq \ker f$. Show that $f$ is a linear combination of $f_1, \dots, f_n$.
6. (B) Show that a finite dimensional subspace $F$ of a normed space $E$ has a closed complement. Hint: extend the coordinate functionals of a basis of $F$.
7. (B) Show that a sequence $(x_n)$ with $f(x_n) \to 0$ for each $f \in E^*$ is bounded.
8. (C) Show that $E^*$ separable implies $E$ separable. Hint: pick $x_n$ with $\|x_n\| = 1$ and $|f_n(x_n)| \ge \|f_n\|/2$ for a dense sequence $(f_n)$, and use the corollary on the closure of a subspace.

### Notes and history

Leonidas Alaoglu published the weak-* compactness of the dual unit ball in 1940. The file `Mathlib.Analysis.Normed.Module.DoubleDual` has the authors Heather Macbeth and Michał Świętek. The file `Mathlib.Analysis.LocallyConvex.SeparatingDual` has the authors Sébastien Gouëzel and Filippo A. E. Nuccio, and the file `Mathlib.Analysis.Normed.Module.WeakDual` has the authors Kalle Kytölä, Yury Kudryashov and Michał Świętek.

### Reference

<?reference?>
