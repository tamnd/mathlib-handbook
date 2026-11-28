---
title: Covering maps and lifting
kind: theory
modules:
  - Mathlib.Topology.Covering.Basic
  - Mathlib.Topology.Covering.Deck
  - Mathlib.Topology.Covering.Quotient
  - Mathlib.Topology.Homotopy.Lifting
explains:
  E3: [IsEvenlyCovered, IsCoveringMap, IsCoveringMap.liftPath, IsCoveringMap.liftHomotopy, IsCoveringMap.existsUnique_continuousMap_lifts, IsQuotientCoveringMap, deck, IsQuotientCoveringMap.fundamentalGroupEquiv]
  E2: [IsCoveringMapOn, IsCoveringMap.isLocalHomeomorph, IsCoveringMap.isOpenMap, IsCoveringMap.isSeparatedMap, IsCoveringMap.eqOn_of_comp_eqOn, IsCoveringMap.const_of_comp, isLocalHomeomorph_iff_isCoveringMap, IsCoveringMap.exists_path_lifts, IsCoveringMap.liftPath_lifts, IsCoveringMap.liftPath_zero, IsCoveringMap.liftHomotopy_lifts, IsCoveringMap.liftHomotopy_zero, IsCoveringMap.liftHomotopyRel, IsCoveringMap.liftPath_apply_one_eq_of_homotopicRel, IsCoveringMap.monodromy, IsCoveringMap.monodromyPerm, IsCoveringMap.injective_path_homotopic_map, IsCoveringMap.existsUnique_continuousMap_lifts_of_range_le, IsQuotientCoveringMap.isCoveringMap, isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul, Subgroup.isQuotientCoveringMap, IsQuotientCoveringMap.fundamentalGroupToMulOpposite, deck.mem_iff]
  E1: auto
families: []
requires: [V05.C01, V05.C06, V13.C01, V13.C05, V13.C06, V27.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Covering maps and lifting

### Overview

A covering map $p : E \to X$ looks, over a small open set of $X$, like a stack of disjoint copies of that set. The map $\mathbb{R} \to S^1$, $s \mapsto e^{2\pi i s}$, is the model: over a short arc of the circle the preimage is a disjoint union of intervals, one for each integer. Paths and homotopies in $X$ lift uniquely to $E$ once the lift of the starting point is fixed. This lifting property turns questions on the fundamental group of $X$ into questions on the fibers of $p$, and it is the tool that computes $\pi_1(S^1)$ in the next section.

This section defines covering maps and proves the uniqueness of lifts, the lifting of paths and homotopies, and the lifting criterion. It treats quotients by group actions and deck transformations, and it computes the fundamental group of such a quotient when the total space is simply connected.

### Definitions

**Definition (Evenly covered point).** Let $p : E \to X$ be continuous, $x \in X$ and $F$ a discrete space. The point $x$ is *evenly covered* with fiber $F$ when an open set $U \ni x$ and a homeomorphism $h : p^{-1}(U) \to U \times F$ exist with $\operatorname{pr}_1 \circ h = p$. For $i \in F$ the set $h^{-1}(U \times \{i\})$ is a *sheet* over $U$.

The sheets are open, pairwise disjoint and cover $p^{-1}(U)$.

**Definition (Covering map).** A continuous map $p : E \to X$ is a *covering map* when each $x \in X$ is evenly covered with fiber $p^{-1}(x)$, with the subspace topology. It is a *covering map on* $S \subseteq X$ when this holds for each $x \in S$.

The definition does not ask $p$ to be surjective: an empty fiber is evenly covered with $U \times \emptyset = \emptyset$.

**Definition (Lift).** Let $p : E \to X$ and $f : A \to X$ be continuous. A *lift* of $f$ is a continuous map $\tilde f : A \to E$ with $p \circ \tilde f = f$.

**Definition (Deck transformation).** A *deck transformation* of $p : E \to X$ is a homeomorphism $h : E \to E$ with $p \circ h = p$. The deck transformations form a subgroup $\operatorname{Deck}(p)$ of the group of homeomorphisms of $E$.

**Definition (Quotient covering map).** Let a group $G$ act on $E$ by homeomorphisms, and let $p : E \to X$ be a quotient map. Then $p$ is a *quotient covering map* for $G$ when $p(e_1) = p(e_2)$ exactly for $e_1 \in G e_2$, and each $e \in E$ has a neighbourhood $U$ such that $gU \cap U \neq \emptyset$ implies $g = 1$.

**Definition (Properly discontinuous action).** An action of $G$ on $E$ is *properly discontinuous* when, for compact sets $K$ and $L$, only finitely many $g \in G$ have $gK \cap L \neq \emptyset$.

### Theorems and proofs

**Proposition (Local homeomorphism).** A covering map is a local homeomorphism and an open map.

*Proof.* Let $e \in E$ and $x = p(e)$, with $U$ and $h$ as in the definition. Let $i$ be the second coordinate of $h(e)$. Since $F$ is discrete, $U \times \{i\}$ is open in $U \times F$, so the sheet $V = h^{-1}(U \times \{i\})$ is open in $p^{-1}(U)$, which is open in $E$. On $V$ the map $p$ is the composite of $h$ with the homeomorphism $U \times \{i\} \to U$, so $p|_V$ is a homeomorphism onto the open set $U$. So each open $O \subseteq E$ is a union of sets $O \cap V$, each mapped onto an open set, and $p(O)$ is open. $\square$

**Theorem (Uniqueness of lifts).** Let $p$ be a covering map, $A$ a connected space and $g_1, g_2 : A \to E$ continuous with $p \circ g_1 = p \circ g_2$. If $g_1(a) = g_2(a)$ for one $a$, then $g_1 = g_2$.

*Proof.* Let $S = \{a \in A : g_1(a) = g_2(a)\}$. It is nonempty. Fix $a \in A$, put $x = p(g_1(a)) = p(g_2(a))$, and take $U$ and $h$ for $x$. Let $V_1$ and $V_2$ be the sheets that contain $g_1(a)$ and $g_2(a)$, and let $W = g_1^{-1}(V_1) \cap g_2^{-1}(V_2)$, an open neighbourhood of $a$. If $a \in S$, then $V_1 = V_2$, and on $W$ both $g_1$ and $g_2$ take values in $V_1$, where $p$ is injective. Since $p \circ g_1 = p \circ g_2$, they agree on $W$, so $W \subseteq S$. If $a \notin S$, then $V_1 \neq V_2$: two points of one sheet with the same image under $p$ are equal. Distinct sheets are disjoint, so $g_1 \neq g_2$ on $W$, and $W \cap S = \emptyset$. So $S$ is open and closed, and $S = A$ by connectedness. $\square$

**Theorem (Path lifting).** Let $p$ be a covering map, $\gamma : I \to X$ a path and $e \in E$ with $p(e) = \gamma(0)$. Exactly one lift $\Gamma$ of $\gamma$ with $\Gamma(0) = e$ exists.

*Proof.* Uniqueness follows from the previous theorem, since $I$ is connected. For existence, the sets $\gamma^{-1}(U)$, with $U$ evenly covered, form an open cover of the compact metric space $I$. By the Lebesgue number lemma there is a subdivision $0 = t_0 < t_1 < \dots < t_n = 1$ such that $\gamma([t_k, t_{k+1}]) \subseteq U_k$ for an evenly covered $U_k$. Define $\Gamma$ on $[t_0, t_k]$ by induction on $k$. Put $\Gamma(0) = e$. If $\Gamma$ is defined on $[t_0, t_k]$, let $V$ be the sheet over $U_k$ that contains $\Gamma(t_k)$, and set $\Gamma(t) = (p|_V)^{-1}(\gamma(t))$ for $t \in [t_k, t_{k+1}]$. At $t_k$ the new value is $(p|_V)^{-1}(\gamma(t_k)) = \Gamma(t_k)$, because $\Gamma(t_k) \in V$ and $p(\Gamma(t_k)) = \gamma(t_k)$. The pasting lemma gives continuity, and $p \circ \Gamma = \gamma$ holds on each piece. $\square$

**Theorem (Homotopy lifting).** Let $p$ be a covering map, $H : I \times A \to X$ continuous and $f_0 : A \to E$ a lift of $H(0, -)$. Exactly one lift $\tilde H : I \times A \to E$ of $H$ with $\tilde H(0, -) = f_0$ exists.

*Proof.* For each $a$, let $\tilde H(-, a)$ be the lift of the path $t \mapsto H(t, a)$ that starts at $f_0(a)$. This defines $\tilde H$, and it is the only candidate, by the uniqueness of path lifts. It remains to show that $\tilde H$ is continuous near each $(t, a_0)$. By compactness of $I$ and the tube lemma there are an open $W \ni a_0$ and a subdivision $0 = t_0 < \dots < t_n = 1$ with $H([t_k, t_{k+1}] \times W) \subseteq U_k$ for evenly covered $U_k$. Build a continuous lift $G$ on $I \times W_n$, for some open $W_n \ni a_0$, by induction. Put $W_0 = W$ and $G(0, a) = f_0(a)$. Suppose $G$ is defined and continuous on $[0, t_k] \times W_k$. Let $V$ be the sheet over $U_k$ that contains $G(t_k, a_0)$, put $W_{k+1} = W_k \cap G(t_k, -)^{-1}(V)$, which is open, and set $G(t, a) = (p|_V)^{-1}(H(t, a))$ for $t \in [t_k, t_{k+1}]$ and $a \in W_{k+1}$. The two definitions agree at $t = t_k$, so $G$ is continuous on $[0, t_{k+1}] \times W_{k+1}$. For each $a \in W_n$, the path $G(-, a)$ is a lift of $H(-, a)$ that starts at $f_0(a)$, so it equals $\tilde H(-, a)$. Thus $\tilde H = G$ on $I \times W_n$, and $\tilde H$ is continuous there. $\square$

**Corollary (Homotopic paths lift to paths with the same end).** Let $\gamma_0 \simeq \gamma_1$ be path homotopic paths from $x$ to $y$, and let $\Gamma_0$ and $\Gamma_1$ be their lifts that start at $e$. Then $\Gamma_0(1) = \Gamma_1(1)$, and $\Gamma_0 \simeq \Gamma_1$.

*Proof.* Let $K$ be a path homotopy, with $K(s, t)$ for the homotopy time $s$ and the path time $t$. Lift $K$ by the theorem, with $A = I$ and initial lift $\Gamma_0$. The map $s \mapsto \tilde K(s, 0)$ lifts the constant path at $x$ and starts at $e$; the constant path at $e$ is another such lift, so $\tilde K(s, 0) = e$ for all $s$. In the same way $\tilde K(s, 1) = \Gamma_0(1)$ for all $s$. So $\tilde K(1, -)$ is a lift of $\gamma_1$ that starts at $e$, hence equals $\Gamma_1$, and $\tilde K$ is a path homotopy from $\Gamma_0$ to $\Gamma_1$. $\square$

**Corollary (Injectivity on the fundamental group).** For a covering map $p$ and $e \in E$, the map $p_* : \pi_1(E, e) \to \pi_1(X, p(e))$ is injective. More generally $p$ is injective on each Hom set of the fundamental groupoid.

*Proof.* Let $\alpha, \beta$ be paths in $E$ from $e$ to $e'$ with $p \circ \alpha \simeq p \circ \beta$. The paths $\alpha$ and $\beta$ are the lifts of $p \circ \alpha$ and $p \circ \beta$ that start at $e$, so $\alpha \simeq \beta$ by the previous corollary. $\square$

**Theorem (Lifting criterion).** Let $p$ be a covering map and $A$ simply connected and locally path connected. Let $f : A \to X$ be continuous, $a_0 \in A$ and $e_0 \in E$ with $p(e_0) = f(a_0)$. Exactly one lift $F$ of $f$ with $F(a_0) = e_0$ exists.

*Proof.* Uniqueness follows from the uniqueness of lifts, since $A$ is connected. For $a \in A$ choose a path $\alpha$ from $a_0$ to $a$, and let $F(a)$ be the end point of the lift of $f \circ \alpha$ that starts at $e_0$. Two such paths are path homotopic, because $A$ is simply connected, so their images under $f$ are path homotopic and the end points of the lifts agree. So $F$ is well defined, and $p(F(a)) = f(a)$. For continuity at $a$, take an evenly covered $U \ni f(a)$ and the sheet $V \ni F(a)$. Choose a path connected neighbourhood $W$ of $a$ with $f(W) \subseteq U$. For $a' \in W$ and a path $\eta$ in $W$ from $a$ to $a'$, the path $\alpha \cdot \eta$ goes from $a_0$ to $a'$. Its image lifts to the lift of $f \circ \alpha$ followed by $(p|_V)^{-1} \circ f \circ \eta$, which starts at $F(a) \in V$. So $F(a') = (p|_V)^{-1}(f(a'))$, and $F$ is continuous on $W$. $\square$

**Theorem (Quotients by group actions).** Let $p : E \to X$ be a quotient covering map for $G$. Then $p$ is a covering map, and the action of $G$ on each fiber is free and transitive. Each $g \in G$ acts as a deck transformation.

*Proof.* Let $e \in E$, and choose an open $U \ni e$ with $gU \cap U \neq \emptyset \Rightarrow g = 1$. Then $p^{-1}(p(U)) = \bigcup_g gU$, which is open, so $p(U)$ is open because $p$ is a quotient map. The sets $gU$ are pairwise disjoint: if $gU \cap g'U \neq \emptyset$, then $g'^{-1}gU \cap U \neq \emptyset$, so $g = g'$. The map $p|_{gU}$ is injective: if $p(gu) = p(gu')$, then $u' = ku$ for some $k$, so $kU \cap U \ni u'$ and $k = 1$. It is open, because $p^{-1}(p(O)) = \bigcup_k kO$ is open for open $O$. So $p|_{gU} : gU \to p(U)$ is a homeomorphism, and $(g, u) \mapsto gu$ gives $p(U) \times G \cong p^{-1}(p(U))$, with $G$ discrete. The fiber over $p(e)$ is the orbit $Ge$, and $g \mapsto ge$ is a bijection by the disjointness. Finally $p(ge) = p(e)$ for all $e$, and $g$ acts by a homeomorphism. $\square$

**Theorem (The fundamental group of a quotient).** Let $p : E \to X$ be a quotient covering map for $G$, with $E$ simply connected, $x = p(e)$. For a loop $\gamma$ at $x$, let $\varphi[\gamma]$ be the unique $g$ with $\Gamma(1) = g e$, where $\Gamma$ is the lift that starts at $e$. Then $\varphi$ is a bijection $\pi_1(X, x) \to G$ with $\varphi[\gamma \cdot \delta] = \varphi[\gamma]\varphi[\delta]$, where $\gamma \cdot \delta$ runs $\gamma$ first.

*Proof.* The map is well defined by the corollary on homotopic paths. For the product, let $\varphi[\gamma] = g$ and $\varphi[\delta] = h$, with lifts $\Gamma$ and $\Delta$ from $e$. The path $g \Delta$ is a lift of $\delta$, since $g$ is a deck transformation, and it starts at $ge = \Gamma(1)$. So $\Gamma \cdot g\Delta$ is the lift of $\gamma \cdot \delta$, and it ends at $g h e$. Surjectivity: $E$ is path connected, so a path $\Gamma$ from $e$ to $ge$ exists, and $p \circ \Gamma$ is a loop with $\varphi = g$. Injectivity: if $\Gamma(1) = e$, then $\Gamma$ is a loop in $E$, homotopic to the constant loop, so $\gamma = p \circ \Gamma$ is nullhomotopic. $\square$

### Examples

**Example (The exponential map and the lift of a path).** Let $p : \mathbb{R} \to S^1$, $p(s) = (\cos 2\pi s, \sin 2\pi s)$. For the arc $U = S^1 \setminus \{(-1, 0)\}$, the preimage is $\bigsqcup_{n \in \mathbb{Z}} (n - 1/2, n + 1/2)$, and $p$ maps each interval homeomorphically onto $U$. The same holds for $S^1 \setminus \{(1, 0)\}$, so $p$ is a covering map. The half circle $\gamma(t) = (\cos \pi t, \sin \pi t)$ from $(1, 0)$ to $(-1, 0)$ has the lift $\Gamma(t) = t/2$ that starts at $0$. Check: $p(t/2) = (\cos \pi t, \sin \pi t)$.

**Counterexample (A local homeomorphism that is not a covering).** Let $q : (0, 2) \to S^1$ be the restriction of $p$. It is surjective and a local homeomorphism. The point $(1, 0)$ is not evenly covered. For a small arc $U$ around it, $q^{-1}(U) = (0, \varepsilon) \cup (1 - \varepsilon, 1 + \varepsilon) \cup (2 - \varepsilon, 2)$, and the piece $(0, \varepsilon)$ maps onto only half of $U$. A homeomorphism $q^{-1}(U) \cong U \times F$ would map each component onto $U$. So $q$ is not a covering map. The index proves the converse for compact Hausdorff $E$ and Hausdorff $X$: then each local homeomorphism is a covering map.

**Example (The translation action).** The group $\mathbb{Z}$ acts on $\mathbb{R}$ by $n \cdot s = s + n$. For $U = (s - 1/3, s + 1/3)$, the set $U + n$ meets $U$ only for $n = 0$. So $\mathbb{R} \to \mathbb{R}/\mathbb{Z}$ is a quotient covering map, and each translation $s \mapsto s + n$ is a deck transformation of $p$.

### The library around it

::: mathlib
`IsEvenlyCovered` · `Mathlib.Topology.Covering.Basic`

`IsEvenlyCovered f x I` says that `I` is discrete and that an open `U ∋ x` with open preimage and a homeomorphism `H : f ⁻¹' U ≃ₜ U × I` with `(H e).1 = f e` exist. `IsCoveringMapOn f s` asks this for `x ∈ s` with `I = f ⁻¹' {x}`.

<?decl IsEvenlyCovered?>
:::

::: mathlib
`IsCoveringMap` · `Mathlib.Topology.Covering.Basic`

`IsCoveringMap f` is `∀ x, IsEvenlyCovered f x (f ⁻¹' {x})`; surjectivity is not part of it. The basic consequences are `IsCoveringMap.isLocalHomeomorph`, `IsCoveringMap.isOpenMap` and `IsCoveringMap.isSeparatedMap`. Uniqueness of lifts is `IsCoveringMap.eqOn_of_comp_eqOn`, on a preconnected set, and `IsCoveringMap.const_of_comp`. The lemma `isLocalHomeomorph_iff_isCoveringMap` is the converse for compact Hausdorff `E`. Examples elsewhere in the index are `Complex.isCoveringMap_exp` and `isCoveringMap_zpow`.

<?decl IsCoveringMap?>
:::

::: mathlib
`IsCoveringMap.liftPath` · `Mathlib.Topology.Homotopy.Lifting`

`cov.liftPath γ e γ_0` is the lift of `γ : C(I, X)` with `γ_0 : γ 0 = p e`, chosen from `IsCoveringMap.exists_path_lifts`. Its properties are `liftPath_lifts` and `liftPath_zero`.

<?decl IsCoveringMap.liftPath?>
:::

::: mathlib
`IsCoveringMap.liftHomotopy` · `Mathlib.Topology.Homotopy.Lifting`

`cov.liftHomotopy H f H_0` lifts `H : C(I × A, X)` with initial lift `f : C(A, E)`; the time is the first coordinate. The source states that this makes a covering map a Hurewicz fibration. `IsCoveringMap.liftHomotopyRel` lifts a homotopy relative to a set, and `IsCoveringMap.liftPath_apply_one_eq_of_homotopicRel` is the first corollary. `IsCoveringMap.injective_path_homotopic_map` is the second. `IsCoveringMap.monodromy` and `IsCoveringMap.monodromyPerm` give the action of paths on fibers.

<?decl IsCoveringMap.liftHomotopy?>
:::

::: mathlib
`IsCoveringMap.existsUnique_continuousMap_lifts` · `Mathlib.Topology.Homotopy.Lifting`

The statement is `∃! F : C(A, E), F a₀ = e₀ ∧ p ∘ F = f` under `[SimplyConnectedSpace A] [LocallyPathConnectedSpace A]`. The general lifting criterion is `IsCoveringMap.existsUnique_continuousMap_lifts_of_range_le`, with the hypothesis `(map f a₀).range ≤ (mapOfEq ⟨p, _⟩ he).range` on fundamental groups.

<?decl IsCoveringMap.existsUnique_continuousMap_lifts?>
:::

::: mathlib
`IsQuotientCoveringMap` · `Mathlib.Topology.Covering.Quotient`

The structure extends `IsQuotientMap f` and `ContinuousConstSMul G E` with the fields `apply_eq_iff_mem_orbit` and `disjoint`, as in the definition. `IsQuotientCoveringMap.isCoveringMap` is the first claim of the theorem. `isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul` gives the quotient by a `ProperlyDiscontinuousSMul` action with `IsCancelSMul`, on a locally compact Hausdorff space. `Subgroup.isQuotientCoveringMap` treats the quotient of a topological group by a discrete subgroup. The additive version is `IsAddQuotientCoveringMap`.

<?decl IsQuotientCoveringMap?>
:::

::: mathlib
`deck` · `Mathlib.Topology.Covering.Deck`

`deck p` is the subgroup of `E ≃ₜ E` of the `h` with `p ∘ h = p`; this is `deck.mem_iff`.

<?decl deck?>
:::

::: mathlib
`IsQuotientCoveringMap.fundamentalGroupEquiv` · `Mathlib.Topology.Homotopy.Lifting`

Under `[SimplyConnectedSpace E]` this is a group isomorphism `FundamentalGroup X x ≃* Gᵐᵒᵖ`. The opposite group appears because `p * q` in `FundamentalGroup` runs `q` first, while the theorem above multiplies in path order. The homomorphism is `IsQuotientCoveringMap.fundamentalGroupToMulOpposite`, which is surjective for path connected `E` and injective for simply connected `E`.

<?decl IsQuotientCoveringMap.fundamentalGroupEquiv?>
:::

Common errors of a learner: `IsCoveringMap` does not imply surjectivity, so `IsCoveringMap.isQuotientMap` needs a separate surjectivity hypothesis. The fiber in `IsEvenlyCovered` must be discrete in its own topology. A local homeomorphism need not be a covering map, as the counterexample shows. The isomorphism of fundamental groups goes to `Gᵐᵒᵖ`, not to `G`.

### Exercises

1. (A) Find the lift of the loop $\gamma(t) = (\cos 4\pi t, \sin 4\pi t)$ under $p(s) = (\cos 2\pi s, \sin 2\pi s)$ that starts at $1$, and its end point. *Hint:* Try a linear function of $t$.
2. (A) Show that a homeomorphism is a covering map, and that the projection $X \times F \to X$ is a covering map for discrete $F$. *Hint:* Take $U = X$.
3. (B) Show that a deck transformation of a covering map with connected $E$ that fixes one point is the identity. *Hint:* Apply the uniqueness of lifts to $h$ and $\mathrm{id}_E$ as lifts of $p$.
4. (B) Let $p : E \to X$ be a covering map, $X$ connected. Show that all fibers have the same cardinality. *Hint:* Show that the set of $x$ with a fiber of a given cardinality is open and closed.
5. (C) Show that every continuous map $f : S^2 \to S^1$ is nullhomotopic, if you know that $S^2$ is simply connected and locally path connected. *Hint:* Lift $f$ to $\mathbb{R}$ and use the straight-line homotopy in $\mathbb{R}$.
6. (C) Let $G$ be a finite group acting freely on a Hausdorff space $E$ by homeomorphisms. Show that $E \to E/G$ is a quotient covering map. *Hint:* Separate the finitely many points $ge$ by disjoint open sets and intersect their translates.

### Notes and history

Covering spaces appear in the work of Poincaré on the fundamental group in 1895. The Mathlib sources follow Hatcher for the lifting of homotopies, the injectivity on fundamental groups and the lifting criterion.

The Mathlib Author of `Topology.Covering.Basic` is Thomas Browning. The Mathlib Author of `Topology.Covering.Deck` is Kim Morrison. The Mathlib Author of `Topology.Covering.Quotient` and `Topology.Homotopy.Lifting` is Junyan Xu.

### Reference

<?reference?>
