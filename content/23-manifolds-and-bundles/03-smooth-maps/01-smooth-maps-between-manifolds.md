---
title: Smooth maps between manifolds
kind: theory
modules:
  - Mathlib.Geometry.Manifold.ContMDiff.Defs
  - Mathlib.Geometry.Manifold.ContMDiff.Basic
  - Mathlib.Geometry.Manifold.Notation
explains:
  E3: [ContMDiffWithinAt, ContMDiffAt, ContMDiff, contMDiffWithinAt_iff, contDiffWithinAt_localInvariantProp]
  E2: [ContMDiffOn, ContDiffWithinAtProp, contMDiffAt_iff, contMDiffOn_iff, contMDiff_iff, contMDiffAt_iff_of_mem_maximalAtlas, ContMDiff.continuous, contMDiff_zero_iff, ContMDiff.of_le, contMDiff_infty, contMDiff_of_locally_contMDiffOn, contMDiffAt_iff_contMDiffAt_nhds, ContMDiffWithinAt.comp, ContMDiffAt.comp, ContMDiff.comp, contMDiff_id, contMDiff_const, contMDiff_isOpenEmbedding, contMDiff_subtypeVal, contMDiff_inclusion, ContMDiff.piecewise]
  E1: auto
families: []
requires: [V23.C01, V23.C02, V17.C04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Smooth maps between manifolds

### Overview

A map $f : M \to M'$ between manifolds is $C^n$ at $x$ if it is continuous at $x$ and if it is $C^n$ when read in charts near $x$ and $f(x)$. Two questions arise at once. The first is which charts to use. The second is how to differentiate at a boundary point, where the chart takes values in a half space. Mathlib answers the second with the extended charts of Chapter 2: the map read in charts is a map between normed spaces, and it is required to be $C^n$ within the range of the model. It answers the first with the local invariant properties of Chapter 1: the definition uses the preferred charts, and the general theorem of that chapter shows that any charts of the maximal atlases give the same notion.

This section gives the definitions, the formula in extended charts, the invariance under the groupoids of $C^n$ maps, and the composition rule.

### Definitions

Fix models $I : H \to E$ and $I' : H' \to E'$ over $\mathbb{K}$, charted spaces $M$ over $H$ and $M'$ over $H'$, and $n \in \mathbb{N} \cup \{\infty, \omega\}$.

**Definition (The property in the model).** For $g : H \to H'$, $s \subseteq H$ and $y \in H$, the property $P_n(g, s, y)$ says that $I' \circ g \circ I^{-1}$ is $C^n$ within $(I^{-1})^{-1}(s) \cap \mathrm{range}\, I$ at $I(y)$.

**Definition ($C^n$ maps).** Let $f : M \to M'$, $s \subseteq M$ and $x \in M$. The map $f$ is *$C^n$ within $s$ at $x$* if it satisfies the lift of $P_n$ of Chapter 1, Section 2: $f$ is continuous within $s$ at $x$, and $P_n(\varphi'_{f(x)} \circ f \circ \varphi_x^{-1},\ (\varphi_x^{-1})^{-1}(s),\ \varphi_x(x))$ holds. It is *$C^n$ at $x$* if it is $C^n$ within $M$ at $x$, *$C^n$ on $s$* if it is $C^n$ within $s$ at every point of $s$, and *$C^n$* if it is $C^n$ at every point.

Over $\mathbb{R}$, $C^\infty$ maps are called *smooth*.

::: mathlib
`ContMDiffWithinAt` · `Mathlib.Geometry.Manifold.ContMDiff.Defs`

`ContMDiffWithinAt I I' n f s x` is defined as `LiftPropWithinAt (ContDiffWithinAtProp I I' n) f s x`, with `ContDiffWithinAtProp I I' n g s y` the property $P_n$. The index `n` has type `WithTop ℕ∞`, so `∞` is `((⊤ : ℕ∞) : WithTop ℕ∞)` and `ω` is `⊤`. Then `ContMDiffAt I I' n f x`, `ContMDiffOn I I' n f s` and `ContMDiff I I' n f` follow. The definitions need no `IsManifold` instance.

<?decl ContMDiffWithinAt?>
<?decl ContMDiffAt?>
<?decl ContMDiff?>
:::

### Theorems and proofs

**Theorem (The definition in extended charts).** $f$ is $C^n$ within $s$ at $x$ if and only if $f$ is continuous within $s$ at $x$ and the map $\hat\varphi'_{f(x)} \circ f \circ \hat\varphi_x^{-1}$ is $C^n$ within $(\hat\varphi_x^{-1})^{-1}(s) \cap \mathrm{range}\, I$ at $\hat\varphi_x(x)$.

*Proof.* Write $\varphi = \varphi_x$, $\psi = \varphi'_{f(x)}$ and $g = \psi \circ f \circ \varphi^{-1}$. By definition, $P_n(g, (\varphi^{-1})^{-1}(s), \varphi(x))$ says that $I' \circ g \circ I^{-1}$ is $C^n$ within $(I^{-1})^{-1}((\varphi^{-1})^{-1}(s)) \cap \mathrm{range}\, I$ at $I(\varphi(x))$. Now $I' \circ g \circ I^{-1} = (I' \circ \psi) \circ f \circ (\varphi^{-1} \circ I^{-1}) = \hat\psi \circ f \circ \hat\varphi^{-1}$, the set is $(\hat\varphi^{-1})^{-1}(s) \cap \mathrm{range}\, I$, and the point is $\hat\varphi(x)$. So the two conditions are the same. $\square$

**Theorem (Invariance).** $P_n$ is a local invariant property for the groupoids $G_n(I)$ and $G_n(I')$.

*Proof.* There are four conditions.

*Locality.* Let $u$ be open with $y \in u$. The set $(I^{-1})^{-1}(u)$ is open, since $I^{-1}$ is continuous, and it contains $I(y)$. Being $C^n$ within a set at a point depends only on the intersection of the set with a neighbourhood of the point (Volume 17, Chapter 4). So $P_n(g, s, y)$ and $P_n(g, s \cap u, y)$ are equivalent.

*Congruence.* If $g = g'$ on $s$ and $g(y) = g'(y)$, then $I' \circ g \circ I^{-1}$ and $I' \circ g' \circ I^{-1}$ agree on $(I^{-1})^{-1}(s) \cap \mathrm{range}\, I$ and at $I(y)$, because $I^{-1}(I(h)) = h$. A $C^n$ map within a set stays $C^n$ when it is changed outside the set and the point.

*Right invariance.* Let $e \in G_n(I)$, $y \in e.\mathrm{source}$, and assume $P_n(g, s, y)$. Let $F = I' \circ g \circ I^{-1}$, $A = (I^{-1})^{-1}(s) \cap \mathrm{range}\, I$ and $\Phi = I \circ e^{-1} \circ I^{-1}$. Since $e^{-1} \in G_n(I)$, $\Phi$ is $C^n$ on $(I^{-1})^{-1}(e.\mathrm{target}) \cap \mathrm{range}\, I$, and $\Phi(I(e(y))) = I(y)$. Since $I^{-1} \circ I = \mathrm{id}$, $I' \circ (g \circ e^{-1}) \circ I^{-1} = F \circ \Phi$. Let $B = (I^{-1})^{-1}(e.\mathrm{target} \cap (e^{-1})^{-1}(s)) \cap \mathrm{range}\, I$. It is the set of $P_n(g \circ e^{-1}, (e^{-1})^{-1}(s), e(y))$ intersected with the open neighbourhood $(I^{-1})^{-1}(e.\mathrm{target})$ of $I(e(y))$. For $z \in B$, $\Phi(z) \in \mathrm{range}\, I$ and $I^{-1}(\Phi(z)) = e^{-1}(I^{-1}(z)) \in s$, so $\Phi$ maps $B$ into $A$. By the chain rule for $C^n$ maps within sets, $F \circ \Phi$ is $C^n$ within $B$ at $I(e(y))$. Locality gives $P_n(g \circ e^{-1}, (e^{-1})^{-1}(s), e(y))$.

*Left invariance.* Let $e' \in G_n(I')$, $s \subseteq g^{-1}(e'.\mathrm{source})$, $g(y) \in e'.\mathrm{source}$, and assume $P_n(g, s, y)$. Let $\Psi = I' \circ e' \circ I'^{-1}$, which is $C^n$ on $C = (I'^{-1})^{-1}(e'.\mathrm{source}) \cap \mathrm{range}\, I'$. Since $I'^{-1} \circ I' = \mathrm{id}$, $I' \circ (e' \circ g) \circ I^{-1} = \Psi \circ F$. For $z \in A$, $F(z) = I'(g(I^{-1}(z)))$ with $g(I^{-1}(z)) \in e'.\mathrm{source}$, so $F$ maps $A$ into $C$. Also $F(I(y)) \in C$. The chain rule gives that $\Psi \circ F$ is $C^n$ within $A$ at $I(y)$, which is $P_n(e' \circ g, s, y)$. $\square$

**Corollary (Independence of the charts).** Let $M$ and $M'$ be $C^n$ manifolds. Let $e$ and $e'$ be in the maximal atlases of $M$ and $M'$, with $x \in e.\mathrm{source}$ and $f(x) \in e'.\mathrm{source}$. Then $f$ is $C^n$ at $x$ if and only if $f$ is continuous at $x$ and $e'_{I'} \circ f \circ e_I^{-1}$ is $C^n$ within $\mathrm{range}\, I$ at $e_I(x)$.

*Proof.* By the theorem on invariance, Chapter 1, Section 2 applies: the lift of $P_n$ can be computed in any charts of the maximal atlases. The formula of the first theorem, with $e$ and $e'$ in place of the preferred charts and $s = M$, gives the claim. $\square$

**Theorem (Composition).** Let $f : M \to M'$ be $C^n$ within $s$ at $x$, let $g : M' \to M''$ be $C^n$ within $t$ at $f(x)$, and let $f(s) \subseteq t$. Then $g \circ f$ is $C^n$ within $s$ at $x$. No manifold hypothesis is needed.

*Proof.* Continuity within $s$ at $x$ is clear. Write $\hat\varphi = \hat\varphi_x$, $\hat\psi = \hat\varphi'_{f(x)}$ and $\hat\chi = \hat\varphi''_{g(f(x))}$. By the first theorem, $F = \hat\psi \circ f \circ \hat\varphi^{-1}$ is $C^n$ within $A = (\hat\varphi^{-1})^{-1}(s) \cap \mathrm{range}\, I$ at $a = \hat\varphi(x)$, and $G = \hat\chi \circ g \circ \hat\psi^{-1}$ is $C^n$ within $B = (\hat\psi^{-1})^{-1}(t) \cap \mathrm{range}\, I'$ at $F(a) = \hat\psi(f(x))$. By Chapter 2, Section 2, $\hat\varphi^{-1}$ maps $\mathcal{N}_{\mathrm{range}\, I}(a)$ onto $\mathcal{N}(x)$. Since $f$ is continuous within $s$ at $x$, there is a neighbourhood $V$ of $a$ such that every $z \in A \cap V$ has $f(\hat\varphi^{-1}(z)) \in \psi.\mathrm{source}$. For such $z$, $\hat\psi^{-1}(F(z)) = f(\hat\varphi^{-1}(z))$, which lies in $t$, so $F(z) \in B$, and $G(F(z)) = \hat\chi(g(f(\hat\varphi^{-1}(z))))$. The chain rule gives that $G \circ F$ is $C^n$ within $A \cap V$ at $a$, and $A \cap V$ agrees with $A$ near $a$. On $A \cap V$ and at $a$, $G \circ F$ equals $\hat\chi \circ (g \circ f) \circ \hat\varphi^{-1}$. By the first theorem, $g \circ f$ is $C^n$ within $s$ at $x$. $\square$

The proof uses only the preferred charts at $x$, $f(x)$ and $g(f(x))$, so no change of charts appears.

::: mathlib
`contMDiffWithinAt_iff` · `Mathlib.Geometry.Manifold.ContMDiff.Defs`

`contMDiffWithinAt_iff` is the first theorem, and `contMDiffAt_iff` the version with `range I`. The global forms `contMDiffOn_iff` and `contMDiff_iff` quantify over all pairs of preferred charts and need `[IsManifold I n M] [IsManifold I' n M']`. The invariance is `contDiffWithinAt_localInvariantProp n`, and the independence is `contMDiffAt_iff_of_mem_maximalAtlas`, with `e ∈ IsManifold.maximalAtlas I n M`. The composition rules `ContMDiffWithinAt.comp` (with an explicit point and `MapsTo f s t`), `ContMDiffAt.comp` and `ContMDiff.comp` have no `IsManifold` hypothesis.

<?decl contMDiffWithinAt_iff?>
<?decl contDiffWithinAt_localInvariantProp?>
<?decl contMDiffAt_iff_of_mem_maximalAtlas?>
<?decl ContMDiff.comp?>
:::

### Examples

**Example (Identity and constants).** The identity is $C^n$: in charts it is $\hat\varphi_x \circ \hat\varphi_x^{-1}$, the identity near $\hat\varphi_x(x)$ within $\mathrm{range}\, I$. A constant map is $C^n$: in charts it is constant (`contMDiff_id`, `contMDiff_const`).

**Example (Open subsets).** For an open set $U \subseteq M$ with the charts of Chapter 2, Section 1, the inclusion $U \to M$ is $C^n$ (`contMDiff_subtypeVal`), and so is the inclusion $U \to V$ for $U \subseteq V$ (`contMDiff_inclusion`). In charts these maps are the identity.

**Example (A continuous map that is not smooth).** On $\mathbb{R}$ with the trivial model, $f(t) = |t|$ is $C^0$ and not $C^1$ at $0$. On the half line $[0, \infty)$ with the model of Chapter 2, $g(t) = \sqrt{t}$ is $C^0$, and not $C^1$ at $0$: its derivative within $[0, \infty)$ does not exist at $0$. The map $h(t) = t$ from $[0, \infty)$ to $\mathbb{R}$ is $C^\omega$, with one sided derivative $1$ at $0$.

**Example (Gluing).** If $f$ and $g$ are $C^n$ and agree near the frontier of $s$, the map equal to $f$ on $s$ and to $g$ outside is $C^n$ (`ContMDiff.piecewise`). Near each point it equals $f$ or $g$.

### The library around it

The module `Mathlib.Geometry.Manifold.ContMDiff.Defs` follows the API of `ContDiff` in Volume 17. It has the monotonicity `ContMDiff.of_le` in $n$, the characterisation `contMDiff_infty` of $C^\infty$ as $C^k$ for every $k$, the equivalence `contMDiff_zero_iff` of $C^0$ with continuity, the implication `ContMDiff.continuous`, and the locality `contMDiff_of_locally_contMDiffOn`. The lemma `contMDiffAt_iff_contMDiffAt_nhds` says that a map $C^n$ at $x$, with $n \neq \omega$, is $C^n$ near $x$. It needs both `IsManifold` instances: the charts at nearby points differ from the charts at $x$.

The module `Mathlib.Geometry.Manifold.Notation` defines elaborators that infer the models. In the scope `Manifold`, `CMDiff n f` stands for `ContMDiff I I' n f`, and `CMDiffAt n f x`, `CMDiff[s] n f` and `CMDiffAt[s] n f x` stand for the other three. The same module gives `MDiff f` and `mfderiv% f x` for Chapter 4. The elaborators look for the models in the local context and refuse a product of normed spaces, where two models are possible.

Common errors of a learner:

- Writing `ContMDiff I I' ∞ f` and meaning analytic maps. The index `∞` is smooth, and `ω` is analytic.
- Forgetting the continuity in the definition. Without it, the expression in charts uses junk values of the inverse charts outside their targets, and a discontinuous map can pass the test in charts.
- Expecting `contMDiff_iff` without `IsManifold` instances. The pointwise `contMDiffAt_iff` needs none.
- Using `CMDiff n f` on a map into `E × F` and getting an error: the elaborator does not choose between the two models.

### Exercises

1. (A) Show that $f$ is $C^n$ on an open set $U$ if and only if $f$ is $C^n$ at every point of $U$.
2. (A) Show that a $C^n$ map is $C^m$ for $m \le n$, from the same fact for maps between normed spaces.
3. (A) Show that $f$ is $C^0$ if and only if $f$ is continuous. Hint: use the description of $C^0$ maps within a set in Volume 17, Chapter 4, and the continuity of the extended charts.
4. (B) Prove the congruence condition of the theorem on invariance in full, including the role of the point $I(y)$.
5. (B) Let $f : M \to M'$ be continuous. Show that if $M$ has the charts of an open subset of $E$ and $M' = E'$, then $f$ is $C^n$ if and only if $f$ is $C^n$ as a map between open sets of normed spaces.
6. (B) Give an example of a map from the circle to $\mathbb{R}$ that is $C^1$ and not $C^2$, and check it in both charts.
7. (C) Show by an example that the condition $f(s) \subseteq t$ in the composition theorem cannot be dropped.

### Notes and history

The definition of differentiable maps through charts goes back to the first definitions of differentiable manifolds. The approach through local invariant properties of a pseudogroup is that of the general theory of $G$-structures. In Mathlib it makes chart independence a single theorem, used for smoothness, for differentiability in Chapter 4 and for local structomorphisms.

### Reference

<?reference?>
