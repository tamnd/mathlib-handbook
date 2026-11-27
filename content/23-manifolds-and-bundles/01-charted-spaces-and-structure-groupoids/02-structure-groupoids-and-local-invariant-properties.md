---
title: Structure groupoids and local invariant properties
kind: theory
modules:
  - Mathlib.Geometry.Manifold.StructureGroupoid
  - Mathlib.Geometry.Manifold.HasGroupoid
  - Mathlib.Geometry.Manifold.LocalInvariantProperties
  - Mathlib.Geometry.Manifold.ConformalGroupoid
explains:
  E3: [StructureGroupoid, HasGroupoid, StructureGroupoid.maximalAtlas, StructureGroupoid.LocalInvariantProp, ChartedSpace.LiftPropWithinAt, StructureGroupoid.LocalInvariantProp.liftPropWithinAt_indep_chart]
  E2: [Pregroupoid, Pregroupoid.groupoid, mem_groupoid_of_pregroupoid, continuousGroupoid, idGroupoid, ClosedUnderRestriction, closedUnderRestriction_iff_id_le, HasGroupoid.compatible, hasGroupoid_of_pregroupoid, hasGroupoid_of_le, StructureGroupoid.subset_maximalAtlas, StructureGroupoid.compatible_of_mem_maximalAtlas, mem_maximalAtlas_iff, Structomorph, TopologicalSpace.Opens.instChartedSpace, TopologicalSpace.Opens.instHasGroupoid, ChartedSpace.LiftPropAt, ChartedSpace.LiftProp, ChartedSpace.liftPropAt_iff, StructureGroupoid.LocalInvariantProp.liftPropWithinAt_indep_chart_source, StructureGroupoid.LocalInvariantProp.liftProp_of_locally_liftPropOn, StructureGroupoid.HasGroupoid.comp, conformalGroupoid, conformalPregroupoid]
  E1: auto
families: []
requires: [V13.C01, V13.C04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Structure groupoids and local invariant properties

### Overview

To do analysis on a charted space, one asks that each change of charts $\varphi^{-1} \gg \psi$ belong to a chosen class $G$ of partial homeomorphisms of $H$: the continuous maps, the $C^k$ maps, the conformal maps. A structure groupoid is such a class. This section defines structure groupoids, charted spaces with a groupoid, and the maximal atlas. Then it shows that a property of maps in the model that is invariant under the groupoid, read in charts, does not depend on the charts. Chapter 3 defines smooth maps in this way.

### Definitions

**Definition (Structure groupoid).** A *structure groupoid* on $H$ is a set $G$ of partial homeomorphisms from $H$ to $H$ such that:

1. if $e, e' \in G$, then $e \gg e' \in G$;
2. if $e \in G$, then $e^{-1} \in G$;
3. the identity of $H$ is in $G$;
4. (locality) if for each $x \in e.\mathrm{source}$ there is an open $s \ni x$ with $e|_s \in G$, then $e \in G$;
5. if $e \in G$ and $e'$ has the same source as $e$ and agrees with $e$ on it, then $e' \in G$.

The largest is the *continuous groupoid* of all partial homeomorphisms. The smallest is the *identity groupoid*: the identity and the partial homeomorphisms with empty source. A groupoid is *closed under restriction* if $e|_s \in G$ for all $e \in G$ and all open $s$. 

::: mathlib
`StructureGroupoid` · `Mathlib.Geometry.Manifold.StructureGroupoid`

`StructureGroupoid H` is a structure with `members : Set (OpenPartialHomeomorph H H)` and the fields `trans'`, `symm'`, `id_mem'`, `locality'` and `mem_of_eqOnSource'`. The lemmas `StructureGroupoid.trans`, `.symm`, `.id_mem`, `.locality` and `.mem_of_eqOnSource` state the conditions. The extremes are `continuousGroupoid H` and `idGroupoid H`. `ClosedUnderRestriction G` is a class, and `closedUnderRestriction_iff_id_le` says that it holds if and only if `idRestrGroupoid ≤ G`.

<?decl StructureGroupoid?>
<?decl continuousGroupoid?>
<?decl idGroupoid?>
<?decl ClosedUnderRestriction?>
<?decl closedUnderRestriction_iff_id_le?>
:::

Most groupoids come from a property of maps on open sets.

**Definition (Pregroupoid).** A *pregroupoid* on $H$ is a property $P(f, u)$ of maps $f : H \to H$ and open sets $u \subseteq H$ such that: $P(f, u)$ and $P(g, v)$ imply $P(g \circ f, u \cap f^{-1}(v))$ when this set is open; $P(\mathrm{id}, H)$ holds; $P(f, u)$ holds when each $x \in u$ has an open $v \ni x$ with $P(f, u \cap v)$; and $P(f, u)$ with $g = f$ on $u$ gives $P(g, u)$. The *groupoid of* $P$ is the set of $e$ with $P(e, e.\mathrm{source})$ and $P(e^{-1}, e.\mathrm{target})$. It is a structure groupoid (Exercise 2), and `mem_groupoid_of_pregroupoid` states its members.

**Definition (Groupoid structure).** A charted space $M$ over $H$ *has the groupoid* $G$ if $e^{-1} \gg e' \in G$ for all $e, e'$ in the atlas.

::: mathlib
`HasGroupoid` · `Mathlib.Geometry.Manifold.HasGroupoid`

`HasGroupoid M G` is a class in `Prop` with the one field `compatible`. `hasGroupoid_of_le` passes to a larger groupoid. For a pregroupoid, `hasGroupoid_of_pregroupoid` asks for the property of each change of charts on its source.

<?decl HasGroupoid?>
<?decl hasGroupoid_of_pregroupoid?>
<?decl Pregroupoid.groupoid?>
:::

**Definition (Maximal atlas).** Let $M$ be a charted space over $H$ and $G$ a groupoid on $H$. The *maximal atlas* of $M$ for $G$ is the set of partial homeomorphisms $e : M \to H$ such that $e^{-1} \gg e' \in G$ and $e'^{-1} \gg e \in G$ for every $e'$ in the atlas.

If $M$ has the groupoid $G$, the atlas is a subset of the maximal atlas.

**Definition (Local invariant property).** Let $G$ and $G'$ be groupoids on $H$ and $H'$. A property $P(f, s, x)$ of maps $f : H \to H'$, sets $s \subseteq H$ and points $x \in H$ is *local invariant* for $(G, G')$ if:

1. (locality) for $u$ open with $x \in u$, $P(f, s, x) \Leftrightarrow P(f, s \cap u, x)$;
2. (right invariance) for $e \in G$ and $x \in e.\mathrm{source}$, $P(f, s, x)$ implies $P(f \circ e^{-1}, (e^{-1})^{-1}(s), e(x))$;
3. (congruence) if $f = g$ on $s$ and $f(x) = g(x)$, then $P(f, s, x)$ implies $P(g, s, x)$;
4. (left invariance) for $e' \in G'$ with $f(s) \subseteq e'.\mathrm{source}$ and $f(x) \in e'.\mathrm{source}$, $P(f, s, x)$ implies $P(e' \circ f, s, x)$.

**Definition (Lift of a property).** Let $M, M'$ be charted spaces over $H, H'$, with preferred charts $\varphi$ and $\varphi'$. A map $g : M \to M'$ has the *lifted property* within $s$ at $x$ if $g$ is continuous within $s$ at $x$ and
$$P\big(\varphi'_{g(x)} \circ g \circ \varphi_x^{-1},\ (\varphi_x^{-1})^{-1}(s),\ \varphi_x(x)\big).$$
It has the lifted property at $x$ if this holds with $s = M$, on $s$ if it holds within $s$ at each $x \in s$, and everywhere if it holds at each $x$.

::: mathlib
`ChartedSpace.LiftPropWithinAt` · `Mathlib.Geometry.Manifold.LocalInvariantProperties`

`StructureGroupoid.LocalInvariantProp G G' P` is a structure in `Prop` with the fields `is_local`, `right_invariance'`, `congr_of_forall` and `left_invariance'`. `ChartedSpace.LiftPropWithinAt P g s x` is a structure with the fields `continuousWithinAt` and `prop`. The variants are `LiftPropAt`, `LiftPropOn` and `LiftProp`, and `ChartedSpace.liftPropAt_iff` unfolds `LiftPropAt`.

<?decl StructureGroupoid.LocalInvariantProp?>
<?decl ChartedSpace.LiftPropWithinAt?>
<?decl ChartedSpace.liftPropAt_iff?>
:::

### Theorems and proofs

**Theorem (Members of the maximal atlas are compatible).** Let $e, e'$ be in the maximal atlas of $M$ for $G$. Then $e^{-1} \gg e' \in G$.

*Proof.* By locality it is enough to show that each $y$ in the source of $e^{-1} \gg e'$ has an open neighbourhood $o$ with $(e^{-1} \gg e')|_o \in G$. Put $x = e^{-1}(y)$ and let $c = \varphi_x$ be the preferred chart. Let $o = e.\mathrm{target} \cap (e^{-1})^{-1}(c.\mathrm{source})$. It is open and contains $y$. By the definition of the maximal atlas, $a = e^{-1} \gg c$ and $b = c^{-1} \gg e'$ are in $G$, so $a \gg b \in G$. The source of $a \gg b$ is the set of $z \in e.\mathrm{target}$ with $e^{-1}(z) \in c.\mathrm{source}$ and $c^{-1}(c(e^{-1}(z))) = e^{-1}(z) \in e'.\mathrm{source}$. This is the source of $(e^{-1} \gg e')|_o$. On it, $(a \gg b)(z) = e'(c^{-1}(c(e^{-1}(z)))) = e'(e^{-1}(z))$. By condition 5, $(e^{-1} \gg e')|_o \in G$. $\square$

The main theorem rests on a lemma: a local invariant property depends only on germs.

**Lemma (Germs).** Let $P$ satisfy locality and congruence. Let $u$ be open with $x \in u$. If $f = g$ on $u$ and $s \cap u = t \cap u$, then $P(f, s, x) \Leftrightarrow P(g, t, x)$.

*Proof.* By locality $P(f, s, x) \Leftrightarrow P(f, t \cap u, x)$. Congruence in both directions gives $P(f, t \cap u, x) \Leftrightarrow P(g, t \cap u, x)$, and locality again gives $P(g, t, x)$. $\square$

**Theorem (Independence of the charts).** Let $P$ be local invariant for $(G, G')$. Let $e$ be in the maximal atlas of $M$ for $G$ with $x \in e.\mathrm{source}$, and $f$ in the maximal atlas of $M'$ for $G'$ with $g(x) \in f.\mathrm{source}$. Then $g$ has the lifted property within $s$ at $x$ if and only if $g$ is continuous within $s$ at $x$ and $P(f \circ g \circ e^{-1}, (e^{-1})^{-1}(s), e(x))$.

*Proof.* Assume that $g$ is continuous within $s$ at $x$. Write $\varphi = \varphi_x$, $\varphi' = \varphi'_{g(x)}$. The proof changes the target chart, then the source chart.

Target. Let $c$ be one of $\varphi, e$, and put $k = g \circ c^{-1}$, $t = (c^{-1})^{-1}(s)$ and $y = c(x)$. Since $c^{-1}$ is continuous at $y$ and maps $t$ into $s$, $k$ is continuous within $t$ at $y$, so there is an open $u \ni y$ with $k(t \cap u) \subseteq O = \varphi'.\mathrm{source} \cap f.\mathrm{source}$. By locality, $P(h, t, y) \Leftrightarrow P(h, t \cap u, y)$ for every $h$. The element $d = \varphi'^{-1} \gg f$ and its inverse $f^{-1} \gg \varphi'$ are in $G'$ by the definition of the maximal atlas, since $\varphi'$ is in the atlas. For $z \in t \cap u$, $\varphi'(k(z)) \in \varphi'.\mathrm{target}$ and $\varphi'^{-1}(\varphi'(k(z))) = k(z) \in f.\mathrm{source}$, so $\varphi' \circ k$ maps $t \cap u$ into $d.\mathrm{source}$., and $y$ into it. Left invariance gives $P(d \circ \varphi' \circ k, t \cap u, y)$ from $P(\varphi' \circ k, t \cap u, y)$, and since $d \circ \varphi' \circ k = f \circ k$ on $t \cap u$ and at $y$, congruence gives $P(f \circ k, t \cap u, y)$. The converse is the same with $d^{-1}$ in place of $d$: $f \circ k$ maps $t \cap u$ into $d^{-1}.\mathrm{source} = f.\mathrm{target} \cap (f^{-1})^{-1}(\varphi'.\mathrm{source})$, and $d^{-1} \circ f \circ k = \varphi' \circ k$ there. So $P(\varphi' \circ g \circ c^{-1}, t, y) \Leftrightarrow P(f \circ g \circ c^{-1}, t, y)$.

Source. Let $h = f \circ g$. The elements $a = e^{-1} \gg \varphi$ and $a^{-1} = \varphi^{-1} \gg e$ are in $G$ by the definition of the maximal atlas, and $e(x) \in a.\mathrm{source}$. Right invariance applied to $P(h \circ e^{-1}, (e^{-1})^{-1}(s), e(x))$ gives $P(h \circ e^{-1} \circ a^{-1}, (a^{-1})^{-1}((e^{-1})^{-1}(s)), a(e(x)))$. Here $a(e(x)) = \varphi(x)$, and $a^{-1} = e \circ \varphi^{-1}$ on $a.\mathrm{target}$. On the open set $w = \varphi.\mathrm{target} \cap (\varphi^{-1})^{-1}(e.\mathrm{source}) \ni \varphi(x)$, $e^{-1}(e(\varphi^{-1}(z))) = \varphi^{-1}(z)$, so on $w$ the map is $h \circ \varphi^{-1}$ and the set is $(\varphi^{-1})^{-1}(s)$. The lemma on germs gives $P(h \circ \varphi^{-1}, (\varphi^{-1})^{-1}(s), \varphi(x))$. The converse applies right invariance with $a^{-1}$ in the same way.

The two steps give $P(\varphi' \circ g \circ \varphi^{-1}, \ldots, \varphi(x)) \Leftrightarrow P(f \circ g \circ \varphi^{-1}, \ldots, \varphi(x)) \Leftrightarrow P(f \circ g \circ e^{-1}, \ldots, e(x))$. If $g$ is not continuous within $s$ at $x$, both sides are false. $\square$

::: mathlib
`StructureGroupoid.LocalInvariantProp.liftPropWithinAt_indep_chart` · `Mathlib.Geometry.Manifold.LocalInvariantProperties`

The theorem has the hypotheses `e ∈ G.maximalAtlas M`, `x ∈ e.source`, `f ∈ G'.maximalAtlas M'` and `g x ∈ f.source`, and the conclusion `LiftPropWithinAt P g s x ↔ ContinuousWithinAt g s x ∧ P (f ∘ g ∘ e.symm) (e.symm ⁻¹' s) (e x)`. The versions `_source` and `_target` change one chart, and `liftProp_of_locally_liftPropOn` says that a property that holds on an open neighbourhood of each point holds everywhere. No `HasGroupoid` hypothesis appears: the proof uses only the definition of the maximal atlas.

<?decl StructureGroupoid.LocalInvariantProp.liftPropWithinAt_indep_chart?>
<?decl StructureGroupoid.compatible_of_mem_maximalAtlas?>
<?decl StructureGroupoid.maximalAtlas?>
:::

### Examples

**Example (The cube chart).** Let $c : \mathbb{R} \to \mathbb{R}$, $c(t) = t^3$. The atlas $\{c\}$ makes $\mathbb{R}$ a charted space $\mathbb{R}_c$ with the groupoid of $C^1$ maps of Chapter 2, since its only change of charts is the identity. The change of charts $\mathrm{id} \circ c^{-1} = t \mapsto t^{1/3}$ is not differentiable at $0$, so $c$ is not in the maximal atlas of $\mathbb{R}$ for the $C^1$ groupoid. The two structures are still isomorphic (Chapter 3, Section 3).

**Example (Open subsets).** If $M$ has the groupoid $G$ and $G$ is closed under restriction, every open subset $U$ has the groupoid $G$. Its changes of charts are restrictions of those of $M$. This is `TopologicalSpace.Opens.instHasGroupoid`, over the charted space `TopologicalSpace.Opens.instChartedSpace`.

**Example (Conformal maps).** On a real normed space $X$, the property "$f$ is conformal at each point of $u$" is a pregroupoid. The chain rule gives the composition axiom, and the others are local. Its groupoid is `conformalGroupoid`.

::: mathlib
`Structomorph` · `Mathlib.Geometry.Manifold.HasGroupoid`

`Structomorph G M M'` is a homeomorphism `h` with `c.symm ≫ₕ h ≫ₕ c' ∈ G` for all charts `c`, `c'` of the atlases.

<?decl Structomorph?>
<?decl TopologicalSpace.Opens.instHasGroupoid?>
<?decl conformalGroupoid?>
:::

### The library around it

Chapter 2 defines the groupoid `contDiffGroupoid n I`, and `IsManifold I n M` extends `HasGroupoid M (contDiffGroupoid n I)`. Chapter 3 defines `ContMDiffWithinAt` as a `LiftPropWithinAt`. The lemma `StructureGroupoid.HasGroupoid.comp` treats a model $H_2$ that is itself a charted space over $H_1$ with a groupoid $G_1$: if the members of $G_2$ are local structomorphisms for $G_1$, a space with $G_2$ over $H_2$ has $G_1$ over $H_1$.

Common errors of a learner:

- Expecting `HasGroupoid M G` to change the atlas. It is a condition on the given atlas.
- Using `G.compatible` for charts in the maximal atlas. It is for the atlas. Use `compatible_of_mem_maximalAtlas`.
- Forgetting `ClosedUnderRestriction G` when passing to open subsets. The instance on `TopologicalSpace.Opens` needs it.

### Exercises

1. (A) Show that the intersection of two structure groupoids is a structure groupoid.
2. (B) Prove that the groupoid of a pregroupoid is a structure groupoid. Hint: the target of $e \gg e'$ is $e'.\mathrm{target} \cap (e'^{-1})^{-1}(e.\mathrm{target})$, and for locality of $e^{-1}$ use the open sets $e.\mathrm{target} \cap (e^{-1})^{-1}(s)$.
3. (A) Show that the cube chart $c$ is in the maximal atlas of $\mathbb{R}$ for the continuous groupoid, and not in the maximal atlas for the $C^1$ groupoid.
4. (B) Prove that a groupoid is closed under restriction if and only if it contains the restriction of the identity to each open set.
5. (B) Let $P(f, s, x)$ be "$f$ is continuous within $s$ at $x$". Show that $P$ is local invariant for the continuous groupoids, and that its lift is continuity within $s$ at $x$.
6. (C) Let $G$ be closed under restriction. Show that the property "there is $e \in G$ with $x \in e.\mathrm{source}$ and $f = e$ on $s \cap e.\mathrm{source}$" is local invariant for $(G, G)$. Hint: use $e'^{-1} \gg e$ and $e \gg e'$.

### Notes and history

Pseudogroups of transformations go back to Lie and to Élie Cartan. Veblen and Whitehead (1932) and later Ehresmann used them to define the many kinds of manifolds in one framework. A structure groupoid is a pseudogroup in that literature. The term "local invariant property" is a choice of Mathlib.

### Reference

<?reference?>
