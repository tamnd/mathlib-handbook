---
title: Charted spaces
kind: theory
modules:
  - Mathlib.Geometry.Manifold.ChartedSpace
explains:
  E3: [ChartedSpace, chartAt, atlas]
  E2: [mem_chart_source, chart_mem_atlas, chart_source_mem_nhds, chartedSpaceSelf, chartAt_self_eq, ModelProd, prodChartedSpace, prodChartedSpace_chartAt, piChartedSpace, ChartedSpace.comp, ChartedSpace.locallyCompactSpace, ChartedSpace.t1Space, ChartedSpace.secondCountable_of_countable_cover, ChartedSpaceCore, ChartedSpaceCore.toChartedSpace]
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

## Charted spaces

### Overview

A chart identifies an open part of a space $M$ with an open part of a model space $H$, and a charted space has enough charts to cover it. This section defines partial homeomorphisms and charted spaces, proves that local properties of $H$ pass to $M$, and gives the first constructions: the model space, products, and a topology built from charts. In Mathlib the model $H$ is any topological space, and the charts need not be compatible. Compatibility comes in Section 2.

### Definitions

Volume 13 does not treat partial homeomorphisms, so the definition comes first.

**Definition (Partial homeomorphism).** Let $X$ and $Y$ be topological spaces. A *partial homeomorphism* $e$ from $X$ to $Y$ is a pair of maps $e : X \to Y$ and $e^{-1} : Y \to X$, with an open set $e.\mathrm{source} \subseteq X$ and an open set $e.\mathrm{target} \subseteq Y$, such that:

1. $e$ maps the source into the target, and $e^{-1}$ maps the target into the source;
2. $e^{-1}(e(x)) = x$ for $x$ in the source, and $e(e^{-1}(y)) = y$ for $y$ in the target;
3. $e$ is continuous on the source, and $e^{-1}$ is continuous on the target.

So $e$ restricts to a homeomorphism from the source onto the target. The maps are total functions, and their values outside the source and the target carry no meaning. The *inverse* $e^{-1}$ exchanges the roles. The *composition* $e \gg e'$ is $e' \circ e$ on the open source $e.\mathrm{source} \cap e^{-1}(e'.\mathrm{source})$. The *restriction* of $e$ to an open set $s$ has the source $e.\mathrm{source} \cap s$.

::: mathlib
`OpenPartialHomeomorph` · `Mathlib.Topology.OpenPartialHomeomorph.Defs`

The structure extends `PartialEquiv X Y`, which holds the maps, the source and the target with the conditions 1 and 2, and adds the openness and continuity fields. The inverse is `e.symm`, the composition is `e.trans e'` with the notation `e ≫ₕ e'`, and the restriction is `e.restr s`.

<?decl OpenPartialHomeomorph?>
<?decl OpenPartialHomeomorph.trans?>
:::

**Definition (Charted space).** Let $H$ be a topological space. A *charted space* modelled on $H$ is a topological space $M$ with a set $\mathcal{A}$ of partial homeomorphisms from $M$ to $H$, the *atlas*, and a map $x \mapsto \varphi_x$ from $M$ to $\mathcal{A}$, the *preferred chart*, such that $x \in \varphi_x.\mathrm{source}$ for every $x$.

The definition asks nothing on the changes of charts $\varphi^{-1} \gg \psi$. It does not ask that $M$ be Hausdorff or second countable.

::: mathlib
`ChartedSpace` · `Mathlib.Geometry.Manifold.ChartedSpace`

`ChartedSpace H M` is a class with the fields `atlas : Set (OpenPartialHomeomorph M H)`, `chartAt : M → OpenPartialHomeomorph M H`, `mem_chart_source : ∀ x, x ∈ (chartAt x).source` and `chart_mem_atlas : ∀ x, chartAt x ∈ atlas`. The model `H` is explicit in `atlas H M` and `chartAt H x`, because one type can be a charted space over several models. The class is data: instances with different atlases are different. By `chart_source_mem_nhds`, the source of `chartAt H x` is a neighbourhood of `x`.

<?decl ChartedSpace?>
<?decl chartAt?>
<?decl atlas?>
<?decl chart_source_mem_nhds?>
:::

**Definition (Model product).** For model spaces $H$ and $H'$, the model of a product of charted spaces is $H \times H'$, and the chart at $(x, y)$ is the product $\varphi_x \times \psi_y$.

::: mathlib
`ModelProd` · `Mathlib.Geometry.Manifold.ChartedSpace`

`ModelProd H H'` is a definition equal to `H × H'`. The instance `prodChartedSpace` lives on `ChartedSpace (ModelProd H H') (M × M')`, and `prodChartedSpace_chartAt` gives its chart. The new name avoids a conflict: over itself, `H × H'` has the instance `chartedSpaceSelf` with the chart `id`, and the product instance would have the chart `id × id`. The two are equal (`chartedSpaceSelf_prod`) but not equal by definition. For finite families, `piChartedSpace` uses `ModelPi H`.

<?decl ModelProd?>
<?decl prodChartedSpace?>
<?decl prodChartedSpace_chartAt?>
<?decl piChartedSpace?>
:::

### Theorems and proofs

**Lemma (Charts transport open and compact sets).** Let $e$ be a partial homeomorphism from $X$ to $Y$. If $V \subseteq e.\mathrm{source}$ is open in $X$, then $e(V)$ is open in $Y$. If $K \subseteq e.\mathrm{target}$ is compact, then $e^{-1}(K)$ is compact. The sets $e.\mathrm{source} \cap e^{-1}(W)$, for $W$ open in $Y$, are open in $X$.

*Proof.* Condition 2 gives $e(V) = e.\mathrm{target} \cap (e^{-1})^{-1}(V)$, which is open since $e^{-1}$ is continuous on the open target. The second claim holds since $e^{-1}$ is continuous on $K$, and the third since $e$ is continuous on the open source. $\square$

**Theorem (Local compactness passes to charted spaces).** Let $M$ be a charted space modelled on $H$. If $H$ is locally compact, then $M$ is locally compact.

*Proof.* Let $x \in M$ and let $U$ be a neighbourhood of $x$. Write $\varphi = \varphi_x$. Choose an open set $V$ with $x \in V \subseteq U \cap \varphi.\mathrm{source}$. By the lemma, $\varphi(V)$ is an open set of $H$ that contains $\varphi(x)$. Since $H$ is locally compact, there is a compact neighbourhood $K$ of $\varphi(x)$ with $K \subseteq \varphi(V)$. Put $L = \varphi^{-1}(K)$. By the lemma, $L$ is compact. Since $K \subseteq \varphi(V)$ and $\varphi^{-1} \circ \varphi = \mathrm{id}$ on $V$, $L \subseteq V \subseteq U$. The set $O = \varphi.\mathrm{source} \cap \varphi^{-1}(\mathrm{int}\, K)$ is open by the lemma, contains $x$, and lies in $L$, since $z = \varphi^{-1}(\varphi(z))$ for $z \in O$. So $L$ is a compact neighbourhood of $x$ in $U$. $\square$

The same proof gives local connectedness and local path connectedness. The separation axiom $T_1$ also passes, with a different proof.

**Theorem (The axiom $T_1$ passes to charted spaces).** Let $M$ be a charted space modelled on $H$. If $H$ is $T_1$, then $M$ is $T_1$.

*Proof.* Let $z \neq y$ in $M$. It is enough to find an open set that contains $z$ and not $y$. Write $\varphi = \varphi_z$. If $y \notin \varphi.\mathrm{source}$, the source is such a set. If $y \in \varphi.\mathrm{source}$, then $\varphi(y) \neq \varphi(z)$, since $\varphi$ is injective on its source. Since $H$ is $T_1$, the set $W = H \setminus \{\varphi(y)\}$ is open and contains $\varphi(z)$. The set $\varphi.\mathrm{source} \cap \varphi^{-1}(W)$ is open, contains $z$, and does not contain $y$. $\square$

**Example (The line with two origins).** The Hausdorff property does not pass. Let $M = (\mathbb{R} \times \{0, 1\}) / \sim$, where $(t, 0) \sim (t, 1)$ for $t \neq 0$, with the quotient topology. Let $0_0$ and $0_1$ be the classes of $(0, 0)$ and $(0, 1)$. For $i \in \{0, 1\}$, the map $\varphi_i : t \mapsto [(t, i)]$ is a homeomorphism from $\mathbb{R}$ onto the open set $M \setminus \{0_{1-i}\}$, and the two inverses make $M$ a charted space over $\mathbb{R}$. Each neighbourhood of $0_0$ contains $\varphi_0((-\varepsilon, \varepsilon))$ for some $\varepsilon > 0$, and each neighbourhood of $0_1$ contains $\varphi_1((-\varepsilon, \varepsilon))$. These two sets meet in $\varphi_0(\varepsilon / 2) = \varphi_1(\varepsilon / 2)$. So $0_0$ and $0_1$ have no disjoint neighbourhoods, and $M$ is not Hausdorff. The change of charts is the identity of $\mathbb{R} \setminus \{0\}$, so $M$ is even a smooth manifold in the sense of Chapter 2.

**Theorem (Products of charted spaces).** Let $M$ and $M'$ be charted spaces modelled on $H$ and $H'$. The products $e \times e'$ of charts, with the preferred charts $\varphi_x \times \psi_y$, make $M \times M'$ a charted space modelled on $H \times H'$.

*Proof.* The product $e \times e'$ has the open source $e.\mathrm{source} \times e'.\mathrm{source}$ and the open target $e.\mathrm{target} \times e'.\mathrm{target}$. The two maps are continuous on these sets since their components are, and conditions 1 and 2 hold in each component. Finally $(x, y) \in \varphi_x.\mathrm{source} \times \psi_y.\mathrm{source}$. $\square$

**Theorem (Topology from charts).** Let $M$ be a set without topology, and let $\mathcal{A}$ be a set of partial bijections $e$ from $M$ to $H$, with a chart $\varphi_x \in \mathcal{A}$ whose source contains $x$ for each $x$. Assume that for all $e, e' \in \mathcal{A}$ the set $(e^{-1} \gg e').\mathrm{source} = e.\mathrm{target} \cap (e^{-1})^{-1}(e'.\mathrm{source})$ is open in $H$, and that $e' \circ e^{-1}$ is continuous on it. Give $M$ the topology generated by the sets $e.\mathrm{source} \cap e^{-1}(W)$, for $e \in \mathcal{A}$ and $W$ open in $H$. Then each $e \in \mathcal{A}$ is a partial homeomorphism, and $M$ is a charted space.

*Proof.* Fix $e \in \mathcal{A}$. With $W = H$, the source of $e$ is open. With $e' = e$, the hypothesis says that $e.\mathrm{target} \cap (e^{-1})^{-1}(e.\mathrm{source}) = e.\mathrm{target}$ is open. The map $e$ is continuous on its source, since the sets $e.\mathrm{source} \cap e^{-1}(W)$ are generating sets. For the continuity of $e^{-1}$ on the target it is enough to check the generating sets. Let $e' \in \mathcal{A}$ and $W$ open. For $y \in e.\mathrm{target}$, $e^{-1}(y) \in e'.\mathrm{source} \cap e'^{-1}(W)$ holds if and only if $y$ is in the source of $e^{-1} \gg e'$ and $(e' \circ e^{-1})(y) \in W$. By the hypotheses this set is open in the open set $(e^{-1} \gg e').\mathrm{source}$, so it is open in $H$. $\square$

::: mathlib
`ChartedSpaceCore` · `Mathlib.Geometry.Manifold.ChartedSpace`

The theorem above is `ChartedSpaceCore H M`: a structure with `atlas : Set (PartialEquiv M H)`, `chartAt`, `mem_chart_source`, `chart_mem_atlas`, and the two conditions `open_source` and `continuousOn_toFun` on `e.symm.trans e'`. `ChartedSpaceCore.toChartedSpace` gives the charted space. It is a definition, not an instance, since an instance would put a second topology on types that have one.

<?decl ChartedSpaceCore?>
<?decl ChartedSpaceCore.toChartedSpace?>
:::

### Examples

**Example (The model space).** Every topological space $H$ is a charted space over itself, with the atlas $\{\mathrm{id}_H\}$ and the chart $\mathrm{id}_H$ at each point. In Mathlib this is the instance `chartedSpaceSelf`, with `chartAt_self_eq : chartAt H x = OpenPartialHomeomorph.refl H`.

**Example (The circle).** Let $S^1 = \{(u, v) \in \mathbb{R}^2 : u^2 + v^2 = 1\}$, with $N = (0, 1)$ and $S = (0, -1)$. The stereographic projection from $N$ is $\sigma_N(u, v) = u / (1 - v)$, a homeomorphism from $S^1 \setminus \{N\}$ onto $\mathbb{R}$. Its inverse is $t \mapsto (2t, t^2 - 1) / (t^2 + 1)$. The projection from $S$ is $\sigma_S(u, v) = u / (1 + v)$. On $S^1 \setminus \{N, S\}$, $\sigma_N(u, v)\, \sigma_S(u, v) = u^2 / (1 - v^2) = 1$. So the change of charts is $t \mapsto 1/t$ on $\mathbb{R} \setminus \{0\}$. The two charts make $S^1$ a charted space over $\mathbb{R}$, with the preferred chart $\sigma_N$ at $(u, v)$ when $v \le 0$ and $\sigma_S$ when $v > 0$.

**Example (Change of model).** If $M$ is a charted space over $H'$ and $H'$ over $H$, then $M$ is a charted space over $H$, with the chart $\varphi_x \gg \chi_{\varphi_x(x)}$ at $x$, where $\chi$ is the preferred chart of $H'$. This is the definition `ChartedSpace.comp H H' M`.

### The library around it

The module has more transfer results: `ChartedSpace.locallyConnectedSpace`, `ChartedSpace.discreteTopology`, and `ChartedSpace.secondCountable_of_countable_cover`. The last says that $M$ is second countable if $H$ is and countably many chart sources cover $M$. A homeomorphism pushes a charted space forward (`Homeomorph.chartedSpace`), and a disjoint union over one model has the instance `ChartedSpace.sum`.

::: mathlib
`ChartedSpace.t1Space` · `Mathlib.Geometry.Manifold.ChartedSpace`

The two transfer theorems are `ChartedSpace.locallyCompactSpace H M`, under `[LocallyCompactSpace H]`, and `ChartedSpace.t1Space H M`, under `[T1Space H]`. The docstring of the second notes that the analogue for `T2Space` fails.

<?decl ChartedSpace.locallyCompactSpace?>
<?decl ChartedSpace.t1Space?>
<?decl ChartedSpace.secondCountable_of_countable_cover?>
<?decl ChartedSpace.comp?>
:::

Common errors of a learner:

- Writing `chartAt x` without the model. The model is explicit: `chartAt H x`.
- Assuming that a charted space is Hausdorff. A theorem that needs it must ask for `[T2Space M]`.
- Assuming that the charts of the atlas are compatible. `ChartedSpace` gives no condition on changes of charts. The condition is the class `HasGroupoid` of Section 2.
- Writing the product model as `H × H'`. The instance on `M × M'` uses `ModelProd H H'`, and a statement with `H × H'` does not find it.

### Exercises

1. (A) Show that the composition $e \gg e'$ of two partial homeomorphisms has an open source and an open target, and compute the target.
2. (A) Show that the circle with the two charts $\sigma_N$ and $\sigma_S$ is a charted space, and check the formula for $\sigma_N^{-1}$. Hint: solve $t = u / (1 - v)$ with $u^2 + v^2 = 1$.
3. (A) Let $M$ be a charted space over $H$. Show that the sources of the charts $\varphi_x$ form an open cover of $M$. Show that if $H$ is discrete, then $M$ is discrete.
4. (B) Show that $\mathbb{R}$, with the single chart $x \mapsto x^3$, is a charted space over $\mathbb{R}$, different from `chartedSpaceSelf ℝ`.
5. (B) Let $U \subseteq M$ be open. Write the charts of the charted space on $U$ and prove the conditions.
6. (B) Let $M$ be the line with two origins. Show that $M$ is $T_1$, locally compact and second countable, and that the classes of $(1/n, 0)$ have two limits.
7. (C) Show that the projective line $\mathbb{RP}^1 = (\mathbb{R}^2 \setminus \{0\}) / \mathbb{R}^\times$ is a charted space over $\mathbb{R}$ with the two charts $[x : y] \mapsto y/x$ and $[x : y] \mapsto x/y$, built with the theorem on topology from charts. Show that this topology is the quotient topology. Hint: the change of charts is $t \mapsto 1/t$.

### Notes and history

Charts and atlases in the modern sense come from the work of Hermann Weyl on Riemann surfaces (1913) and of Veblen and Whitehead and of Whitney in the 1930s. Partial homeomorphisms with total functions and explicit sources avoid subtypes, so that charts compose as ordinary functions. Many texts ask that the atlas be maximal, or that $M$ be Hausdorff and second countable. Mathlib asks for none of these and adds them as separate hypotheses.

### Reference

<?reference?>
