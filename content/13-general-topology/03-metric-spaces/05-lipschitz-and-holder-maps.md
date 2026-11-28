---
title: Lipschitz and Hölder maps
kind: api
modules:
  - Mathlib.Topology.EMetricSpace.Lipschitz
  - Mathlib.Topology.MetricSpace.Lipschitz
  - Mathlib.Topology.MetricSpace.Antilipschitz
  - Mathlib.Topology.MetricSpace.Bilipschitz
  - Mathlib.Topology.MetricSpace.Holder
  - Mathlib.Topology.MetricSpace.HolderNorm
explains:
  E2: [LipschitzWith.comp, LipschitzWith.uniformContinuous, LipschitzWith.edist_iterate_succ_le_geometric, LipschitzOnWith.extend_real, AntilipschitzWith.injective, AntilipschitzWith.to_rightInverse, uniformity_eq_of_bilipschitz, holderWith_one, HolderWith.uniformContinuous, HolderWith.interpolate]
  E1: auto
families: []
requires: [V04, V13.C01, V13.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Lipschitz and Hölder maps

### Overview

A map $f$ between two metric spaces is $K$-Lipschitz if $d(f(x), f(y)) \le K\, d(x, y)$ for all $x$ and $y$. It is $K$-antilipschitz if $d(x, y) \le K\, d(f(x), f(y))$, and it is Hölder of order $r$ with constant $C$ if $d(f(x), f(y)) \le C\, d(x, y)^r$. These conditions are quantitative forms of continuity and of injectivity. They control the size of images, they give uniform continuity, and they are the hypotheses of the contraction mapping theorem and of the theorem of Picard and Lindelöf.

In Mathlib all three definitions use the extended distance $\mathrm{edist}$ of Section 4 and a constant in `NNReal`. So they apply to pseudo extended metric spaces, and the same lemma covers metric spaces and extended metric spaces. This section describes the definitions, the algebra of the constants, the metric forms of the conditions, the extension theorem for real functions, the antilipschitz and bilipschitz maps, the Hölder maps and the Hölder norm.

### The library around it

#### The Lipschitz conditions

The module `Mathlib.Topology.EMetricSpace.Lipschitz` defines four predicates.

| Lean name | Condition |
|---|---|
| `LipschitzWith K f` | $\forall x\, y,\ \mathrm{edist}(f x, f y) \le K \cdot \mathrm{edist}(x, y)$ |
| `LipschitzOnWith K f s` | the same for $x, y \in s$ |
| `LocallyLipschitz f` | each point has a neighbourhood $t$ and a $K$ with `LipschitzOnWith K f t` |
| `LocallyLipschitzOn s f` | the same for the points of $s$, with neighbourhoods inside $s$ |

The constant is an element of `NNReal`, cast to $[0, \infty]$. The product $K \cdot \infty$ is $\infty$ for $K > 0$ and $0$ for $K = 0$, so points at infinite distance give no condition when $K > 0$. The lemma `LipschitzWith.edist_le_mul` reads the definition, and `LipschitzWith.of_edist_le` gives the case $K = 1$.

The constants follow the rules of composition. The lemma `LipschitzWith.comp` states that if $g$ is $K_g$-Lipschitz and $f$ is $K_f$-Lipschitz, then $g \circ f$ is $K_g K_f$-Lipschitz. Proof: $\mathrm{edist}(g(f x), g(f y)) \le K_g\, \mathrm{edist}(f x, f y) \le K_g K_f\, \mathrm{edist}(x, y)$, where the second step multiplies the bound for $f$ by $K_g$. The other basic rules are `LipschitzWith.id` (constant $1$), `LipschitzWith.const` (constant $0$), `LipschitzWith.iterate` (constant $K^n$ for $f^{[n]}$), `LipschitzWith.weaken` (a larger constant), `LipschitzWith.prodMk` (constant $\max(K_f, K_g)$ into the product with the max distance), and `LipschitzWith.uncurry`: if $f(\cdot, b)$ is $K_\alpha$-Lipschitz for each $b$ and $f(a, \cdot)$ is $K_\beta$-Lipschitz for each $a$, then the map on the product is $(K_\alpha + K_\beta)$-Lipschitz. The lemma `LipschitzWith.zero_iff` says that a $0$-Lipschitz map into an extended metric space is constant, since $0 \cdot \infty = 0$ in $[0, \infty]$. The forms for sets have the same names in the namespace LipschitzOnWith, with `LipschitzOnWith.mono` for a smaller set.

The topological consequences come next. The lemma `LipschitzWith.uniformContinuous` states that a Lipschitz map is uniformly continuous. Proof: for $\varepsilon > 0$, take $\delta = \varepsilon / K$ (or any $\delta$ if $K = 0$); then $\mathrm{edist}(x, y) < \delta$ gives $\mathrm{edist}(f x, f y) \le K \delta \le \varepsilon$, with a strict inequality from `LipschitzWith.edist_lt_of_edist_lt_div`. Then `LipschitzWith.continuous` follows, and `LipschitzWith.locallyLipschitz` and `LocallyLipschitz.continuous` give the local forms. Images of balls satisfy `LipschitzWith.mapsTo_eball`: for $K \ne 0$ the map sends $B(x, r)$ into $B(f x, K r)$. Images of sets satisfy `LipschitzWith.ediam_image_le`: $\mathrm{ediam}(f(s)) \le K\, \mathrm{ediam}(s)$.

The lemma `LipschitzWith.edist_iterate_succ_le_geometric` is the first step of the contraction mapping theorem of Chapter 9, Section 8:
$$\mathrm{edist}(f^{[n]} x, f^{[n+1]} x) \le \mathrm{edist}(x, f x) \cdot K^n.$$
Proof: the two points are the images of $x$ and $f x$ under $f^{[n]}$, and `LipschitzWith.iterate` gives the constant $K^n$. For $K < 1$ the sum of these distances is finite, so the orbit is a Cauchy sequence.

Two lemmas prove joint continuity from separate conditions. `continuous_prod_of_continuous_lipschitzWith` states: if $f(a, \cdot)$ is continuous for each $a$ and $f(\cdot, b)$ is $K$-Lipschitz for each $b$, with one $K$ for all $b$, then $f$ is continuous on the product. The variant `continuous_prod_of_dense_continuous_lipschitzWith` asks for continuity in the second variable only on a dense set of $a$. Monoids of endomorphisms have `LipschitzWith.mul_end` and `LipschitzWith.pow_end`.

#### Metric forms and the real line

The module `Mathlib.Topology.MetricSpace.Lipschitz` translates the conditions into the real distance. The lemma `lipschitzWith_iff_dist_le_mul` says that $f$ is $K$-Lipschitz between pseudometric spaces if and only if $d(f x, f y) \le K\, d(x, y)$ for all $x, y$. Its halves are `LipschitzWith.of_dist_le_mul` and `LipschitzWith.dist_le_mul`. The lemma `LipschitzWith.of_le_add_mul` is the form for real functions: $f(x) \le f(y) + K\, d(x, y)$ for all $x, y$ is enough, because the roles of $x$ and $y$ swap.

The distance functions are $1$-Lipschitz: `LipschitzWith.dist_left` and `LipschitzWith.dist_right` (from the triangle inequality), and `LipschitzWith.dist` on the product. The lattice operations on $\mathbb{R}$ are also $1$-Lipschitz, with `lipschitzWith_max`, `lipschitzWith_min` and the forms `LipschitzWith.max` and `LipschitzWith.min` for pairs of maps. The lemma `Set.separatesPoints_lipschitzWith_one` says that the $1$-Lipschitz real functions separate the points of a metric space: the map $y \mapsto d(x, y)$ takes different values at $x$ and at a point $y \ne x$.

The lemma `LipschitzOnWith.extend_real` is the extension theorem for real functions: a real function that is $K$-Lipschitz on a set $s$ of a pseudometric space has a $K$-Lipschitz extension to the whole space. Proof sketch: for $s$ nonempty, put $g(y) = \inf_{x \in s} (f(x) + K\, d(y, x))$. Each map $y \mapsto f(x) + K\, d(y, x)$ is $K$-Lipschitz, and an infimum of $K$-Lipschitz real functions is $K$-Lipschitz when it is finite. The infimum is finite since $f(x) + K\, d(y, x) \ge f(x_0) - K\, d(x, x_0) + K\, d(y, x) \ge f(x_0) - K\, d(y, x_0)$ for a fixed $x_0 \in s$. For $y \in s$ the Lipschitz bound gives $f(x) + K\, d(y, x) \ge f(y)$, and $x = y$ gives equality, so $g = f$ on $s$. The lemma `LipschitzOnWith.extend_pi` applies this to each coordinate for maps into $\iota \to \mathbb{R}$ with $\iota$ finite; the sup distance keeps the constant $K$.

On bounded sets, `LipschitzWith.diam_image_le` bounds the real diameter, `LipschitzWith.isBounded_image` keeps boundedness, and `LipschitzWith.mapsTo_ball` maps balls into balls. The lemma `LipschitzWith.properSpace` says that if $f : X \to Y$ is a proper map and $Y$ is a proper space, a Lipschitz $f$ forces $X$ to be proper. The lemma `LipschitzWith.toLocallyBoundedMap` turns a Lipschitz map into a map of bornologies.

#### Antilipschitz and bilipschitz maps

The module `Mathlib.Topology.MetricSpace.Antilipschitz` defines `AntilipschitzWith K f`: $\mathrm{edist}(x, y) \le K\, \mathrm{edist}(f x, f y)$ for all $x, y$. The lemma `AntilipschitzWith.injective` states that an antilipschitz map on an extended metric space is injective. Proof: if $f x = f y$, then $\mathrm{edist}(x, y) \le K \cdot 0 = 0$, so $x = y$. On a pseudo extended metric space the conclusion is only $\mathrm{edist}(x, y) = 0$.

The lemma `AntilipschitzWith.to_rightInverse` states that if $f$ is $K$-antilipschitz and $g$ is a right inverse of $f$, then $g$ is $K$-Lipschitz. Proof: for $x, y$ in the target, $f(g x) = x$ and $f(g y) = y$, so the antilipschitz bound at $g x$ and $g y$ reads $\mathrm{edist}(g x, g y) \le K\, \mathrm{edist}(x, y)$. The converse `LipschitzWith.to_rightInverse` says that a right inverse of a Lipschitz map is antilipschitz.

The structural lemmas need a uniformly continuous $f$. Then `AntilipschitzWith.isUniformEmbedding` makes $f$ a uniform embedding of an extended metric space; with a complete source, `AntilipschitzWith.isComplete_range` makes the range complete and `AntilipschitzWith.isClosedEmbedding` makes $f$ a closed embedding. Other lemmas: `AntilipschitzWith.comp` (if $f$ is $K_f$-antilipschitz and $g$ is $K_g$-antilipschitz, then $g \circ f$ is $K_f K_g$-antilipschitz), `AntilipschitzWith.le_mul_ediam_image`, `AntilipschitzWith.isBounded_preimage`, `AntilipschitzWith.tendsto_cobounded`, and `AntilipschitzWith.properSpace`, which sends properness from the source to the target of a continuous antilipschitz surjection.

The module `Mathlib.Topology.MetricSpace.Bilipschitz` treats a map $f$ that is both $K_1$-antilipschitz and $K_2$-Lipschitz. Such a map is used to compare two metrics on one type. The lemma `uniformity_eq_of_bilipschitz` states that the uniformity of the source equals the uniformity induced by $f$ from the target. Proof: the Lipschitz bound gives that the induced uniformity is coarser, by `LipschitzWith.uniformContinuous`; the antilipschitz bound gives the other inclusion, by `AntilipschitzWith.comap_uniformity_le`. The same idea gives `isBounded_iff_of_bilipschitz` and `bornology_eq_of_bilipschitz` for the bornologies. These lemmas are the tools to replace a uniform structure by an equivalent one, for example on a product with the $\ell^1$ distance in place of the max distance.

#### Hölder maps

The module `Mathlib.Topology.MetricSpace.Holder` defines `HolderWith C r f`: $\mathrm{edist}(f x, f y) \le C \cdot \mathrm{edist}(x, y)^r$, with $C$ and $r$ in `NNReal`, and the form `HolderOnWith C r f s` for a set. The lemma `holderWith_one` states that `HolderWith C 1 f` holds if and only if `LipschitzWith C f` holds. Proof: $\mathrm{edist}(x, y)^1 = \mathrm{edist}(x, y)$, so the two conditions are the same. The case $r = 0$ is special, since $\mathrm{edist}^0 = 1$: then the condition says $\mathrm{edist}(f x, f y) \le C$, and `holderWith_zero_iff` treats $C = 0$.

The lemma `HolderWith.uniformContinuous` states that for $r > 0$ a Hölder map is uniformly continuous. Proof: for $\varepsilon > 0$, choose $\delta > 0$ with $C \delta^r < \varepsilon$, which is possible because $\delta^r \to 0$ as $\delta \to 0$ for $r > 0$; then $\mathrm{edist}(x, y) < \delta$ gives $\mathrm{edist}(f x, f y) \le C \delta^r < \varepsilon$. The hypothesis $0 < r$ is needed: a $0$-Hölder map is any map with bounded oscillation. Then `HolderWith.continuous` follows. Composition has `HolderWith.comp`: if $g$ is $(C_g, r_g)$-Hölder and $f$ is $(C_f, r_f)$-Hölder, then $g \circ f$ is Hölder with constant $C_g C_f^{r_g}$ and order $r_g r_f$. For diameters, `HolderWith.ediam_image_le` gives $\mathrm{ediam}(f(s)) \le C\, \mathrm{ediam}(s)^r$.

The lemma `HolderWith.interpolate` states: if $f$ is $(C_1, r)$-Hölder and $(C_2, s)$-Hölder and $t_1 + t_2 = 1$, then $f$ is Hölder with constant $C_1^{t_1} C_2^{t_2}$ and order $r t_1 + s t_2$. Proof: write $D = \mathrm{edist}(f x, f y)$ and $d = \mathrm{edist}(x, y)$. Then $D = D^{t_1} D^{t_2} \le (C_1 d^r)^{t_1} (C_2 d^s)^{t_2} = C_1^{t_1} C_2^{t_2} d^{r t_1 + s t_2}$. On a bounded space the order can also go down: `HolderWith.of_le` turns an $r$-Hölder map into an $s$-Hölder map for $s \le r$, with a constant that depends on the bound on the distances.

#### The Hölder norm

The module `Mathlib.Topology.MetricSpace.HolderNorm` defines `MemHolder r f` as the existence of some $C$ with `HolderWith C r f`, the extended Hölder norm `eHolderNorm r f`, which is the infimum of these $C$ in $[0, \infty]$, and the real form `nnHolderNorm r f`. The infimum is attained: `memHolder_iff_holderWith` states that $f$ is in the Hölder class if and only if `HolderWith (nnHolderNorm r f) r f` holds. The norm is $\infty$ exactly outside the class (`eHolderNorm_eq_top`), and it is $0$ exactly for the constant maps (`eHolderNorm_eq_zero`). For maps into a normed group, `eHolderNorm_add_le` is the triangle inequality of the norm, with the scalar forms `eHolderNorm_smul` and `MemHolder.smul`. Since constants have norm $0$, the Hölder norm is only a seminorm on the Hölder class.

#### Common errors

1. The constant of `LipschitzWith` is in `NNReal`, not in $\mathbb{R}$. A real constant needs a cast, and a proof often needs `NNReal.coe_le_coe` or a similar lemma to move between the two types.
2. `HolderWith.uniformContinuous` and `HolderWith.continuous` need $0 < r$. A proof that forgets this hypothesis fails, because a $0$-Hölder map need not be continuous.
3. `AntilipschitzWith.injective` needs an `EMetricSpace` on the source. On a pseudometric space the correct conclusion is a zero distance, not equality.

### Exercises

1. (A) Show that $x \mapsto \sqrt{x}$ on $[0, \infty)$ is Hölder of order $1/2$ with constant $1$ and is not Lipschitz.
2. (A) Use `LipschitzWith.comp` and `LipschitzWith.iterate` to show that a $K$-Lipschitz map $f$ with $K < 1$ has $f^{[n]}$ with constant $K^n$, and state the bound that `LipschitzWith.edist_iterate_succ_le_geometric` gives.
3. (B) Prove `LipschitzWith.dist_left`, and show that $y \mapsto \inf_{x \in s} d(x, y)$ is $1$-Lipschitz.
4. (B) Let $f$ be a $K$-Lipschitz map from a set $s$ of a metric space into $\mathbb{R}^n$. Explain why `LipschitzOnWith.extend_pi` gives a $K$-Lipschitz extension for the max distance on $\mathbb{R}^n$, and show that the same extension is $\sqrt{n} K$-Lipschitz for the Euclidean distance.
5. (B) Show that a bilipschitz bijection between metric spaces sends Cauchy sequences to Cauchy sequences in both directions, and relate this to `uniformity_eq_of_bilipschitz`.
6. (C) Show that a Hölder map $f : [0, 1] \to \mathbb{R}$ of order $r > 1$ is constant.

### Reference

<?reference?>
