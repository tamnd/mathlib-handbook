---
title: Homotopies and homotopy equivalence
kind: theory
modules:
  - Mathlib.Topology.Homotopy.Affine
  - Mathlib.Topology.Homotopy.Basic
  - Mathlib.Topology.Homotopy.Contractible
  - Mathlib.Topology.Homotopy.Equiv
  - Mathlib.Topology.Homotopy.HSpaces
  - Mathlib.Topology.Homotopy.LocallyContractible
  - Mathlib.Topology.Homotopy.Product
explains:
  E3: [ContinuousMap.Homotopy, ContinuousMap.Homotopic, ContinuousMap.HomotopyRel, ContinuousMap.HomotopyEquiv, ContinuousMap.Homotopy.affine, ContractibleSpace, ContinuousMap.Nullhomotopic, HSpace]
  E2: [ContinuousMap.Homotopy.refl, ContinuousMap.Homotopy.symm, ContinuousMap.Homotopy.trans, ContinuousMap.Homotopy.comp, ContinuousMap.HomotopyWith, ContinuousMap.HomotopicRel, ContinuousMap.Homotopy.evalAt_affine, ContinuousMap.HomotopyEquiv.refl, ContinuousMap.HomotopyEquiv.symm, ContinuousMap.HomotopyEquiv.trans, Homeomorph.toHomotopyEquiv, contractible_iff_id_nullhomotopic, id_nullhomotopic, ContractibleSpace.hequiv_unit, ContinuousMap.HomotopyEquiv.contractibleSpace, LocallyContractibleSpace, StronglyLocallyContractibleSpace, StronglyLocallyContractibleSpace.locallyContractible, IsTopologicalGroup.toHSpace, HSpace.prod, Path.instHSpace, Path.delayReflRight, ContinuousMap.Homotopy.prod, ContinuousMap.HomotopyRel.prod, Path.Homotopic.prod]
  E1: auto
families: []
requires: [V13.C01, V13.C06, V14.C01, V22.C06, V24.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Homotopies and homotopy equivalence

### Overview

Two continuous maps are homotopic when one map can be deformed into the other through a continuous family of maps. Homotopy is the basic relation of algebraic topology. The fundamental group, the homotopy groups and homology do not change when a map is replaced by a homotopic map. A space is then studied up to homotopy equivalence, which is weaker than homeomorphism. A disk and a point are homotopy equivalent, so they have the same invariants.

This section defines homotopies and the homotopy relation, homotopies relative to a subset, homotopy equivalences and contractible spaces. It constructs the straight-line homotopy in a convex set, and it treats products of homotopies, local contractibility and H-spaces. Throughout, $I$ denotes the unit interval $[0,1]$ and all maps are continuous.

### Definitions

**Definition (Homotopy).** Let $f_0, f_1 : X \to Y$ be continuous maps. A *homotopy* from $f_0$ to $f_1$ is a continuous map $F : I \times X \to Y$ with $F(0, x) = f_0(x)$ and $F(1, x) = f_1(x)$ for all $x \in X$. For each $t \in I$ the map $F_t = F(t, -)$ is continuous, and the family $(F_t)$ deforms $f_0$ into $f_1$. The maps $f_0$ and $f_1$ are *homotopic*, written $f_0 \simeq f_1$, when a homotopy from $f_0$ to $f_1$ exists.

The time coordinate comes first here, as in Mathlib. Many textbooks put it second.

**Definition (Homotopy relative to a set).** Let $S \subseteq X$. A homotopy $F$ from $f_0$ to $f_1$ is *relative to* $S$ when $F(t, x) = f_0(x)$ for all $t \in I$ and all $x \in S$. Then $f_0$ and $f_1$ agree on $S$, and the deformation does not move the points of $S$. More generally, a homotopy *with property* $P$ is a homotopy such that each map $F_t$ satisfies $P$.

**Definition (Homotopy equivalence).** A continuous map $f : X \to Y$ is a *homotopy equivalence* when a continuous map $g : Y \to X$ exists with $g \circ f \simeq \mathrm{id}_X$ and $f \circ g \simeq \mathrm{id}_Y$. The map $g$ is a *homotopy inverse* of $f$. The spaces $X$ and $Y$ are *homotopy equivalent*, written $X \simeq_h Y$, when a homotopy equivalence between them exists.

**Definition (Nullhomotopic map, contractible space).** A map $f : X \to Y$ is *nullhomotopic* when it is homotopic to a constant map. A space $X$ is *contractible* when it is homotopy equivalent to a one-point space.

**Definition (Local contractibility).** A space $X$ is *locally contractible* when, for each point $x$ and each neighbourhood $U$ of $x$, a neighbourhood $V \subseteq U$ of $x$ exists such that the inclusion $V \to U$ is nullhomotopic. The space is *strongly locally contractible* when each point has a basis of neighbourhoods that are contractible spaces.

**Definition (H-space).** An *H-space* is a space $X$ with a continuous multiplication $\mu : X \times X \to X$ and a point $e$ with $\mu(e, e) = e$, such that the maps $x \mapsto \mu(e, x)$ and $x \mapsto \mu(x, e)$ are homotopic to $\mathrm{id}_X$ relative to $\{e\}$. The multiplication need not be associative, and no inverse is required.

### Theorems and proofs

The proofs use the *pasting lemma*: if $X = A \cup B$ with $A$ and $B$ closed, and $h$ is continuous on $A$ and on $B$, then $h$ is continuous, because $h^{-1}(C) = (h|_A)^{-1}(C) \cup (h|_B)^{-1}(C)$ is closed for closed $C$.

**Theorem (Homotopy is an equivalence relation).** For spaces $X$ and $Y$, the relation $\simeq$ on continuous maps $X \to Y$ is reflexive, symmetric and transitive.

*Proof.* For reflexivity, the map $F(t, x) = f(x)$ is a homotopy from $f$ to $f$. For symmetry, let $F$ be a homotopy from $f_0$ to $f_1$. The map $\bar F(t, x) = F(1 - t, x)$ is continuous, as a composite of $F$ with the continuous map $(t, x) \mapsto (1 - t, x)$. It satisfies $\bar F(0, x) = f_1(x)$ and $\bar F(1, x) = f_0(x)$. For transitivity, let $F$ be a homotopy from $f_0$ to $f_1$ and $G$ a homotopy from $f_1$ to $f_2$. Define $H(t, x) = F(2t, x)$ for $t \le 1/2$ and $H(t, x) = G(2t - 1, x)$ for $t \ge 1/2$. At $t = 1/2$ both formulas give $F(1, x) = f_1(x) = G(0, x)$, so $H$ is well defined. The sets $[0, 1/2] \times X$ and $[1/2, 1] \times X$ are closed and cover $I \times X$, and $H$ is continuous on each of them. By the pasting lemma $H$ is continuous. It satisfies $H(0, x) = f_0(x)$ and $H(1, x) = f_2(x)$. $\square$

If $F$ and $G$ are both relative to $S$, then $\bar F$ and $H$ are also relative to $S$, by the same formulas. So homotopy relative to $S$ is also an equivalence relation.

**Proposition (Homotopy respects composition).** Let $f_0 \simeq f_1 : X \to Y$ and $g_0 \simeq g_1 : Y \to Z$. Then $g_0 \circ f_0 \simeq g_1 \circ f_1$.

*Proof.* Let $F$ and $G$ be the two homotopies. Define $H(t, x) = G(t, F(t, x))$. The map $H$ is the composite of $(t, x) \mapsto (t, F(t, x))$ with $G$, so it is continuous. At $t = 0$ it gives $g_0(f_0(x))$, and at $t = 1$ it gives $g_1(f_1(x))$. $\square$

**Theorem (Homotopy equivalence is an equivalence relation).** The relation $\simeq_h$ on topological spaces is reflexive, symmetric and transitive. Each homeomorphism is a homotopy equivalence.

*Proof.* A homeomorphism $f$ with inverse $g$ satisfies $g \circ f = \mathrm{id}$ and $f \circ g = \mathrm{id}$, and equal maps are homotopic by reflexivity. In particular $\mathrm{id}_X$ is a homotopy equivalence. Symmetry holds because the definition is symmetric in $f$ and $g$. For transitivity, let $f : X \to Y$ have homotopy inverse $g$, and let $f' : Y \to Z$ have homotopy inverse $g'$. Then
$$(g \circ g') \circ (f' \circ f) = g \circ (g' \circ f') \circ f \simeq g \circ \mathrm{id}_Y \circ f = g \circ f \simeq \mathrm{id}_X,$$
where the first step uses the proposition on composition with the constant homotopies of $g$ and $f$. The same computation in the other order gives $(f' \circ f) \circ (g \circ g') \simeq \mathrm{id}_Z$. $\square$

**Theorem (Straight-line homotopy).** Let $E$ be a real topological vector space, let $C \subseteq E$ be convex, and let $f, g : X \to C$ be continuous. Then $H(t, x) = (1 - t) f(x) + t\, g(x)$ is a homotopy from $f$ to $g$ with values in $C$. If $f$ and $g$ agree on $S \subseteq X$, then $H$ is relative to $S$.

*Proof.* Addition and scalar multiplication are continuous in $E$, so $H$ is continuous as a map into $E$. For each $(t, x)$ the point $H(t, x)$ lies on the segment from $f(x)$ to $g(x)$, and this segment lies in $C$ because $C$ is convex. A continuous map into $E$ with values in $C$ is continuous into $C$ with the subspace topology. The values at $t = 0$ and $t = 1$ are $f(x)$ and $g(x)$. If $f(x) = g(x)$, then $H(t, x) = f(x)$ for all $t$. $\square$

**Corollary (Convex sets are contractible).** A nonempty convex subset $C$ of a real topological vector space is contractible.

*Proof.* Choose $c \in C$. Let $p : C \to \{\ast\}$ be the unique map and $i : \{\ast\} \to C$ the map with value $c$. Then $p \circ i = \mathrm{id}$. The map $i \circ p$ is the constant map with value $c$, and the straight-line homotopy joins $\mathrm{id}_C$ to it inside $C$. So $p$ is a homotopy equivalence. $\square$

**Proposition (Contractibility through the identity).** A space $X$ is contractible if and only if $X$ is nonempty and $\mathrm{id}_X$ is nullhomotopic.

*Proof.* Suppose $p : X \to \{\ast\}$ and $i : \{\ast\} \to X$ are inverse homotopy equivalences. The point $c = i(\ast)$ shows that $X$ is nonempty, and $\mathrm{id}_X \simeq i \circ p$, which is the constant map with value $c$. Conversely, let $\mathrm{id}_X$ be homotopic to the constant map with value $c$. Define $i(\ast) = c$. Then $p \circ i = \mathrm{id}$ and $i \circ p$ is that constant map, so $i \circ p \simeq \mathrm{id}_X$. $\square$

**Proposition (Contractible spaces are path connected).** A contractible space is path connected.

*Proof.* Let $H$ be a homotopy from $\mathrm{id}_X$ to the constant map with value $c$. For $x \in X$ the map $t \mapsto H(t, x)$ is a continuous path from $x$ to $c$. Join $x$ to $y$ through $c$. $\square$

**Proposition (Strong local contractibility implies local contractibility).** A strongly locally contractible space is locally contractible.

*Proof.* Let $U$ be a neighbourhood of $x$. Choose a contractible neighbourhood $V \subseteq U$ of $x$ from the basis. The inclusion $j : V \to U$ equals $j \circ \mathrm{id}_V$. The map $\mathrm{id}_V$ is homotopic to a constant map $k$, and by composition $j \circ \mathrm{id}_V \simeq j \circ k$, which is constant. $\square$

The converse is false. The source file cites an example of Borsuk and Mazurkiewicz of a space that is locally contractible but not strongly locally contractible.

**Proposition (Products of homotopies).** Let $F$ be a homotopy from $f_0$ to $f_1 : X \to Y$ and $G$ a homotopy from $g_0$ to $g_1 : X \to Z$. Then $(t, x) \mapsto (F(t, x), G(t, x))$ is a homotopy from $(f_0, g_0)$ to $(f_1, g_1) : X \to Y \times Z$. A product of two contractible spaces is contractible.

*Proof.* A map into a product is continuous when both coordinates are continuous, and the end values are correct coordinate by coordinate. For the second claim, let $H$ and $K$ contract $\mathrm{id}_Y$ and $\mathrm{id}_Z$ to the constants $c$ and $d$. The map $(t, (y, z)) \mapsto (H(t, y), K(t, z))$ is continuous, as a pair of composites of $H$ and $K$ with projections. It joins $\mathrm{id}_{Y \times Z}$ to the constant map with value $(c, d)$. $\square$

**Theorem (Topological groups and loop spaces are H-spaces).** A topological group $G$ with $\mu(x, y) = xy$ and $e = 1$ is an H-space. For a point $x_0$ of a space $X$, the space $\Omega(X, x_0)$ of loops at $x_0$ with the compact-open topology is an H-space, with $\mu(\alpha, \beta) = \alpha \cdot \beta$, the loop that runs $\alpha$ and then $\beta$, and with $e$ the constant loop.

*Proof.* For a group, $x \mapsto 1 \cdot x$ and $x \mapsto x \cdot 1$ are equal to $\mathrm{id}_G$, and the constant homotopy is relative to $\{1\}$. For the loop space, $\mu$ is continuous because $I$ is compact Hausdorff, so that evaluation and the pasting of two halves are continuous on spaces of maps from $I$. The equation $\mu(e, e) = e$ holds since both halves are constant. Now let $\varphi(s) = \max(0, 2s - 1)$. Then $e \cdot \gamma = \gamma \circ \varphi$, because the first half is constant at $x_0 = \gamma(0)$ and the second half runs $\gamma(2s - 1)$. Define $K(t, \gamma)(s) = \gamma((1 - t)\varphi(s) + t s)$. The argument $(1 - t)\varphi(s) + ts$ lies in $I$ and is $0$ at $s = 0$ and $1$ at $s = 1$, so $K(t, \gamma)$ is a loop at $x_0$. The map $K$ is continuous, since evaluation $C(I, X) \times I \to X$ is continuous. It satisfies $K(0, \gamma) = e \cdot \gamma$ and $K(1, \gamma) = \gamma$. If $\gamma = e$, then $K(t, e) = e$ for all $t$, so $K$ is relative to $\{e\}$. The case of $\gamma \cdot e$ uses $\psi(s) = \min(1, 2s)$ in the same way. $\square$

### Examples

**Example (The straight-line homotopy in a disk).** Let $D \subseteq \mathbb{R}^2$ be the closed unit disk, with $f = \mathrm{id}_D$ and $g$ the constant map with value $0$. The straight-line homotopy is $H(t, x) = (1 - t) x$. Check by hand that it stays in $D$: $\lvert H(t, x) \rvert = (1 - t)\lvert x \rvert \le \lvert x \rvert \le 1$. At $t = 0$ it is $x$ and at $t = 1$ it is $0$. So $D$ is contractible, and $H$ is relative to $\{0\}$ because $H(t, 0) = 0$.

**Counterexample (The straight line can leave the space).** Let $X = \mathbb{R}^2 \setminus \{0\}$, with $f = \mathrm{id}_X$ and $g = -\mathrm{id}_X$. The formula $H(t, x) = (1 - t)x - t x = (1 - 2t)x$ gives $H(1/2, x) = 0$, which is not in $X$. So the straight line is not a homotopy in $X$, because $X$ is not convex. The maps are still homotopic. The rotation $R_\theta$ by the angle $\theta$ gives $K(t, x) = R_{\pi t}(x)$, with $K(0, x) = x$ and $K(1, x) = -x$, and $\lvert K(t, x) \rvert = \lvert x \rvert \neq 0$.

**Example (The circle as an H-space).** The unit circle $S^1 \subseteq \mathbb{C}$ is a topological group under multiplication. So it is an H-space with $e = 1$. Chapter 2 shows that it is not contractible.

### The library around it

::: mathlib
`ContinuousMap.Homotopy` · `Mathlib.Topology.Homotopy.Basic`

A term `F : ContinuousMap.Homotopy f₀ f₁` is a bundled continuous map `C(I × X, Y)` with the fields `map_zero_left` and `map_one_left`. The time is the first coordinate. The basic constructions are `Homotopy.refl`, `Homotopy.symm` (which uses `σ t = 1 - t`), `Homotopy.trans` (the two halves of the proof above) and `Homotopy.comp` (the formula $G(t, F(t,x))$). The variants `ContinuousMap.HomotopyWith` and `ContinuousMap.HomotopyRel` carry a property of each stage or the condition on a set `S`.

<?decl ContinuousMap.Homotopy?>
:::

The relation `ContinuousMap.Homotopic f₀ f₁` is `Nonempty (Homotopy f₀ f₁)`, and it is an `Equivalence`. The type `ContinuousMap.HomotopyRel f₀ f₁ S` is `HomotopyWith f₀ f₁ P`, where `P f` says that `f x = f₀ x` for all `x ∈ S`; `ContinuousMap.HomotopicRel` is its relation. Paths use it with `S = {0, 1}`.

::: mathlib
`ContinuousMap.HomotopyEquiv` · `Mathlib.Topology.Homotopy.Equiv`

The structure has `toFun`, `invFun` and the proofs `left_inv : (invFun.comp toFun).Homotopic (ContinuousMap.id X)` and `right_inv`. The notation is `X ≃ₕ Y`. `HomotopyEquiv.refl`, `HomotopyEquiv.symm`, `HomotopyEquiv.trans` and `Homeomorph.toHomotopyEquiv` are the parts of the theorem above.

<?decl ContinuousMap.HomotopyEquiv?>
:::

::: mathlib
`ContinuousMap.Homotopy.affine` · `Mathlib.Topology.Homotopy.Affine`

For `f g : C(X, E)` with `E` a real topological vector space, `affine f g` is the homotopy `(t, x) ↦ AffineMap.lineMap (f x) (g x) t`. It lives on the whole space `E`, not on a convex subset. The lemma `evalAt_affine` says that the path at a fixed `x` is the segment `Path.segment (f x) (g x)`. For a convex set, use `Convex.contractibleSpace` from `Mathlib.Analysis.Convex.Contractible`.

<?decl ContinuousMap.Homotopy.affine?>
:::

::: mathlib
`ContractibleSpace` · `Mathlib.Topology.Homotopy.Contractible`

The class `ContractibleSpace X` asks for `Nonempty (X ≃ₕ Unit)`. The lemma `contractible_iff_id_nullhomotopic` is the proposition above, and `id_nullhomotopic` extracts the nullhomotopy. `ContinuousMap.HomotopyEquiv.contractibleSpace` transports the class along a homotopy equivalence. Instances outside this module give `Convex.contractibleSpace`, `StarConvex.contractibleSpace`, `RealTopologicalVectorSpace.contractibleSpace` and `Metric.contractibleSpace_ball`.

<?decl ContractibleSpace?>
:::

::: mathlib
`ContinuousMap.Nullhomotopic` · `Mathlib.Topology.Homotopy.Contractible`

`Nullhomotopic f` is `∃ y, Homotopic f (ContinuousMap.const _ y)`. The lemmas `Nullhomotopic.comp_left` and `Nullhomotopic.comp_right` say that a composite with a nullhomotopic map is nullhomotopic.

<?decl ContinuousMap.Nullhomotopic?>
:::

The weak notion of local contractibility is the definition `LocallyContractibleSpace`. The class that instances use is `StronglyLocallyContractibleSpace`, which asks for a basis of contractible neighbourhoods. The theorem `StronglyLocallyContractibleSpace.locallyContractible` is the proposition above. The module gives instances for open subsets and products.

::: mathlib
`HSpace` · `Mathlib.Topology.Homotopy.HSpaces`

The class has `hmul : C(X × X, X)`, the point `e`, the equation `hmul_e_e`, and the two homotopies `eHmul` and `hmulE`, each a `HomotopyRel` relative to `{e}`. The notation `⋀` for the multiplication is scoped in `HSpaces`. The instances are `HSpace.prod`, `IsTopologicalGroup.toHSpace` and `Path.instHSpace` on `Path x x`. The last one uses `Path.delayReflRight`, which deforms `γ.trans (Path.refl x)` to `γ`.

<?decl HSpace?>
:::

The module `Mathlib.Topology.Homotopy.Product` gives `ContinuousMap.Homotopy.prod`, the product of two homotopies, and its relative form `ContinuousMap.HomotopyRel.prod`. For paths, `Path.Homotopic.prod` forms the product of two homotopy classes of paths; the next section uses it for the groupoid of a product.

```lean
open ContinuousMap in
example {X E : Type*} [TopologicalSpace X] [AddCommGroup E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [Module ℝ E] [ContinuousSMul ℝ E]
    (f g : C(X, E)) : Homotopic f g :=
  ⟨Homotopy.affine f g⟩
```

Common errors of a learner: The time coordinate of a homotopy comes first, so `F (t, x)` and not `F (x, t)`. `Homotopy.affine` does not take a convex set; a homotopy into a convex subset needs maps into the subtype. `LocallyContractibleSpace` is a definition and not a class, so instance search does not find it; the class is `StronglyLocallyContractibleSpace`. An H-space in Mathlib need not be associative, and the H-space on the loop space is on `Path x x`, not on a quotient.

### Exercises

1. (A) Let $X = [0,1]$ and $f(x) = x^2$, $g(x) = x$ as maps $X \to [0,1]$. Write the straight-line homotopy from $f$ to $g$ and check that it stays in $[0,1]$. Is it relative to $\{0, 1\}$? *Hint:* Compute $H(t, 0)$ and $H(t, 1)$.
2. (A) Show that any two maps $X \to \mathbb{R}^n$ are homotopic, and that any two maps $\mathbb{R}^n \to Y$ into a path connected space $Y$ are homotopic. *Hint:* For the second claim, contract the domain first.
3. (B) Show that $\mathbb{R}^n \setminus \{0\}$ is homotopy equivalent to the sphere $S^{n-1}$. *Hint:* Use $x \mapsto x / \lvert x \rvert$ and the straight-line homotopy in $\mathbb{R}^n \setminus \{0\}$ from $x$ to $x / \lvert x \rvert$; check that it never meets $0$.
4. (B) Show that a retract of a contractible space is contractible. *Hint:* If $r \circ i = \mathrm{id}_A$ and $H$ contracts $X$, consider $r \circ H \circ (\mathrm{id}_I \times i)$.
5. (B) Show that the composite of a nullhomotopic map with any map, on either side, is nullhomotopic. *Hint:* Use the proposition on composition.
6. (C) Let $X$ be an H-space with $e$, and let $\mathrm{id}_X$ be homotopic relative to $\{e\}$ to the constant map. Show that $\mu$ is homotopic to the first projection $X \times X \to X$. *Hint:* Compose $\mu$ with the homotopy on the second factor, then use $\mu(x, e) \simeq x$.

### Notes and history

Homotopy of paths appears in the work of Poincaré on the fundamental group in 1895. The notion of homotopy type became central in the work of Hurewicz from 1935 and of Whitehead from 1949, and the axioms of Eilenberg and Steenrod (1945, 1952) state homotopy invariance as an axiom for homology. For H-spaces the Mathlib source cites Serre (1951).

The Mathlib Author of `Topology.Homotopy.Affine` is Yury G. Kudryashov. The Mathlib Author of `Topology.Homotopy.Basic` and `Topology.Homotopy.Equiv` is Shing Tak Lam. The Mathlib Author of `Topology.Homotopy.Contractible` and `Topology.Homotopy.Product` is Praneeth Kolichala. The Mathlib Authors of `Topology.Homotopy.HSpaces` are Filippo A. E. Nuccio and Junyan Xu. The Mathlib Author of `Topology.Homotopy.LocallyContractible` is Kim Morrison.

### Reference

<?reference?>
