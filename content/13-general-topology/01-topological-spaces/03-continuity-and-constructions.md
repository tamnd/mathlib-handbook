---
title: Continuous maps, homeomorphisms and constructions of spaces
kind: theory
modules:
  - Mathlib.Topology.Continuous
  - Mathlib.Topology.Homeomorph.Defs
  - Mathlib.Topology.Defs.Induced
  - Mathlib.Topology.Constructions
  - Mathlib.Topology.Constructions.SumProd
  - Mathlib.Topology.List
  - Mathlib.Topology.Hom.ContinuousEval
  - Mathlib.Topology.Hom.ContinuousEvalConst
  - Mathlib.Topology.WithTopology
  - Mathlib.Topology.PreorderRestrict
explains:
  E3: [Continuous, Homeomorph, TopologicalSpace.induced, TopologicalSpace.coinduced]
  E2: [continuous_def, Continuous.comp, continuous_iff_isClosed, continuous_id, continuous_const, continuous_induced_rng, continuous_coinduced_dom, continuous_iff_le_induced, continuous_iff_coinduced_le, continuous_subtypeVal, Continuous.subtype_mk, instTopologicalSpaceProd, continuous_fst, continuous_snd, Continuous.prodMk, isOpen_prod_iff, Pi.topologicalSpace, continuous_pi, continuous_apply, continuous_quot_mk, continuous_quot_lift, Topology.IsEmbedding, IsOpenMap, Homeomorph.isOpen_preimage]
  E1: auto
families: []
requires: [V01, V04]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Continuous maps, homeomorphisms and constructions of spaces

### Overview

A continuous map is a map for which the preimage of each open set is open. On $\mathbb{R}$ this is the $\varepsilon$-$\delta$ definition, as Chapter 3 proves. In general it is the only definition that uses no more than the open sets. Two spaces are the same for topology when there is a homeomorphism between them: a bijection that is continuous in both directions.

This section defines continuity and homeomorphisms and proves the equivalent forms of continuity. It then builds new spaces from old ones. A map into a space induces a topology on its domain, and a map out of a space induces a topology on its codomain. The subspace topology, the product topology and the quotient topology are special cases. Each is characterised by a universal property, which says which maps into or out of the new space are continuous. The universal property is the form that a proof uses, and it is the form that Mathlib states.

### Definitions

**Definition (Continuous map).** Let $X$ and $Y$ be topological spaces. A map $f : X \to Y$ is continuous if $f^{-1}(V)$ is open in $X$ for each open $V \subseteq Y$.

*Remarks.* The definition uses preimages, not images. Images do not work: the constant map $\mathbb{R} \to \mathbb{R}$ with value $0$ is continuous, and it sends the open set $\mathbb{R}$ to $\{0\}$, which is not open. A map whose images of open sets are open is an open map, a different notion. Continuity depends on both topologies. Each map out of a discrete space is continuous, and each map into an indiscrete space is continuous.

::: mathlib
`Continuous` · `Mathlib.Topology.Defs.Basic`

`Continuous f` is a structure with one field, `isOpen_preimage : ∀ s, IsOpen s → IsOpen (f ⁻¹' s)`. As with `IsClosed`, the structure makes the unfolding explicit, and `continuous_def` states it as an equivalence. The topologies are instance arguments. For a map between two topologies on one type, write `Continuous[t₁, t₂] f`.

<?decl Continuous?>
:::

::: mathlib
`continuous_def` · `Mathlib.Topology.Continuous`

The definition as an equivalence: `f` is continuous if and only if each open preimage condition holds.

<?decl continuous_def?>
:::

**Definition (Homeomorphism, open map, embedding).** A homeomorphism $f : X \to Y$ is a bijection such that $f$ and $f^{-1}$ are continuous. A map $f$ is open if $f(U)$ is open for each open $U$. A map $f : X \to Y$ is an embedding if it is injective and the topology of $X$ is the topology induced by $f$ (below), so that $f$ is a homeomorphism from $X$ onto the subspace $f(X)$.

::: mathlib
`Homeomorph` · `Mathlib.Topology.Homeomorph.Defs`

A homeomorphism `X ≃ₜ Y` is a structure that extends an equivalence `X ≃ Y` (Volume 1) with the two fields `continuous_toFun` and `continuous_invFun`. It is data, not a proposition: it carries the inverse map. Composition is `Homeomorph.trans`, the inverse is `Homeomorph.symm`, and the coercion to a function lets one write `h x`.

<?decl Homeomorph?>
:::

::: mathlib
`Homeomorph.isOpen_preimage` · `Mathlib.Topology.Homeomorph.Defs`

Under a homeomorphism, a preimage is open if and only if the set is open. A homeomorphism preserves each topological property, and Mathlib has many lemmas of the form `Homeomorph.isCompact_preimage` or `Homeomorph.connectedSpace` for this.

<?decl Homeomorph.isOpen_preimage?>
:::

::: mathlib
`IsOpenMap` · `Mathlib.Topology.Defs.Basic`

`IsOpenMap f` says that the image of each open set is open. The closed analogue is `IsClosedMap`.

<?decl IsOpenMap?>
:::

::: mathlib
`Topology.IsEmbedding` · `Mathlib.Topology.Defs.Induced`

`IsEmbedding f` is a structure with two fields: `IsInducing f`, which says that the topology of the domain is the induced topology, and `Function.Injective f`. The names live in the namespace `Topology`, so a file writes `open Topology` to use them unqualified.

<?decl Topology.IsEmbedding?>
:::

**Definition (Induced and coinduced topologies).** Let $f : X \to Y$ be a map of sets.

- If $Y$ has a topology $\mathcal{T}_Y$, the induced topology on $X$ is $f^{*}\mathcal{T}_Y = \{f^{-1}(V) : V \in \mathcal{T}_Y\}$.
- If $X$ has a topology $\mathcal{T}_X$, the coinduced topology on $Y$ is $f_{*}\mathcal{T}_X = \{V \subseteq Y : f^{-1}(V) \in \mathcal{T}_X\}$.

Both are topologies, because the preimage commutes with unions and intersections: $f^{-1}(\bigcup V_i) = \bigcup f^{-1}(V_i)$, $f^{-1}(V \cap W) = f^{-1}(V) \cap f^{-1}(W)$ and $f^{-1}(Y) = X$. The induced topology is the coarsest topology on $X$ that makes $f$ continuous. The coinduced topology is the finest topology on $Y$ that makes $f$ continuous.

::: mathlib
`TopologicalSpace.induced` · `Mathlib.Topology.Defs.Induced`

`induced f t` is the topology on the domain whose open sets are the preimages of the `t`-open sets. The lemma `isOpen_induced_iff` unfolds it.

<?decl TopologicalSpace.induced?>
:::

::: mathlib
`TopologicalSpace.coinduced` · `Mathlib.Topology.Defs.Induced`

`coinduced f t` is the topology on the codomain whose open sets are the sets with an open preimage.

<?decl TopologicalSpace.coinduced?>
:::

**Definition (Subspace, product and quotient topologies).**

- Let $A \subseteq X$. The subspace topology on $A$ is the topology induced by the inclusion $A \hookrightarrow X$. Its open sets are the sets $A \cap U$ with $U$ open in $X$.
- Let $(X_i)_{i \in I}$ be spaces and $\pi_j : \prod_i X_i \to X_j$ the projections. The product topology is the topology generated by the sets $\pi_j^{-1}(U)$ with $j \in I$ and $U$ open in $X_j$. For two factors, the sets $U \times V$ with $U$ and $V$ open form a basis.
- Let $\sim$ be an equivalence relation on $X$ and $q : X \to X/{\sim}$ the quotient map. The quotient topology is the topology coinduced by $q$. A set of classes is open when the union of the classes is open in $X$.

*Remarks.* The product topology is not the box topology, which has the basis of all sets $\prod_i U_i$ with each $U_i$ open. For a finite product they agree. For an infinite product the product topology has as basis the sets $\prod_i U_i$ with $U_i$ open and $U_i = X_i$ for all but finitely many $i$. This follows from the theorem on subbases of Section 2: a finite intersection of sets $\pi_j^{-1}(U)$ constrains only finitely many coordinates.

::: mathlib
`instTopologicalSpaceProd` · `Mathlib.Topology.Constructions.SumProd`

The topology on `X × Y` is defined as `induced Prod.fst t₁ ⊓ induced Prod.snd t₂`. The infimum is the coarsest common refinement, so this is the coarsest topology that makes both projections continuous, which is the product topology.

<?decl instTopologicalSpaceProd?>
:::

::: mathlib
`Pi.topologicalSpace` · `Mathlib.Topology.Constructions`

The product topology on the dependent function type `(i : ι) → Y i` is the infimum over `i` of the topologies induced by the evaluations `fun f ↦ f i`. A function type `ι → Y` gets the same instance, so `ℝ → ℝ` carries the topology of pointwise convergence. This is a frequent surprise: the topology on `ℝ → ℝ` is not the topology of uniform convergence.

<?decl Pi.topologicalSpace?>
:::

::: mathlib
`isOpen_prod_iff` · `Mathlib.Topology.Constructions.SumProd`

A set in `X × Y` is open if and only if each point of it lies in an open box `u ×ˢ v` inside the set. The notation `×ˢ` is the product of two sets.

<?decl isOpen_prod_iff?>
:::

### Theorems and proofs

**Theorem (Equivalent forms of continuity).** For a map $f : X \to Y$ the following are equivalent.

1. $f$ is continuous.
2. $f^{-1}(F)$ is closed for each closed $F \subseteq Y$.
3. $f(\overline{A}) \subseteq \overline{f(A)}$ for each $A \subseteq X$.
4. $f^{-1}(B)$ is open for each $B$ in a fixed basis $\mathcal{B}$ of $Y$.

*Proof.* (1 ⇔ 2) The preimage commutes with complements: $f^{-1}(Y \setminus F) = X \setminus f^{-1}(F)$. So the preimage of each open set is open if and only if the preimage of each closed set is closed.

(2 ⇒ 3) Let $A \subseteq X$. The set $F = \overline{f(A)}$ is closed, so $f^{-1}(F)$ is closed by 2. It contains $A$, because $f(A) \subseteq F$. By minimality of the closure, $\overline{A} \subseteq f^{-1}(F)$, that is, $f(\overline{A}) \subseteq \overline{f(A)}$.

(3 ⇒ 2) Let $F \subseteq Y$ be closed and $A = f^{-1}(F)$. By 3, $f(\overline{A}) \subseteq \overline{f(A)} \subseteq \overline{F} = F$. So $\overline{A} \subseteq f^{-1}(F) = A$. So $A = \overline{A}$ is closed.

(1 ⇔ 4) Each basic set is open, so 1 gives 4. Conversely, an open $V \subseteq Y$ is a union $\bigcup_k B_k$ of basic sets, and $f^{-1}(V) = \bigcup_k f^{-1}(B_k)$ is a union of open sets. $\square$

::: mathlib
`continuous_iff_isClosed` · `Mathlib.Topology.Continuous`

Form 2 of the theorem. The direction 1 ⇒ 3 is `image_closure_subset_closure_image`, and form 4 is `IsTopologicalBasis.continuous_iff`.

<?decl continuous_iff_isClosed?>
:::

**Theorem (Composition).** The identity map and each constant map are continuous. If $f : X \to Y$ and $g : Y \to Z$ are continuous, then $g \circ f$ is continuous.

*Proof.* The preimage of an open $U$ under the identity is $U$. The preimage under a constant map is $\emptyset$ or $X$. For the composite, $(g \circ f)^{-1}(W) = f^{-1}(g^{-1}(W))$. If $W$ is open, $g^{-1}(W)$ is open by continuity of $g$, and then $f^{-1}(g^{-1}(W))$ is open by continuity of $f$. $\square$

::: mathlib
`Continuous.comp` · `Mathlib.Topology.Continuous`

`hg.comp hf : Continuous (g ∘ f)`. Note the order: the proof for the outer map comes first, as in `g ∘ f`. The variant `Continuous.comp'` states the result for `fun x ↦ g (f x)`, the form that `simp` and `fun_prop` see.

<?decl Continuous.comp?>
:::

::: mathlib
`continuous_id` · `Mathlib.Topology.Continuous`

The identity is continuous.

<?decl continuous_id?>
:::

::: mathlib
`continuous_const` · `Mathlib.Topology.Continuous`

A constant map is continuous.

<?decl continuous_const?>
:::

**Theorem (Universal property of the induced topology).** Let $f : X \to Y$, give $X$ the topology induced by $f$, and let $Z$ be a space. A map $g : Z \to X$ is continuous if and only if $f \circ g : Z \to Y$ is continuous.

*Proof.* If $g$ is continuous, then $f \circ g$ is a composite of continuous maps, since $f$ is continuous for the induced topology. Conversely, assume that $f \circ g$ is continuous, and let $U \subseteq X$ be open. By definition $U = f^{-1}(V)$ for an open $V \subseteq Y$. Then $g^{-1}(U) = g^{-1}(f^{-1}(V)) = (f \circ g)^{-1}(V)$ is open. $\square$

::: mathlib
`continuous_induced_rng` · `Mathlib.Topology.Order`

The universal property: into a space with the induced topology, `g` is continuous if and only if `f ∘ g` is. The lemma `continuous_induced_dom` says that `f` itself is continuous for the induced topology.

<?decl continuous_induced_rng?>
:::

::: mathlib
`continuous_iff_le_induced` · `Mathlib.Topology.Order`

In the language of the lattice of topologies: `f` is continuous if and only if the topology of the domain is finer than the induced topology, `t₁ ≤ induced f t₂`. This lemma and `continuous_iff_coinduced_le` show the reason for the order of Section 1: induced and coinduced form a Galois connection (Volume 4) in this order.

<?decl continuous_iff_le_induced?>
:::

**Theorem (Universal property of the coinduced topology).** Let $f : X \to Y$, give $Y$ the topology coinduced by $f$, and let $Z$ be a space. A map $h : Y \to Z$ is continuous if and only if $h \circ f$ is continuous.

*Proof.* If $h$ is continuous, so is $h \circ f$, since $f$ is continuous for the coinduced topology. Conversely, assume $h \circ f$ is continuous and let $W \subseteq Z$ be open. Then $f^{-1}(h^{-1}(W)) = (h \circ f)^{-1}(W)$ is open in $X$. By definition of the coinduced topology, $h^{-1}(W)$ is open in $Y$. $\square$

::: mathlib
`continuous_coinduced_dom` · `Mathlib.Topology.Order`

The universal property of the coinduced topology.

<?decl continuous_coinduced_dom?>
:::

::: mathlib
`continuous_iff_coinduced_le` · `Mathlib.Topology.Order`

`f` is continuous if and only if `coinduced f t₁ ≤ t₂`.

<?decl continuous_iff_coinduced_le?>
:::

**Corollary (Subspaces and quotients).** Let $A \subseteq X$ have the subspace topology. A map $g : Z \to A$ is continuous if and only if it is continuous as a map into $X$. Let $X/{\sim}$ have the quotient topology. A map $h : X/{\sim} \to Z$ is continuous if and only if $h \circ q$ is continuous.

*Proof.* These are the two universal properties, for the inclusion and for $q$. $\square$

::: mathlib
`continuous_subtypeVal` · `Mathlib.Topology.Constructions`

A subset `s` of `X` becomes the subtype `↥s`, with the induced topology as instance. The inclusion `Subtype.val` is continuous, and `Continuous.subtype_mk` gives the other half of the universal property: a continuous map into `X` with values in `s` is continuous into `↥s`.

<?decl continuous_subtypeVal?>
:::

::: mathlib
`Continuous.subtype_mk` · `Mathlib.Topology.Constructions`

A continuous map with values in a subset restricts to a continuous map into the subtype.

<?decl Continuous.subtype_mk?>
:::

::: mathlib
`continuous_quot_mk` · `Mathlib.Topology.Constructions`

The quotient map `Quot.mk r` is continuous for the quotient topology.

<?decl continuous_quot_mk?>
:::

::: mathlib
`continuous_quot_lift` · `Mathlib.Topology.Constructions`

A continuous map that is constant on the classes lifts to a continuous map on the quotient. This is the universal property in the form that a proof needs.

<?decl continuous_quot_lift?>
:::

**Theorem (Universal property of the product).** Let $Z$ be a space and $f : Z \to \prod_i X_i$. Then $f$ is continuous if and only if each coordinate $\pi_i \circ f$ is continuous.

*Proof.* Each projection $\pi_i$ is continuous, since $\pi_i^{-1}(U)$ is a member of the subbasis. So if $f$ is continuous, each $\pi_i \circ f$ is continuous. Conversely, assume that each $\pi_i \circ f$ is continuous. By form 4 of the equivalent forms of continuity, applied to the basis of finite intersections of subbasic sets, it suffices to check the preimages of the sets $\pi_{i_1}^{-1}(U_1) \cap \dots \cap \pi_{i_n}^{-1}(U_n)$. The preimage is $(\pi_{i_1} \circ f)^{-1}(U_1) \cap \dots \cap (\pi_{i_n} \circ f)^{-1}(U_n)$, a finite intersection of open sets. $\square$

::: mathlib
`continuous_pi` · `Mathlib.Topology.Constructions`

A map into a product is continuous if each coordinate is continuous. The converse uses `continuous_apply`, which says that each evaluation is continuous.

<?decl continuous_pi?>
:::

::: mathlib
`continuous_apply` · `Mathlib.Topology.Constructions`

Evaluation at `i` is continuous on the product.

<?decl continuous_apply?>
:::

::: mathlib
`Continuous.prodMk` · `Mathlib.Topology.Constructions.SumProd`

For two factors: if `f` and `g` are continuous, so is `fun x ↦ (f x, g x)`.

<?decl Continuous.prodMk?>
:::

::: mathlib
`continuous_fst` · `Mathlib.Topology.Constructions.SumProd`

The first projection is continuous.

<?decl continuous_fst?>
:::

::: mathlib
`continuous_snd` · `Mathlib.Topology.Constructions.SumProd`

The second projection is continuous.

<?decl continuous_snd?>
:::

### Examples

**Example (A continuous bijection that is not a homeomorphism).** Let $X = [0, 1)$ with the subspace topology of $\mathbb{R}$, and $S^1 = \{z \in \mathbb{C} : |z| = 1\}$ with the subspace topology of $\mathbb{C}$. The map $f(t) = e^{2\pi i t}$ is a continuous bijection $X \to S^1$. It is not a homeomorphism. The set $U = [0, 1/2)$ is open in $X$, since $U = X \cap (-1, 1/2)$. Its image $f(U)$ is the upper half circle with the point $1$ and without the point $-1$. Each open set of $\mathbb{C}$ that contains $1$ contains points $e^{2\pi i t}$ with $t$ slightly less than $1$, and these are not in $f(U)$. So $f(U)$ is not open in $S^1$, and $f^{-1}$ is not continuous. Chapter 5 shows that this cannot happen when the domain is compact and the codomain is Hausdorff.

**Example (The circle as a quotient).** Let $\sim$ on $[0, 1]$ identify $0$ with $1$ and nothing else. The map $g(t) = e^{2\pi i t}$ is continuous on $[0, 1]$ and constant on the classes. By the universal property it gives a continuous bijection $\bar g : [0,1]/{\sim} \to S^1$. Its inverse is continuous by the theorem of Chapter 5 cited above, since $[0,1]/{\sim}$ is compact and $S^1$ is Hausdorff. So the quotient is homeomorphic to the circle.

**Counterexample (The box topology).** Give $\mathbb{R}^{\mathbb{N}}$ the box topology, and let $\Delta : \mathbb{R} \to \mathbb{R}^{\mathbb{N}}$ be the diagonal map $\Delta(t) = (t, t, t, \dots)$. Each coordinate of $\Delta$ is the identity, which is continuous. The set $B = \prod_n (-1/(n+1), 1/(n+1))$ is open in the box topology. Its preimage is $\Delta^{-1}(B) = \bigcap_n (-1/(n+1), 1/(n+1)) = \{0\}$, which is not open. So $\Delta$ is not continuous, and the universal property of the product fails for the box topology. For the product topology $\Delta$ is continuous, by the theorem. This is the reason for the definition of the product topology.

**Example (Maps into the cofinite topology).** Let $Y$ have the cofinite topology and $f : X \to Y$. The closed sets of $Y$ are $Y$ and the finite sets. By form 2 of continuity, $f$ is continuous if and only if $f^{-1}(F)$ is closed for each finite $F$. A finite set is a finite union of points, and a preimage of a union is the union of the preimages. So $f$ is continuous if and only if each fibre $f^{-1}(y)$ is closed. For example, each injective map $\mathbb{R} \to Y$ is continuous, since its fibres are empty or points, and points are closed in $\mathbb{R}$.

### The library around it

The lemmas on continuity are in `Mathlib.Topology.Continuous`, and the constructions in `Mathlib.Topology.Constructions` and `Mathlib.Topology.Constructions.SumProd`. Each construction has its universal property and a family of lemmas `continuous_*` for the maps that it comes with: `continuous_fst`, `continuous_snd`, `continuous_inl`, `continuous_inr`, `continuous_apply`, `continuous_subtypeVal`, `continuous_quot_mk`. The dot notation lemmas `Continuous.fst`, `Continuous.snd`, `Continuous.prodMk`, `Continuous.comp` and `Continuous.subtype_mk` combine them. Most of these lemmas carry the attribute `fun_prop`, and the tactic `fun_prop` proves a goal `Continuous (fun x ↦ ...)` by breaking the term into these pieces. The tactic `continuity` is an older tool for the same task.

A homeomorphism is data `X ≃ₜ Y`; the property "this map is a homeomorphism" is `IsHomeomorph f`. Embeddings, open embeddings and closed embeddings are `IsEmbedding`, `IsOpenEmbedding` and `IsClosedEmbedding` in the namespace `Topology`. The quotient topology on `Quotient s` and the quotient of a type by a setoid both come with instances.

The module `Mathlib.Topology.List` gives a topology on `List α`, the instance `instTopologicalSpaceList`, and on the vectors `List.Vector α n`. A list near $[a_1, \dots, a_n]$ is a list of the same length whose entries are near the $a_i$: the neighbourhood filters satisfy `nhds_nil` and `nhds_cons`. The list operations are continuous, for example `List.continuous_cons` and `List.continuous_insertIdx`, and the length is locally constant, `List.continuousAt_length`.

Two classes in `Mathlib.Topology.Hom.ContinuousEvalConst` and `Mathlib.Topology.Hom.ContinuousEval` treat a type `F` of bundled maps $X \to Y$ with a topology of its own, such as `C(X, Y)`. The class `ContinuousEvalConst F X Y` says that the evaluation $f \mapsto f(x)$ at each fixed point is continuous, and `ContinuousEval F X Y` says that the joint evaluation $(f, x) \mapsto f(x)$ is continuous. The lemmas `Continuous.eval_const` and `Continuous.eval` then give the continuity of $z \mapsto f_z(x)$ and of $z \mapsto f_z(g(z))$, and `ContinuousEval.of_continuous_forget` transfers the class along a continuous forgetful map. These classes let one lemma serve each type of continuous maps with a good topology.

The module `Mathlib.Topology.WithTopology` gives a type synonym `WithTopology X t` that carries a chosen topology $t$ on $X$ as its instance, even when $X$ has an instance already. The maps `WithTopology.toTopology` and `WithTopology.ofTopology` go to the synonym and back, they are bijective (`WithTopology.toTopology_bijective`), and `WithTopology.isOpen_iff` describes the open sets. The constructible topology of Chapter 10 uses this synonym. The module `Mathlib.Topology.PreorderRestrict` proves that the restriction of a function on a preorder to the elements below $a$ is continuous for the product topologies (`Preorder.continuous_restrictLe`, `Preorder.continuous_frestrictLe`).

Common errors of a learner:

- The topology on a function type `ι → Y` is the product topology, that is, pointwise convergence. The uniform topology needs the type `ι →ᵇ Y` of bounded continuous functions, or `C(ι, Y)` with the compact open topology.
- In `hg.comp hf` the outer function comes first.
- A continuous bijection need not be a homeomorphism. To build `X ≃ₜ Y` from an equivalence, both continuity proofs are needed, or the compact to Hausdorff criterion `Continuous.homeoOfEquivCompactToT2`.

The reference table at the end of the section lists the declarations of the modules.

### Exercises

1. (A) Show that $f : X \to Y$ is continuous if $X$ is discrete or $Y$ is indiscrete.
2. (A) Let $A \subseteq X$ have the subspace topology. Show that the closed sets of $A$ are the sets $A \cap F$ with $F$ closed in $X$, and that the closure of $B \subseteq A$ in $A$ is $A \cap \overline{B}$.
3. (A) Show that the projections $X \times Y \to X$ are open maps. Show that they need not be closed maps. Hint: the hyperbola $\{xy = 1\}$ in $\mathbb{R}^2$.
4. (B) (Pasting lemma) Let $X = A \cup B$ with $A$ and $B$ closed, and let $f : X \to Y$ be such that $f|_A$ and $f|_B$ are continuous. Show that $f$ is continuous. Show that the lemma fails for $A = (-\infty, 0]$ and $B = (0, \infty)$ in $\mathbb{R}$.
5. (B) Show that $(0, 1)$ is homeomorphic to $\mathbb{R}$, and that $[0, 1)$ is homeomorphic to $[0, \infty)$.
6. (B) Show that the subspace $\mathbb{Q} \subseteq \mathbb{R}$ is not discrete, and that the subspace $\{1/n : n \ge 1\}$ is discrete while $\{0\} \cup \{1/n : n \ge 1\}$ is not.
7. (B) Let $X$ have the cofinite topology and $Y$ be $\mathbb{R}$. Show that each continuous map $X \to \mathbb{R}$ from an infinite $X$ is constant. Hint: the preimages of two disjoint open intervals are disjoint open sets.
8. (C) Show that the quotient of $\mathbb{R}$ by the relation $x \sim y \iff x - y \in \mathbb{Q}$ has the indiscrete topology.

### Notes and history

The preimage definition of continuity is in Hausdorff (1914) in the language of neighbourhoods. The product topology for infinite products was defined by Tychonoff (1930), and its choice over the box topology is justified by the universal property and by the theorem of Tychonoff in Chapter 5. The universal properties as the main form of the constructions are the point of view of Bourbaki, *Topologie générale* I, §2 to §4, where the initial and final topologies of a family of maps are defined.

In Mathlib, the subspace, product and quotient instances are all defined with `induced`, `coinduced` and the infimum and supremum of topologies. This makes the universal properties formal consequences of the Galois connection between `induced f` and `coinduced f`.

### Reference

<?reference?>
