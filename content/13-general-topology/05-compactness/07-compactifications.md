---
title: Compactifications
kind: api
modules:
  - Mathlib.Topology.Compactification.OnePoint.Basic
  - Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
  - Mathlib.Topology.Compactification.OnePoint.Sphere
  - Mathlib.Topology.Compactification.StoneCech
explains:
  E2: [OnePoint.isOpen_iff_of_mem, OnePoint.hasBasis_nhds_infty, OnePoint.continuous_iff, OnePoint.isOpenEmbedding_coe, OnePoint.equivOfIsEmbeddingOfRangeEq, onePointEquivSphereOfFinrankEq, OnePoint.equivProjectivization, ultrafilter_converges_iff, stoneCechExtend, stoneCech_hom_ext]
  E1: auto
families: []
requires: [V04, V07, V13.C01, V13.C02, V13.C04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Compactifications

### Overview

A compactification of a space $X$ is a compact space that contains a dense copy of $X$. This section gives the two standard compactifications in Mathlib.

The *one-point compactification* `OnePoint X` adds one new point $\infty$ to $X$. The open sets of $X$ stay open, and a set that contains $\infty$ is open when its complement in $X$ is closed and compact. The space `OnePoint X` is always compact. It is Hausdorff when $X$ is locally compact and Hausdorff. The one-point compactification of $\mathbb{R}^n$ is the sphere $S^n$, and the one-point compactification of a field $K$ is the projective line over $K$.

The *Stone-Čech compactification* `StoneCech X` has a universal property: each continuous map from $X$ to a compact Hausdorff space extends in a unique way to a continuous map on `StoneCech X`. Mathlib builds it from the ultrafilters on $X$. The space of all ultrafilters on a type, with its own topology, is the Stone-Čech compactification of the type with the discrete topology.

The section uses compact sets from Section 1, local compactness from Section 4, ultrafilters and the filter `Filter.coclosedCompact` from Chapter 2, and the separation axioms of Chapter 4.

### The library around it

#### The one-point compactification

The module `Mathlib.Topology.Compactification.OnePoint.Basic` defines `OnePoint X` as `Option X`. The new point is `OnePoint.infty`, with the scoped notation `∞`, and the inclusion is `OnePoint.some`, which is also a coercion. The cases are handled by `OnePoint.rec`, `OnePoint.elim`, `OnePoint.forall` and `OnePoint.exists`. A function $f : X \to Y$ gives `OnePoint.map f`, which sends $\infty$ to $\infty$.

The topology `OnePoint.instTopologicalSpace` is described by two lemmas:

- `OnePoint.isOpen_iff_of_notMem`: a set without $\infty$ is open if and only if its preimage in $X$ is open;
- `OnePoint.isOpen_iff_of_mem`: a set with $\infty$ is open if and only if the complement of its preimage in $X$ is closed and compact.

The closed sets have the dual description in `OnePoint.isClosed_iff_of_mem` and `OnePoint.isClosed_iff_of_notMem`. The open set with a given closed compact complement is `OnePoint.opensOfCompl`.

The neighborhoods follow from the topology:

- `OnePoint.nhds_coe_eq`: the neighborhoods of a point $x$ of $X$ are the images of the neighborhoods of $x$ in $X$;
- `OnePoint.nhds_infty_eq`: the neighborhood filter of $\infty$ is the image of `Filter.coclosedCompact X`, together with the point $\infty$;
- `OnePoint.hasBasis_nhds_infty`: the sets $(X \setminus s) \cup \{\infty\}$ for closed compact $s$ form a basis at $\infty$.

The inclusion is an open embedding by `OnePoint.isOpenEmbedding_coe`. Its range is dense when $X$ is not compact, by `OnePoint.isDenseEmbedding_coe`. When $X$ is compact, $\infty$ is an isolated point.

The separation and compactness instances are:

- `OnePoint.instCompactSpace`: for each $X$, without hypotheses;
- `OnePoint.instT0Space` and `OnePoint.instT1Space`: from the same axiom on $X$;
- `OnePoint.instNormalSpaceOfWeaklyLocallyCompactSpaceOfR1Space`: if $X$ is weakly locally compact and $R_1$, then `OnePoint X` is normal. With $T_1$ this gives $T_2$;
- `OnePoint.instConnectedSpaceOfPreconnectedSpaceOfNoncompactSpace`: if $X$ is preconnected and not compact, then `OnePoint X` is connected;
- `OnePoint.instTotallySeparatedSpaceOfDiscreteTopology`: for a discrete space.

**Theorem.** The space `OnePoint X` is compact.

*Proof sketch.* Let $\mathcal{U}$ be an open cover. One member $U_0$ contains $\infty$, so the complement $K$ of the preimage of $U_0$ in $X$ is compact. The other members of $\mathcal{U}$ give an open cover of $K$, so finitely many of them cover $K$. These members and $U_0$ cover `OnePoint X`.

The theorem `OnePoint.continuous_iff` describes continuous maps out of `OnePoint X`. A map $f$ is continuous if and only if $f$ restricted to $X$ is continuous and $f(x)$ tends to $f(\infty)$ along `Filter.coclosedCompact X`. The constructor `OnePoint.continuousMapMk` builds a continuous map on `OnePoint X` from a map in `C(X, Y)` with a limit at infinity. For $X = \mathbb{N}$, the space `OnePoint ℕ` is the convergent sequence with its limit, and `OnePoint.continuousMapNatEquiv` identifies `C(OnePoint ℕ, Y)` with the convergent sequences in a Hausdorff space $Y$. The map `OnePoint.map f` is continuous if and only if $f$ is continuous and tends to `Filter.coclosedCompact Y` along `Filter.coclosedCompact X` (`OnePoint.continuous_map_iff`). A homeomorphism $X \cong Y$ gives `Homeomorph.onePointCongr`.

The module also proves `Continuous.homeoOfEquivCompactToT2.t1_counterexample`. It says that the homeomorphism criterion of Section 1 fails when the target is only $T_1$. The example is the identity from the one-point compactification of an infinite discrete space to the same type with the cofinite topology.

#### Recognizing a one-point compactification

The definition `OnePoint.equivOfIsEmbeddingOfRangeEq` gives a homeomorphism `OnePoint X ≃ₜ Y`. Its hypotheses are: $Y$ is compact and Hausdorff, $f : X \to Y$ is an embedding, and the range of $f$ is the complement of one point $y$. The homeomorphism sends $\infty$ to $y$ and $x$ to $f(x)$.

The module `Mathlib.Topology.Compactification.OnePoint.Sphere` uses this result with the stereographic projection. The homeomorphism `onePointHyperplaneHomeoUnitSphere` identifies the one-point compactification of a hyperplane $v^\perp$ in a finite dimensional inner product space with the unit sphere. The homeomorphism `onePointEquivSphereOfFinrankEq` identifies `OnePoint V`, for a finite dimensional real vector space $V$ with the usual topology, with the unit sphere of `EuclideanSpace ℝ ι` when $\dim V + 1$ is the cardinality of $\iota$.

The module `Mathlib.Topology.Compactification.OnePoint.ProjectiveLine` is algebraic. For a division ring $K$, `OnePoint.equivProjectivization K` is a bijection from `OnePoint K` to the projective line `Projectivization K (Fin 2 → K)`. It sends $k$ to the line through $(k, 1)$ and $\infty$ to the line through $(1, 0)$. For a field, the group `GL (Fin 2) K` acts on `OnePoint K` by the action `OnePoint.instGLAction`, which is the action by Möbius transformations $z \mapsto (az + b)/(cz + d)$. The lemmas `OnePoint.smul_infty_eq_ite` and `OnePoint.smul_some_eq_ite` compute the action, and `OnePoint.equivProjectivization_smul` says that the bijection respects it. Volume 12 uses this action on `OnePoint ℝ` to define the cusps of a subgroup of the modular group.

#### The space of ultrafilters

The module `Mathlib.Topology.Compactification.StoneCech` first puts a topology on `Ultrafilter α` for each type $\alpha$. The basic open sets are the sets $\{u \mid s \in u\}$ for $s \subseteq \alpha$, and `ultrafilterBasis_is_basis` says that they form a basis. These sets are also closed, by `ultrafilter_isClosed_basic`. The space is compact by `ultrafilter_compact`, Hausdorff by `Ultrafilter.t2Space`, and totally disconnected. The map `pure : α → Ultrafilter α` is a dense embedding of the discrete space $\alpha$ (`isDenseEmbedding_pure`).

The convergence of ultrafilters in this space has a short form. By `ultrafilter_converges_iff`, an ultrafilter $\mathcal{U}$ on `Ultrafilter α` converges to $x$ if and only if $x$ is the join of $\mathcal{U}$, the ultrafilter of sets $s$ with $\{u \mid s \in u\} \in \mathcal{U}$.

For a map $f : \alpha \to \gamma$ into a compact Hausdorff space, `Ultrafilter.extend f` sends an ultrafilter $u$ to the limit of `Ultrafilter.map f u`. This limit exists because $\gamma$ is compact, and it is unique because $\gamma$ is Hausdorff. The extension is continuous (`continuous_ultrafilter_extend`) and equal to $f$ on the principal ultrafilters (`ultrafilter_extend_extends`).

#### The Stone-Čech compactification

For a topological space $\alpha$, the construction has two steps. The type `PreStoneCech α` is the quotient of `Ultrafilter α` by the relation that identifies two ultrafilters that converge to a common point. It has the universal property, but it need not be Hausdorff. The type `StoneCech α` is the Hausdorff quotient `T2Quotient (PreStoneCech α)`.

The API of `StoneCech α` is:

- `stoneCechUnit : α → StoneCech α`, continuous by `continuous_stoneCechUnit`, with dense range by `denseRange_stoneCechUnit`;
- `instCompactSpaceStoneCech` and `instT2SpaceStoneCech`;
- `stoneCechExtend hg`, for a continuous $g : \alpha \to \beta$ with $\beta$ compact Hausdorff, with `continuous_stoneCechExtend` and `stoneCechExtend_extends`;
- `stoneCech_hom_ext`: two continuous maps from `StoneCech α` to a Hausdorff space that agree on the image of `stoneCechUnit` are equal.

**Theorem.** Let $\beta$ be compact Hausdorff and $g : \alpha \to \beta$ continuous. There is exactly one continuous $\bar g$ on `StoneCech α` with $\bar g \circ \iota = g$, where $\iota$ is `stoneCechUnit`.

*Proof sketch.* Existence: `Ultrafilter.extend g` is continuous on `Ultrafilter α`. Two ultrafilters that converge to the same point $x$ have the same image, $g(x)$, because $g$ is continuous. So the extension passes to `PreStoneCech α`, and then to the Hausdorff quotient because $\beta$ is Hausdorff. Uniqueness: two continuous maps to a Hausdorff space that agree on a dense set are equal.

The map `stoneCechUnit` need not be injective. It is injective, and an embedding, when $\alpha$ is completely regular and Hausdorff. The categorical form, the left adjoint to the inclusion of compact Hausdorff spaces, is in Volume 27.

#### Common errors

1. Expecting `OnePoint X` to be Hausdorff for each Hausdorff $X$. Lean finds `T2Space (OnePoint X)` only through `NormalSpace` and `T1Space`, and the normal space instance needs `WeaklyLocallyCompactSpace X`. The one-point compactification of $\mathbb{Q}$ is not Hausdorff.
2. Treating `stoneCechUnit` as an inclusion. The name `stoneCechExtend` suggests an extension, but `stoneCechUnit` can identify points, for example when $\alpha$ has the indiscrete topology. Do not use a lemma about embeddings without a proof that it is one.
3. Mixing up the two topologies on ultrafilters. `Ultrafilter α` has the topology of this section for each type $\alpha$, with no topology on $\alpha$. The topology of $\alpha$ is used only in `PreStoneCech α` and `StoneCech α`.

### Exercises

1. (A) Show that `OnePoint (Fin 3)` is a discrete space with four points, and that $\infty$ is isolated.
2. (A) Use `OnePoint.continuous_iff` to prove that a sequence $u : \mathbb{N} \to Y$ with limit $L$ gives a continuous map on `OnePoint ℕ`. Then find `OnePoint.continuousMapMkNat`.
3. (B) Prove that `OnePoint ℝ` is homeomorphic to the unit circle with `onePointEquivSphereOfFinrankEq`.
4. (B) Prove that the sets $\{u \mid s \in u\}$ are clopen in `Ultrafilter α`, and deduce that the space is totally disconnected.
5. (B) Let $\alpha$ be a compact Hausdorff space. Prove that `stoneCechExtend continuous_id` is a left inverse of `stoneCechUnit`, and deduce that `stoneCechUnit` is injective.
6. (C) Prove that `OnePoint ℚ` is not Hausdorff: the point $\infty$ and the point $0$ have no disjoint neighborhoods.

### Reference

<?reference?>
