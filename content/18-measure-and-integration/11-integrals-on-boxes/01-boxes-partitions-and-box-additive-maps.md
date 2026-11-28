---
title: Boxes, partitions and box additive maps
kind: api
modules:
  - Mathlib.Analysis.BoxIntegral.Box.Basic
  - Mathlib.Analysis.BoxIntegral.Box.SubboxInduction
  - Mathlib.Analysis.BoxIntegral.Partition.Basic
  - Mathlib.Analysis.BoxIntegral.Partition.Split
  - Mathlib.Analysis.BoxIntegral.Partition.Tagged
  - Mathlib.Analysis.BoxIntegral.Partition.SubboxInduction
  - Mathlib.Analysis.BoxIntegral.Partition.Additive
  - Mathlib.Analysis.BoxIntegral.Partition.Measure
  - Mathlib.Analysis.BoxIntegral.UnitPartition
explains:
  E2: [BoxIntegral.Box, BoxIntegral.Prepartition, BoxIntegral.Prepartition.IsPartition, BoxIntegral.TaggedPrepartition, BoxIntegral.TaggedPrepartition.IsHenstock, BoxIntegral.TaggedPrepartition.IsSubordinate, BoxIntegral.BoxAdditiveMap, BoxIntegral.Prepartition.splitMany, BoxIntegral.Box.subbox_induction_on, MeasureTheory.Measure.toBoxAdditive]
  E1: auto
families: []
requires: [V13, V18.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Boxes, partitions and box additive maps

### Overview

The integral of Riemann is a limit of sums. Cut a box into small boxes, choose a point in each small box, and add the values of the function at the points, each times the volume of its box. The integrals of Henstock and Kurzweil and of McShane are limits of the same sums along other filters. Mathlib builds all of them on one common theory of boxes and partitions in the namespace `BoxIntegral`.

This section explains the objects of that theory. A box is a product of half open intervals. A prepartition of a box is a finite set of disjoint subboxes, and a partition is a prepartition that covers the box. A tagged prepartition adds a point to each subbox. A box additive map is a function on boxes that adds up over partitions, such as the volume. Section 2 of this chapter defines the integrals from these objects.

The space $\mathbb{R}^n$ is the type `ι → ℝ` for a finite type `ι`. The section needs the topology of Volume 13 and the measures of Chapter 2.

### The library around it

#### Boxes

The structure `BoxIntegral.Box ι` holds two points `lower` and `upper` of `ι → ℝ` and a proof that `lower i < upper i` for every `i`. As a set, a box is the product of the half open intervals $(l_i, u_i]$. The lemma `BoxIntegral.Box.coe_eq_pi` states this. The half open form makes the boxes of a partition disjoint as sets. The closed box $[l, u]$ is `BoxIntegral.Box.Icc I`, and it is compact, by `BoxIntegral.Box.isCompact_Icc`.

A box is never empty. The empty box is the bottom element of `WithBot (BoxIntegral.Box ι)`, and the constructor `BoxIntegral.Box.mk'` returns it when the bounds do not give a box. Boxes are ordered by inclusion: the lemma `BoxIntegral.Box.le_iff_bounds` says that $I \le J$ if and only if $J$ has the smaller lower point and the larger upper point. Two boxes have a supremum, the smallest box that contains both. Their infimum lies in `WithBot`, since two boxes may be disjoint.

The number `BoxIntegral.Box.distortion I` is the largest ratio of the distance from the lower point to the upper point to the length of one edge. The metric on `ι → ℝ` is the sup metric, so this distance is the longest edge. A cube has distortion $1$, and a thin box has a large distortion. The lemma `BoxIntegral.Box.dist_le_distortion_mul` bounds the distance from the lower point to the upper point by the distortion times the length of any edge. For a box in dimension $n + 1$, `BoxIntegral.Box.face I i` is the box in dimension $n$ that forgets the coordinate $i$. The divergence theorem uses faces.

#### Prepartitions and partitions

The structure `BoxIntegral.Prepartition I` is a finite set `boxes` of subboxes of `I` that are pairwise disjoint. Its union is `BoxIntegral.Prepartition.iUnion`. The predicate `BoxIntegral.Prepartition.IsPartition` says that the union is all of `I`. The lemma `BoxIntegral.Prepartition.isPartition_iff_iUnion_eq` states this form.

Prepartitions form a lattice. The order is refinement: $\pi_1 \le \pi_2$ means that every box of $\pi_1$ lies in a box of $\pi_2$. The top element `⊤` is the prepartition with the single box `I`, and the bottom element has no boxes. The infimum of two prepartitions has as its boxes the nonempty intersections of their boxes, by `BoxIntegral.Prepartition.inf_def`. Other constructions are:

| Lean name | Construction |
|---|---|
| `BoxIntegral.Prepartition.single` | the prepartition with one subbox $J \le I$ |
| `BoxIntegral.Prepartition.biUnion` | refine each box $J$ of $\pi$ by a prepartition of $J$ |
| `BoxIntegral.Prepartition.restrict` | the intersections of the boxes of $\pi$ with a box $J$ |
| `BoxIntegral.Prepartition.filter` | the boxes that satisfy a predicate |
| `BoxIntegral.Prepartition.disjUnion` | the union of two prepartitions with disjoint unions |
| `BoxIntegral.Prepartition.ofWithBot` | the nonempty boxes of a finite set of `WithBot` boxes |

The sum of a function over the boxes of a refinement `π.biUnion πi` is the double sum, by `BoxIntegral.Prepartition.sum_biUnion_boxes`.

#### Splitting along hyperplanes

The hyperplane $x_i = a$ cuts a box into two parts. These are `BoxIntegral.Box.splitLower I i a` and `BoxIntegral.Box.splitUpper I i a`, both in `WithBot`, since one part is empty when $a$ is outside the box. The prepartition `BoxIntegral.Prepartition.split I i a` has these two parts as boxes, and it is a partition, by `BoxIntegral.Prepartition.isPartitionSplit`.

The prepartition `BoxIntegral.Prepartition.splitMany I s` cuts $I$ along a finite set $s$ of hyperplanes. It gives a grid of boxes. The lemma `BoxIntegral.Prepartition.IsPartition.exists_splitMany_le` says that every partition has a refinement of this form. The proof of additivity uses this lemma: a property that holds for cuts along one hyperplane holds for all partitions. The complement `BoxIntegral.Prepartition.compl π` is a prepartition whose union is $I \setminus \bigcup \pi$, and `BoxIntegral.Prepartition.exists_iUnion_eq_diff` states its existence.

#### Tagged prepartitions

The structure `BoxIntegral.TaggedPrepartition I` is a prepartition with a point `tag J` in the closed box `Icc I` for each box $J$. Two conditions on tags matter.

1. `BoxIntegral.TaggedPrepartition.IsHenstock` says that each tag lies in the closed box $[J]$ of its own box. Riemann and Henstock sums use this condition, and McShane sums do not.
2. `BoxIntegral.TaggedPrepartition.IsSubordinate π r` says, for a gauge $r : \mathbb{R}^n \to (0, \infty)$, that each closed box $[J]$ lies in the closed ball of radius $r(\text{tag } J)$ about its tag. A constant gauge gives the condition of Riemann on the size of boxes. A gauge that varies gives the integral of Henstock and Kurzweil.

The lemma `BoxIntegral.TaggedPrepartition.IsSubordinate.diam_le` bounds the diameter of each box by $2 r$. The lemma `BoxIntegral.TaggedPrepartition.IsHenstock.card_filter_tag_eq_le` says that, in a Henstock prepartition, at most $2^n$ boxes share one tag.

#### Partitions for every gauge

The integrals of Section 2 make sense only if partitions exist for every gauge. This is the lemma of Cousin. The induction principle `BoxIntegral.Box.subbox_induction_on` proves it. A property $p$ of boxes holds for $I$ if two conditions hold. First, $p$ holds for a box when it holds for the $2^n$ halves of the box. Second, each point $z$ of $[I]$ has a neighbourhood in which $p$ holds for every small enough dyadic subbox that contains $z$. The halves are the boxes of `BoxIntegral.Prepartition.splitCenter`. The proof bisects and uses the compactness of $[I]$.

The lemma `BoxIntegral.Box.exists_taggedPartition_isHenstock_isSubordinate_homothetic` applies this principle. For every gauge $r$ it gives a partition of $I$ that is Henstock and subordinate to $r$, with boxes homothetic to $I$ and the same distortion. The lemma `BoxIntegral.Prepartition.exists_tagged_le_isHenstock_isSubordinate_iUnion_eq` does the same for a refinement of a given prepartition. The construction `BoxIntegral.TaggedPrepartition.unionComplToSubordinate` completes a tagged prepartition into a tagged partition, with the new part subordinate to a given gauge.

#### Box additive maps

The structure `BoxIntegral.BoxAdditiveMap ι M I₀` is a function on the subboxes of `I₀` with values in `M` such that $f(J) = \sum_{J' \in \pi} f(J')$ for every partition $\pi$ of $J$. The notation is `ι →ᵇᵃ[I₀] M` after `open BoxIntegral`, and `ι →ᵇᵃ M` takes $I_0 = \top$, which allows all boxes. The lemma `BoxIntegral.BoxAdditiveMap.sum_partition_boxes` states the additivity. The constructor `BoxIntegral.BoxAdditiveMap.ofMapSplitAdd` needs only additivity under the cut by one hyperplane, by the refinement lemma above.

Box additive maps form an additive group and a module. The map `BoxIntegral.BoxAdditiveMap.toSMul` turns a real valued map $\nu$ into a map with values in `E →L[ℝ] E`, which sends $J$ to multiplication by $\nu(J)$. This is the form that the integral of Section 2 needs for functions with values in `E`. The map `BoxIntegral.BoxAdditiveMap.upperSubLower` takes a family of box additive maps on the faces normal to the coordinate $i$ and gives the map $J \mapsto f(\text{upper face of } J) - f(\text{lower face of } J)$ in dimension $n + 1$. It appears in the divergence theorem.

#### Volume as a box additive map

A locally finite measure on $\mathbb{R}^n$ is finite on boxes. The map `MeasureTheory.Measure.toBoxAdditive μ` is $J \mapsto \mu(J)$ as a real valued box additive map. For Lebesgue measure, `BoxIntegral.Box.volume_apply` gives the product of the lengths of the edges:
$$\operatorname{vol}(J) = \prod_i (u_i - l_i).$$
The map `BoxIntegral.BoxAdditiveMap.volume` is the version with values in `E →L[ℝ] E`. The lemmas `BoxIntegral.Box.measurableSet_coe` and `BoxIntegral.Box.coe_ae_eq_Icc` say that a box is measurable and equal to its closure up to a null set.

#### Unit partitions and lattice points

The file `Mathlib.Analysis.BoxIntegral.UnitPartition` cuts space into cubes of side $1/n$ with vertices on the lattice $\frac{1}{n} \mathbb{Z}^d$. The tagged prepartition `BoxIntegral.unitPartition.prepartition n B` uses the cubes in a box $B$, with tags at their upper vertices. The predicate `BoxIntegral.hasIntegralVertices B` says that the vertices of $B$ have integer coordinates, and then the prepartition is a partition. Two counting results follow.

| Lean name | Statement |
|---|---|
| `tendsto_card_div_pow_atTop_volume` | the number of points of $\frac{1}{n} \mathbb{Z}^d$ in $s$, divided by $n^d$, tends to the volume of $s$ |
| `tendsto_tsum_div_pow_atTop_integral` | the sum of a continuous $F$ over these points, divided by $n^d$, tends to $\int_s F$ |

Both need $s$ bounded and measurable with a null frontier. Number theory uses them to count lattice points in large domains.

#### Common errors

1. Treating a box as a closed set. The coercion to sets gives $\prod_i (l_i, u_i]$. Use `BoxIntegral.Box.Icc` for the closed box, and `BoxIntegral.Box.coe_ae_eq_Icc` to pass between the two up to a null set.
2. Confusing a prepartition with a partition. A prepartition need not cover the box. Most results about integral sums need `BoxIntegral.Prepartition.IsPartition` or `BoxIntegral.TaggedPrepartition.IsPartition`.
3. Expecting the tag in the box for every integral. The tag lies only in the ambient closed box unless the prepartition is Henstock. McShane sums do not ask for the condition.

### Exercises

1. (A) Show that two boxes of a prepartition are disjoint as sets.
2. (A) Show that the volume of the box with lower point $0$ and upper point $(a, b)$ in $\mathbb{R}^2$ is $a b$.
3. (B) Show that the cut of a box along the hyperplane $x_i = a$ with $l_i < a < u_i$ gives a partition with two boxes.
4. (B) Show that the map $J \mapsto \prod_i (u_i - l_i)$ is box additive, with `BoxIntegral.BoxAdditiveMap.ofMapSplitAdd`.
5. (B) Show that for every constant gauge there is a Henstock partition of a box subordinate to it.
6. (C) Prove the lemma of Cousin in dimension one: for every gauge on $[a, b]$ there is a tagged partition subordinate to it.

### Reference

<?reference?>
