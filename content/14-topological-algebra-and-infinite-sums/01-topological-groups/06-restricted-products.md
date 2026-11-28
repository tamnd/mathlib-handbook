---
title: Restricted products
kind: api
modules:
  - Mathlib.Topology.Algebra.RestrictedProduct.Basic
  - Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
  - Mathlib.Topology.Algebra.RestrictedProduct.Units
explains:
  E2: [RestrictedProduct, RestrictedProduct.structureMap, RestrictedProduct.inclusion, RestrictedProduct.topologicalSpace, RestrictedProduct.isOpenEmbedding_structureMap, RestrictedProduct.isTopologicalRing, RestrictedProduct.locallyCompactSpace_of_group, RestrictedProduct.unitsEquiv]
  E1: auto
families: []
requires: [V05, V13.C01, V13.C04, V13.C05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Restricted products

### Overview

Let $(R_i)_{i \in \iota}$ be a family of spaces and let $A_i \subseteq R_i$ be a subset for each $i$. The restricted product is the set of families $x = (x_i)$ with $x_i \in A_i$ for all but finitely many $i$. The adeles of a number field are the main example. There $R_v$ is the completion $K_v$ at a place $v$ and $A_v$ is its ring of integers $\mathcal{O}_v$. The adeles form a locally compact ring, although the full product $\prod_v K_v$ is not locally compact.

Mathlib defines the restricted product for an arbitrary filter $\mathcal{F}$ on $\iota$ in place of the cofinite filter. This section describes the type, its maps, its algebraic structure, its topology and its units.

### The library around it

#### The type and its notation

The type `RestrictedProduct R A 𝓕` is the subtype of `(i : ι) → R i` of the families $x$ with $\forall^{\mathcal{F}} i,\ x_i \in A_i$. The notation is `Πʳ i, [R i, A i]_[𝓕]`, and `Πʳ i, [R i, A i]` is the form for the cofinite filter. An element is built with `RestrictedProduct.mk x h`. An element is a function by the instance `RestrictedProduct.instDFunLike`, and `RestrictedProduct.eventually` recovers the condition. Two elements are equal when they agree at each index (`RestrictedProduct.ext`). The lemma `RestrictedProduct.range_coe` says that the image in the full product is exactly the set $\{x \mid \forall^{\mathcal{F}} i,\ x_i \in A_i\}$.

The choice of filter gives the two extreme cases. For $\mathcal{F} = \bot$ the condition is empty and the restricted product is the full product. For $\mathcal{F} = \top$ the condition holds for each $i$, and the restricted product is $\prod_i A_i$. For a principal filter $\mathcal{P}(S)$ the condition is $x_i \in A_i$ for $i \in S$.

#### Maps between restricted products

| Lean name | Statement |
|---|---|
| `RestrictedProduct.structureMap` | the map $\prod_i A_i \to$ `Πʳ i, [R i, A i]_[𝓕]` |
| `RestrictedProduct.inclusion` | for $\mathcal{F} \le \mathcal{G}$, the map from the product over $\mathcal{G}$ to the product over $\mathcal{F}$ |
| `RestrictedProduct.exists_inclusion_eq_of_eventually` | an element in the image of `RestrictedProduct.inclusion` is one whose condition holds along $\mathcal{G}$ |
| `RestrictedProduct.map` | a family $\varphi_i : G_i \to H_i$ with $\varphi_i(C_i) \subseteq D_i$ along $\mathcal{F}$ gives a map |
| `RestrictedProduct.mapAlong` | the same along a map $f : \iota_2 \to \iota_1$ of index types |
| `RestrictedProduct.range_structureMap` | the image of `RestrictedProduct.structureMap` is the set of $x$ with $x_i \in A_i$ for each $i$ |

A larger filter gives a smaller type, so `RestrictedProduct.inclusion` goes from the product over the larger filter to the one over the smaller filter. This order is easy to get wrong. The lemma `RestrictedProduct.inclusion_eq_id` says that `RestrictedProduct.inclusion` for $\mathcal{F} \le \mathcal{F}$ is the identity.

#### Algebraic structure

Let each $A_i$ be the carrier of a subobject $B_i$ of an algebraic structure on $R_i$. The library then takes $A_i = B_i$ through a `SetLike` instance and gives the restricted product the same structure. There are instances for each level, from multiplication to `CommRing`, such as `RestrictedProduct.instMulCoeOfMulMemClass` and `RestrictedProduct.instCommRingCoeOfSubringClass`. The operations act coordinatewise. A finite set of coordinates can leave $B_i$, but for the others the closure of $B_i$ under the operations keeps the result in $B_i$.

The library has the homomorphisms that come with the structure. `RestrictedProduct.evalMonoidHom` and `RestrictedProduct.evalRingHom` evaluate at one index. `RestrictedProduct.coeMonoidHom` is the inclusion into the full product. `RestrictedProduct.mapAlongMonoidHom` and `RestrictedProduct.mapAlongRingHom` are the algebraic forms of `RestrictedProduct.mapAlong`. For the cofinite filter, `RestrictedProduct.mulSingle i g` is the element that is $g$ at $i$ and $1$ elsewhere, with the usual lemmas `RestrictedProduct.mulSingle_eq_same`, `RestrictedProduct.mulSingle_eq_of_ne` and `RestrictedProduct.mulSingle_mul`. The additive form is `RestrictedProduct.single`.

#### The topology

The topology `RestrictedProduct.topologicalSpace R A 𝓕` is defined in two steps.

1. For a principal filter $\mathcal{P}(S)$, the restricted product carries the topology induced from the full product. This is `RestrictedProduct.topologicalSpace_eq_of_principal`, and `RestrictedProduct.isEmbedding_coe_of_principal` says that the map into the product is an embedding.
2. For a general filter, the topology is the finest one that makes each map `RestrictedProduct.inclusion` from a principal filter $\mathcal{P}(S) \ge \mathcal{F}$ continuous. This is `RestrictedProduct.topologicalSpace_eq_iSup`.

So a map out of a restricted product is continuous if and only if it is continuous on each piece of a principal filter: this is `RestrictedProduct.continuous_dom`. A map into a restricted product with a principal filter is continuous if and only if each coordinate is continuous (`RestrictedProduct.continuous_rng_of_principal_iff_forall`).

The cases $\bot$ and $\top$ give homeomorphisms with full products: `RestrictedProduct.homeoBot` is $\prod_i R_i \simeq$ the product over $\bot$, and `RestrictedProduct.homeoTop` is $\prod_i A_i \simeq$ the product over $\top$.

For the cofinite filter and open sets $A_i$, the topology has the classical description. The product $\prod_i A_i$ is an open subset of the restricted product, by `RestrictedProduct.isOpenEmbedding_structureMap`, and `RestrictedProduct.nhds_eq_map_structureMap` says that its neighbourhoods are those of the product topology. The set $\{x \mid \forall i,\ x_i \in A_i\}$ is open by `RestrictedProduct.isOpen_forall_mem`. A basis of open sets is therefore the family of sets $\prod_{i \in F} U_i \times \prod_{i \notin F} A_i$ with $F$ finite and $U_i$ open.

#### Topological algebra

Assume that each $B_i$ is open, given as an instance `Fact (∀ i, IsOpen (B i))`. Then the algebraic operations are continuous.

| Lean name | Statement |
|---|---|
| `RestrictedProduct.instContinuousMulCoeCofinite` | multiplication is continuous for the cofinite filter |
| `RestrictedProduct.isTopologicalGroup` | if each $R_i$ is a topological group, so is the restricted product |
| `RestrictedProduct.isTopologicalRing` | if each $R_i$ is a topological ring, so is the restricted product |
| `RestrictedProduct.weaklyLocallyCompactSpace_of_cofinite` | weakly locally compact if all but finitely many $A_i$ are compact |
| `RestrictedProduct.locallyCompactSpace_of_group` | a restricted product of locally compact groups with compact $B_i$ for almost all $i$ is locally compact |
| `RestrictedProduct.instT2Space` | the restricted product of Hausdorff spaces is Hausdorff |

The locally compact result is the one that the adeles need. The proof is short. The open subgroup $\prod_i B_i$ is a product of compact groups for almost all $i$ and of locally compact groups for the others, so it is locally compact by the theorem of Tychonoff. A topological group with a locally compact open subgroup is locally compact.

#### Units

The module `Mathlib.Topology.Algebra.RestrictedProduct.Units` describes the units. An element $x$ is a unit if and only if each $x_i$ is a unit in $R_i$ and, along $\mathcal{F}$, $x_i$ is a unit of the submonoid $B_i$. This is `RestrictedProduct.isUnit_iff`. The equivalence `RestrictedProduct.unitsEquiv` identifies the group of units with the restricted product of the groups $R_i^\times$ with respect to the groups $B_i^\times$. For the adeles this gives the ideles: $\mathbb{A}_K^\times$ is the restricted product of the $K_v^\times$ with respect to the $\mathcal{O}_v^\times$. The topology of the ideles is not the one induced from the adeles, so this section treats only the algebraic identification.

#### Common errors

1. For $\mathcal{F} \le \mathcal{G}$, the map `RestrictedProduct.inclusion R A h` goes from the product over $\mathcal{G}$ to the product over $\mathcal{F}$. Writing it in the other direction gives a type error that names the two filters.
2. The ring and group instances need the sets $A_i$ in the form `↑(B i)` for a subobject `B i`. A family of plain sets gives no `Ring` instance, even if each set is closed under the operations.
3. The continuity results need the instance `Fact (∀ i, IsOpen (B i))`. Without it, instance search for `IsTopologicalRing` fails with no clear message.

### Exercises

1. (A) Show that for a finite index type, the restricted product over the cofinite filter is the full product, and find the lemma that gives the homeomorphism.
2. (A) Use `RestrictedProduct.isUnit_iff` to prove that an element of the restricted product of the fields $\mathbb{Q}_p$ with respect to the rings $\mathbb{Z}_p$ is a unit if and only if each coordinate is nonzero and almost all coordinates have absolute value 1.
3. (B) Prove that $\prod_i A_i$ is open in the restricted product with the cofinite filter when each $A_i$ is open, without `RestrictedProduct.isOpenEmbedding_structureMap`.
4. (B) Show that the restricted product of the discrete groups $\mathbb{Z}/2$ with respect to the trivial subgroups is the direct sum, and describe its topology.
5. (C) Explain why the restricted product topology on the units is finer than the topology induced from the restricted product of the rings, with the ideles of $\mathbb{Q}$ as the example.

### Reference

<?reference?>
