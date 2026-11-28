---
title: The lattices of open and closed sets
kind: api
modules:
  - Mathlib.Topology.Sets.Opens
  - Mathlib.Topology.Sets.Closeds
  - Mathlib.Topology.Sets.Order
  - Mathlib.Topology.Sets.OpenCover
explains:
  E2: [TopologicalSpace.Opens, TopologicalSpace.Opens.instFrame, TopologicalSpace.Opens.coe_himp, TopologicalSpace.Opens.gi, TopologicalSpace.Closeds.coe_sSup, TopologicalSpace.Closeds.complOrderIso, TopologicalSpace.Clopens.instBooleanAlgebra, TopologicalSpace.Opens.isBasis_iff_nbhd]
  E1: auto
families: []
requires: [V01, V04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The lattices of open and closed sets

### Overview

Section 1 treats an open set as a set `s : Set X` together with a proof of `IsOpen s`. For many purposes it is better to have a type whose elements are the open sets. The type `TopologicalSpace.Opens X` is this type. Its elements carry their openness, so a function that takes an open set needs no separate hypothesis, and the order on the type is the order of the lattice of open sets. The same idea gives the types `TopologicalSpace.Closeds X` of closed sets, `TopologicalSpace.Clopens X` of clopen sets and `TopologicalSpace.IrreducibleCloseds X` of irreducible closed sets.

These types matter in three places. Sheaf theory and algebraic geometry index presheaves by `Opens X`. The theory of locales, or pointless topology, studies the frame of open sets in place of the space. Stone duality studies the Boolean algebra of clopen sets. This section describes the four modules `Mathlib.Topology.Sets.Opens`, `Mathlib.Topology.Sets.Closeds`, `Mathlib.Topology.Sets.Order` and `Mathlib.Topology.Sets.OpenCover`. It uses the complete lattices of Volume 4.

### The library around it

#### The type of open sets

A term of `TopologicalSpace.Opens X` is a structure with a carrier set and a proof that the carrier is open. The type is a `SetLike` type, so an open set $U$ coerces to `↑U : Set X`, and `x ∈ U` means `x ∈ ↑U`. The extensionality lemma `TopologicalSpace.Opens.ext` says that two open sets with the same carrier are equal. The instance `TopologicalSpace.Opens.instCanLiftSetCoeIsOpen` lets the tactic lift turn a set $s$ with `IsOpen s` into a term of `Opens X`.

The order on `Opens X` is inclusion. With this order, `Opens X` is a complete lattice, `TopologicalSpace.Opens.instCompleteLattice`, and the operations have these carriers.

| Lean name | Statement |
|---|---|
| `TopologicalSpace.Opens.coe_top` | $\uparrow\top = X$ |
| `TopologicalSpace.Opens.coe_bot` | $\uparrow\bot = \emptyset$ |
| `TopologicalSpace.Opens.coe_sup` | $\uparrow(U \sqcup V) = U \cup V$ |
| `TopologicalSpace.Opens.coe_inf` | $\uparrow(U \sqcap V) = U \cap V$ |
| `TopologicalSpace.Opens.coe_iSup` | $\uparrow(\bigsqcup_i U_i) = \bigcup_i U_i$ |
| `TopologicalSpace.Opens.coe_sSup` | $\uparrow(\mathrm{sSup}\ S) = \bigcup_{U \in S} U$ |
| `TopologicalSpace.Opens.coe_iInf` | $\uparrow(\bigsqcap_i U_i) = \bigcap_i U_i$ for a finite index type |
| `TopologicalSpace.Opens.coe_himp` | $\uparrow(U \Rightarrow V) = \mathrm{int}(U^c \cup V)$ |
| `TopologicalSpace.Opens.coe_compl_eq_interior_compl` | $\uparrow(U^c) = \mathrm{int}(X \setminus U)$ |

The supremum is the union, because a union of open sets is open. The infimum of an infinite family is not the intersection, because an infinite intersection of open sets need not be open. It is the interior of the intersection, the largest open set inside each $U_i$. So `TopologicalSpace.Opens.coe_iInf` needs a finite index type. Membership has the same pattern: `TopologicalSpace.Opens.mem_iSup` and `TopologicalSpace.Opens.mem_sSup` give the union, and `TopologicalSpace.Opens.mem_inf` the intersection.

The map from sets to open sets is the interior, `TopologicalSpace.Opens.interior`, with `TopologicalSpace.Opens.coe_interior`. The coercion and the interior form a Galois connection: $\uparrow U \subseteq s$ if and only if $U \le \mathrm{int}(s)$. This is `TopologicalSpace.Opens.gc`. The proof is the universal property of the interior: it is the largest open subset of $s$. Since the interior of an open set is itself, the connection is a Galois coinsertion, `TopologicalSpace.Opens.gi`. A Galois coinsertion transfers the complete lattice structure from `Set X` to `Opens X`, and this is how the library builds the instance.

#### The frame of open sets

A frame is a complete lattice in which finite meets distribute over arbitrary joins:

$$U \sqcap \bigsqcup_i V_i = \bigsqcup_i (U \sqcap V_i).$$

The lattice `Opens X` is a frame, `TopologicalSpace.Opens.instFrame`. The proof is one line: both sides have the carrier $U \cap \bigcup_i V_i = \bigcup_i (U \cap V_i)$, by the distributive law of sets. A frame has a Heyting implication, the largest $W$ with $U \sqcap W \le V$. In `Opens X` it is the interior of $U^c \cup V$, by `TopologicalSpace.Opens.coe_himp`. The complement $U^c = U \Rightarrow \bot$ is the interior of $X \setminus U$, the largest open set disjoint from $U$. So `Opens X` is a Heyting algebra, and in general not a Boolean algebra: in $\mathbb{R}$, $U = (0, \infty)$ has $U^c = (-\infty, 0)$ and $U \sqcup U^c \ne \top$.

A continuous map $f : X \to Y$ gives `TopologicalSpace.Opens.comap f`, the preimage map $\mathrm{Opens}\ Y \to \mathrm{Opens}\ X$. It is a frame homomorphism: it keeps finite meets and all joins. The lemmas `TopologicalSpace.Opens.coe_comap`, `TopologicalSpace.Opens.comap_id` and `TopologicalSpace.Opens.comap_comp` say that it is the preimage and that it is functorial, in the contravariant direction. The frame homomorphism `TopologicalSpace.Opens.frameHom` is the coercion to `Set X`. A homeomorphism $h$ gives the order isomorphism `Homeomorph.opensCongr h`.

The element $U$ of a complete lattice is compact if each cover of $U$ by a join has a finite subcover. The lemma `TopologicalSpace.Opens.isCompactElement_iff` says that an open set is a compact element of `Opens X` if and only if it is a compact set. So the order theory of frames recovers compactness.

#### Bases and open covers

A family $B$ of open sets is a basis, `TopologicalSpace.Opens.IsBasis B`, if its carriers form a topological basis in the sense of Section 2. The lemma `TopologicalSpace.Opens.isBasis_iff_nbhd` gives the local form: for each open $U$ and $x \in U$, there is $U' \in B$ with $x \in U' \le U$. The lemma `TopologicalSpace.Opens.isBasis_iff_cover` gives the lattice form: each open $U$ is the supremum of a subfamily of $B$. These two forms agree. If each point of $U$ has a basic set $U'_x$ inside $U$, then $U$ is the union of the $U'_x$. Conversely, if $U = \bigcup B'$ with $B' \subseteq B$, then a point of $U$ lies in some member of $B'$.

For a basis of compact open sets, `TopologicalSpace.Opens.IsBasis.isCompact_open_iff_eq_finite_iUnion` says that the compact open sets are the finite unions of basic sets. This is the first step to spectral spaces in Chapter 10.

The module `Mathlib.Topology.Sets.OpenCover` defines `TopologicalSpace.IsOpenCover u` for a family `u : ι → Opens X`: the supremum of the family is $\top$, by `TopologicalSpace.IsOpenCover.iSup_eq_top`. Each point then has a member of the cover as a neighbourhood, `TopologicalSpace.IsOpenCover.exists_mem_nhds`. The preimage of an open cover under a continuous map is an open cover, `TopologicalSpace.IsOpenCover.comap`. A compact space has a finite subcover, `TopologicalSpace.IsOpenCover.exists_finite_of_compactSpace`. The lemma `TopologicalSpace.IsOpenCover.isTopologicalBasis` glues bases of the members of a cover into a basis of $X$.

#### Closed sets and clopen sets

The module `Mathlib.Topology.Sets.Closeds` treats closed sets in the same way. The type `TopologicalSpace.Closeds X` is a complete lattice under inclusion. Now the infimum is the intersection, `TopologicalSpace.Closeds.coe_iInf` and `TopologicalSpace.Closeds.coe_sInf`, for any family. The finite supremum is the union, `TopologicalSpace.Closeds.coe_sup`, but the infinite supremum is the closure of the union:

$$\uparrow(\mathrm{sSup}\ S) = \overline{\textstyle\bigcup_{F \in S} F},$$

by `TopologicalSpace.Closeds.coe_sSup`. The map from sets is `TopologicalSpace.Closeds.closure`, and the closure and the coercion form a Galois insertion, `TopologicalSpace.Closeds.gi`. The lattice is a coframe, `TopologicalSpace.Closeds.instCoframe`, the order dual of a frame.

Complement gives an order isomorphism `TopologicalSpace.Closeds.complOrderIso` from `Closeds X` to the order dual of `Opens X`. The functions `TopologicalSpace.Closeds.compl` and `TopologicalSpace.Opens.compl` are the two directions, with `TopologicalSpace.Closeds.compl_compl` and `TopologicalSpace.Opens.compl_compl`. In a $T_1$ space, singletons are closed, and `TopologicalSpace.Closeds.isAtom_iff` says that the atoms of `Closeds X` are the singletons. Dually, `TopologicalSpace.Opens.isCoatom_iff` says that the coatoms of `Opens X` are the complements of points.

The type `TopologicalSpace.Clopens X` holds the sets that are closed and open. Here the complement of a clopen set is clopen, so `TopologicalSpace.Clopens.instBooleanAlgebra` makes `Clopens X` a Boolean algebra, with `TopologicalSpace.Clopens.coe_sup`, `TopologicalSpace.Clopens.coe_inf` and `TopologicalSpace.Clopens.coe_compl`. Only finite operations exist, since an infinite union of clopen sets need not be closed. The product of two clopen sets is clopen, through the instance `TopologicalSpace.Clopens.instSProdProd`. The maps `TopologicalSpace.Clopens.toOpens` and `TopologicalSpace.Clopens.toCloseds` forget one half of the property.

The type `TopologicalSpace.IrreducibleCloseds X` holds the irreducible closed sets. A continuous map sends an irreducible closed set to one, by the closure of its image, `TopologicalSpace.IrreducibleCloseds.map`. The order isomorphism `TopologicalSpace.IrreducibleCloseds.orderIsoSubtype` identifies the type with the subtype of sets that are irreducible and closed. This type is the set of points of the sober space of Chapter 10.

#### Clopen upper sets and open neighbourhoods

The module `Mathlib.Topology.Sets.Order` defines `ClopenUpperSet X` for a topological space with an order: the clopen sets that are upper sets, with `ClopenUpperSet.upper` and `ClopenUpperSet.isClopen`. They form a bounded lattice, `ClopenUpperSet.instBoundedOrder` and `ClopenUpperSet.instLattice`. These sets are the elements of the dual lattice in Priestley duality, which Chapter 10 describes.

The type `TopologicalSpace.OpenNhdsOf x` in `Mathlib.Topology.Sets.Opens` holds the open sets that contain a fixed point $x$. It is a distributive lattice with a top element, and `TopologicalSpace.OpenNhdsOf.basis_nhds` says that its members form a basis of $\mathcal{N}(x)$. It is the index category for the stalk of a sheaf at $x$.

#### Common errors

1. The infimum of an infinite family in `Opens X` is the interior of the intersection, not the intersection. `TopologicalSpace.Opens.coe_iInf` needs a finite index type. The same warning holds for the supremum in `Closeds X`, which is the closure of the union.
2. `Opens X` is a Heyting algebra, not a Boolean algebra. The complement $U^c$ of an open set in `Opens X` is the interior of the set complement, and `U ⊔ Uᶜ = ⊤` fails in general.
3. `TopologicalSpace.Opens.comap` goes in the direction opposite to the map. A map $X \to Y$ gives a frame homomorphism from `Opens Y` to `Opens X`, and it needs a bundled continuous map `C(X, Y)`.

### Exercises

1. (A) Prove `TopologicalSpace.Opens.coe_sup` and `TopologicalSpace.Opens.coe_inf` from the definitions.
2. (A) In $\mathbb{R}$, compute the infimum in `Opens ℝ` of the family $U_n = (-1/n, 1/n)$.
3. (B) Prove that `Opens X` is a frame, and compute the Heyting implication $U \Rightarrow V$.
4. (B) Show that `Opens X` is a Boolean algebra if and only if each open set of $X$ is closed.
5. (B) Prove that a family $B$ of open sets is a basis if and only if each open set is a join of members of $B$, as in `TopologicalSpace.Opens.isBasis_iff_cover`.
6. (C) Prove `TopologicalSpace.Opens.isCompactElement_iff`: an open set is a compact element of the frame `Opens X` if and only if it is a compact subset of $X$.

### Reference

<?reference?>
