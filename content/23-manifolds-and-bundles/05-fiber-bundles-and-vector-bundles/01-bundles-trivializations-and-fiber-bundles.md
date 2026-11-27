---
title: Bundles, trivializations and fiber bundles
kind: theory
modules:
  - Mathlib.Data.Bundle
  - Mathlib.Topology.FiberBundle.Trivialization
  - Mathlib.Topology.FiberBundle.Basic
  - Mathlib.Topology.FiberBundle.Constructions
  - Mathlib.Topology.FiberBundle.IsHomeomorphicTrivialBundle
explains:
  E3: [Bundle.TotalSpace, Bundle.Trivialization, FiberBundle, FiberBundleCore]
  E2: [Bundle.TotalSpace.proj, Bundle.TotalSpace.mk', Bundle.Trivial, Bundle.Pullback, Bundle.pullbackTotalSpaceEmbedding, Bundle.Pretrivialization, Bundle.Trivialization.source_eq, Bundle.Trivialization.target_eq, Bundle.Trivialization.proj_toFun, Bundle.Trivialization.mk_proj_snd, Bundle.Trivialization.coordChange, Bundle.Trivialization.coordChangeHomeomorph, FiberBundle.trivializationAt, MemTrivializationAtlas, FiberBundle.mem_trivializationAt_proj_source, FiberBundle.totalSpaceMk_isInducing, FiberBundle.continuous_proj, FiberBundle.isOpenMap_proj, FiberBundle.isQuotientMap_proj, FiberBundle.surjective_proj, FiberBundle.t2Space, FiberBundleCore.Fiber, FiberBundleCore.localTriv, FiberBundleCore.localTriv_apply, FiberBundleCore.trivChange, FiberBundleCore.fiberBundle, FiberPrebundle, FiberPrebundle.toFiberBundle, Bundle.Trivial.fiberBundle, Bundle.Trivial.homeomorphProd, Bundle.Trivialization.prod, FiberBundle.prod, Bundle.Trivialization.pullback, FiberBundle.pullback, IsHomeomorphicTrivialFiberBundle]
  E1: auto
families: []
requires: [V23.C02, V23.C03, V23.C04, V13.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Bundles, trivializations and fiber bundles

### Overview

The total space of a family $(E_b)_{b \in B}$ is the set of pairs $(b, v)$ with $v \in E_b$, with the projection $(b, v) \mapsto b$. A fiber bundle with fiber $F$ is such a total space with a topology for which each point of $B$ has a neighbourhood $U$ over which the total space is homeomorphic to $U \times F$, compatibly with the projections. These homeomorphisms are the trivializations.

This section defines total spaces, trivializations and fiber bundles. It proves that the projection is continuous and open and that changes of trivializations are homeomorphisms of the fiber. Its main theorem constructs a fiber bundle from an open cover of the base and transition functions that satisfy the cocycle condition. The examples are the trivial bundle, products, pullbacks and the Möbius band.

### Definitions

Let $B$ and $F$ be topological spaces and $E : B \to \mathrm{Type}$ a family of types.

**Definition (Total space).** The total space of $E$ is the set $\mathrm{Tot}(E)$ of pairs $(b, v)$ with $b \in B$ and $v \in E_b$. Its projection is $\pi(b, v) = b$. The trivial family over $B$ with fiber $F$ has $E_b = F$ for all $b$. The pullback of $E$ along $f : B' \to B$ is the family $(f^*E)_{b'} = E_{f(b')}$.

**Definition (Trivialization).** Let $Z$ be a topological space and $\pi : Z \to B$. A trivialization of $\pi$ with fiber $F$ consists of an open set $U \subseteq B$, the base set, and a homeomorphism
$$e : \pi^{-1}(U) \to U \times F$$
with $\mathrm{pr}_1 \circ e = \pi$ on $\pi^{-1}(U)$. A pretrivialization is the same without topology on $Z$: a bijection with these properties.

**Definition (Fiber bundle).** Let $\mathrm{Tot}(E)$ and each fiber $E_b$ carry topologies. Then $E$ is a fiber bundle with fiber $F$ if

1. for each $b$, the map $E_b \to \mathrm{Tot}(E)$, $v \mapsto (b, v)$, is an inducing map, so that $E_b$ has the topology of a subspace;
2. there is a set of trivializations of $\pi$ with fiber $F$, the atlas, and for each $b \in B$ a chosen trivialization in the atlas whose base set contains $b$.

**Definition (Coordinate change).** Let $e$ and $e'$ be trivializations with base sets $U$ and $U'$, and let $b \in U \cap U'$. The coordinate change from $e$ to $e'$ at $b$ is the map $g_{e e'}(b) : F \to F$ with
$$e'(e^{-1}(b, y)) = (b, g_{e e'}(b)(y)).$$

**Definition (Fiber bundle core).** A fiber bundle core with fiber $F$ over $B$ consists of an index set $\iota$, open sets $U_i \subseteq B$ for $i \in \iota$, a map $b \mapsto i(b)$ with $b \in U_{i(b)}$, and maps $g_{ij} : B \to F \to F$ such that

1. $g_{ii}(b)(v) = v$ for $b \in U_i$;
2. $(b, v) \mapsto g_{ij}(b)(v)$ is continuous on $(U_i \cap U_j) \times F$;
3. $g_{jk}(b)(g_{ij}(b)(v)) = g_{ik}(b)(v)$ for $b \in U_i \cap U_j \cap U_k$, the cocycle condition.

::: mathlib
`Bundle.TotalSpace` · `Mathlib.Data.Bundle`

`Bundle.TotalSpace F E` is a structure with two fields, `proj : B` and `snd : E proj`, a sigma type. The argument `F` plays no role in the set. It is there so that instances of topology on the total space can depend on the model fiber. `Bundle.Trivialization F proj` extends `OpenPartialHomeomorph Z (B × F)` of Chapter 1 with `baseSet`, `source_eq`, `target_eq` and `proj_toFun`. The class `FiberBundle F E` holds data: the atlas `trivializationAtlas'` and the choice `trivializationAt'`. The trivialization at $b$ is `FiberBundle.trivializationAt F E b`.

<?decl Bundle.TotalSpace?>
<?decl Bundle.Trivialization?>
<?decl FiberBundle?>
<?decl FiberBundleCore?>
:::

### Theorems and proofs

**Theorem (The projection).** Let $E$ be a fiber bundle. Then $\pi : \mathrm{Tot}(E) \to B$ is continuous and open. If $F$ is nonempty, $\pi$ is surjective and a quotient map.

*Proof.* Let $e$ be a trivialization with base set $U$. Its source $\pi^{-1}(U)$ is open, and on it $\pi = \mathrm{pr}_1 \circ e$, a composition of continuous maps. The sources of the chosen trivializations cover $\mathrm{Tot}(E)$, because the trivialization at $b$ contains the whole fiber over $b$. Continuity is local, so $\pi$ is continuous.

Let $V \subseteq \mathrm{Tot}(E)$ be open. Then $\pi(V)$ is the union over the chosen trivializations $e$ of $\pi(V \cap \pi^{-1}(U_e)) = \mathrm{pr}_1(e(V \cap \pi^{-1}(U_e)))$. The set $e(V \cap \pi^{-1}(U_e))$ is open in $U_e \times F$, which is open in $B \times F$, and $\mathrm{pr}_1$ is an open map. So $\pi(V)$ is open.

If $F$ has a point $y$, then $e_b^{-1}(b, y)$ lies over $b$, so $\pi$ is surjective. A continuous open surjection is a quotient map. $\square$

**Theorem (Coordinate changes).** Let $e, e'$ be trivializations with base sets $U, U'$. Then $(b, y) \mapsto g_{e e'}(b)(y)$ is continuous on $(U \cap U') \times F$, and for each $b \in U \cap U'$ the map $g_{e e'}(b)$ is a homeomorphism of $F$ with inverse $g_{e' e}(b)$.

*Proof.* The map $h = e' \circ e^{-1}$ is a homeomorphism from $(U \cap U') \times F$ onto itself, as a composition of restrictions of homeomorphisms. It preserves the first coordinate, since both $e$ and $e'$ commute with the projections. So $h(b, y) = (b, g_{e e'}(b)(y))$, and $g_{e e'} = \mathrm{pr}_2 \circ h$ is continuous. The inverse of $h$ is $e \circ e'^{-1}$, which gives $g_{e' e}(b) \circ g_{e e'}(b) = \mathrm{id}_F$ and the other composition. Each $g_{e e'}(b)$ is the restriction of a continuous map to the slice $\{b\} \times F$, so it is continuous, and so is its inverse. $\square$

The coordinate changes of a fiber bundle satisfy the three conditions of a core. The next theorem is the converse.

**Theorem (Construction from a core).** Let $(U_i, i(\cdot), g_{ij})$ be a fiber bundle core with fiber $F$, and let $E_b = F$ for all $b$. There is a topology on $\mathrm{Tot}(E)$ such that for each $i$ the map
$$T_i(b, v) = (b, g_{i(b) i}(b)(v)), \qquad b \in U_i,$$
is a trivialization over $U_i$. With these trivializations $E$ is a fiber bundle.

*Proof.* Step 1: $T_i$ is a bijection from $\pi^{-1}(U_i)$ to $U_i \times F$. Its candidate inverse is $S_i(b, w) = (b, g_{i\, i(b)}(b)(w))$. For $b \in U_i$, the point $b$ lies in $U_{i(b)} \cap U_i$. The cocycle condition for the indices $(i(b), i, i(b))$ and condition 1 give $g_{i\, i(b)}(b)(g_{i(b) i}(b)(v)) = g_{i(b) i(b)}(b)(v) = v$, so $S_i \circ T_i = \mathrm{id}$. The indices $(i, i(b), i)$ give $T_i \circ S_i = \mathrm{id}$.

Step 2: the changes. For $b \in U_i \cap U_j$, the cocycle condition for $(i, i(b), j)$ gives
$$T_j(S_i(b, w)) = (b, g_{i(b) j}(b)(g_{i\, i(b)}(b)(w))) = (b, g_{ij}(b)(w)).$$
So $T_j \circ S_i$ is continuous on $(U_i \cap U_j) \times F$ by condition 2.

Step 3: the topology. Give $\mathrm{Tot}(E)$ the topology generated by the sets $T_i^{-1}(W)$, for all $i$ and all open $W \subseteq U_i \times F$. Then each $\pi^{-1}(U_i) = T_i^{-1}(U_i \times F)$ is open, and $T_i$ is continuous on it by definition. To show that $S_i$ is continuous, it suffices to show that $T_i(G \cap \pi^{-1}(U_i))$ is open for each generator $G = T_j^{-1}(W)$. This set is
$$\{(b, w) \in (U_i \cap U_j) \times F : T_j(S_i(b, w)) \in W\},$$
which is open by Step 2, because $(U_i \cap U_j) \times F$ is open. So $T_i$ is a homeomorphism onto $U_i \times F$, and $\mathrm{pr}_1 \circ T_i = \pi$.

Step 4: the fibers. Give $E_b = F$ its own topology. The map $v \mapsto T_{i(b)}(b, v) = (b, v)$ is a homeomorphism of $F$ onto the slice $\{b\} \times F$, so $v \mapsto (b, v)$ is inducing. Take the $T_i$ as the atlas and $T_{i(b)}$ as the trivialization at $b$. $\square$

A fiber bundle core gives the fibers the type $F$ itself. Mathlib does not form the disjoint union of the sets $U_i \times F$ and divide by the gluing relation. The total space is the sigma type, and only its topology comes from the core.

### Examples

**Example (The trivial bundle).** For $E_b = F$, the total space is $B \times F$ as a set. With the product topology, the identity is a trivialization over $B$, and $E$ is a fiber bundle with an atlas of one element.

**Example (Products).** Let $E_1, E_2$ be fiber bundles over $B$ with fibers $F_1, F_2$. The family $b \mapsto E_{1,b} \times E_{2,b}$ is a fiber bundle with fiber $F_1 \times F_2$. A trivialization over $U_1 \cap U_2$ is $(b, (v, w)) \mapsto (b, (e_1(b, v)_2, e_2(b, w)_2))$, where the index $2$ is the second coordinate. Its inverse uses $e_1^{-1}$ and $e_2^{-1}$ on the fibers.

**Example (Pullbacks).** Let $E$ be a fiber bundle over $B$ and $f : B' \to B$ continuous. The total space of $f^*E$ maps injectively to $B' \times \mathrm{Tot}(E)$ by $(b', v) \mapsto (b', (f(b'), v))$, and it gets the induced topology. For a trivialization $e$ over $U$, the map $(b', v) \mapsto (b', e(f(b'), v)_2)$ is a trivialization of $f^*E$ over $f^{-1}(U)$.

**Example (The Möbius band).** Let $B = S^1$, $F = \mathbb{R}$, $U_0 = S^1 \setminus \{1\}$ and $U_1 = S^1 \setminus \{-1\}$. The intersection $U_0 \cap U_1$ is the union of the open upper half $A_+$ and the open lower half $A_-$. Put $g_{00} = g_{11} = \mathrm{id}$, and $g_{01}(b) = g_{10}(b) = \mathrm{id}$ for $b \in A_+$, $g_{01}(b) = g_{10}(b) = -\mathrm{id}$ for $b \in A_-$. These maps are continuous on $(U_0 \cap U_1) \times \mathbb{R}$, since $A_+$ and $A_-$ are open. The cocycle condition holds because $(\pm 1)^2 = 1$. The theorem gives a fiber bundle, the Möbius band.

It is not homeomorphic to $S^1 \times \mathbb{R}$ over $S^1$. The zero section $z(b) = (b, 0)$ is well defined, since the $g_{ij}$ fix $0$. Over $U_0$ the complement of $z$ has the two connected parts $U_0 \times (0, \infty)$ and $U_0 \times (-\infty, 0)$ in the chart $T_0$, and over $U_1$ the same in $T_1$. Over $A_+$ the positive parts of the two charts meet, and over $A_-$ the positive part of $T_0$ meets the negative part of $T_1$. So the four parts form one connected set: the complement of $z$ is connected. In $S^1 \times \mathbb{R}$ the complement of the graph of any continuous section $s$ has the two disjoint open parts $\{t > s(b)\}$ and $\{t < s(b)\}$. A homeomorphism over $S^1$ sends $z$ to such a section and its complement to the complement, which is a contradiction.

### The library around it

::: mathlib
`FiberBundleCore.localTriv` · `Mathlib.Topology.FiberBundle.Basic`

`FiberBundleCore ι B F` has the fields `baseSet`, `isOpen_baseSet`, `indexAt`, `mem_baseSet_at`, `coordChange`, `coordChange_self`, `continuousOn_coordChange` and `coordChange_comp`. Its fibers are `Z.Fiber b`, which is `F`. The trivialization $T_i$ is `Z.localTriv i`, with formula `FiberBundleCore.localTriv_apply`, and the instance `FiberBundleCore.fiberBundle` is the theorem. `FiberPrebundle` and `FiberPrebundle.toFiberBundle` do the same from pretrivializations whose changes are continuous, when the fibers are not all equal to $F$.

<?decl FiberBundleCore.localTriv_apply?>
<?decl FiberPrebundle.toFiberBundle?>
<?decl FiberBundle.isOpenMap_proj?>
<?decl Bundle.Trivialization.coordChangeHomeomorph?>
:::

The constructions are instances in `Mathlib.Topology.FiberBundle.Constructions`: `Bundle.Trivial.fiberBundle`, `FiberBundle.prod` and `FiberBundle.pullback`. `FiberBundle.prod` asks for a zero in each fiber, because the inverse of a trivialization on a fiber outside the base set must return some value. `FiberBundle.pullback` asks for nonempty fibers and a map in `ContinuousMapClass`. The predicate `IsHomeomorphicTrivialFiberBundle F proj` says that a map is homeomorphic over $B$ to the projection $B \times F \to B$.

The documentation of `Mathlib.Topology.FiberBundle.Basic` explains the choices. The atlas is data in the class, not an existence statement, so that a bundle has one preferred trivialization at each point, as a manifold has one preferred chart. In infinite dimension, transition functions with values in the continuous linear maps need not be continuous for the operator norm, so a bundle is not just a cocycle. The fibers are declared to be types in advance, so that $T_xM$ is $E$ itself and no quotient is formed.

Common errors of a learner:

- Expecting `(e p).2` to make sense outside the source of `e`. A trivialization is a partial homeomorphism, with junk values outside its source.
- Confusing `Bundle.TotalSpace.mk b v` with a pair in `B × F`. Its second component has type `E b`.
- Forgetting that a fiber bundle core gives every fiber the type $F$. Two fibers $E_b$ and $E_{b'}$ are then the same type, and the type checker accepts sums of vectors in different fibers.

### Exercises

1. (A) Prove that the fibers $\pi^{-1}(b)$ of a fiber bundle are homeomorphic to $F$.
2. (A) Show that the coordinate change $g_{ee}(b)$ is the identity for $b$ in the base set of $e$.
3. (B) Let $E$ be a fiber bundle with fiber $F$. Show that if $B$ and $F$ are $T_2$, then the total space is $T_2$. Hint: separate two points in different fibers with $\pi$, and two points in the same fiber with one trivialization.
4. (B) Show that the pullback of the Möbius band along the map $z \mapsto z^2$ of $S^1$ is homeomorphic to $S^1 \times \mathbb{R}$ over $S^1$.
5. (B) Let $E$ be a fiber bundle over $B$ and $f : B' \to B$, $g : B'' \to B'$ continuous. Show that $g^* f^* E$ and $(f \circ g)^* E$ have the same fibers, and that the identity of their total spaces is a homeomorphism.
6. (C) Let $E$ be a fiber bundle over $[0, 1]$. Prove that $E$ is homeomorphic over $[0, 1]$ to $[0, 1] \times F$. Hint: use the Lebesgue number of the cover by base sets, and glue the trivializations over consecutive intervals by a coordinate change at the common point.

### Notes and history

The Möbius band is named after August Ferdinand Möbius. The book of Norman Steenrod on the topology of fibre bundles (1951) fixed the language of coordinate bundles with transition functions. The file header of `Mathlib.Topology.FiberBundle.Basic` names Sébastien Gouëzel, Floris van Doorn and Heather Macbeth as authors, and that of `Mathlib.Data.Bundle` names Nicolò Cavalleri.

### Reference

<?reference?>
