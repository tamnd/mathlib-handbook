---
title: Blocks, primitive actions and the Iwasawa criterion
kind: api
modules:
  - Mathlib.GroupTheory.GroupAction.Blocks
  - Mathlib.GroupTheory.GroupAction.Primitive
  - Mathlib.GroupTheory.GroupAction.Iwasawa
explains:
  E2: [MulAction.IsBlock, MulAction.IsBlock.ncard_block_mul_ncard_orbit_eq, MulAction.block_stabilizerOrderIso, MulAction.isCoatom_stabilizer_iff_preprimitive, MulAction.IsPreprimitive.of_prime_card, MulAction.IsBlockSystem.of_normal, MulAction.IsPreprimitive.isQuasiPreprimitive, MulAction.IwasawaStructure.commutator_le, MulAction.IwasawaStructure.isSimpleGroup]
  E1: auto
families: []
requires: [V01, V05.C03, V05.C04, V05.C05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Blocks, primitive actions and the Iwasawa criterion

### Overview

Let a group $G$ act transitively on a set $X$. A block is a subset $B$ of $X$ such that each translate $g \cdot B$ is equal to $B$ or disjoint from $B$. When $B$ is a block, its translates cut $X$ into pieces of the same size, and $G$ permutes these pieces. So the action of $G$ on $X$ is built from an action on the set of pieces and actions inside the pieces. The action is primitive when the only blocks are the trivial ones: the empty set, the points and $X$ itself. Primitive actions are the atoms of the theory of permutation groups.

These modules hold the definitions of blocks and block systems, the dictionary between blocks that contain a point $a$ and subgroups that contain the stabilizer of $a$, and the classes `MulAction.IsPreprimitive` and `MulAction.IsQuasiPreprimitive`. The last module proves the Iwasawa criterion, a standard tool to prove that a group is simple. The section uses orbits and stabilizers from Section 1 of this chapter, the index of a subgroup from Chapter 4, and normal subgroups from Chapter 5.

### The library around it

#### Blocks

The definition `MulAction.IsBlock` says that for all $g_1, g_2 \in G$, the sets $g_1 \cdot B$ and $g_2 \cdot B$ are equal or disjoint. It only needs a `SMul G X`, so it applies also to monoid actions. For a group action, the condition with one translate is enough. The library gives the main equivalent forms as `iff` lemmas, each with a matching projection on `MulAction.IsBlock`:

| Lean name | Statement |
| --- | --- |
| `MulAction.isBlock_iff_smul_eq_or_disjoint` | $B$ is a block if and only if, for each $g$, $g \cdot B = B$ or $g \cdot B \cap B = \emptyset$ |
| `MulAction.isBlock_iff_smul_eq_of_nonempty` | $B$ is a block if and only if $g \cdot B \cap B \neq \emptyset$ implies $g \cdot B = B$ |
| `MulAction.isBlock_iff_smul_eq_of_mem` | $B$ is a block if and only if $a \in B$ and $g \cdot a \in B$ imply $g \cdot B = B$ |
| `MulAction.isBlock_iff_disjoint_smul_of_ne` | $B$ is a block if and only if $g \cdot B \neq B$ implies that $g \cdot B$ and $B$ are disjoint |
| `MulAction.isBlock_iff_pairwiseDisjoint_range_smul` | $B$ is a block if and only if the translates of $B$ are pairwise disjoint as a family of sets |

The projections are `MulAction.IsBlock.smul_eq_or_disjoint`, `MulAction.IsBlock.smul_eq_of_nonempty` and `MulAction.IsBlock.smul_eq_of_mem`. Three stronger notions sit next to blocks. A trivial block, `MulAction.IsTrivialBlock`, is a set that is a subsingleton or equal to `Set.univ`. A fixed block, `MulAction.IsFixedBlock`, satisfies $g \cdot B = B$ for all $g$. An invariant block, `MulAction.IsInvariantBlock`, satisfies $g \cdot B \subseteq B$ for all $g$. For a group action, `MulAction.isInvariantBlock_iff_isFixedBlock` shows that the last two agree, and `MulAction.IsFixedBlock.isBlock` and `MulAction.IsTrivialBlock.isBlock` show that both kinds are blocks.

The first examples are `MulAction.IsBlock.empty`, `MulAction.IsBlock.singleton`, `MulAction.IsBlock.univ`, and `MulAction.IsBlock.orbit`: an orbit is a fixed block. Blocks are closed under translation (`MulAction.IsBlock.translate`), intersection (`MulAction.IsBlock.inter`, `MulAction.IsBlock.iInter`), restriction to a subgroup (`MulAction.IsBlock.subgroup`) and preimage under an equivariant map (`MulAction.IsBlock.preimage`). A block of $G$ is also a block of every subgroup, but not conversely.

Two families of blocks come from subgroups. If $G_a \le H$, where $G_a$ is the stabilizer of $a$, then the orbit $H \cdot a$ is a block (`MulAction.IsBlock.of_orbit`), and its stabilizer is $H$ (`MulAction.stabilizer_orbit_eq`). If $N$ is a normal subgroup, then each orbit of $N$ is a block (`MulAction.IsBlock.orbit_of_normal`). In the other direction, if $B$ is a block and $a \in B$, then $G_a \le G_B$, where $G_B$ is the stabilizer of the set $B$ (`MulAction.IsBlock.stabilizer_le`).

#### Block systems and counting

A block system, `MulAction.IsBlockSystem`, is a set of blocks that is a partition of $X$ in the sense of `Setoid.IsPartition`. For a transitive action and a nonempty block $B$, the translates of $B$ form a block system (`MulAction.IsBlock.isBlockSystem`). For a normal subgroup $N$, the orbits of $N$ form a block system (`MulAction.IsBlockSystem.of_normal`). The proof of the second fact: the orbits of any action partition $X$ (`MulAction.IsPartition.of_orbits`), and for $g \in G$ the normality of $N$ gives $g \cdot (N \cdot a) = N \cdot (g \cdot a)$ (`MulAction.smul_orbit_eq_orbit_smul`). So a translate of an orbit of $N$ is again an orbit of $N$, and two orbits are equal or disjoint.

Let $X$ be finite, let the action be transitive and let $B$ be a nonempty block. Then the translates of $B$ partition $X$, they all have $|B|$ elements, and transitivity shows that each point lies in one of them. So $|B| \cdot |G \cdot B| = |X|$, where $G \cdot B$ is the orbit of $B$ in the set of subsets. This is `MulAction.IsBlock.ncard_block_mul_ncard_orbit_eq`, and its consequence `MulAction.IsBlock.ncard_dvd_card` says that $|B|$ divides $|X|$. The lemma `MulAction.IsBlock.ncard_block_eq_relIndex` gives $|B|$ as the relative index of $G_x$ in $G_B$ for $x \in B$. The sizes use `Set.ncard` and `Nat.card`, so they are $0$ for infinite sets.

#### Blocks and subgroups

Fix a point $a$ of a transitive action. The blocks that contain $a$ form the type `MulAction.BlockMem`, with the order of inclusion. The map $B \mapsto G_B$ is an order isomorphism from these blocks to the subgroups $H$ with $G_a \le H$. This is `MulAction.block_stabilizerOrderIso`. Its inverse sends $H$ to the orbit $H \cdot a$. The two lemmas above give the proof: $G_a \le G_B$ for a block $B$ that contains $a$, the orbit $H \cdot a$ is a block with stabilizer $H$, and transitivity gives $G_B \cdot a = B$ (`MulAction.IsBlock.orbit_stabilizer_eq`).

Under this isomorphism the trivial blocks $\{a\}$ and $X$ go to $G_a$ and $G$. So the action has no nontrivial block that contains $a$ if and only if $G_a$ is a maximal subgroup.

#### Primitive actions

The class `MulAction.IsPreprimitive` holds when the action is pretransitive and every block is trivial (`MulAction.IsPreprimitive.isTrivialBlock_of_isBlock`). The prefix "pre" means that the definition allows the empty set, in the same way as `MulAction.IsPretransitive`. A shorter test is `MulAction.IsPreprimitive.of_isTrivialBlock_base`: it is enough to check the blocks that contain one point $a$. With the order isomorphism above, this gives `MulAction.isCoatom_stabilizer_iff_preprimitive`: for a transitive action on a set with at least two points, the action is primitive if and only if the stabilizer of a point is a coatom, that is, a maximal subgroup. The lemma `MulAction.isSimpleOrder_blockMem_iff_isPreprimitive` states the same fact on the side of blocks.

Some tests for primitivity:

1. If $|X|$ is a prime $p$, a transitive action is primitive (`MulAction.IsPreprimitive.of_prime_card`). Proof: the size of a nonempty block divides $p$, so it is $1$ or $p$.
2. If $|X| \le 2$, every subset is a trivial block (`MulAction.isTrivialBlock_of_card_le_two`).
3. Primitivity goes along a surjective equivariant map (`MulAction.IsPreprimitive.of_surjective`), and `MulAction.isPreprimitive_congr` gives the equivalence for a bijective equivariant map with a surjective map of groups.
4. `MulAction.IsPreprimitive.of_card_lt` uses `MulAction.IsBlock.subsingleton_of_card_lt`: a block with more than $|X|/2$ translates is a subsingleton.

A primitive action separates points by translates of a finite set: `MulAction.IsPreprimitive.exists_mem_smul_and_notMem_smul` says that if $A$ is finite, nonempty and not all of $X$, then for $a \neq b$ there is $g$ with $a \in g \cdot A$ and $b \notin g \cdot A$.

#### Quasiprimitive actions

The class `MulAction.IsQuasiPreprimitive` holds when the action is pretransitive and every normal subgroup that acts nontrivially is transitive. The field `MulAction.IsQuasiPreprimitive.isPretransitive_of_normal` states this, with the condition `MulAction.fixedPoints N X ≠ Set.univ` for "acts nontrivially". The instance `MulAction.IsPreprimitive.isQuasiPreprimitive` shows that a primitive action is quasiprimitive. Proof: the orbits of a normal subgroup $N$ are blocks. In a primitive action they are points or all of $X$. If they are all points, $N$ fixes every point. Otherwise one orbit is $X$, and $N$ is transitive.

#### The Iwasawa criterion

An Iwasawa structure, `MulAction.IwasawaStructure`, attaches to each point $x$ a subgroup `T x` of $G$. The subgroups are commutative (`MulAction.IwasawaStructure.is_comm`), they move with the action, $T(g \cdot x) = g\, T(x)\, g^{-1}$ (`MulAction.IwasawaStructure.is_conj`, with `MulAut.conj`), and together they generate $G$ (`MulAction.IwasawaStructure.is_generator`).

The first form of the criterion is `MulAction.IwasawaStructure.commutator_le`: if the action is quasiprimitive and $N$ is a normal subgroup that acts nontrivially, then the commutator subgroup `commutator G` is contained in $N$. Proof sketch: $N$ is transitive, so $G = N G_a$ for a point $a$. Then each conjugate $g T(a) g^{-1}$ with $g = n h$, $h \in G_a$, is equal to $n T(a) n^{-1}$, because $T(h \cdot a) = T(a)$. So $G$ is generated by $N$ and $T(a)$, and $N T(a)$ is a subgroup since $N$ is normal. Hence $G/N$ is an image of the commutative group $T(a)$, and the commutators lie in $N$.

The second form is `MulAction.IwasawaStructure.isSimpleGroup`: if also $G$ is nontrivial, the action is faithful (`FaithfulSMul`), and $G$ is perfect, `commutator G = ⊤`, then $G$ is simple. Proof: a normal subgroup $N \neq 1$ acts nontrivially by faithfulness, so it contains `commutator G`, which is $G$. A standard use is the simplicity of $\mathrm{PSL}_n(K)$, with the action on the points of projective space and the subgroups of transvections with a given center.

#### Common errors

1. `MulAction.IsBlock` takes the group as an explicit argument, `MulAction.IsBlock G B`, while the set is the only explicit argument of `MulAction.IsTrivialBlock B`. A block for a subgroup $H$ is written `MulAction.IsBlock H B` with $H$ coerced to a type, and it is a weaker condition than `MulAction.IsBlock G B`.
2. `MulAction.IsPreprimitive` contains `MulAction.IsPretransitive` and allows the empty type. Statements that need two points, such as `MulAction.isCoatom_stabilizer_iff_preprimitive`, carry a separate `Nontrivial X` hypothesis.
3. The counting lemmas use `Set.ncard` and `Nat.card`, which are $0$ for infinite sets. The divisibility `MulAction.IsBlock.ncard_dvd_card` is then true but empty of content, so check the finiteness hypotheses before an argument by size.

### Exercises

1. (A) Let $G$ be the dihedral group of order $8$ acting on the four vertices of a square. Show that the pairs of opposite vertices are blocks, and deduce that the action is not primitive.
2. (A) Show that the intersection of two blocks that contain a common point $a$ is a block that contains $a$, and give the corresponding statement about subgroups that contain $G_a$.
3. (B) Show that a transitive action of a group $G$ on a finite set $X$ with $|X| \ge 2$ and $G$ commutative is primitive if and only if $|X|$ is prime.
4. (B) Let $G$ act primitively and faithfully on $X$, and let $N \neq 1$ be a normal subgroup. Show that $N$ is transitive. Then show that if $N$ is commutative, it acts regularly, that is, its stabilizers are trivial.
5. (B) Use `MulAction.IwasawaStructure.commutator_le` to show: if $G$ has an Iwasawa structure for a quasiprimitive action, and $N$ is a normal subgroup that acts nontrivially, then $G/N$ is commutative.
6. (C) Show that the action of $S_n$ on the set of $2$-element subsets of $\{1, \dots, n\}$ is primitive for $n \ge 5$. Hint: compute the stabilizer of a pair and show that it is a maximal subgroup.

### Reference

<?reference?>
