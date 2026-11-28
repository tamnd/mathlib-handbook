---
title: Directed sets, cofinal sets and antichains
kind: api
modules:
  - Mathlib.Order.Directed
  - Mathlib.Order.Cofinal
  - Mathlib.Order.Antichain
  - Mathlib.Order.DirectedInverseSystem
explains:
  E2: [directedOn_of_sup_mem, Monotone.directed_le, constant_of_monotone_antitone, isTop_iff_isMax, not_isCofinal_iff_bddAbove, isCofinal_range_of_strictMono, inter_subsingleton_of_isChain_of_isAntichain, setOfPred_maximal_antichain, DirectLimit.equivOfIsTop]
  E1: auto
families: []
requires: [V01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Directed sets, cofinal sets and antichains

### Overview

A set is *directed* when each two of its elements have a common upper bound in the set. Directed sets are the index sets of nets in topology, of direct limits in algebra and of the suprema in domain theory. A set is *cofinal* when each element of the order lies below some element of the set. An *antichain* is the opposite of a chain: a set where no two distinct elements are comparable. The three notions are short to state, but each has a large API, because Mathlib states them for an arbitrary relation and not only for `≤`.

The modules of this section hold this API. `Mathlib.Order.Directed` defines `Directed`, `DirectedOn` and the class `IsDirected`. `Mathlib.Order.Cofinal` gives the lemmas on `IsCofinal`, a predicate that `Mathlib.Order.Bounds.Defs` defines. `Mathlib.Order.Antichain` treats `IsAntichain` and its strong and weak variants. `Mathlib.Order.DirectedInverseSystem` uses directed orders to build the direct limit of a system of types, and constructs bijections in an inverse system by transfinite recursion. The section uses chains and maximal elements from the earlier sections of this chapter.

### The library around it

**Three forms of directedness.** Let $r$ be a relation on $\alpha$, written $x \preccurlyeq y$. Mathlib has three predicates.

| Lean name | Statement |
| --- | --- |
| `Directed r f` | for all $i, j$ there is $k$ with $f(i) \preccurlyeq f(k)$ and $f(j) \preccurlyeq f(k)$ |
| `DirectedOn r s` | for all $x, y \in s$ there is $z \in s$ with $x \preccurlyeq z$ and $y \preccurlyeq z$ |
| `IsDirected α r` | the class: for all $a, b$ there is $c$ with $a \preccurlyeq c$ and $b \preccurlyeq c$ |

`Directed` is for an indexed family $f : \iota \to \alpha$, `DirectedOn` is for a set, and `IsDirected` is for the whole type. The translations are `directedOn_iff_directed` (a set is directed when its inclusion map is), `directedOn_range` (a family is directed when its range is), `directedOn_univ_iff` and `directed_id_iff`. The abbreviation `IsDirectedOrder α` stands for `IsDirected α (· ≤ ·)`, and `IsCodirectedOrder α` for the relation `≥`. Most lemmas take `(· ≤ ·)` or `(· ≥ ·)` as the relation, so a directed family of sets in Mathlib is often written `Directed (· ⊆ ·) f`. To use the class, `directed_of r a b` and `exists_ge_ge a b` give the common upper bound, and `directed_of₃` gives one for three elements when $r$ is transitive.

**Sources of directed sets.** Each join-semilattice is directed, by the instance `SemilatticeSup.instIsDirectedOrder`: the bound of $a$ and $b$ is $a \sqcup b$. Each order with a top is directed, by `OrderTop.instIsDirectedOrder`. A total relation makes each family directed, by `Std.Total.directed`, so each family in a linear order is directed. A chain is directed by `IsChain.directedOn`. A set closed under $\sqcup$ is directed, and this is `directedOn_of_sup_mem`: if $i \sqcup j \in S$ for all $i, j \in S$, then `DirectedOn (· ≤ ·) S`. The proof takes $z = x \sqcup y$, which is in $S$ and above $x$ and $y$ by `le_sup_left` and `le_sup_right`. Monotone maps send directed orders to directed families: `Monotone.directed_le` states that if $\alpha$ is directed and $f$ is monotone, then $f$ is directed for `≤`. Proof: for $i, j$ take $k \ge i, j$; then $f(i) \le f(k)$ and $f(j) \le f(k)$. The dual forms are `Antitone.directed_ge` and `Monotone.directed_ge`. Directedness passes to images and products with `directedOn_image`, `Directed.mono_comp`, `DirectedOn.prod` and `DirectedOn.pi`, and to weaker relations with `DirectedOn.mono`. The dual order of a codirected order is directed: `OrderDual.isDirected_le`.

**Consequences of directedness.** In a directed preorder a maximal element is a greatest element. This is `isTop_iff_isMax`, with the one-way form `IsMax.isTop`. Proof: let $a$ be maximal and $b$ any element. Take $c$ with $a \le c$ and $b \le c$. Maximality gives $c \le a$, so $b \le c \le a$. So a directed order has at most one maximal element up to equivalence, and `isTop_or_exists_gt` says that each element is a top or has a strictly larger element. A function on a directed order that is both monotone and antitone is constant: `constant_of_monotone_antitone`. Proof: for $a, b$ take $c \ge a, b$. Then $f(a) \le f(c)$ by monotonicity and $f(c) \le f(a)$ by antitonicity, so $f(a) = f(c)$, and in the same way $f(b) = f(c)$. The lemma `Monotone.forall_le_of_antitone` is the version with two functions: if $f$ is monotone, $g$ is antitone and $f \le g$, then $f(m) \le g(n)$ for all $m, n$.

**Cofinal sets.** A set $s$ is cofinal when `IsCofinal s`, that is $\forall x, \exists y \in s, x \le y$. The basic rules are `IsCofinal.univ`, `IsCofinal.mono` for supersets, and `IsCofinal.trans` for a cofinal subset of a cofinal subset. With a top element, `isCofinal_iff_top_mem` says that a set is cofinal exactly when it contains $\top$, and `isCofinal_singleton_iff` says that $\{x\}$ is cofinal exactly when $x$ is a top. A cofinal set contains each maximal element, by `IsCofinal.mem_of_isMax`, and no set $(-\infty, x)$ is cofinal, by `not_isCofinal_Iio`, since nothing in it lies above $x$. The lemma `isCofinal_iff_iUnion_Iic_eq_univ` restates the definition as a union of rays.

In a linear order without a maximum, a set is cofinal exactly when it is not bounded above. This is `not_isCofinal_iff_bddAbove`. Proof: if $s$ is not cofinal, some $x$ has no element of $s$ above it, so each $y \in s$ satisfies $y < x$ by linearity, and $x$ is an upper bound. If $s$ has an upper bound $b$, take $c > b$, which exists since there is no maximum; no element of $s$ is above $c$. The one-way forms are `IsCofinal.of_not_bddAbove` and `IsCofinal.not_bddAbove`. In a directed partial order each ray $[x, \infty)$ is cofinal (`IsCofinal.Ici`), and so is each nonempty upper set (`IsUpperSet.isCofinal`). The image of a cofinal set under an order isomorphism is cofinal: `OrderIso.map_isCofinal`. The upper adjoint of a Galois connection has a cofinal range, by `GaloisConnection.isCofinal_range`. In a well-order the range of a strictly monotone map $f : \alpha \to \alpha$ is cofinal, by `isCofinal_range_of_strictMono`. The proof uses the fact that $x \le f(x)$ for each $x$, which holds because the least $x$ with $f(x) < x$ would give $f(f(x)) < f(x)$, a smaller counterexample. The cardinal cofinality of an order is in the set theory volume.

**Antichains.** The predicate `IsAntichain r s` is defined as `s.Pairwise rᶜ`: distinct elements of $s$ are never related. With the relation `≤`, this means that no two distinct elements are comparable, and `isAntichain_iff_forall_not_lt` restates it in a partial order as $\neg (a < b)$ for $a, b \in s$. The structural lemmas follow the pattern of `Set.Pairwise`: `IsAntichain.subset` for subsets, `IsAntichain.mono` for smaller relations, `IsAntichain.image` and `IsAntichain.preimage` for maps, `isAntichain_insert` and `isAntichain_union` for the addition of elements, and `IsAntichain.swap` for the reversed relation. Order embeddings keep antichains, by `IsAntichain.image_embedding`, and `IsAntichain.to_dual` passes to the order dual. In a Boolean algebra the complements of an antichain form an antichain, by `IsAntichain.image_compl`.

Chains and antichains meet in at most one point. The lemma `isChain_and_isAntichain_iff_subsingleton` says that a set is both a chain and an antichain exactly when it has at most one element, and `inter_subsingleton_of_isChain_of_isAntichain` gives the form for two sets. Proof: let $a, b \in s \cap t$ with $a \ne b$. Since $s$ is a chain, $a \preccurlyeq b$ or $b \preccurlyeq a$. Since $t$ is an antichain, neither holds. So $a = b$. The maximal elements of any predicate form an antichain: `setOfPred_maximal_antichain` states that $\{x \mid \text{Maximal } P\ x\}$ is an antichain for `≤`. Proof: if $x \le y$ with both maximal, then $y \le x$ by the maximality of $x$, so $x = y$. The dual is `setOfPred_minimal_antichain`. A function that is strictly monotone and antitone on $s$ makes $s$ an antichain, by `IsAntichain.of_strictMonoOn_antitoneOn`. An antichain with a bottom element is the singleton $\{\bot\}$, by `IsAntichain.bot_mem_iff`.

The variants are `IsStrongAntichain r s`, where two distinct elements have no common upper bound at all, `IsMaxAntichain r s`, an antichain contained in no larger antichain, with `maximal_isAntichain_iff` as the link with `Maximal`, and `IsWeakAntichain s` on a product $\prod_i \alpha_i$, where no two distinct elements satisfy `StrongLT`, the strict order in each coordinate. A strong antichain is an antichain for a reflexive relation: `IsStrongAntichain.isAntichain`.

**Direct limits and inverse systems.** A family of types $F_i$ indexed by a preorder, with maps $f_{ij} : F_i \to F_j$ for $i \le j$, is a *directed system* when $f_{ii} = \mathrm{id}$ and $f_{jk} \circ f_{ij} = f_{ik}$. This is the class `DirectedSystem F f`, with the fields `DirectedSystem.map_self` and `DirectedSystem.map_map`. When the index order is directed, `DirectLimit F f` is the quotient of the sigma type $\Sigma_i F_i$ by the relation `DirectLimit.setoid`: $(i, x) \sim (j, y)$ when $f_{ik}(x) = f_{jk}(y)$ for some $k \ge i, j$. Directedness makes the relation transitive. The API has an induction principle `DirectLimit.induction`, the fact `DirectLimit.exists_eq_mk` that each element comes from some $F_i$, the universal map `DirectLimit.lift` with its rule `DirectLimit.lift_def`, and the maps `DirectLimit.map` and `DirectLimit.map₂`. If all $f_{ij}$ are injective, so are the maps into the limit (`DirectLimit.mk_injective`). When the index order has a top $m$, the limit is $F_m$: `DirectLimit.equivOfIsTop`. The inverse map sends $x$ to the class of $(m, x)$, and the forward map sends the class of $(i, x)$ to $f_{im}(x)$, which is well defined by the compatibility of the maps.

The dual class `InverseSystem f` has maps $F_j \to F_i$ for $i \le j$. The set `InverseSystem.limit f i` is the inverse limit of the $F_j$ with $j < i$, and `InverseSystem.piLT X i` is the product of the $X_j$ with $j < i$. Over a well-ordered index type with successors, `InverseSystem.globalEquiv` builds by transfinite recursion a bijection $F_i \simeq \prod_{j < i} X_j$ from bijections $F_{i+1} \simeq F_i \times X_i$ at successor steps and $F_i \simeq \lim_{j < i} F_j$ at limit steps. The bijections are natural, by `InverseSystem.globalEquiv_naturality`.

#### Common errors

1. `Directed` takes a family and `DirectedOn` takes a set. For a set $s$, write `DirectedOn (· ≤ ·) s`, or pass to the family of its inclusion map with `directedOn_iff_directed`.
2. The relation comes first. `Directed (· ≤ ·) f` and `Directed (· ≥ ·) f` are different statements: the first asks for upper bounds and the second for lower bounds. A decreasing sequence of sets is directed for `(· ⊇ ·)`, not for `(· ⊆ ·)`.
3. `IsAntichain r s` uses the relation `r`, not its strict part. For `IsAntichain (· < ·) s` in a partial order, the condition is the same as for `(· ≤ ·)`, but for a preorder two equivalent distinct elements are allowed in an antichain for `<` and not for `≤`.

### Exercises

1. (A) Prove that each nonempty finite subset of a directed preorder has an upper bound, by induction with `directed_of`.
2. (A) Prove that the even numbers are cofinal in `ℕ`, and that a finite subset of `ℕ` is never cofinal.
3. (B) Prove that in a linear order each antichain for `≤` has at most one element, and compare with `IsAntichain.subsingleton`.
4. (B) Show that the family of finite subsets of a type, ordered by inclusion, is directed, and that the union of a directed family of sets closed under $\sqcup$ in a lattice is again closed under $\sqcup$.
5. (B) Let $f : \mathbb{N} \to \mathbb{N}$ be strictly monotone. Prove $n \le f(n)$ for all $n$, and deduce that the range of $f$ is cofinal.
6. (C) Prove Dilworth's theorem for a finite partial order: the least number of chains that cover the order equals the largest size of an antichain.

### Reference

<?reference?>
