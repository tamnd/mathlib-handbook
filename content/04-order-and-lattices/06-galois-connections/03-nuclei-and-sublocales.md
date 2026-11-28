---
title: Nuclei and sublocales
kind: api
modules:
  - Mathlib.Order.Nucleus
  - Mathlib.Order.Sublocale
explains:
  E2: [Nucleus, Nucleus.map_himp_le, Nucleus.mem_range, Nucleus.toSublocale, Sublocale, nucleusIsoSublocale, Sublocale.restrict, Nucleus.comp_eq_right_iff_le]
  E1: auto
families: []
requires: [V04.C03, V04.C04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Nuclei and sublocales

### Overview

A frame is a complete lattice in which finite infima distribute over arbitrary suprema: $a \sqcap \bigsqcup_i b_i = \bigsqcup_i (a \sqcap b_i)$. The open sets of a topological space form a frame. Point-free topology studies frames as spaces in their own right, and it calls them locales when it looks at them as spaces. A subspace of a space then has an order form: a sublocale.

There are two equivalent ways to describe a sublocale of a frame $X$. The first is a nucleus: a closure operator $n$ on $X$ that also keeps binary infima. The second is a subset $S$ of $X$ that is closed under arbitrary infima and under the implications $a \Rightarrow b$ with $b \in S$. The set of the fixed points of a nucleus is a sublocale, and each sublocale is the set of fixed points of exactly one nucleus. This section describes the two notions and the order isomorphism between them.

The nucleus is a special closure operator, so the section uses the closure operators and the Galois insertions of the previous sections of this chapter. It also uses frames and Heyting implication from the lattice chapters. A reader who knows the closure of a set in a topological space has a model: for a subspace $Y$ of a space with open sets $\mathcal{O}$, the map that sends an open set $U$ to the union of the open sets $V$ with $V \cap Y \subseteq U$ is a nucleus on $\mathcal{O}$.

### The library around it

#### Nuclei

The structure `Nucleus X` is defined for a meet-semilattice $X$. A nucleus is an infimum-preserving map $n : X \to X$, given as an `InfHom`, with two more properties:

1. inflationary: $x \le n(x)$ for each $x$, the lemma `Nucleus.le_apply`;
2. idempotent: $n(n(x)) \le n(x)$ for each $x$, which gives the equality $n(n(x)) = n(x)$ of `Nucleus.idempotent`.

So a nucleus is a closure operator that keeps binary infima, and `Nucleus.toClosureOperator` forgets the extra property. The class `NucleusClass` gives the same three properties to other types of maps, in the pattern of the morphism classes of Chapter 2. The coercion to a function is the simp normal form. The lemmas `Nucleus.map_inf`, `Nucleus.monotone` and `Nucleus.ext` state the infimum property, the monotonicity and the extensionality. The order on nuclei is the pointwise order, and `Nucleus.coe_le_coe` says that the coercion respects it.

The nuclei of a complete lattice form a complete lattice, `Nucleus.instCompleteLattice`. The infimum is pointwise: `Nucleus.inf_apply` gives $(m \sqcap n)(x) = m(x) \sqcap n(x)$, and `Nucleus.sInf_apply` gives the same formula for a set of nuclei. The supremum is not pointwise, because the pointwise supremum of two nuclei need not be idempotent. The bottom nucleus is the identity, `Nucleus.bot_apply`, and the top nucleus is the constant map $\top$, `Nucleus.top_apply`.

The order on nuclei has a second description. By `Nucleus.comp_eq_right_iff_le`, $n \circ m = m$ if and only if $n \le m$. The proof is short. If $n \le m$, then $m(x) \le n(m(x)) \le m(m(x)) = m(x)$, so $n(m(x)) = m(x)$. If $n \circ m = m$, then $n(x) \le n(m(x)) = m(x)$, because $n$ is monotone and $x \le m(x)$.

#### Nuclei on a frame

On a frame $X$, the Heyting implication $a \Rightarrow b$ is the largest $c$ with $a \sqcap c \le b$. The main inequality is `Nucleus.map_himp_le`:
$$n(x \Rightarrow y) \le x \Rightarrow n(y).$$
Proof. By the definition of the implication, it is enough to show $x \sqcap n(x \Rightarrow y) \le n(y)$. Now $x \le n(x)$, so
$$x \sqcap n(x \Rightarrow y) \le n(x) \sqcap n(x \Rightarrow y) = n(x \sqcap (x \Rightarrow y)) \le n(y),$$
where the equality uses that $n$ keeps infima and the last step uses $x \sqcap (x \Rightarrow y) \le y$ and the monotonicity of $n$. The consequence `Nucleus.map_himp_apply` says $n(x \Rightarrow n(y)) = x \Rightarrow n(y)$: an implication into a fixed point is a fixed point.

The fixed points of a nucleus are its range, by `Nucleus.mem_range`: $x \in \operatorname{range} n$ if and only if $n(x) = x$. One direction is the idempotence, the other is trivial. The range is again a frame, `Nucleus.instFrameElemRangeCoe`, and `Nucleus.restrict` is the frame morphism from $X$ onto the range. With the inclusion of the range, it forms a Galois insertion, `Nucleus.giRestrict`. The lemma `Nucleus.range_subset_range` says that a larger nucleus has a smaller range.

The nuclei of a frame form a frame again, `Nucleus.instFrame`, with a Heyting implication described by `Nucleus.himp_apply`. These instances are the base of the point-free study of subspaces.

#### Sublocales

The structure `Sublocale X`, for a frame $X$, is a subset with two closure properties: the infimum of each subset lies in it, `Sublocale.sInf_mem`, and $a \Rightarrow b$ lies in it when $b$ does, `Sublocale.himp_mem`. As special cases, $\top$ is in each sublocale, `Sublocale.top_mem`, since $\top$ is the infimum of the empty set, and binary infima stay in it, `Sublocale.inf_mem`. A sublocale is a `SetLike` object, so `a ∈ S` and the coercion to a set work as for subgroups.

A sublocale is a frame with the induced order, `Sublocale.carrier.instFrame`. The infimum and the implication of the sublocale are those of $X$, by `Sublocale.coe_inf`, `Sublocale.coe_sInf` and `Sublocale.coe_himp`. The supremum is not that of $X$: the supremum of two elements of $S$ is the least element of $S$ above both. The map `Sublocale.restrict` is the frame morphism from $X$ onto $S$ that sends $x$ to the least element of $S$ above $x$, and `Sublocale.giRestrict` is the Galois insertion with the inclusion. The lemma `Sublocale.restrict_of_mem` says that the map fixes the elements of $S$.

The sublocales of a frame are ordered by inclusion. They form a coframe, `Sublocale.instCoframe`: the order dual of a frame. This matches the topological picture, in which the subspaces of a space have arbitrary intersections and finite unions that distribute in the dual way.

#### The correspondence

The two constructions are inverse to each other.

| Lean name | Statement |
|---|---|
| `Nucleus.toSublocale` | the range of a nucleus is a sublocale |
| `Nucleus.coe_toSublocale` | the set of `n.toSublocale` is `Set.range n` |
| `Sublocale.toNucleus` | the map $x \mapsto$ the least element of $S$ above $x$ |
| `Sublocale.range_toNucleus` | the range of `S.toNucleus` is $S$ |
| `Nucleus.toSublocale_le_toSublocale` | $\operatorname{range} m \subseteq \operatorname{range} n \iff n \le m$ |
| `Sublocale.toNucleus_le_toNucleus` | $S.\mathrm{toNucleus} \le T.\mathrm{toNucleus} \iff T \le S$ |
| `nucleusIsoSublocale` | the order isomorphism between `(Nucleus X)ᵒᵈ` and `Sublocale X` |

The proof that the range of a nucleus $n$ is a sublocale has two steps. Let $s$ be a subset of the range. For each $y \in s$, the element $\inf s$ is below $y$, so $n(\inf s) \le n(y) = y$. So $n(\inf s) \le \inf s$, and $\inf s$ is a fixed point. For the implication, let $b$ be a fixed point. Then `Nucleus.map_himp_le` gives $n(a \Rightarrow b) \le a \Rightarrow n(b) = a \Rightarrow b$, so $a \Rightarrow b$ is a fixed point. The isomorphism `nucleusIsoSublocale` reverses the order, because a larger nucleus moves more elements and so fixes fewer of them. This is why the nuclei form a frame and the sublocales form a coframe.

#### Common errors

1. The supremum of two nuclei is not the pointwise supremum. The lemma `Nucleus.inf_apply` has no analogue for `⊔`, and a proof that unfolds the supremum must go through the complete lattice structure.
2. The correspondence `nucleusIsoSublocale` starts at `(Nucleus X)ᵒᵈ`, not at `Nucleus X`. A rewrite with it changes the direction of each inequality.
3. The supremum in a sublocale is not the supremum of $X$. Only the infimum and the implication have `coe` lemmas.

### Exercises

1. (A) Show that for each element $a$ of a frame, the map $x \mapsto a \Rightarrow x$ is a nucleus.
2. (A) Show that for each element $a$ of a frame, the map $x \mapsto a \sqcup x$ is a nucleus, and describe its range.
3. (B) Prove `Nucleus.mem_range` from `Nucleus.idempotent`.
4. (B) Prove that the set of the fixed points of a nucleus is closed under arbitrary infima, without `Nucleus.toSublocale`.
5. (B) Show that the pointwise supremum of two nuclei is inflationary and monotone, and give an example in a finite frame where it is not a nucleus.
6. (C) For a subspace $Y$ of a topological space, prove that the map that sends an open set $U$ to the union of the open sets $V$ with $V \cap Y \subseteq U$ is a nucleus on the frame of open sets, and identify its fixed points.

### Reference

<?reference?>
