---
title: Monotone functions, monotone convergence and limits superior
kind: api
modules:
  - Mathlib.Topology.Order.Monotone
  - Mathlib.Topology.Order.MonotoneContinuity
  - Mathlib.Topology.Order.MonotoneConvergence
  - Mathlib.Topology.Order.LiminfLimsup
  - Mathlib.Topology.Order.Lattice
  - Mathlib.Topology.Order.PartialSups
  - Mathlib.Topology.Order.IsNormal
explains:
  E2: [Monotone.countable_not_continuousAt, Monotone.continuous_of_surjective, SupConvergenceClass, tendsto_atTop_ciSup, IsClosed.csSup_mem, Monotone.map_sSup_of_continuousAt, Filter.Tendsto.limsup_eq, tendsto_of_liminf_eq_limsup, TopologicalLattice, Order.isNormal_iff_strictMono_and_continuous]
  E1: auto
families: []
requires: [V04, V13.C01, V13.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Monotone functions, monotone convergence and limits superior

### Overview

A monotone function on an ordered space has strong regularity. It has one-sided limits at each point, it has at most countably many points of discontinuity, and it is continuous as soon as its image has no gaps. A monotone sequence that is bounded above converges to its supremum. These facts are the base of the theory of functions of bounded variation, of the Lebesgue-Stieltjes measures and of many convergence proofs.

This section describes the modules that hold these results. It also covers the limit superior and the limit inferior of a function along a filter in an order topology, the classes of topological lattices in which $\sup$ and $\inf$ are continuous, and the normal functions of ordinals.

The text uses the order topology of Section 1 and the one-sided filters and least upper bounds of Section 2. The definitions of `Filter.limsup` and `Filter.liminf` are in Volume 4.

### The library around it

#### Monotone maps and suprema

The module `Mathlib.Topology.Order.Monotone` starts with the suprema of closed sets. A nonempty closed set that is bounded above contains its supremum. This is `IsClosed.csSup_mem`, and `csSup_mem_closure` says that the supremum is always in the closure. Both follow from `IsLUB.mem_closure` of Section 2, because the conditional supremum of a nonempty bounded set is its least upper bound.

A monotone map that is continuous at a supremum commutes with it:

$$f(\sup s) = \sup f(s).$$

This is `Monotone.map_sSup_of_continuousAt`, in a complete lattice and with the hypothesis $f(\bot) = \bot$ for the empty set. *Proof.* Monotony gives $\sup f(s) \le f(\sup s)$. For the other inequality, $\sup s$ is in the closure of $s$, so $f(\sup s)$ is in the closure of $f(s)$ by continuity, and this closure lies below the upper bound $\sup f(s)$. The conditional forms such as `Monotone.map_ciSup_of_continuousAt` ask for bounded sets, and the forms for `MonotoneOn` and `Antitone` follow the same pattern. A continuous monotone map is left and right order-continuous (`Monotone.leftOrdContinuous`).

Each monotone map has one-sided limits: at $x$ from the left, $f$ tends to $\sup f((-\infty, x))$. This is `Monotone.tendsto_nhdsLT`, and `Monotone.tendsto_nhdsGT` is the limit from the right. The main countability result follows. If $f$ is monotone and the target is second countable, the set of points of discontinuity of $f$ is countable:

$$\{x : f \text{ is not continuous at } x\} \text{ is countable.}$$

This is `Monotone.countable_not_continuousAt`. *Proof sketch.* At a point of discontinuity the left limit is strictly below the right limit, or one of them differs from $f(x)$. So each such point opens a nonempty gap in the target, and the gaps of distinct points are disjoint. In a second countable order there are at most countably many disjoint nonempty open intervals, by `Set.PairwiseDisjoint.countable_of_Ioo` of Section 1. The forms `MonotoneOn.countable_not_continuousWithinAt` work on a set. A related result says that a monotone map takes the same value at two distinct points for only countably many values (`Monotone.countable_setOfPred_two_preimages`).

#### Continuity from the image

The module `Mathlib.Topology.Order.MonotoneContinuity` proves continuity from properties of the image. If $f$ is monotone, the target is densely ordered, and $f$ is surjective, then $f$ is continuous (`Monotone.continuous_of_surjective`). *Proof.* By Section 2 it is enough to prove continuity from the right and from the left at each point $a$. Let $b > f(a)$. By density there is $c$ with $f(a) < c < b$, and by surjectivity $c = f(x)$ for some $x$, with $x > a$ by monotony. Then $f$ maps $[a, x)$ into $[f(a), c)$, which lies below $b$. The form `Monotone.continuous_of_denseRange` asks only for a dense range.

The local forms are a family with long names. The lemma `continuousWithinAt_right_of_monotoneOn_of_exists_between` proves continuity from the right at $a$ when each interval $(f(a), b)$ contains a value of $f$. The lemma `StrictMonoOn.continuousAt_of_image_mem_nhds` proves continuity at $a$ when the image of a neighbourhood is a neighbourhood. Each order isomorphism between order topologies is a homeomorphism (`OrderIso.toHomeomorph`).

#### Monotone convergence

The module `Mathlib.Topology.Order.MonotoneConvergence` states the monotone convergence theorem with a class. The class `SupConvergenceClass α` says that for each set $s$ with least upper bound $a$, the inclusion of $s$ tends to $a$ along `Filter.atTop` of $s$. Each linear order with the order topology is an instance (`LinearOrder.supConvergenceClass`), and the class is stable under finite and infinite products. The dual class is `InfConvergenceClass`.

The main result says that a monotone sequence that is bounded above converges to its supremum:

$$f \text{ monotone},\ f \text{ bounded above} \implies f(n) \to \sup_n f(n).$$

This is `tendsto_atTop_ciSup`. *Proof.* The supremum $a$ is the least upper bound of the range. By the class, the identity of the range tends to $a$. The map $f$ sends `Filter.atTop` into `Filter.atTop` of its range, because $f$ is monotone. The composition gives the limit. In a complete lattice the bound is automatic (`tendsto_atTop_iSup`), and `tendsto_atTop_isLUB` uses an arbitrary least upper bound. Conversely a monotone sequence with a limit stays below the limit (`Monotone.ge_of_tendsto`) and the limit is its supremum (`iSup_eq_of_tendsto`). A monotone map converges if and only if it converges along a cofinal subsequence (`tendsto_iff_tendsto_subseq_of_monotone`).

#### Limits superior

The module `Mathlib.Topology.Order.LiminfLimsup` connects the order notions of Volume 4 with limits. The class `BoundedLENhdsClass α` says that each neighbourhood filter is bounded above, so that a limsup along it makes sense (`isBounded_le_nhds`). A linear order with `ClosedIciTopology` has the class (`BoundedLENhdsClass.of_closedIciTopology`). In the order topology the limit superior of the neighbourhood filter of $a$ is $a$ (`limsSup_nhds`).

If $u \to a$ along a proper filter, then $\limsup u = a$ and $\liminf u = a$. These are `Filter.Tendsto.limsup_eq` and `Filter.Tendsto.liminf_eq`. Conversely, if the limit inferior and the limit superior are equal to $a$ and $u$ is bounded, then $u \to a$. This is `tendsto_of_liminf_eq_limsup`. *Proof.* Let $a' > a$. Since $\limsup u = a < a'$, eventually $u < a'$. In the same way, for $a' < a$, eventually $a' < u$. Then `tendsto_order` of Section 1 gives $u \to a$.

The limit superior is the greatest cluster value: `isGreatest_mapClusterPt_limsup`. In a first countable space a sequence along a countably generated filter has a subsequence that tends to the limit superior (`exists_seq_tendsto_limsup`). A monotone map continuous at the limit superior commutes with it (`Monotone.map_limsup_of_continuousAt`). For a monotone map the limit inferior from the left at $a$ is the supremum of the values below $a$ (`Monotone.liminf_nhdsLT_eq_iSup₂`). The criterion `tendsto_of_no_upcrossings` proves convergence of a bounded sequence that crosses no interval $[a, b]$ infinitely often, with $a$ and $b$ in a dense set. The martingale convergence theorem in Volume 20 uses this criterion.

#### Topological lattices

The module `Mathlib.Topology.Order.Lattice` defines the classes `ContinuousSup L` and `ContinuousInf L`. They say that the map $(x, y) \mapsto x \sqcup y$ is continuous, and the same for $\sqcap$. The class `TopologicalLattice L` has both. A linear order with an order-closed topology is a topological lattice (`LinearOrder.topologicalLattice`), because $\sqcup$ is $\max$ there. The lemmas `Continuous.sup`, `Filter.Tendsto.sup_nhds` and `Continuous.finset_sup` follow the usual pattern of the continuity API. The module `Mathlib.Topology.Order.PartialSups` adds the partial suprema $x \mapsto \sup_{k \le n} f_k(x)$ of a sequence of continuous maps (`Continuous.partialSups`).

#### Normal functions

The module `Mathlib.Topology.Order.IsNormal` gives the topological meaning of the normal functions of ordinal arithmetic. On well-ordered types with the order topology, a function is normal if and only if it is strictly monotone and continuous:

$$\text{IsNormal}(f) \iff f \text{ strictly monotone and continuous.}$$

This is `Order.isNormal_iff_strictMono_and_continuous`. The condition of normality says that $f(a) = \sup_{b < a} f(b)$ at each limit $a$. By Section 2, this is continuity at limits, and the other points are isolated.

#### Common errors

1. The lemma `Monotone.map_sSup_of_continuousAt` needs $f(\bot) = \bot$. Without it the empty set breaks the equation, because $\sup \emptyset = \bot$ and $\sup f(\emptyset) = \bot$ while $f(\bot)$ can be larger. Use the conditional form with a nonempty set instead.
2. The lemma `tendsto_atTop_ciSup` needs the class `SupConvergenceClass`. For $\mathbb{R}$ the class comes from the order topology, but for a type with a topology that is not the order topology, an instance search fails, and the lemma does not apply.
3. The converse `tendsto_of_liminf_eq_limsup` needs the bounds of the sequence as hypotheses. In $\mathbb{R}$ the limit superior of an unbounded sequence is a junk value, and both junk values can agree.

### Exercises

1. (A) Prove that a closed, nonempty and bounded subset of $\mathbb{R}$ has a greatest element, with `IsClosed.csSup_mem`.
2. (A) Let $u_n = 1 - 1/(n+1)$. Use `tendsto_atTop_ciSup` to prove that $u_n \to 1$, and compute the supremum.
3. (B) Give a monotone function $f : \mathbb{R} \to \mathbb{R}$ that is discontinuous at each rational point. Explain why it does not contradict `Monotone.countable_not_continuousAt`.
4. (B) Prove that an order isomorphism $\mathbb{R} \to (0, 1)$ is a homeomorphism, without `OrderIso.toHomeomorph`, by `Monotone.continuous_of_surjective`.
5. (B) Prove that if $u_n \to a$ in $\mathbb{R}$, then $\limsup u_n = a$, and give a bounded sequence with $\liminf u_n < \limsup u_n$.
6. (C) Prove that a monotone function on an interval of $\mathbb{R}$ is continuous at a point $a$ if and only if its left and right limits at $a$ agree with $f(a)$.

### Reference

<?reference?>
