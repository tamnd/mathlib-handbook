---
title: Neighbourhoods within a set and of a set
kind: api
modules:
  - Mathlib.Topology.NhdsWithin
  - Mathlib.Topology.NhdsSet
  - Mathlib.Topology.NhdsKer
  - Mathlib.Topology.Piecewise
  - Mathlib.Topology.Partial
explains:
  E2: [mem_nhdsWithin, nhdsWithin_restrict, tendsto_nhdsWithin_iff, nhdsWithin_eq_map_subtypeVal, mem_nhdsSet_iff_forall, nhdsSet_union, mem_nhdsKer_singleton, continuous_if]
  E1: auto
families: []
requires: [V04, V13.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Neighbourhoods within a set and of a set

### Overview

Section 2 defines three filters next to the neighbourhood filter $\mathcal{N}(x)$. The filter $\mathcal{N}_s(x) = \mathcal{N}(x) \sqcap \mathcal{P}(s)$, written `𝓝[s] x`, holds the neighbourhoods of $x$ relative to a set $s$. The filter $\mathcal{N}(s)$ of a set, written `𝓝ˢ s`, holds the sets that are neighbourhoods of each point of $s$. The set `nhdsKer s` is the intersection of all open sets that contain $s$. Section 2 gives the definitions. This section describes the API that the library builds on them.

The API is large because one-sided limits, limits at a punctured point, continuity on a set and uniform statements over a compact set all use these filters. A reader who proves a statement about `ContinuousWithinAt` or `ContinuousOn` uses the lemmas of `Mathlib.Topology.NhdsWithin` all the time. The section also covers two small modules: `Mathlib.Topology.Piecewise` on functions defined by cases, and `Mathlib.Topology.Partial` on partial functions.

### The library around it

#### Neighbourhoods within a set

The module `Mathlib.Topology.NhdsWithin` describes the filter `nhdsWithin x s`. The first group of lemmas says what its members are.

| Lean name | Statement |
|---|---|
| `mem_nhdsWithin` | $t \in \mathcal{N}_s(x) \iff \exists u$ open, $x \in u$, $u \cap s \subseteq t$ |
| `mem_nhdsWithin_iff_exists_mem_nhds_inter` | $t \in \mathcal{N}_s(x) \iff \exists u \in \mathcal{N}(x)$, $u \cap s \subseteq t$ |
| `mem_nhdsWithin_iff_eventually` | $t \in \mathcal{N}_s(x) \iff$ eventually near $x$, $y \in s \to y \in t$ |
| `eventually_nhdsWithin_iff` | $p$ holds eventually in $\mathcal{N}_s(x)$ iff eventually near $x$, $y \in s \to p(y)$ |
| `self_mem_nhdsWithin` | $s \in \mathcal{N}_s(x)$ |
| `nhdsWithin_basis_open` | the sets $u \cap s$, $u$ open with $x \in u$, form a basis |

The proof of `mem_nhdsWithin` is short. A member of $\mathcal{N}(x) \sqcap \mathcal{P}(s)$ contains $v \cap w$ with $v \in \mathcal{N}(x)$ and $s \subseteq w$, so it contains $v \cap s$. The set $v$ contains an open $u$ with $x \in u$, and $u \cap s \subseteq v \cap s$. The converse is clear.

The second group computes the filter for special sets. The filter depends only on the trace of $s$ near $x$.

| Lean name | Statement |
|---|---|
| `nhdsWithin_univ` | $\mathcal{N}_{X}(x) = \mathcal{N}(x)$ |
| `nhdsWithin_empty` | $\mathcal{N}_\emptyset(x) = \bot$ |
| `nhdsWithin_singleton` | $\mathcal{N}_{\{x\}}(x) = \mathrm{pure}\ x$ |
| `nhdsWithin_insert` | $\mathcal{N}_{\{x\} \cup s}(x) = \mathrm{pure}\ x \sqcup \mathcal{N}_s(x)$ |
| `nhdsWithin_inter` | $\mathcal{N}_{s \cap t}(x) = \mathcal{N}_s(x) \sqcap \mathcal{N}_t(x)$ |
| `nhdsWithin_union` | $\mathcal{N}_{s \cup t}(x) = \mathcal{N}_s(x) \sqcup \mathcal{N}_t(x)$ |
| `nhdsWithin_restrict` | $\mathcal{N}_s(x) = \mathcal{N}_{s \cap t}(x)$ for $t$ open with $x \in t$ |
| `IsOpen.nhdsWithin_eq` | $\mathcal{N}_s(x) = \mathcal{N}(x)$ for $s$ open with $x \in s$ |
| `nhdsWithin_le_iff` | $\mathcal{N}_s(x) \le \mathcal{N}_t(x) \iff t \in \mathcal{N}_s(x)$ |

The statement of `nhdsWithin_restrict` has a one-line proof: $\mathcal{N}_{s \cap t}(x) = \mathcal{N}(x) \sqcap \mathcal{P}(s) \sqcap \mathcal{P}(t)$, and $\mathcal{N}(x) \le \mathcal{P}(t)$ since $t$ is a neighbourhood of $x$. The monotonicity in $s$ is `nhdsWithin_mono`, in `Mathlib.Topology.Neighborhoods`, and `nhdsWithin_le_nhds` compares with the full filter. The lemma `nhds_of_nhdsWithin_of_nhds` goes back: if $s \in \mathcal{N}(x)$ and $t \in \mathcal{N}_s(x)$, then $t \in \mathcal{N}(x)$.

For an order, two filters of this kind are the one-sided neighbourhoods `𝓝[<] x` and `𝓝[>] x`, and the punctured neighbourhoods `𝓝[≠] x`. The lemma `punctured_nhds_eq_nhdsWithin_sup_nhdsWithin` splits the punctured filter of a linear order into the left and the right parts, and `nhds_eq_nhdsWithin_sup_nhdsWithin` splits $\mathcal{N}(x)$ along a cover $X = I_1 \cup I_2$. The lemma `continuousAt_iff_punctured_nhds` says that $f$ is continuous at $a$ if and only if $f(y) \to f(a)$ as $y \to a$ with $y \ne a$.

#### Limits into a set and the subtype

A limit into $\mathcal{N}_s(a)$ is a limit into $\mathcal{N}(a)$ that eventually stays in $s$. This is `tendsto_nhdsWithin_iff`:

$$f \to \mathcal{N}_s(a) \text{ along } l \iff f \to \mathcal{N}(a) \text{ along } l \text{ and } \forall^f n \in l,\ f(n) \in s.$$

The proof is the definition of the infimum: a map tends to $F \sqcap G$ if and only if it tends to $F$ and to $G$, and a map tends to $\mathcal{P}(s)$ if and only if it is eventually in $s$. The two halves have their own names, `tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within` and `tendsto_nhds_of_tendsto_nhdsWithin`. The special case `tendsto_nhdsWithin_range` drops the second condition when $s$ is the range of $f$. The congruence lemma `tendsto_nhdsWithin_congr` changes $f$ on $s$, and `tendsto_nhdsWithin_mono_left` shrinks the set of the source.

The relative filter is also the image of a filter on the subtype. If $a \in s$, then `nhdsWithin_eq_map_subtypeVal` gives

$$\mathcal{N}_s(a) = \mathrm{map}\ (\uparrow)\ \mathcal{N}_{s}(\langle a, h \rangle),$$

where the right side uses the neighbourhood filter of the point $\langle a, h \rangle$ of the subspace $s$. The proof uses that the subspace topology is induced: $\mathcal{N}(\langle a, h\rangle) = \mathrm{comap}\ (\uparrow)\ \mathcal{N}(a)$, and the image of this comap is $\mathcal{N}(a) \sqcap \mathcal{P}(\mathrm{range}\ (\uparrow)) = \mathcal{N}_s(a)$. So a statement about limits in the subspace is a statement about `𝓝[s] a`, and the library uses both forms. The lemmas `mem_nhds_subtype_iff_nhdsWithin`, `tendsto_nhdsWithin_iff_subtype` and `eventually_nhds_subtype_iff` translate between them.

Other lemmas of the module treat closure and products. The lemma `mem_closure_ne_iff_frequently_within` says that $z$ is a limit point of $s$ if and only if $s$ is frequent in `𝓝[≠] z`. The lemma `IsClosed.mem_of_nhdsWithin_neBot` says that a closed set contains each $x$ with $\mathcal{N}_s(x) \ne \bot$. For products, `nhdsWithin_prod` gives the product of two relative neighbourhoods, and `nhdsWithin_pi_eq` computes the relative filter of a box $\prod_{i \in I} s_i$ for a finite $I$. The instance `instNeBotNhdsWithinUnivPi` and the lemma `nhdsWithin_pi_neBot` say when the filter of a box is proper.

#### The neighbourhood filter of a set

The filter `nhdsSet s` is the supremum $\bigsqcup_{x \in s} \mathcal{N}(x)$. A set is in it if and only if it is a neighbourhood of each point of $s$, by `mem_nhdsSet_iff_forall`, and this holds if and only if it contains an open set that contains $s$, by `mem_nhdsSet_iff_exists`. So `hasBasis_nhdsSet` gives the basis of open sets $U \supseteq s$. The first statement is the definition of a supremum of filters: $t \in \bigsqcup_i F_i$ if and only if $t \in F_i$ for each $i$. The second statement takes for each $x \in s$ an open $U_x \subseteq t$ with $x \in U_x$, and the union $\bigcup_x U_x$.

| Lean name | Statement |
|---|---|
| `nhdsSet_singleton` | $\mathcal{N}(\{x\}) = \mathcal{N}(x)$ |
| `nhdsSet_union` | $\mathcal{N}(s \cup t) = \mathcal{N}(s) \sqcup \mathcal{N}(t)$ |
| `nhdsSet_iUnion` | $\mathcal{N}(\bigcup_i s_i) = \bigsqcup_i \mathcal{N}(s_i)$ |
| `nhds_le_nhdsSet` | $\mathcal{N}(x) \le \mathcal{N}(s)$ for $x \in s$ |
| `nhdsSet_eq_principal_iff` | $\mathcal{N}(s) = \mathcal{P}(s) \iff s$ is open |
| `nhdsSet_interior` | $\mathcal{N}(\mathrm{int}\ s) = \mathcal{P}(\mathrm{int}\ s)$ |
| `subset_interior_iff_mem_nhdsSet` | $s \subseteq \mathrm{int}\ t \iff t \in \mathcal{N}(s)$ |
| `nhdsSet_diagonal` | the filter of the diagonal of $X \times X$ is $\bigsqcup_x \mathcal{N}(x, x)$ |

The lemma `eventually_nhdsSet_iff_forall` is the eventual form: a property holds near $s$ if and only if it holds near each point of $s$. The value of this filter appears with compact sets. If a property holds near each point of a compact set $K$, then it holds on a neighbourhood of $K$, and the statement "on a neighbourhood of $K$" is "eventually in `𝓝ˢ K`". The lemma `IsClosed.nhdsSet_le_sup` cuts the filter of $s$ along a closed set $t$, and `Filter.Eventually.union_nhdsSet` treats a union.

The filter `nhdsSetWithin s t`, written `𝓝ˢ[t] s`, is $\mathcal{N}(s) \sqcap \mathcal{P}(t)$. Its API is in `Mathlib.Topology.NhdsWithin`, and it follows the pattern of `nhdsWithin`: `mem_nhdsSetWithin`, `nhdsSetWithin_hasBasis`, `nhdsSetWithin_univ`, `nhdsSetWithin_singleton`.

#### The neighbourhood kernel

The module `Mathlib.Topology.NhdsKer` treats `nhdsKer s`, the intersection of the open sets that contain $s$. It is the kernel of the filter $\mathcal{N}(s)$, the intersection of its members. In a $T_1$ space it is $s$ itself. In general it is larger, and it is described by specialization. The point $x$ specializes to $y$, written $x \rightsquigarrow y$ and `x ⤳ y` in Lean, if $\mathcal{N}(x) \le \mathcal{N}(y)$. This holds if and only if $y$ lies in the closure of $\{x\}$, and if and only if each open set that contains $y$ also contains $x$. The lemma `mem_nhdsKer_singleton` says that $x \in \mathrm{nhdsKer}\ \{y\}$ if and only if $x \rightsquigarrow y$. The proof is a reading of the definitions: $x \in \mathrm{nhdsKer}\ \{y\}$ means that each open $U$ with $y \in U$ contains $x$, and this is the third form of $x \rightsquigarrow y$.

The general form is `mem_nhdsKer_iff_specializes`: $x \in \mathrm{nhdsKer}\ s$ if and only if $x \rightsquigarrow y$ for some $y \in s$. The operation is a closure operator for the topology of the specialization order: `subset_nhdsKer`, `nhdsKer_mono`, `nhdsKer_nhdsKer`, and `IsOpen.nhdsKer_eq` for an open $s$. Unlike the intersection of open sets in general, it commutes with all unions: `nhdsKer_union`, `nhdsKer_iUnion`, `nhdsKer_sUnion`. It commutes with products by `nhdsKer_prod` and `nhdsKer_pi`. The lemma `nhdsKer_eq_nhdsKer_iff_nhdsSet` says that two sets have the same kernel if and only if they have the same neighbourhood filter.

#### Functions defined by cases

The module `Mathlib.Topology.Piecewise` answers one question: when is a function defined by cases continuous? Let $f, g : X \to Y$ and let $p$ be a predicate. The function $x \mapsto \text{if } p(x) \text{ then } f(x) \text{ else } g(x)$ is continuous if $f$ is continuous on the closure of $\{p\}$, $g$ is continuous on the closure of $\{\neg p\}$, and $f = g$ on the frontier of $\{p\}$. This is `continuous_if`. The form `continuous_piecewise` uses `Set.piecewise`, and `Continuous.if` asks for continuity of $f$ and $g$ on all of $X$. The versions `ContinuousOn.if` and `ContinuousOn.piecewise` work on a set.

The proof of `continuous_if` uses `Filter.Tendsto.piecewise_nhdsWithin` at each point $a$. Near $a$, split the filter $\mathcal{N}(a)$ into $\mathcal{N}_{\{p\}}(a) \sqcup \mathcal{N}_{\{\neg p\}}(a)$. If $a$ lies in the closure of $\{p\}$, then $f$ tends to $f(a)$ along the first part. If $a$ lies in the closure of $\{\neg p\}$, then $g$ tends to $g(a)$ along the second part. If $a$ lies in both closures, it lies in the frontier, and $f(a) = g(a)$. If $a$ lies in only one closure, the other part is the bottom filter. In each case the function tends to its value at $a$.

The lemma `continuousAt_update_same` treats a change of $f$ at one point: `Function.update f x y` is continuous at $x$ if and only if $f(z) \to y$ as $z \to x$ with $z \ne x$. The lemma `IsOpen.ite` says that a set given by cases from two open sets is open when the two sets agree on the frontier.

#### Partial functions

The module `Mathlib.Topology.Partial` connects the topology with the partial functions `X →. Y` and the filter predicates `Filter.PTendsto` and `Filter.RTendsto`. The predicate `PContinuous f` says that the preimage of each open set under $f$ is open. The lemma `open_dom_of_pcontinuous` shows that the domain of such an $f$ is open, and `pcontinuous_iff'` gives the filter form. The lemma `continuousWithinAt_iff_ptendsto_res` says that continuity within $s$ at $x$ is the limit of the restriction of $f$ to $s$, a partial function. The lemmas `ptendsto_nhds` and `rtendsto_nhds` give the criterion with open sets. This module is a bridge for the theory of computable functions and is rare in analysis.

#### Common errors

1. `𝓝[s] x` does not need $x \in s$. If $x \notin \overline{s}$, then the filter is $\bot$, and each statement `Tendsto f (𝓝[s] x) l` is true for a trivial reason. A theorem that needs a real limit asks for `(𝓝[s] x).NeBot` or for $x \in \overline{s}$.
2. `nhdsWithin_eq_map_subtypeVal` needs the proof $a \in s$, since the point of the subtype needs it. For $a \notin s$, use `mem_nhdsWithin_iff_eventually` and stay in $X$.
3. `nhdsKer s` is the intersection of the open sets that contain $s$, not the interior of $s$ and not the closure. In a $T_1$ space it is $s$, and the lemmas about it only matter for spaces that are not $T_1$.

### Exercises

1. (A) Prove `nhdsWithin_union` from `nhdsWithin` as $\mathcal{N}(x) \sqcap \mathcal{P}(s)$ and the distributive law of filters.
2. (A) Show that `𝓝[s] x = ⊥` if and only if $x$ is not in the closure of $s$.
3. (A) Use `continuous_if` to prove that $x \mapsto \max(x, 0)$, written by cases, is continuous on $\mathbb{R}$.
4. (B) Prove that $s \in \mathcal{N}(K)$ for a compact $K$ if and only if $s$ contains an open set that contains $K$, and give an example where $\mathcal{N}(K)$ has no countable basis.
5. (B) In the Sierpiński space $\{0, 1\}$ with open sets $\emptyset, \{1\}, \{0, 1\}$, compute `nhdsKer {1}` and `nhdsKer {0}`, and check `mem_nhdsKer_singleton`.
6. (C) Prove `nhdsKer_iUnion`: the neighbourhood kernel commutes with all unions. Show by an example that the intersection of the open sets that contain $s$ need not be open.

### Reference

<?reference?>
