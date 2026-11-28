---
title: Continuity on a set, dense embeddings and extension
kind: api
modules:
  - Mathlib.Topology.ContinuousOn
  - Mathlib.Topology.ExtendFrom
  - Mathlib.Topology.DenseEmbedding
explains:
  E2: [continuousOn_iff_continuous_domRestrict, ContinuousOn.comp, continuous_of_cover_nhds, ContinuousOn.union_of_isClosed, IsDenseInducing, IsDenseInducing.extend, IsDenseInducing.extend_eq, IsDenseInducing.continuous_extend, isClosed_property, continuous_extendFrom]
  E1: auto
families: []
requires: [V01, V04, V13.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Continuity on a set, dense embeddings and extension

### Overview

Analysis often meets a function that is continuous only on a part of its domain. The function $x \mapsto 1/x$ on $\mathbb{R}$ is continuous on $\mathbb{R} \setminus \{0\}$, and the function $\sqrt{x}$ is continuous on $[0, \infty)$. Mathlib keeps such a function on the whole type and adds a set to the predicate: `ContinuousOn f s` says that $f$ is continuous on $s$ for the subspace topology of $s$. Section 2 defined the pointwise form `ContinuousWithinAt f s x`, the limit `Tendsto f (𝓝[s] x) (𝓝 (f x))` along the filter `𝓝[s] x` of neighbourhoods of $x$ within $s$.

This section describes the library around these two predicates in `Mathlib.Topology.ContinuousOn`. It then treats the converse problem: a function is given on a part of a space, and the task is to extend it continuously to the whole space. The module `Mathlib.Topology.DenseEmbedding` solves this problem along a dense inducing map, and the module `Mathlib.Topology.ExtendFrom` solves it from a dense subset. The completion of Chapter 7 uses these extensions.

### The library around it

#### The two predicates and the subspace

By definition, `ContinuousOn f s` is the statement `∀ x ∈ s, ContinuousWithinAt f s x`. The value of $f$ outside $s$ plays no part. The link with the subspace topology is the equivalence `continuousOn_iff_continuous_domRestrict`:

$$\text{ContinuousOn } f\ s \iff \text{the restriction } s \to Y,\ x \mapsto f(x), \text{ is continuous.}$$

The restriction is `s.domRestrict f`, a function on the subtype. The pointwise form is `continuousWithinAt_iff_continuousAt_domRestrict`. When $f$ maps $s$ into a set $t$, the restriction with values in $t$ is continuous by `ContinuousOn.mapsToRestrict`. A proof that wants to use a theorem about continuous maps on a space can pass to the subtype with these lemmas, apply the theorem, and come back.

The predicate has the open set characterisation `continuousOn_iff`: for each $x \in s$ and each open $t \ni f(x)$ there is an open $u \ni x$ with $u \cap s \subseteq f^{-1}(t)$. The closed set form is `continuousOn_iff_isClosed`. On an open set $s$ there is the shorter form `continuousOn_open_iff`: $s \cap f^{-1}(t)$ is open for each open $t$.

The relation with the global notions goes in both directions.

| Lean name | Statement |
|---|---|
| `Continuous.continuousOn` | a continuous map is continuous on each set |
| `ContinuousAt.continuousWithinAt` | continuity at $x$ gives continuity at $x$ within each set |
| `continuousWithinAt_univ` | within `Set.univ` is the same as at the point |
| `continuousWithinAt_iff_continuousAt` | within $s$ is the same as at $x$ when $s \in \mathcal{N}(x)$ |
| `ContinuousOn.continuousAt` | continuity on $s$ gives continuity at each $x$ with $s \in \mathcal{N}(x)$ |
| `IsOpen.continuousOn_iff` | on an open set, continuity on $s$ is continuity at each point of $s$ |
| `continuousWithinAt_of_notMem_closure` | each map is continuous within $s$ at a point outside the closure of $s$ |

#### Composition, restriction and congruence

The composition lemma needs a condition on the sets. `ContinuousOn.comp` states: if $g$ is continuous on $t$, $f$ is continuous on $s$ and $f$ maps $s$ into $t$ (`Set.MapsTo f s t`), then $g \circ f$ is continuous on $s$. The proof is one line at each point: `ContinuousWithinAt.comp` composes the limits $f \to f(x)$ along `𝓝[s] x` and $g \to g(f(x))$ along `𝓝[t] (f x)`, and the hypothesis `Set.MapsTo f s t` says that $f$ sends `𝓝[s] x` into `𝓝[t] (f x)`. The variants `ContinuousOn.comp_inter` and `ContinuousWithinAt.comp_inter` use $s \cap f^{-1}(t)$ in place of a `Set.MapsTo` hypothesis. `Continuous.comp_continuousOn` and `ContinuousOn.comp_continuous` treat the case where one map is continuous everywhere. The forms such as `ContinuousWithinAt.comp_of_eq` take an extra equality $f(x) = y$, which helps when the point $f(x)$ appears in a rewritten form.

A smaller set gives a weaker condition: `ContinuousOn.mono` and `ContinuousWithinAt.mono` restrict to a subset. The set matters only near the point. `continuousWithinAt_congr_set` replaces $s$ by $t$ when $s$ and $t$ agree near $x$, and `continuousWithinAt_insert_self` says that adding the point $x$ to $s$ changes nothing. Two functions that agree on $s$ are continuous on $s$ together, by `ContinuousOn.congr` and `continuousOn_congr`. Two functions that agree eventually along `𝓝[s] x` and at $x$ are continuous within $s$ at $x$ together, by `ContinuousWithinAt.congr_of_eventuallyEq`.

The constructions of Chapter 1 have their relative forms: `ContinuousOn.prodMk`, `ContinuousOn.fst`, `ContinuousOn.snd`, `ContinuousOn.prodMap`, `continuousWithinAt_prod_iff`, `continuousOn_pi` and `continuousWithinAt_pi`. Most of these lemmas carry the attribute `fun_prop`, so the tactic `fun_prop` proves goals of the form `ContinuousOn (fun x ↦ ...) s`.

#### Gluing continuity from pieces

Three lemmas build global continuity from local pieces.

- `continuous_of_cover_nhds`: if each point has a neighbourhood $s_i$ from a family, and $f$ is continuous on each $s_i$, then $f$ is continuous.
- `ContinuousOn.union_of_isClosed`: continuity on two closed sets gives continuity on their union. The equivalence form is `continuousOn_union_iff_of_isClosed`.
- `continuousOn_iUnion_iff_of_isOpen`: continuity on a union of open sets is continuity on each of them.

The proof of `continuous_of_cover_nhds` is short. Fix $x$ and take $i$ with $s_i \in \mathcal{N}(x)$. Then $f$ is continuous within $s_i$ at $x$, and since $s_i$ is a neighbourhood of $x$, the filter `𝓝[s_i] x` is `𝓝 x`, so $f$ is continuous at $x$. For two closed sets $A$ and $B$, a point $x \in A \setminus B$ has the neighbourhood $B^c$, and on $B^c$ the union $A \cup B$ agrees with $A$; a point in $A \cap B$ uses `continuousWithinAt_union`, which splits `𝓝[A ∪ B] x` as the supremum of `𝓝[A] x` and `𝓝[B] x`. This is the pasting lemma of a first course, used to define a path as the concatenation of two paths.

The module also has the closure lemmas `ContinuousWithinAt.mem_closure_image` and `ContinuousOn.image_closure`: a map continuous on the closure of $s$ sends it into the closure of $f(s)$. The lemmas `continuousOn_singleton`, `Set.Subsingleton.continuousOn` and `continuousOn_const` give the trivial cases, and `ContinuousOn.iterate` gives the continuity of the iterates $f^{[n]}$ on a set that $f$ maps into itself.

#### Dense inducing maps

The structure `IsDenseInducing i` says that $i : \alpha \to \beta$ is inducing (the topology of $\alpha$ is the topology induced by $i$) and that its range is dense. The structure `IsDenseEmbedding i` adds that $i$ is injective. The constructors are `IsDenseInducing.mk` and `IsDenseEmbedding.mk'`. Examples: the inclusion of a dense subset, `Dense.isDenseEmbedding_val`; the inclusion of $\mathbb{Q}$ in $\mathbb{R}$. The map of a uniform space into its completion is dense inducing. Products of dense embeddings are dense embeddings, by `IsDenseEmbedding.prodMap`. The neighbourhood filter of $a$ is the preimage of the neighbourhood filter of $i(a)$, `IsDenseInducing.nhds_eq_comap`, and density gives that `comap i (𝓝 b)` is a proper filter for each $b$.

Density gives a principle of extension of identities, `isClosed_property`: if $p$ defines a closed set and $p(i(a))$ holds for each $a$, then $p(b)$ holds for each $b$. The reason: the set $\{b \mid p(b)\}$ is closed and contains the dense set $i(\alpha)$, so it is all of $\beta$. The variants `isClosed_property2`, `isClosed_property3` and `DenseRange.induction_on` treat two or three variables. A typical use is `DenseRange.equalizer`: two continuous maps into a Hausdorff space that agree on a dense range are equal.

#### Extension along a dense inducing map

Let $i : \alpha \to \beta$ be dense inducing and $f : \alpha \to \gamma$. The definition `IsDenseInducing.extend` gives $\bar f : \beta \to \gamma$ with

$$\bar f(b) = \lim_{\mathrm{comap}\, i\, \mathcal{N}(b)} f,$$

the value `Filter.limUnder` of $f$ along the filter of points of $\alpha$ whose image is near $b$. If the limit does not exist, the value is a junk value. The main results are these.

- `IsDenseInducing.extend_eq`: if $\gamma$ is Hausdorff and $f$ is continuous, then $\bar f(i(a)) = f(a)$.
- `IsDenseInducing.extend_eq_of_tendsto`: if $f$ tends to $c$ along `comap i (𝓝 b)`, then $\bar f(b) = c$.
- `IsDenseInducing.continuous_extend`: if $\gamma$ is regular (`T3Space`) and $f$ has a limit along `comap i (𝓝 b)` for each $b$, then $\bar f$ is continuous.
- `IsDenseInducing.extend_unique`: a continuous $g$ with $g \circ i = f$ is equal to $\bar f$.

The regularity hypothesis in `IsDenseInducing.continuous_extend` is a real condition, and Chapter 4 defines it. The proof sketch: fix $b$ and a closed neighbourhood $V$ of $\bar f(b)$. By hypothesis there is an open $U \ni b$ with $f(i^{-1}(U)) \subseteq V$. For $b' \in U$ the value $\bar f(b')$ is a limit of values of $f$ in $V$, and $V$ is closed, so $\bar f(b') \in V$. Since closed neighbourhoods form a basis in a regular space, $\bar f$ is continuous at $b$. The pointwise form is `IsDenseInducing.continuousAt_extend`. The form for a dense subset is `Dense.extend`, with `Dense.continuous_extend` and `Dense.extend_eq`.

#### Extension from a subset

The module `Mathlib.Topology.ExtendFrom` defines `extendFrom A f`, the function $x \mapsto \lim_{\mathcal{N}_A(x)} f$, where $\mathcal{N}_A(x)$ is `𝓝[A] x`. Here $f$ is a function on the whole space $X$, and only its values on $A$ count. `extendFrom_extends` says that the extension agrees with $f$ on $A$ when $f$ is continuous on $A$ and $Y$ is Hausdorff. `continuous_extendFrom` says that the extension is continuous when $A$ is dense, $Y$ is regular, and $f$ has a limit within $A$ at each point. The relative form `continuousOn_extendFrom` gives continuity on a set $B \subseteq \overline{A}$. This form suits a function given by a formula on an open set, such as $\sin(x)/x$ on $\mathbb{R} \setminus \{0\}$.

#### Common errors

1. `ContinuousOn f s` does not say that $f$ is continuous at the points of $s$. The function $\mathbf{1}_{[0,1]}$ is continuous on $[0,1]$, but it is not continuous at $0$. Use `ContinuousOn.continuousAt` with a proof that $s$ is a neighbourhood of the point.
2. `ContinuousOn.comp` needs `Set.MapsTo f s t`, not $f(s) = t$ and not a statement about the range of $f$. The tactic `fun_prop` cannot find this hypothesis by itself in most cases.
3. `IsDenseInducing.extend f` is defined for each $f$, also when no continuous extension exists. Each useful lemma about it has a hypothesis on limits or on continuity, and the extension lemmas need a Hausdorff or regular codomain.

### Exercises

1. (A) Prove that $x \mapsto 1/x$ is continuous on $\{x \in \mathbb{R} \mid x \ne 0\}$, and state the result as `ContinuousOn (fun x : ℝ ↦ x⁻¹) {0}ᶜ`.
2. (A) Use `ContinuousOn.union_of_isClosed` to prove that the function equal to $x$ on $(-\infty, 0]$ and to $x^2$ on $[0, \infty)$ is continuous.
3. (B) Show that `ContinuousOn f s` does not follow from continuity of $f$ on each of two sets whose union is $s$, if the sets are not closed and not open. Give a counterexample on $\mathbb{R}$.
4. (B) Prove `DenseRange.equalizer` from `isClosed_property` and the fact that the equalizer of two continuous maps into a Hausdorff space is closed.
5. (B) Let $i : \mathbb{Q} \to \mathbb{R}$ be the inclusion. Show that $f(q) = 1$ for $q^2 < 2$ and $f(q) = 0$ for $q^2 > 2$ is continuous on $\mathbb{Q}$ but has no continuous extension to $\mathbb{R}$. Which hypothesis of `IsDenseInducing.continuous_extend` fails?
6. (C) Prove `IsDenseInducing.continuous_extend` in detail from the sketch above. Explain where the proof uses that the closed neighbourhoods of a point form a basis of its neighbourhood filter.

### Reference

<?reference?>
