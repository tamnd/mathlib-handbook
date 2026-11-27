---
title: Flows and invariant sets
kind: theory
modules:
  - Mathlib.Dynamics.Flow
explains:
  E3: [Flow, IsInvariant, IsForwardInvariant, Flow.orbit, Flow.forwardOrbit, Flow.restrict, Flow.toHomeomorph, Flow.IsSemiconjugacy, Flow.IsFactorOf]
  E2: [Flow.map_add, Flow.map_zero, Flow.continuous_toFun, Flow.fromIter, Flow.fromIter_apply, Homeomorph.flow, Homeomorph.flow_apply, Flow.reverse, Flow.isInvariant_iff_image_eq, isForwardInvariant_iff_isInvariant, Flow.isInvariant_orbit, Flow.orbit_restrict, Flow.IsSemiconjugacy.comp, Flow.IsSemiconjugacy.isFactorOf, Flow.IsFactorOf.trans, Flow.toAddAction]
  E1: auto
families: []
requires: [V05, V13, V14, V17, V21.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Flows and invariant sets

### Overview

A flow is a family of maps $\phi_t$, one for each time $t$, with $\phi_{s + t} = \phi_s \circ \phi_t$ and $\phi_0 = \mathrm{id}$, continuous in the time and the point together. Time may be $\mathbb{N}$ (iterates of a map), $\mathbb{Z}$ (powers of a homeomorphism) or $\mathbb{R}$ (solutions of an autonomous equation). The section defines flows, invariant sets and orbits, and the maps between flows: semiconjugacies and factors. Group actions come from Volume 5, Chapter 6, topological monoids from Volume 14, and the topology from Volume 13.

### Definitions

**Definition (Flow).** Let $\tau$ be a topological additive monoid and $X$ a topological space. A *flow* of $\tau$ on $X$ is a map $\phi : \tau \times X \to X$, written $\phi_t(x) = \phi(t, x)$, such that $\phi$ is continuous on the product $\tau \times X$, $\phi_{s + t}(x) = \phi_s(\phi_t(x))$ and $\phi_0(x) = x$ for all $s, t, x$.

So a flow is a jointly continuous action of $\tau$. Each $\phi_t$ is continuous, as the composite of $x \mapsto (t, x)$ and $\phi$.

::: mathlib
`Flow` · `Mathlib.Dynamics.Flow`

`Flow τ α` is a structure with a field `toFun : τ → α → α` and the proofs `cont' : Continuous (uncurry toFun)`, `map_add'` and `map_zero'`. A flow coerces to a function, so `ϕ t x` is the image of `x` at time `t`. The lemmas `Flow.map_add`, `Flow.map_zero` and `Flow.continuous_toFun` restate the axioms, and `Flow.toAddAction` turns a flow into an `AddAction τ α` of Volume 5.

<?decl Flow?>
:::

**Definition (Invariant set).** A set $S \subseteq X$ is *invariant* under $\phi$ if $\phi_t(S) \subseteq S$ for all $t \in \tau$. When $\tau$ is ordered, $S$ is *forward invariant* if $\phi_t(S) \subseteq S$ for all $t \ge 0$.

**Definition (Orbit).** The *orbit* of $x$ is $\{\phi_t(x) : t \in \tau\}$. When $\tau$ is ordered and addition is monotone, the *forward orbit* is $\{\phi_t(x) : t \ge 0\}$.

::: mathlib
`IsInvariant` · `Mathlib.Dynamics.Flow`

`IsInvariant ϕ s` is `∀ t, MapsTo (ϕ t) s s` for any `ϕ : τ → α → α`, with no topology. `IsForwardInvariant ϕ s` is `∀ ⦃t⦄, 0 ≤ t → MapsTo (ϕ t) s s`. For a flow one writes `IsInvariant ϕ.toFun s`. `Flow.orbit ϕ x` is the range of `fun t ↦ ϕ t x`, and `Flow.forwardOrbit ϕ x` the range over the nonnegative times (`Flow.forwardOrbit_eq_range_nonneg`).

<?decl IsInvariant?>
:::

**Definition (Semiconjugacy, factor).** Let $\phi$ be a flow on $X$ and $\psi$ a flow on $Y$, with the same time $\tau$. A *semiconjugacy* from $\phi$ to $\psi$ is a continuous surjection $\pi : X \to Y$ with $\pi \circ \phi_t = \psi_t \circ \pi$ for all $t$. Then $\psi$ is a *factor* of $\phi$. A semiconjugacy that is a homeomorphism is a *conjugacy*.

::: mathlib
`Flow.IsSemiconjugacy` · `Mathlib.Dynamics.Flow`

`Flow.IsSemiconjugacy π ϕ ψ` is a structure with the fields `cont : Continuous π`, `surj : Surjective π` and `semiconj : ∀ t, Semiconj π (ϕ t) (ψ t)`, where `Semiconj` is the notion of Chapter 1, Section 1. `ψ.IsFactorOf ϕ` says that some `π` is a semiconjugacy from `ϕ` to `ψ`; note the order of the arguments, the factor comes first.

<?decl Flow.IsSemiconjugacy?>
:::

### Theorems and proofs

**Proposition (Time as a group).** Let $\tau$ be a topological additive group and $\phi$ a flow of $\tau$ on $X$. Then each $\phi_t$ is a homeomorphism with inverse $\phi_{-t}$, and $\phi_t(S) = \phi_{-t}^{-1}(S)$ for each set $S$.

*Proof.* The axioms give $\phi_t \circ \phi_{-t} = \phi_{t + (-t)} = \phi_0 = \mathrm{id}$ and $\phi_{-t} \circ \phi_t = \mathrm{id}$ in the same way. Both maps are continuous, so $\phi_t$ is a homeomorphism. For a bijection with inverse $g$, the image of $S$ is the preimage of $S$ under $g$. $\square$

::: mathlib
`Flow.toHomeomorph` · `Mathlib.Dynamics.Flow`

`ϕ.toHomeomorph t : α ≃ₜ α` for `[AddGroup τ]`, with `toHomeomorph_apply` and `toHomeomorph_symm_apply : (ϕ.toHomeomorph t).symm x = ϕ (-t) x`. The image formula is `Flow.image_eq_preimage_symm`. `Flow.reverse` is the flow `t ↦ ϕ (-t)`.

<?decl Flow.toHomeomorph?>
:::

**Theorem (Invariant sets).** Let $\phi$ be a flow of $\tau$ on $X$.

1. Each orbit is invariant, and a union or an intersection of invariant sets is invariant.
2. The closure of an invariant set is invariant.
3. If $\tau$ is a group, then $S$ is invariant if and only if $\phi_t(S) = S$ for all $t$. Then the complement of an invariant set is invariant, and an invariant set is a union of orbits.
4. If $\tau$ is ordered and $0$ is its least element, as for $\mathbb{N}$ or $[0, \infty)$, then forward invariant and invariant are the same.

*Proof.* (1) If $y = \phi_s(x)$, then $\phi_t(y) = \phi_{t + s}(x)$ lies in the orbit of $x$.

(2) Let $S$ be invariant and $t \in \tau$. The map $\phi_t$ is continuous, so $\phi_t(\overline{S}) \subseteq \overline{\phi_t(S)} \subseteq \overline{S}$.

(3) If $S$ is invariant, then $\phi_t(S) \subseteq S$ and $\phi_{-t}(S) \subseteq S$. Apply $\phi_t$ to the second inclusion: $S = \phi_t(\phi_{-t}(S)) \subseteq \phi_t(S)$. So $\phi_t(S) = S$. The converse is clear. Since $\phi_t$ is a bijection with $\phi_t(S) = S$, it also maps the complement onto the complement. If $x \in S$, then $\phi_t(x) \in S$ for all $t$, so the orbit of $x$ lies in $S$, and $S$ is the union of the orbits of its points.

(4) Here every $t$ is $\ge 0$. $\square$

Part 3 fails for monoids: for $\phi_n(x) = x/2^n$ on $\mathbb{R}$, the set $[-1, 1]$ is invariant, but its complement is not.

::: mathlib
`Flow.isInvariant_iff_image_eq` · `Mathlib.Dynamics.Flow`

Part 3 for `[AddGroup τ]`: `IsInvariant ϕ s ↔ ∀ t, ϕ t '' s = s`. Part 1 for orbits is `Flow.isInvariant_orbit`, and part 4 is `isForwardInvariant_iff_isInvariant` under `[IsBotZeroClass τ]`. The index of this edition has no declaration for part 2; it follows from `Set.MapsTo.closure` and `Flow.continuous_toFun`.

<?decl Flow.isInvariant_iff_image_eq?>
:::

**Proposition (Restriction).** If $S$ is invariant, the maps $\phi_t|_S : S \to S$ form a flow of $\tau$ on $S$, and the orbit of $x \in S$ for the restricted flow is the orbit of $x$ for $\phi$.

*Proof.* A map into the subspace $S$ is continuous when its composite with the inclusion is, and here that composite is a restriction of $\phi$. The axioms hold pointwise, and the orbit of $x$ lies in $S$. $\square$

**Theorem (Semiconjugacies).** The composite of two semiconjugacies is a semiconjugacy, so being a factor is a transitive relation. If $\pi$ is a semiconjugacy from $\phi$ to $\psi$, then $\pi$ maps the orbit of $x$ onto the orbit of $\pi(x)$, and the image of a $\phi$-invariant set is $\psi$-invariant.

*Proof.* Let $\pi : X \to Y$ and $\rho : Y \to Z$ be semiconjugacies. Then $\rho \circ \pi$ is continuous and surjective, and $\rho \pi \phi_t = \rho \psi_t \pi = \chi_t \rho \pi$. For the orbit, $\pi(\phi_t(x)) = \psi_t(\pi(x))$, and $t$ runs over all of $\tau$ on both sides. If $S$ is $\phi$-invariant, then $\psi_t(\pi(S)) = \pi(\phi_t(S)) \subseteq \pi(S)$. $\square$

::: mathlib
`Flow.IsFactorOf` · `Mathlib.Dynamics.Flow`

`Flow.IsSemiconjugacy.comp` composes two semiconjugacies, `IsSemiconjugacy.isFactorOf` passes from a semiconjugacy to the factor relation, and `IsFactorOf.trans` and `IsFactorOf.self` make the relation a preorder.

<?decl Flow.IsFactorOf?>
:::

**Proposition (Discrete time).** Let $g : X \to X$ be continuous. Then $\phi_n = g^{[n]}$ is a flow of $\mathbb{N}$ on $X$. If $g$ is a homeomorphism, then $\phi_n = g^n$, $n \in \mathbb{Z}$, is a flow of $\mathbb{Z}$ on $X$.

*Proof.* The axioms are $g^{[m + n]} = g^{[m]} \circ g^{[n]}$ and $g^{[0]} = \mathrm{id}$. Since $\mathbb{N}$ is discrete, $\mathbb{N} \times X$ is the union of the open slices $\{n\} \times X$, and on each slice the map is the continuous $g^{[n]}$. The case of $\mathbb{Z}$ is the same. $\square$

::: mathlib
`Flow.fromIter` · `Mathlib.Dynamics.Flow`

`Flow.fromIter (h : Continuous g) : Flow ℕ α` with `fromIter_apply : (fromIter h) n x = g^[n] x`, and `Homeomorph.flow (f : α ≃ₜ α) : Flow ℤ α` with `Homeomorph.flow_apply : f.flow n x = (f ^ n) x`, the power in the group of homeomorphisms.

<?decl Flow.fromIter?>
:::

### Examples

**Example (A linear equation).** Fix $a \in \mathbb{R}$. The solutions of $x' = ax$ give the flow $\phi_t(x) = e^{at}x$ of $\mathbb{R}$ on $\mathbb{R}$. The axioms are $e^{a(s + t)}x = e^{as}(e^{at}x)$ and $e^{0}x = x$, and $(t, x) \mapsto e^{at}x$ is continuous. For $a \neq 0$ there are three orbits: $\{0\}$, $(0, \infty)$ and $(-\infty, 0)$. The invariant sets are the eight unions of these orbits. For $a < 0$ the interval $[-1, 1]$ is forward invariant, since $|e^{at}x| \le |x|$ for $t \ge 0$, but it is not invariant, since $\phi_{-1}(1) = e^{-a} > 1$.

**Example (A factor of a torus flow).** On the torus $\mathbb{T}^2 = \mathbb{R}^2/\mathbb{Z}^2$, the linear flow $\phi_t(x, y) = (x + t\alpha, y + t\beta)$ has the rotation flow $\psi_t(x) = x + t\alpha$ on $\mathbb{R}/\mathbb{Z}$ as a factor, by the first projection.

### The library around it

The file has no differential equations: the flow of $x' = v(x)$ must be built from the theorem of Picard-Lindelöf of Volume 17, Chapter 8. Later chapters of this volume mostly use maps, with `Flow.fromIter` as the bridge.

Common errors of a learner:

- `Flow` needs a topology on the time type, even for `ℕ` and `ℤ`.
- `IsInvariant` takes a function `τ → α → α`, so for a flow the argument is `ϕ.toFun`, or `ϕ` through the coercion.
- In `ψ.IsFactorOf ϕ` the factor is `ψ`, the first argument.

### Exercises

1. (A) Let $v \in \mathbb{R}^n$. Show that $\phi_t(x) = x + tv$ is a flow of $\mathbb{R}$ on $\mathbb{R}^n$ and describe its orbits.
2. (A) Let $X$ be Hausdorff. Show that the set of points fixed by all $\phi_t$ is closed and invariant. Hint: Chapter 1, Section 1.
3. (B) Show that $\pi(x) = x|x|$ conjugates the flows $e^t x$ and $e^{2t}x$ on $\mathbb{R}$.
4. (B) Let $\pi$ be a semiconjugacy from $\phi$ to $\psi$, flows of $\mathbb{Z}$. Show that if $\phi_n(x) = x$ then $\psi_n(\pi(x)) = \pi(x)$, and give an example in which the minimal period of $\pi(x)$ is smaller than that of $x$.
5. (C) Let $\phi$ be a flow of $\mathbb{R}$ on a Hausdorff space $X$, and $x$ a point with $\phi_T(x) = x$ for some $T > 0$. Show that $\{T \in \mathbb{R} : \phi_T(x) = x\}$ is a closed subgroup of $\mathbb{R}$, and deduce that the orbit of $x$ is a point or is homeomorphic to a circle. Hint: the closed subgroups of $\mathbb{R}$ are $0$, $c\mathbb{Z}$ and $\mathbb{R}$, and a continuous bijection from a compact space to a Hausdorff space is a homeomorphism.
6. (A) Show that a semiconjugacy of flows of $\mathbb{N}$ maps each forward orbit onto a forward orbit.

### Notes and history

Flows of autonomous equations go back to Poincaré's qualitative theory of differential equations. The abstract notion of a continuous action of $\mathbb{R}$ or $\mathbb{Z}$ on a topological space is the starting point of topological dynamics as presented by Gottschalk and Hedlund in 1955.

### Reference

<?reference?>
