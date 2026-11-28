---
title: Functions on sets, restrictions and piecewise functions
kind: api
modules:
  - Mathlib.Data.Set.Function
  - Mathlib.Data.Set.Restrict
  - Mathlib.Data.Set.Piecewise
  - Mathlib.Data.Set.UnionLift
  - Mathlib.Data.Set.BoolIndicator
explains:
  E2: [Set.BijOn.mk, Set.mapsTo_iff_image_subset, Set.InjOn.image_inter, Set.injOn_insert, Set.SurjOn.exists_bijOn_subset, Set.InjOn.leftInvOn_invFunOn, Set.MapsTo.restrict_inj, Set.injOn_iff_injective, Set.range_piecewise, Set.iUnionLift_mk]
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

## Functions on sets, restrictions and piecewise functions

### Overview

In the library a function $f : \alpha \to \beta$ is always defined on all of $\alpha$. But many statements of mathematics are about a function on a set: $f$ is injective on $s$, $f$ sends $s$ into $t$, $f$ is a bijection from $s$ onto $t$. The library states these with predicates that take the function and the sets as arguments, for example `Set.InjOn f s`, and keeps $f$ a total function. A second way is to make a function on the subtype of $s$, a *restriction*. The modules of this section give both ways and the bridges between them.

The section also gives three constructions of functions from sets. The piecewise function `Set.piecewise s f g` is $f$ on $s$ and $g$ off $s$. The map `Set.iUnionLift` glues functions on the sets $S_i$ into one function on their union, if the functions agree on the overlaps. And `Set.boolIndicator s` is the indicator of $s$ with values in `Bool`.

### The library around it

#### The predicates on a set

The predicates are defined in `Mathlib.Data.Set.Operations`, and the module `Mathlib.Data.Set.Function` holds their API, about 500 results. The table gives the definitions.

| Lean name | Meaning |
|---|---|
| `Set.MapsTo f s t` | $\forall x \in s,\ f(x) \in t$ |
| `Set.InjOn f s` | $\forall x, y \in s,\ f(x) = f(y) \implies x = y$ |
| `Set.SurjOn f s t` | $t \subseteq f(s)$ |
| `Set.BijOn f s t` | `MapsTo`, `InjOn` and `SurjOn` together |
| `Set.EqOn f g s` | $\forall x \in s,\ f(x) = g(x)$ |
| `Set.LeftInvOn g f s` | $\forall x \in s,\ g(f(x)) = x$ |
| `Set.InvOn g f s t` | $g$ is a left inverse of $f$ on $s$ and $f$ is a left inverse of $g$ on $t$ |

The definitions unfold to statements with a bound point, so `intro x hx` starts most proofs. The rule `Set.BijOn.mk` builds a bijection on sets from its three parts, and `Set.BijOn.mapsTo`, `Set.BijOn.injOn` and `Set.BijOn.surjOn` take it apart. Each predicate has a bridge to images and preimages:

$$\operatorname{MapsTo}(f, s, t) \iff f(s) \subseteq t \iff s \subseteq f^{-1}(t).$$

These are `Set.mapsTo_iff_image_subset` and `Set.mapsTo_iff_subset_preimage`. In the same way `Set.image_eq_iff_surjOn_mapsTo` says that $f(s) = t$ if and only if $f$ maps $s$ into $t$ and onto $t$, and `Set.BijOn.image_eq` gives $f(s) = t$ for a bijection on sets.

#### Rules for each predicate

The results of the module follow a fixed pattern. For each predicate `P` there are rules for the empty set, the whole type, a singleton, a union, a smaller set, a composition and a function equal on the set: `Set.InjOn.mono`, `Set.MapsTo.comp`, `Set.BijOn.comp`, `Set.EqOn.image_eq` and so on. A rule with the predicate as a hypothesis has a name with a dot after the predicate, as in `Set.InjOn.mono`. A rule that proves the predicate of a construction has a name in snake case, as in `Set.injOn_union`.

Injectivity on a set has the most results. An injective function on $u$ keeps intersections of subsets of $u$:

$$\operatorname{InjOn}(f, u),\ s, t \subseteq u \implies f(s \cap t) = f(s) \cap f(t).$$

This is `Set.InjOn.image_inter`. Without injectivity only the inclusion $\subseteq$ holds, which is `Set.image_inter_subset` of Section 1. Injectivity on a set grows one point at a time by `Set.injOn_insert`: if $a \notin s$, then $f$ is injective on $s \cup \{a\}$ if and only if $f$ is injective on $s$ and $f(a) \notin f(s)$. For two disjoint sets, `Set.injOn_union` asks in addition that the images of the two parts do not meet. An induction on a finite set uses these two rules. Other useful rules are `Set.InjOn.ne_iff`, which gives $f(x) \ne f(y) \iff x \ne y$ for $x, y \in s$, and `Set.InjOn.image_of_comp`, which says that if $g \circ f$ is injective on $s$ then $g$ is injective on $f(s)$.

Each surjection on sets contains a bijection on sets. If $f$ maps $s$ onto $t$, then a subset $s' \subseteq s$ exists such that $f$ is a bijection from $s'$ onto $t$:

$$\operatorname{SurjOn}(f, s, t) \implies \exists\, s' \subseteq s,\ \operatorname{BijOn}(f, s', t).$$

This is `Set.SurjOn.exists_bijOn_subset`, and `Set.exists_subset_bijOn` is the case $t = f(s)$. The proof chooses one preimage in $s$ for each point of $t$, and the chosen set is $s'$.

#### Inverses on a set

The choice of preimages has a name. For a nonempty type $\alpha$, `Function.invFunOn f s b` is a point $a \in s$ with $f(a) = b$ if such a point exists, and an arbitrary point otherwise. The rule `Function.invFunOn_eq` says that $f(\operatorname{invFunOn}(f, s, b)) = b$ when $b \in f(s)$. From it come the inverses on a set:

1. `Set.InjOn.leftInvOn_invFunOn`: if $f$ is injective on $s$, then `Function.invFunOn f s` is a left inverse of $f$ on $s$;
2. `Set.SurjOn.rightInvOn_invFunOn`: if $f$ maps $s$ onto $t$, then it is a right inverse of $f$ on $t$;
3. `Set.BijOn.invOn_invFunOn`: for a bijection on sets it is an inverse on the two sets.

In the other direction, `Set.InvOn.bijOn` says that two maps that are inverses on $s$ and $t$ and that map each set into the other are bijections on sets. The definition `Set.BijOn.equiv` in `Mathlib.Logic.Equiv.Set` turns a bijection on sets into an equivalence of subtypes $s \simeq t$.

#### Restrictions

The second way to talk about a function on a set is the subtype. The module `Mathlib.Data.Set.Restrict` gives four restrictions.

1. `Set.domRestrict s f : s → β` restricts the domain, with `Set.domRestrict_apply` as its rule.
2. `Set.codRestrict f s h : ι → s` restricts the codomain, from a proof $h$ that each value is in $s$.
3. `Set.MapsTo.restrict f s t h : s → t` restricts both, from a proof $h$ of `Set.MapsTo f s t`.
4. `Set.restrictPreimage t f` is the restriction $f^{-1}(t) \to t$.

The bridges between the predicates and the restrictions are short:

$$\operatorname{InjOn}(f, s) \iff \operatorname{Injective}(f|_s), \qquad \operatorname{SurjOn}(f, s, \alpha) \iff \operatorname{Surjective}(f|_s).$$

These are `Set.injOn_iff_injective` and `Set.surjOn_iff_surjective`. For the restriction of both sides, `Set.MapsTo.restrict_inj` says that `Set.MapsTo.restrict f s t h` is injective if and only if $f$ is injective on $s$, and `Set.MapsTo.restrict_surjective_iff` does the same for surjectivity onto $t$. The rule `Set.MapsTo.coe_restrict` says that the inclusion of $t$ after `Set.MapsTo.restrict` is `Set.domRestrict s f`. Use the predicates to state results, and use the restrictions when a later step needs a function between types, for example a card of a subtype.

#### Piecewise functions

For a set $s$ with decidable membership, `Set.piecewise s f g` is the function

$$x \mapsto \begin{cases} f(x) & x \in s, \\ g(x) & x \notin s. \end{cases}$$

The definition is in `Mathlib.Logic.Function.Basic`, and the module `Mathlib.Data.Set.Piecewise` holds the results. The rules `Set.piecewise_eq_of_mem` and `Set.piecewise_eq_of_notMem` compute the values, and `Set.piecewise_eqOn` and `Set.piecewise_eqOn_compl` state them as `Set.EqOn`. The range is the union of two images:

$$\operatorname{range}(\operatorname{piecewise}(s, f, g)) = f(s) \cup g(s^c).$$

This is `Set.range_piecewise`. The rule `Set.injective_piecewise_iff` says that the piecewise function is injective if and only if $f$ is injective on $s$, $g$ is injective on $s^c$, and $f(x) \ne g(y)$ for $x \in s$ and $y \notin s$. Other rules give the piecewise function on `∅`, `Set.univ`, a singleton and an insertion (`Set.piecewise_insert`), and for an order on the values, `Set.piecewise_le` and `Set.le_piecewise` compare it with a third function.

#### Gluing functions on a cover

Let $S : \iota \to \operatorname{Set} \alpha$ be a family of sets, and let $f_i : S_i \to \beta$ be functions that agree on each overlap $S_i \cap S_j$. Then `Set.iUnionLift S f hf T hT` is a function $T \to \beta$ on each set $T \subseteq \bigcup_i S_i$, where the fourth argument is the proof of agreement. Its value at a point of $S_i$ is the value of $f_i$: this is `Set.iUnionLift_mk` and `Set.iUnionLift_of_mem`. When the family covers the whole type, `Set.liftCover` gives a function $\alpha \to \beta$, with the rules `Set.liftCover_coe` and `Set.liftCover_of_mem`.

For a directed family, the module also lifts operations. The results `Set.iUnionLift_unary` and `Set.iUnionLift_binary` say that if each $f_i$ is compatible with a unary or a binary operation, then the glued function is compatible with it too. The library uses them to glue homomorphisms on a directed union of substructures.

#### The Boolean indicator

The function `Set.boolIndicator s : α → Bool` takes the value `true` on $s$ and `false` off $s$. The rule `Set.mem_iff_boolIndicator` gives $x \in s$ if and only if the value is `true`, and `Set.notMem_iff_boolIndicator` gives the dual. The preimages of the two values are $s$ and $s^c$ (`Set.preimage_boolIndicator_true` and `Set.preimage_boolIndicator_false`). It uses classical logic, so it is not a function to evaluate. For an indicator with values in a type with a zero, use `Set.indicator`.

#### Common errors

1. A learner proves `Function.Injective f` when the statement asks for `Set.InjOn f s`. The global form is stronger and often false. Apply `Function.Injective.injOn` only if $f$ is injective on all of $\alpha$.
2. A learner uses `Set.SurjOn f s t` as "$f(s) = t$". It says only $t \subseteq f(s)$. For an equality, add `Set.MapsTo f s t` and use `Set.image_eq_iff_surjOn_mapsTo`.
3. A learner writes `Set.piecewise s f g` and gets an error about a missing instance. The definition needs a decidable membership in $s$. Add `classical` at the start of the proof, or give the instance.

### Exercises

1. (A) Show that $x \mapsto x^2$ is injective on $[0, \infty)$ in $\mathbb{R}$ but not injective on $\mathbb{R}$, and state both facts in Lean.
2. (A) Prove `Set.mapsTo_iff_image_subset` from the definitions.
3. (B) Prove `Set.injOn_insert` from the definition of `Set.InjOn`.
4. (B) Find $f$, $s$, $t$ with $f(s \cap t) \ne f(s) \cap f(t)$, and check which condition of `Set.InjOn.image_inter` fails.
5. (B) Use `Set.injective_piecewise_iff` to show that the map $\mathbb{Z} \to \mathbb{Z}$ equal to $n / 2$ on the even numbers and to $n$ on the odd numbers is not injective.
6. (C) Use `Set.liftCover` to define a function on $\mathbb{R}$ from $x \mapsto 0$ on $(-\infty, 0]$ and $x \mapsto x$ on $[0, \infty)$, and show that it is the function $\max(x, 0)$.

### Reference

<?reference?>
