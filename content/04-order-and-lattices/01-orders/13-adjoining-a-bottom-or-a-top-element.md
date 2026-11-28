---
title: Adjoining a bottom or a top element
kind: api
modules:
  - Mathlib.Order.TypeTags
  - Mathlib.Order.WithBot
  - Mathlib.Order.WithBotTop
  - Mathlib.Order.Set
explains:
  E2: [WithBot.coe_le_coe, WithBot.bot_lt_coe, WithBot.unbot_le_iff, WithBot.unbotD_le_iff, WithBot.monotone_iff, WithBot.instWellFoundedLT, WithBot.le_of_forall_lt_iff_le, WithBot.toDual, WithTop.lt_top_iff_ne_top, WithBotTop.coe_le_coe]
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

## Adjoining a bottom or a top element

### Overview

Many orders in mathematics are an old order with one new point at an end. The degree of a polynomial takes values in $\mathbb{N}$ with a new least point for the zero polynomial. The extended natural numbers are $\mathbb{N}$ with a new greatest point. The extended reals are $\mathbb{R}$ with a new point at each end. Mathlib builds all of these from two type formers. The type `WithBot α` is $\alpha$ with a new element $\bot$ below every element of $\alpha$, and `WithTop α` is $\alpha$ with a new element $\top$ above every element. The type `WithBotTop ι` is `WithBot (WithTop ι)`, with a new point at each end.

As types, `WithBot α` and `WithTop α` are both the option type on $\alpha$. The new point is the empty option, and the old elements enter through the coercion. The two names exist so that each type can carry its own order, and so that the notation $\bot$ or $\top$ names the new point. The type `Polynomial.degree` returns `WithBot ℕ`, the type `ENat` is `WithTop ℕ`, the type `EReal` is `WithBot (WithTop ℝ)`, and the abbreviation `EInt` is `WithBotTop ℤ`.

The module `Mathlib.Order.WithBot` is the main one. It gives the order, the lattice structure, the inverse maps that remove the new point, and the transfer of monotone maps. The module `Mathlib.Order.TypeTags` holds only the type definitions and the recursors. The module `Mathlib.Order.WithBotTop` defines the two sided version. The module `Mathlib.Order.Set` holds two lemmas about ranges.

### The library around it

#### The types and their recursors

The module `Mathlib.Order.TypeTags` defines `WithBot` and `WithTop`, the maps `WithBot.some` and `WithTop.some`, and the recursors `WithBot.recBotCoe` and `WithTop.recTopCoe`. A recursor of this kind asks for a value at the new point and a value at each coerced element. It is tagged as the default induction principle, so the tactics `induction x` and `cases x` on `x : WithBot α` give the two goals with the cases $\bot$ and $\uparrow a$, not the cases of the option type. The lemma `WithBot.none_eq_bot` and `WithBot.some_eq_coe` rewrite the option forms into the order forms when they appear.

Most lemmas in `Mathlib.Order.WithBot` carry the attribute that generates the order dual. One proof about `WithBot` gives the matching statement about `WithTop`, with $\bot$ replaced by $\top$ and each inequality reversed. A lemma name with `WithBot` therefore almost always has a twin with `WithTop`: `WithBot.bot_lt_coe` matches `WithTop.coe_lt_top`, and `WithBot.unbot_le_iff` matches `WithTop.le_untop_iff`.

#### The order

The relation $\le$ on `WithBot α` is an inductive predicate `WithBot.LE` with two rules: $\bot \le y$ for each $y$, and $\uparrow a \le \uparrow b$ when $a \le b$. The lemma `WithBot.le_def` gives the unfolded form $x \le y \leftrightarrow x = \bot \lor \exists a\, b,\ a \le b \land x = \uparrow a \land y = \uparrow b$. In practice, a proof uses three lemmas. The lemma `WithBot.coe_le_coe` says $\uparrow a \le \uparrow b \leftrightarrow a \le b$, the lemma `WithBot.bot_lt_coe` says $\bot < \uparrow a$, and the lemma `WithBot.not_coe_le_bot` says that no coerced element is below $\bot$. The first one is a simp lemma and a norm_cast lemma, so the tactics norm_cast and simp move an inequality between coerced elements down to $\alpha$. The lemma `WithBot.coe_lt_coe` is the strict version.

Mixed comparisons have their own lemmas. The lemma `WithBot.coe_le_iff` says $\uparrow a \le x \leftrightarrow \exists b,\ x = \uparrow b \land a \le b$, and `WithBot.le_coe_iff` says $x \le \uparrow b \leftrightarrow \forall a,\ x = \uparrow a \to a \le b$. The lemma `WithBot.lt_iff_exists_coe` says that $x < y$ holds exactly when $y$ is a coerced element above $x$. The lemma `WithBot.bot_lt_iff_ne_bot` turns $\bot < x$ into $x \ne \bot$. For `WithTop`, the lemma `WithTop.lt_top_iff_ne_top` does the same at the top.

The structure classes go up one step at a time. The module gives a preorder, a partial order, `WithBot.semilatticeSup`, `WithBot.semilatticeInf`, `WithBot.lattice`, `WithBot.distribLattice` and `WithBot.linearOrder` when $\alpha$ has the matching structure. The instance `WithBot.instOrderBot` makes $\bot$ the least element with no hypothesis on $\alpha$. If $\alpha$ has a top element, then `WithBot.instOrderTop` and `WithBot.instBoundedOrder` add it. The lemma `WithBot.coe_top` says that the coerced top is the top of `WithBot α`, and `WithBot.coe_sup`, `WithBot.coe_inf`, `WithBot.coe_max` and `WithBot.coe_min` say that the coercion commutes with the lattice operations.

Some order properties survive the construction. The instance `WithBot.instWellFoundedLT` says that a new least point keeps the relation $<$ well founded, and `WithBot.instWellFoundedGT` says the same for $>$. The proof is a nested induction: the new point is accessible because nothing is below it, and a coerced point is accessible by the accessibility of the old point. The lemma `WithBot.denselyOrdered_iff` says that `WithBot α` is dense if and only if $\alpha$ is dense, when $\alpha$ has no least element. The hypothesis is necessary: if $\alpha$ has a least element $m$, then $\bot < \uparrow m$ is a gap with no element between. The instance `WithBot.noMaxOrder` keeps the absence of a greatest element. The lemmas `WithBot.isMax_coe_iff` and `IsMax.withBot` say that the maximal elements of $\alpha$ stay maximal.

The lemma `WithBot.le_of_forall_lt_iff_le` is an approximation principle. In a dense linear order with no least element, $y \le x$ holds if and only if each $z$ in $\alpha$ with $x < \uparrow z$ also has $y \le \uparrow z$. This lemma is the reason that `EReal` and similar types can test an inequality on real numbers only.

#### Removing the new point

Three functions map `WithBot α` back to $\alpha$. The function `WithBot.unbot` takes a proof that $x \ne \bot$ and returns the underlying element. The lemmas `WithBot.coe_unbot` and `WithBot.unbot_coe` say that it is inverse to the coercion. The function `WithBot.unbotD` takes a default value $d$ and sends $\bot$ to $d$. The function `WithBot.unbotA` takes the default from a proof that $\alpha$ is nonempty, so its value at $\bot$ is an unknown element of $\alpha$ and a proof cannot use that value.

The order lemmas for these maps are adjunction statements. The lemma `WithBot.unbot_le_iff` says $\mathrm{unbot}(x) \le a \leftrightarrow x \le \uparrow a$ for $x \ne \bot$, and `WithBot.le_unbot_iff` is the other side. The lemma `WithBot.unbotD_le_iff` says $\mathrm{unbotD}_a(x) \le b \leftrightarrow x \le \uparrow b$, under the hypothesis that $x = \bot$ implies $a \le b$. The hypothesis covers the one case where the default value matters. The lemma `WithBot.unbotD_eq_iff` describes the fibres of `WithBot.unbotD`.

The instance `WithBot.canLift` lets the tactic `lift x to α using hx` replace a variable $x$ with $hx : x \ne \bot$ by a coerced element. The equivalence `Equiv.withBotSubtypeNe` identifies the subtype of elements different from $\bot$ with $\alpha$. The lemmas `WithBot.forall`, `WithBot.exists` and `WithBot.ne_bot_iff_exists` split a quantifier over `WithBot α` into the case $\bot$ and the coerced cases.

#### Maps and monotonicity

The function `WithBot.map` applies a function to the coerced elements and keeps $\bot$, with the simp lemmas `WithBot.map_bot` and `WithBot.map_coe`. The function `WithBot.map₂` is the two argument version. The lemma `Monotone.withBot_map` says that the map of a monotone function is monotone, and `StrictMono.withBot_map` is the strict version. The lemma `WithBot.monotone_map_iff` gives the converse. The lemma `WithBot.map_le_iff` says that the map of an order embedding reflects the order.

For a function $f$ defined on all of `WithBot α`, the lemma `WithBot.monotone_iff` gives a test with two parts. The function $f$ is monotone if and only if $a \mapsto f(\uparrow a)$ is monotone and $f(\bot) \le f(\uparrow x)$ for each $x$. The lemma `WithBot.strictMono_iff` is the strict version. The coercion itself is monotone and strictly monotone, by `WithBot.coe_mono` and `WithBot.coe_strictMono`. The equivalences `Equiv.withBotCongr` and `Equiv.withTopCongr` lift an equivalence of the base types.

#### Duality

The new bottom of $\alpha$ is the new top of the dual order. The equivalence `WithBot.toDual` maps `WithBot α` to `WithTop αᵒᵈ`, and `WithTop.toDual` maps `WithTop α` to `WithBot αᵒᵈ`. The inverse directions are `WithBot.ofDual` and `WithTop.ofDual`. The lemma `WithBot.toDual_le_toDual_iff` says that `WithBot.toDual` reverses the order. These equivalences are the bridge to use when a result exists for one side only.

#### Both ends and ranges

The module `Mathlib.Order.WithBotTop` defines `WithBotTop ι` as an abbreviation for `WithBot (WithTop ι)`, and `WithTopBot ι` for the other nesting. All instances come from the two layers, so a linear order on $\iota$ gives a bounded linear order on `WithBotTop ι`. The map `WithBotTop.coe` is the composite of the two coercions. The lemmas `WithBotTop.coe_le_coe`, `WithBotTop.coe_lt_coe`, `WithBotTop.coe_strictMono` and `WithBotTop.coe_injective` save the reader from two rewrites. The lemmas `WithBotTop.coe_ne_bot`, `WithBotTop.coe_ne_top` and `WithBotTop.top_ne_bot` separate the three kinds of points, and the recursor `WithBotTop.rec` has one case for each kind.

The module `Mathlib.Order.Set` contains `WithBot.range_eq` and `WithTop.range_eq`. For $f$ on `WithBot α`, the range of $f$ is the range of $f$ on the coerced elements with the point $f(\bot)$ inserted.

#### Common errors

1. The option form of an element does not match the order lemmas. A term built with the option constructors, or a pattern match on the option type, gives goals that the lemmas of `Mathlib.Order.WithBot` do not rewrite. Rewrite with `WithBot.some_eq_coe` and `WithBot.none_eq_bot` first, or use `induction x` so that the recursor `WithBot.recBotCoe` produces the order forms.
2. A cast from $\mathbb{N}$ into `WithBot ℕ` has two forms. The coercion $\uparrow n$ and the natural number cast $(n : \mathrm{WithBot}\ \mathbb{N})$ are equal by `Nat.cast_withBot`, but they are not equal by syntax, so `WithBot.coe_le_coe` can fail on a goal from `Polynomial.degree`. Use `Nat.cast_withBot` or the tactic norm_cast first.
3. The top of `WithBot α` needs a top on $\alpha$. The type `WithBot α` has a greatest element only when $\alpha$ has one, through `WithBot.instOrderTop`. A proof that uses `le_top` on `WithBot α` fails with a missing instance for an arbitrary $\alpha$. Use `WithBotTop α` when both new points are necessary.

### Exercises

1. (A) Let $\alpha$ be a preorder. Prove that the coercion $\alpha \to$ `WithBot α` is an order embedding, and that its range is the set of elements different from $\bot$.
2. (A) Use `WithBot.monotone_iff` to show that the function on `WithBot ℕ` that sends $\bot$ to $0$ and $\uparrow n$ to $n + 1$ is strictly monotone. Then express this function with `WithBot.unbotD` and `WithBot.map`.
3. (A) Let $\alpha$ be a linear order with a least element $m$. Find two elements of `WithBot α` with no element strictly between them. Explain why this does not contradict `WithBot.denselyOrdered_iff`.
4. (B) Prove that `WithBot α` and `WithTop αᵒᵈ` are order isomorphic, with `WithBot.toDual` as the underlying equivalence. Use this to deduce `WithTop.lt_top_iff_ne_top` from `WithBot.bot_lt_iff_ne_bot`.
5. (B) Let $\alpha$ be a linear order. Prove that `WithBot (WithTop α)` and `WithTop (WithBot α)` are order isomorphic. Give the isomorphism by its values on $\bot$, $\top$ and the coerced elements.
6. (C) Prove `WithBot.le_of_forall_lt_iff_le` for $\alpha = \mathbb{Q}$ by hand. Then show that the hypothesis of density is necessary: find $x$ and $y$ in `WithBot ℤ` with $x < y$ such that each integer $z$ with $x < \uparrow z$ also has $y \le \uparrow z$.

### Reference

<?reference?>
