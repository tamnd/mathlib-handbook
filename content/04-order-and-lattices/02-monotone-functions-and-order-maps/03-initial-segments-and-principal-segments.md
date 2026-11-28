---
title: Initial segments and principal segments
kind: api
modules:
  - Mathlib.Order.InitialSeg
  - Mathlib.Order.Interval.Set.InitialSeg
  - Mathlib.Order.Extension.Well
explains:
  E2: [InitialSeg, PrincipalSeg, InitialSeg.eq, InitialSeg.antisymm, InitialSeg.total, PrincipalSeg.trichotomy, RelEmbedding.collapse, PrincipalSeg.orderIsoIio, WellFounded.exists_well_order_ge]
  E1: auto
families: []
requires: [V04.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Initial segments and principal segments

### Overview

An order embedding $f : \alpha \to \beta$ can put the copy of $\alpha$ anywhere in $\beta$. The map $n \mapsto 2n$ on $\mathbb{N}$ is an embedding, but its range has gaps. An *initial segment* is an embedding whose range has no gaps from below: if $b < f(a)$, then $b = f(c)$ for some $c$. So the range is a lower set, and $\alpha$ is a copy of the bottom part of $\beta$. A *principal segment* is an initial segment whose range is exactly the set $\{b \mid b < t\}$ for an element $t$ of $\beta$, the *top*. The inclusion of $\{0, 1, 2\}$ into $\mathbb{N}$ is a principal segment with top $3$, and the identity map of $\mathbb{N}$ is an initial segment that is not principal.

For well-orders these maps are rigid. Between two well-orders there is at most one initial segment, two well-orders are always comparable by an initial segment, and no well-order is a principal segment of itself. These three facts are the base of the theory of ordinals: in `Mathlib.SetTheory.Ordinal.Basic`, an ordinal is a class of isomorphic well-orders, and $o_1 \le o_2$ holds when there is an initial segment between the representatives. The module `Mathlib.Order.InitialSeg` has the two structures and these theorems, `Mathlib.Order.Interval.Set.InitialSeg` connects them with the intervals $(-\infty, j]$ and $(-\infty, j)$, and `Mathlib.Order.Extension.Well` extends a well-founded relation to a well-order.

### The library around it

**The two structures.** Mathlib states the definitions for relations, so that they apply to a type with any well-founded relation, and then gives the notation for orders. `InitialSeg r s`, with the notation `r ≼i s`, extends a relation embedding `r ↪r s` with the field `InitialSeg.mem_range_of_rel'`, which the lemma `InitialSeg.mem_range_of_rel` restates: if `s b (f a)`, then $b$ is in the range of $f$. `PrincipalSeg r s`, with the notation `r ≺i s`, extends a relation embedding with an element `PrincipalSeg.top` and the field that `PrincipalSeg.mem_range_iff_rel` restates: $b$ is in the range if and only if `s b f.top`. For orders, `α ≤i β` is `InitialSeg` for the two relations `<`, and `α <i β` is `PrincipalSeg` for them. The relation is the strict order `<`, not `≤`, because a well-order in Mathlib is a strict relation (`IsWellOrder`).

For orders the definition gives the expected lemmas. `InitialSeg.isLowerSet_range` says that the range of `f : α ≤i β` is a lower set, `InitialSeg.image_Iio` says that $f$ sends $(-\infty, a)$ onto $(-\infty, f(a))$, and `InitialSeg.le_apply_iff` says that $b \le f(a)$ if and only if $b = f(c)$ for some $c \le a$. An initial segment is strictly monotone (`InitialSeg.strictMono`), it is an order embedding by `InitialSeg.toOrderEmbedding`, and between orders with a least element it sends $\bot$ to $\bot$ (`InitialSeg.map_bot`). For a principal segment, `PrincipalSeg.lt_top` says that each value is below the top, and `PrincipalSeg.range_eq_Iio` says that the range is $(-\infty, t)$.

**Constructions.** The identity is `InitialSeg.refl`, and an isomorphism is an initial segment by `OrderIso.toInitialSeg` or `RelIso.toInitialSeg`. Composition has four forms, after the kinds of the two maps: `InitialSeg.trans`, `PrincipalSeg.trans`, `PrincipalSeg.transInitial` and `InitialSeg.transPrincipal`. A composition with at least one principal segment is principal. The map `InitialSeg.leAdd` is the inclusion of $\alpha$ into the lexicographic sum of $\alpha$ and $\beta$. For an element $a$, `PrincipalSeg.ofElement` is the inclusion of the elements below $a$, with top $a$, and `PrincipalSeg.subrelIso` goes back: the domain of a principal segment is isomorphic to the elements below its top. The module `Mathlib.Order.Interval.Set.InitialSeg` gives the forms for intervals of a preorder: `Set.initialSegIic j` is the inclusion of $(-\infty, j]$, `Set.principalSegIio j` is the inclusion of $(-\infty, j)$, and `Set.initialSegIicIicOfLE` includes $(-\infty, i]$ in $(-\infty, j]$ for $i \le j$. In the other direction, `PrincipalSeg.orderIsoIio` turns `f : α <i β` into an isomorphism of $\alpha$ with $(-\infty, t)$, where $t$ is the top of $f$.

**Uniqueness.** The central fact is `InitialSeg.eq`: if $s$ is a well-order, two initial segments `f g : InitialSeg r s` agree at each point. The proof is a well-founded induction on $a$. Suppose that $f$ and $g$ agree at each $c$ with $r(c, a)$. An element $b$ with $s(b, f(a))$ is $f(c)$ for some $c$ with $r(c, a)$, because $f$ is an initial segment and an embedding. So $b = g(c)$, and $s(b, g(a))$. The same argument in the other direction shows that $f(a)$ and $g(a)$ have the same elements below them. In a well-order, trichotomy and irreflexivity then give $f(a) = g(a)$. Mathlib proves the result as an instance: the type `InitialSeg r s` has at most one element. The general form `InitialSeg.subsingleton_of_trichotomous_of_irrefl` asks only that $r$ is well-founded and that $s$ is trichotomous and irreflexive, and `PrincipalSeg.eq` is the same statement for principal segments.

Three consequences follow. `InitialSeg.antisymm` builds an isomorphism `r ≃r s` from initial segments in the two directions: the two compositions are initial segments of a well-order into itself, so by uniqueness they are the identity. `PrincipalSeg.irrefl` says that there is no principal segment of a well-order into itself. A principal segment $f$ of $r$ into $r$ is an initial segment, so $f$ is the identity by uniqueness, but the top of $f$ is not in its range. `PrincipalSeg.top_eq` says that the top depends only on the isomorphism class of the domain.

**Comparison.** The comparison theorem is `InitialSeg.total`: for two well-orders $r$ and $s$, there is an initial segment of $r$ into $s$ or one of $s$ into $r$. Its result is a sum type, so it gives data and not only a proof. The finer form is `PrincipalSeg.trichotomy`, which gives a principal segment of $r$ into $s$, an isomorphism, or a principal segment of $s$ into $r$. The step between the two forms is `InitialSeg.principalSumRelIso`: an initial segment into a well-order is a principal segment or an isomorphism, and `InitialSeg.toPrincipalSeg` gives the principal segment when the map is not surjective. Its top is the least element outside the range.

**Collapse.** A relation embedding into a well-order is not always an initial segment, but it gives one. `RelEmbedding.collapse` takes `f : r ↪r s` with $s$ a well-order and returns an initial segment `InitialSeg r s`. The new map $g$ is defined by well-founded recursion: $g(a)$ is the least element of $\beta$ that is above $g(c)$ for each $c$ with $r(c, a)$. The set is nonempty, because an induction shows $g(c) \le f(c)$, so $f(a)$ is in it. For $n \mapsto 2n$ on $\mathbb{N}$, the collapse is the identity. The lemma `wellFounded_iff_principalSeg` gives a converse view: a transitive relation is well-founded if and only if each relation with a principal segment into it is well-founded.

**Well-order extensions.** The module `Mathlib.Order.Extension.Well` shows that each well-founded relation is contained in a well-order. `WellFounded.exists_well_order_ge` states: for a well-founded relation $r$ on $\alpha$, there is a relation $s$ with $r \le s$ and `IsWellOrder α s`. The construction is `WellFounded.wellOrderExtension`, a linear order on $\alpha$. It compares two elements first by their rank for $r$, which is an ordinal, and it breaks the ties with a fixed well-order of $\alpha$ from the well-ordering theorem. So the proof uses the axiom of choice. For a preorder with a well-founded `<`, the type synonym `WellOrderExtension α` carries this linear order, `toWellOrderExtension` is the identity map into it, and `toWellOrderExtension_strictMono` says that this map is strictly monotone. The relation with the empty relation, which is well-founded, gives a well-order on each type. Compare with `extend_partialOrder` in the section on Zorn's lemma, which extends a partial order to a linear order that is not always a well-order.

#### Common errors

1. An order embedding is not an initial segment. The map $n \mapsto 2n$ gives an element of `ℕ ↪o ℕ`, but no element of `ℕ ≤i ℕ` has the same values. To get an initial segment from an embedding into a well-order, apply `RelEmbedding.collapse`, and keep in mind that its values are different from the values of the embedding.
2. The uniqueness theorems need a well-order on the target. On `ℤ` the map $n \mapsto n + 1$ is an order isomorphism, so `OrderIso.toInitialSeg` gives an initial segment of `ℤ` into itself that is not the identity. Then `InitialSeg.eq` does not apply, because `ℤ` has no well-founded `<`. Look for the argument `[IsWellOrder β s]` in the signature.
3. The relations in `InitialSeg r s` are strict relations. For orders, use the notation `α ≤i β` and `α <i β`, which take `<` on both sides. A term of type `InitialSeg (· ≤ ·) (· ≤ ·)` is well typed, but the lemmas that need `IsWellOrder` do not apply to it, because `≤` is not irreflexive.

### Exercises

1. (A) Prove that for `f : α <i β`, the top `f.top` is not in the range of $f$. Use `PrincipalSeg.mem_range_iff_rel` and the irreflexivity of `<`.
2. (A) Let $e$ be the map $n \mapsto n + 1$ on `ℤ`. Show that `e.toInitialSeg` and `InitialSeg.refl` are two different initial segments of `ℤ` into itself, and explain why this does not contradict `InitialSeg.eq`.
3. (B) Prove `PrincipalSeg.irrefl` for an order with a well-founded `<` from `InitialSeg.eq`, with the argument of the section: compare the principal segment with `InitialSeg.refl`.
4. (B) Use `WellFounded.exists_well_order_ge` with the empty relation to prove that each type $\alpha$ has a well-order. Then show that a nonempty type with a well-order that has no greatest element is infinite.
5. (B) Let `f : ℕ ↪o ℕ` be strictly monotone. Prove by induction that $n \le f(n)$ for each $n$, and deduce that `RelEmbedding.collapse` of $f$ is the identity.
6. (C) Let $r$ and $s$ be well-orders. Prove that at most one of the three cases of `PrincipalSeg.trichotomy` holds. Use `PrincipalSeg.irrefl` together with `PrincipalSeg.transInitial` and `RelIso.toInitialSeg`.

### Reference

<?reference?>
