---
title: Upper sets and lower sets
kind: api
modules:
  - Mathlib.Order.UpperLower.Basic
  - Mathlib.Order.UpperLower.Closure
  - Mathlib.Order.UpperLower.CompleteLattice
  - Mathlib.Order.UpperLower.Fibration
  - Mathlib.Order.UpperLower.Hom
  - Mathlib.Order.UpperLower.LocallyFinite
  - Mathlib.Order.UpperLower.Principal
  - Mathlib.Order.UpperLower.Prod
  - Mathlib.Order.UpperLower.Relative
explains:
  E2: [upperClosure, mem_upperClosure, giUpperClosureCoe, UpperSet.coe_sup, UpperSet.Ici, UpperSet.completelyDistribLattice, upperSetIsoLowerSet, Relation.Fibration, IsRelUpperSet, UpperSet.prod]
  E1: auto
families: []
requires: [V04.C01, V04.C02, V04.C03]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Upper sets and lower sets

### Overview

A subset $s$ of a preorder $\alpha$ is an upper set if it is closed upwards: $a \in s$ and $a \le b$ give $b \in s$. A lower set is closed downwards. The set of the natural numbers $n \ge 5$ is an upper set of $\mathbb{N}$. The set of the subsets of $\{1, 2\}$ is a lower set of the power set of $\mathbb{N}$. The interval $[a, \infty)$ is the principal upper set of $a$. An upper set is also the set where a monotone predicate is true, so upper sets come up each time a property "goes up": a filter is an upper set of `Set α`, and an increasing event is an upper set of a product of copies of $\{0, 1\}$.

Mathlib has two levels for this notion. The predicates `IsUpperSet` and `IsLowerSet` act on a plain `Set α`. The structures `UpperSet α` and `LowerSet α` bundle a set with the proof. The bundled types are complete lattices, and they are completely distributive. The order on `UpperSet α` is the reverse inclusion, and this choice is the source of most errors with them.

The section describes the predicates, the closure maps `upperClosure` and `lowerClosure`, the lattice of upper sets, the principal upper sets, the products, and the relative upper sets. It uses complete lattices from the first section of this chapter and the preorders and lattices of Chapters 1 to 3.

### The library around it

#### The predicates

The predicate `IsUpperSet s` unfolds to $\forall a\, b,\ a \le b \to a \in s \to b \in s$. The module `Mathlib.Order.UpperLower.Basic` has the closure rules. The empty set and `Set.univ` are upper sets, and arbitrary unions and intersections of upper sets are upper sets. The complement exchanges the two notions: `IsUpperSet.compl` turns an upper set into a lower set, and `isUpperSet_compl` is the equivalence. The lemma `isUpperSet_iff_Ici_subset` says that $s$ is an upper set exactly when $[a, \infty) \subseteq s$ for each $a \in s$. The lemma `Set.monotone_mem` says that $s$ is an upper set exactly when the predicate $a \mapsto a \in s$ is monotone, with the order $\mathrm{False} < \mathrm{True}$ on `Prop`.

Other lemmas connect upper sets with other order notions. `IsUpperSet.ordConnected` says that an upper set is order connected. In a linear order, `IsUpperSet.total` says that two upper sets are comparable for inclusion. In an order with no maximal element, `IsUpperSet.not_bddAbove` says that a nonempty upper set is not bounded above.

#### The closure maps

The upper closure of a set $s$ is the smallest upper set that contains $s$. Mathlib defines it as a bundled upper set, `upperClosure s : UpperSet α`. Its membership lemma `mem_upperClosure` is
$$a \in \operatorname{upperClosure}(s) \iff \exists b \in s,\ b \le a.$$
The lemma `coe_upperClosure` writes the carrier as the union of the intervals $[b, \infty)$ for $b \in s$. The proof that this set is an upper set is one line: if $b \le a \le c$ with $b \in s$, then $b \le c$ by transitivity.

The closure is a Galois insertion. The lemma `gc_upperClosure_coe` states the Galois connection between `upperClosure` and the coercion of an upper set to a set, and `giUpperClosureCoe` is the Galois insertion. The order on `UpperSet α` is reversed, so the connection goes from `Set α` to `(UpperSet α)ᵒᵈ`. The general results of Chapter 6 then give the rules for unions. The lemma `upperClosure_union` gives $\operatorname{upperClosure}(s \cup t) = \operatorname{upperClosure}(s) \sqcap \operatorname{upperClosure}(t)$, an infimum in `UpperSet α` whose carrier is the union of the two carriers. The lemma `upperClosure_iUnion` is the same rule for a family. The lemma `upperClosure_singleton` says that the closure of $\{a\}$ is `UpperSet.Ici a`. The lemma `upperClosure_min` says that each upper set that contains $s$ also contains its closure.

The lower closure `lowerClosure` has the dual lemmas with `Iic` in place of `Ici`. The lemma `ordConnected_iff_upperClosure_inter_lowerClosure` says that a set is order connected exactly when it is the intersection of its upper closure and its lower closure. In an order where each interval $[a, \infty)$ is finite, `Set.Finite.upperClosure` in `Mathlib.Order.UpperLower.LocallyFinite` says that the upper closure of a finite set is finite.

#### The lattice of upper sets

The module `Mathlib.Order.UpperLower.CompleteLattice` puts the order structure on the bundled types. On `LowerSet α` the order is inclusion. On `UpperSet α` the order is the reverse inclusion: $s \le t$ means $t \subseteq s$. The reason is that the map $a \mapsto [a, \infty)$ is then monotone, and `UpperSet α` is isomorphic to `LowerSet α` by the complement. So the coercion lemmas are these.

| Lean name | Statement |
|---|---|
| `UpperSet.coe_sup` | $\uparrow(s \sqcup t) = \uparrow s \cap \uparrow t$ |
| `UpperSet.coe_inf` | $\uparrow(s \sqcap t) = \uparrow s \cup \uparrow t$ |
| `UpperSet.coe_top` | $\uparrow\top = \emptyset$ |
| `UpperSet.coe_bot` | $\uparrow\bot = \mathrm{univ}$ |
| `UpperSet.completelyDistribLattice` | the upper sets form a completely distributive lattice |
| `UpperSet.instCompleteLinearOrder` | in a linear order, the upper sets form a complete linear order |
| `upperSetIsoLowerSet` | the complement, as an order isomorphism from `UpperSet α` to `LowerSet α` |

The complement map is `UpperSet.compl`. Both the intersection and the union of a family of upper sets are upper sets, so infima and suprema exist for arbitrary families. The infinite distributive laws hold because they hold in `Set α`, and the lattice is completely distributive. For an order isomorphism $f : \alpha \simeq \beta$, `UpperSet.map` transports upper sets. The operations `UpperSet.erase` and `UpperSet.sdiff` remove a point or a set together with all the points below it, so that the result is again an upper set: the carrier of `UpperSet.sdiff s t` is $s \setminus \operatorname{lowerClosure}(t)$.

#### Principal upper sets

The module `Mathlib.Order.UpperLower.Principal` defines the principal upper set `UpperSet.Ici a`, with carrier $[a, \infty)$, and `LowerSet.Iic a` dually. The membership lemma is `UpperSet.mem_Ici_iff`, and `UpperSet.le_Ici` says $s \le \operatorname{Ici}(a)$ if and only if $a \in s$. With the reverse order, the map $a \mapsto \operatorname{Ici}(a)$ keeps suprema: `UpperSet.Ici_sup` gives $\operatorname{Ici}(a \sqcup b) = \operatorname{Ici}(a) \sqcup \operatorname{Ici}(b)$, because $[a \sqcup b, \infty) = [a, \infty) \cap [b, \infty)$. In a complete lattice, `UpperSet.Ici_sSup` gives the same rule for a set. The module `Mathlib.Order.UpperLower.Hom` bundles these facts as morphisms: `UpperSet.iciSupHom` is a supremum morphism and `UpperSet.icisSupHom` is a complete supremum morphism. The dual `LowerSet.iicInfHom` keeps infima.

#### Fibrations

The module `Mathlib.Order.UpperLower.Fibration` describes relations that lift order relations. For a relation $r$ on $\alpha$, a relation $r'$ on $\beta$ and a map $f : \alpha \to \beta$, the predicate `Relation.Fibration r r' f` says: if $r'\,b\,(f(a))$, then $b = f(c)$ for some $c$ with $r\,c\,a$. So each step below an image point lifts to a step below the source point. Take $r$ and $r'$ to be the relations $\ge$. The lemma `Relation.fibration_iff_isUpperSet_image` says that $f$ is then a fibration exactly when the image of each upper set under $f$ is an upper set. The lemma `Relation.Fibration.isUpperSet_image` is the direction that a proof uses most.

#### Products and relative upper sets

For upper sets $s$ of $\alpha$ and $t$ of $\beta$, `UpperSet.prod s t` is the upper set $s \times t$ of $\alpha \times \beta$, and `IsUpperSet.prod` is the unbundled form. The lemma `UpperSet.Ici_prod_Ici` says $\operatorname{Ici}(a) \times \operatorname{Ici}(b) = \operatorname{Ici}(a, b)$, and `upperClosure_prod` says that the closure of a product is the product of the closures.

The module `Mathlib.Order.UpperLower.Relative` treats upper sets inside a subset. The predicate `IsRelUpperSet s P` says that each element of $s$ satisfies $P$ and that $s$ is closed upwards among the elements that satisfy $P$. The bundled form is `RelUpperSet`. The lemma `isUpperSet_subtype_iff_isRelUpperSet` says that an upper set of the subtype `{x // P x}` is the same as a relative upper set of $\alpha$. For example, `isRelUpperSet_Icc_le` says that the interval $[a, c]$ is a relative upper set for the predicate $x \le c$, and `IsUpperSet.isRelUpperSet_sep` says that the part of an upper set where $P$ holds is a relative upper set.

#### Common errors

1. The order on `UpperSet α` is the reverse inclusion. The supremum of two upper sets is their intersection, by `UpperSet.coe_sup`, and the top element is the empty upper set. A proof that expects the union must use `⊓`.
2. The closure `upperClosure s` is an `UpperSet α`, not a `Set α`. A membership goal needs `mem_upperClosure` or the coercion lemma `coe_upperClosure`, and a goal with `IsUpperSet` on the closure needs the field of the structure.
3. The Galois insertion `giUpperClosureCoe` goes to the dual order `(UpperSet α)ᵒᵈ`. A rule for unions from Chapter 6, such as the image of a supremum, gives an infimum in `UpperSet α`.

### Exercises

1. (A) Show that $\{n \in \mathbb{N} \mid n \ge 5\}$ is an upper set and that its complement is a lower set, with `IsUpperSet.compl`.
2. (A) Compute the carrier of `upperClosure {2, 3}` in $\mathbb{N}$ with the divisibility order, with `mem_upperClosure`.
3. (B) Prove `UpperSet.coe_sup` from the definition of the order on `UpperSet α`.
4. (B) Prove that a set $s$ is an upper set if and only if `upperClosure s` has carrier $s$.
5. (B) In a linear order, prove that two upper sets are comparable for inclusion, and derive `UpperSet.instCompleteLinearOrder` in words.
6. (C) Show that a set of a preorder is order connected if and only if it is the intersection of an upper set and a lower set.

### Reference

<?reference?>
