---
title: Universe lifts, opposites and small types
kind: api
modules:
  - Mathlib.Data.ULift
  - Mathlib.Logic.Function.ULift
  - Mathlib.Data.Prod.PProd
  - Mathlib.Basic.Opposite
  - Mathlib.Data.Opposite
  - Mathlib.Logic.Small.Defs
  - Mathlib.Logic.Small.Basic
  - Mathlib.Logic.Small.Set
  - Mathlib.Logic.Small.List
  - Mathlib.Basic.UnivLE
explains:
  E2: [ULift.up_bijective, Opposite.op_inj_iff, small_congr, small_of_injective, small_of_surjective, not_small_type, univLE_iff]
  E1: auto
families: []
requires: [V01.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Universe lifts, opposites and small types

### Overview

Every type of Lean lives in a universe: `Prop`, `Type 0`, `Type 1`, and so on. A set theorist works in one universe of sets and never meets this structure. A user of Mathlib meets it as soon as two types from different universes must be compared. A product `α × β` lives in the larger of the two universes, and a type of `Type 0` is not a term of `Type 1`. This section explains the tools that move a type between universes, and the notion of a type that is *small* relative to a universe.

The section also treats two wrapper types. The lift `ULift α` is a copy of $\alpha$ in a higher universe, and the opposite `αᵒᵖ` is a copy of $\alpha$ with a new name, which the category theory library uses to reverse arrows. Both wrappers are structures with one field, and both are equivalent to $\alpha$. The previous section built subtypes, products and sums from given types; the wrappers of this section are the simplest constructions of the same kind.

### The library around it

#### Lifts

The structure `ULift.{r} α` has one field `down : α` and the constructor `ULift.up`. For `α : Type s` it lives in `Type (max s r)`. The structure `PLift α` does the same for `α : Sort u` and lands in `Type u`, so it turns a proposition into a type. Both structures are in the Lean core. The module `Mathlib.Data.ULift` proves that they change nothing but the universe.

**Theorem (The lift is a bijection).** The maps $\mathrm{up} : \alpha \to \mathrm{ULift}\ \alpha$ and $\mathrm{down} : \mathrm{ULift}\ \alpha \to \alpha$ are bijective and inverse to each other.

*Proof.* For $a : \alpha$, $\mathrm{down}(\mathrm{up}(a)) = a$ by the projection rule. For $x : \mathrm{ULift}\ \alpha$, $\mathrm{up}(\mathrm{down}(x)) = x$ by the eta rule of structures. So each map is a two-sided inverse of the other, and both are bijective. $\square$

The lemmas are `ULift.up_bijective`, `ULift.down_bijective` and the parts `ULift.up_injective`, `ULift.up_surjective`, `ULift.down_surjective`. The module `Mathlib.Logic.Function.ULift` adds `ULift.down_injective` and `ULift.down_inj`. The bundled form is the equivalence `Equiv.ulift : ULift α ≃ α`. Every lemma has a twin for `PLift` with the same suffix: `PLift.up_bijective`, `PLift.down_injective`, and so on.

The other results move statements through the lift. The quantifier rules `ULift.forall` and `ULift.exists` replace a quantifier over `ULift α` by a quantifier over $\alpha$. The map `ULift.map f` applies $f$ under the lift, and `ULift.map_injective`, `ULift.map_surjective` and `ULift.map_bijective` state that it has a property exactly when $f$ has it. The instances transfer `DecidableEq`, `Nonempty`, `IsEmpty` and `Unique` from $\alpha$ to the lift.

The module `Mathlib.Data.Prod.PProd` treats `PProd α β`, written `α ×' β`, the product of two sorts. It accepts propositions as factors, where `α × β` accepts only types. The lemmas `PProd.forall`, `PProd.exists` and `PProd.mk.eta` are the forms of `Prod.forall`, `Prod.exists` and the eta rule. `Function.Injective.pprod_map` states that a product of injective maps is injective. The equivalence `Equiv.pprodEquivProd` identifies `α ×' β` with `α × β` when both are types.

#### Opposites

The module `Mathlib.Basic.Opposite` defines the structure `Opposite α`, written `αᵒᵖ`, with one field. The two maps are `Opposite.op : α → αᵒᵖ` and `Opposite.unop : αᵒᵖ → α`. A type and its opposite have the same terms, but Lean sees two different types. So an instance on $\alpha$ does not apply to `αᵒᵖ`, and the library can give `αᵒᵖ` new instances. For a category $C$, the category structure on `Cᵒᵖ` reverses all arrows.

**Theorem (Injectivity of op).** For $x, y : \alpha$, $\mathrm{op}(x) = \mathrm{op}(y)$ if and only if $x = y$.

*Proof.* If $\mathrm{op}(x) = \mathrm{op}(y)$, apply $\mathrm{unop}$ to both sides; the rule $\mathrm{unop}(\mathrm{op}(x)) = x$ gives $x = y$. The converse is congruence. $\square$

This is `Opposite.op_inj_iff`, with the twin `Opposite.unop_inj_iff`. The cancellation rules are `Opposite.unop_op` and `Opposite.op_unop`, and the rewriting rules `Opposite.op_eq_iff_eq_unop` and `Opposite.unop_eq_iff_eq_op` move an `op` to the other side of an equation. The equivalence `Opposite.equivToOpposite : α ≃ αᵒᵖ` bundles the two maps. Three other wrappers follow the same pattern for other purposes: `MulOpposite` reverses a multiplication, `AddOpposite` reverses an addition, and `OrderDual` reverses an order. The module `Mathlib.Data.Opposite` has no live declarations; it only imports `Mathlib.Basic.Opposite`.

#### Small types

**Definition (Small type).** A type $\alpha$ in some universe is `w`-*small* if it is equivalent to a type in `Type w`. This is the class `Small.{w} α`, and `small_iff` states the definition: $\exists S : \texttt{Type w},\ \mathrm{Nonempty}(\alpha \simeq S)$.

The definition is a proposition, so it does not name the model. The module `Mathlib.Logic.Small.Defs` chooses one with the axiom of choice: `Shrink α : Type w` and the equivalence `equivShrink α : α ≃ Shrink α`. The recursor `Shrink.rec` proves a statement on `Shrink α` from the statement on the images of the points of $\alpha$.

**Theorem (Smallness is invariant).** If $\alpha \simeq \beta$, then $\alpha$ is `w`-small if and only if $\beta$ is `w`-small.

*Proof.* If $\beta \simeq S$ with $S$ in `Type w`, then the composite $\alpha \simeq \beta \simeq S$ shows that $\alpha$ is small. The other direction uses the inverse equivalence. $\square$

This is `small_congr`, and `small_map` is the direction from $\beta$ to $\alpha$. Every type is small in its own universe (`small_self`), in every larger universe of the form `max w v` (`small_max`, `small_lift`), and in the next universe (`small_succ`). A subsingleton is small in every universe, by the instance `small_subsingleton`.

**Theorem (Smallness along maps).** Let $f : \alpha \to \beta$.

1. If $f$ is injective and $\beta$ is `u`-small, then $\alpha$ is `u`-small.
2. If $f$ is surjective and $\alpha$ is `u`-small, then $\beta$ is `u`-small.

*Proof.* 1. The map $f$ gives an equivalence of $\alpha$ with its range $f(\alpha) \subseteq \beta$, by `Equiv.ofInjective`. Transport the range along $\beta \simeq S$: it becomes a subset $T$ of $S$, and the subtype $T$ is a type in `Type u`. So $\alpha \simeq T$. 2. A surjective $f$ has a right inverse $g : \beta \to \alpha$, by choice. A right inverse is injective, so part 1 applied to $g$ gives the result. $\square$

These are `small_of_injective` and `small_of_surjective`. From them the module `Mathlib.Logic.Small.Basic` derives the instances for the constructions of this chapter: `small_subtype`, `small_prod`, `small_sum`, `small_sigma`, `small_Pi`, `small_set`, `small_quot` and `small_quotient`. The module `Mathlib.Logic.Small.Set` gives the instances for operations on sets, so that a subset built from small sets is small:

| Lean name | Statement |
|---|---|
| `small_subset` | `t ⊆ s` and `↥s` small give `↥t` small |
| `small_union` | `↥(s ∪ t)` is small when `↥s` and `↥t` are |
| `small_image` | `↥(f '' s)` is small when `↥s` is |
| `small_range` | `↥(Set.range f)` is small when the domain is |
| `small_iUnion` | a union over a small index type of small sets is small |
| `small_powerset` | `↥(𝒫 s)` is small when `↥s` is |
| `small_univ_iff` | `↥Set.univ` is small exactly when `α` is |

The module `Mathlib.Logic.Small.List` has the instances `smallList` and `smallVector`: lists and vectors of length $n$ over a small type are small.

**Theorem (A universe is not small in itself).** The type `Type (max u v)` is not `u`-small.

*Proof.* Assume an equivalence $e$ of `Type (max u v)` with a type $S$ in `Type u`. Form the type $T = \Sigma_{s : S}\, e^{-1}(s)$ of pairs of a code and a term of the coded type. It lies in `Type (max u v)`, and so does `Set T`. Define $g : \texttt{Set}\ T \to T$ by sending $A$ to the pair of the code $e(\texttt{Set}\ T)$ and $A$ itself, seen as a term of $e^{-1}(e(\texttt{Set}\ T)) = \texttt{Set}\ T$. Two sets with the same image have the same second component, so $g$ is injective. This contradicts Cantor's theorem in its injective form, `Function.cantor_injective`. $\square$

This is `not_small_type`. In contrast, `small_type` states that `Type u` is small in `Type (max (u + 1) v)`.

#### Comparison of universes

The module `Mathlib.Basic.UnivLE` expresses an inequality of universes as a class. Lean cannot state $u \le v$ as a hypothesis, so the class `UnivLE.{u, v}` states the consequence that matters.

**Definition (Universe inequality).** `UnivLE.{u, v}` holds if every type in `Type u` is `v`-small.

The lemma `univLE_iff` unfolds the definition, and it holds by the definition of the class. The instance `UnivLE.small` makes every `α : Type u` small in `Type v` once `UnivLE.{u, v}` is known. The basic facts are `UnivLE.self`, `UnivLE.zero`, `univLE_max`, `UnivLE.succ` and `UnivLE.trans`, and `Small.trans_univLE` passes from `u`-small to `v`-small. The class appears in the hypotheses of results on limits in categories of types, where the index category must not be larger than the universe of the values.

#### Common errors

1. A learner states a result for `α : Type u` and `β : Type v` and then cannot form `α ≃ β` with a third type `γ : Type w`. Equivalences cross universes freely, but a result proved for one universe does not apply to another. Use `Equiv.ulift` to move a type to a common universe.
2. A learner expects an instance on $\alpha$ to apply to `αᵒᵖ`. The opposite is a new type. Move terms with `Opposite.op` and `Opposite.unop`, and look for the instance under the opposite.
3. A learner tries to compute with `Shrink α`. The type is chosen by `Classical.choice` and has no computable terms; work with `equivShrink α` and its inverse.

### Exercises

1. (A) Prove that `ULift.map f` is injective when $f$ is injective, from `ULift.up_injective` and `ULift.down_injective`.
2. (A) Prove that $\mathrm{op} : \alpha \to \alpha^{\mathrm{op}}$ is surjective, and write the inverse equivalence of `Opposite.equivToOpposite`.
3. (B) Prove that the subtype of a small type is small, with `small_of_injective` and `Subtype.val_injective`.
4. (B) Let $\iota$ be `u`-small and let each $s_i$ be a `u`-small set. Prove that $\bigcup_i s_i$ is small, with `small_of_surjective` and a sigma type.
5. (B) Prove that `UnivLE.{u, v}` and `UnivLE.{v, w}` give `UnivLE.{u, w}`.
6. (C) Prove that `Set (Type u)` is not `u`-small. Hint: compare with `not_small_type`.

### Reference

<?reference?>
