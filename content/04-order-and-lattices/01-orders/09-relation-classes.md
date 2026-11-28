---
title: Relation classes
kind: api
modules:
  - Mathlib.Order.RelClasses
explains:
  E2: [partialOrderOfSO, IsOrderConnected.neg_trans, WellFounded.asymmetric, WellFounded.prod_lex, InvImage.isLinearOrder, Set.not_bounded_iff]
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

## Relation classes

### Overview

The classes `Preorder α`, `PartialOrder α` and `LinearOrder α` of the first section of this chapter bundle a relation `≤` with its axioms. A type has at most one such order in a given context, and Lean finds it by instance search. Often a proof needs a second relation on the same type: the lexicographic order on a product, a well-order on a type that already has an order, the relation $r$ of an ordinal `Ordinal.type r`, or the preimage of an order along a function. For these relations Mathlib has *unbundled* classes. Each of them takes the relation as an explicit argument, for example `IsPartialOrder α r` or `IsWellOrder α r`.

The classes are defined in `Mathlib.Order.Defs.Unbundled`. The module `Mathlib.Order.RelClasses` holds their API: the instances that connect them with the bundled classes, the ways to pull a relation back along a function, the well-founded classes `WellFoundedLT` and `WellFoundedGT`, bounded and unbounded sets for an arbitrary relation, and the lemmas for the notation `⊆` and `⊂`. The section on well-founded orders uses some of these names. This section gives the whole family.

### The library around it

#### The hierarchy of classes

A class of the family states one property or a combination of properties of a relation $r$ on $\alpha$. The base properties come from the standard library of Lean, as the classes `Std.Refl`, `Std.Irrefl`, `Std.Symm`, `Std.Asymm`, `Std.Antisymm`, `Std.Total` and `Std.Trichotomous`. Mathlib adds transitivity and the combinations.

| Lean name | Statement |
|---|---|
| `IsTrans α r` | $r\,a\,b$ and $r\,b\,c$ give $r\,a\,c$ |
| `IsPreorder α r` | $r$ is reflexive and transitive |
| `IsPartialOrder α r` | a preorder that is antisymmetric |
| `IsLinearOrder α r` | a partial order that is total |
| `IsEquiv α r` | a preorder that is symmetric |
| `IsStrictOrder α r` | $r$ is irreflexive and transitive |
| `IsStrictWeakOrder α r` | a strict order where incomparability is transitive |
| `IsStrictTotalOrder α r` | a strict order that is trichotomous |
| `IsOrderConnected α r` | $r\,a\,c$ gives $r\,a\,b$ or $r\,b\,c$ |
| `IsWellOrder α r` | a strict total order that is well-founded |

The bundled classes give the unbundled ones by instances. A preorder gives `instIsPreorderLe` and `instIsStrictOrderLt`, a partial order gives `instIsPartialOrderLe`, and a linear order gives `instIsLinearOrderLe` and `instIsStrictTotalOrderLt`. A linear order with `WellFoundedLT α` gives `isWellOrder_lt`, and with `WellFoundedGT α` it gives `isWellOrder_gt`. So a lemma stated for an unbundled class applies to `(· ≤ ·)` and `(· < ·)` with no extra work.

The way back needs a definition, because a bundled order is data. The definition `partialOrderOfSO r` builds a partial order from a strict order $r$: it sets $x \le y$ if $x = y$ or $r\,x\,y$, and it takes $r$ as `<`. The proof is short. The relation is reflexive by the first case. It is transitive by a case split, with the transitivity of $r$ in the main case. For antisymmetry, suppose $x \le y$ and $y \le x$ with $x \ne y$. Then $r\,x\,y$ and $r\,y\,x$, so $r\,x\,x$ by transitivity, and this contradicts irreflexivity. In the same way, `linearOrderOfSTO r` builds a linear order from a strict total order with decidable $r$, and `IsWellOrder.linearOrder r` builds a linear order from a well-order. These three are `abbrev`s and not instances, because a type can carry many strict orders. A proof introduces one of them with `letI` when it needs it.

The class `IsOrderConnected` is the condition for the strict part of a weak order. The lemma `IsOrderConnected.neg_trans` states: $\lnot r\,a\,b$ and $\lnot r\,b\,c$ give $\lnot r\,a\,c$. The proof is one line: if $r\,a\,c$, then the class gives $r\,a\,b$ or $r\,b\,c$, and both are false. With asymmetry this gives a strict weak order, `isStrictWeakOrder_of_isOrderConnected`. A strict total order is order-connected by `isStrictOrderConnected_of_isStrictTotalOrder`.

#### Pulling a relation back

A function $f : \beta \to \alpha$ and a relation $r$ on $\alpha$ give the relation $(x, y) \mapsto r\,(f\,x)\,(f\,y)$ on $\beta$. Mathlib has two names for it. The standard library calls it `InvImage r f`, and Mathlib writes it as `f ⁻¹'o r`, with the definition `Order.Preimage`. The module gives the same API for both forms, under the prefixes `InvImage` and `Order.Preimage`.

The properties of the first kind go back along each function: reflexivity, irreflexivity, symmetry, asymmetry, transitivity and totality. So `InvImage.isPreorder`, `InvImage.isEquiv`, `InvImage.isStrictOrder` and `InvImage.isStrictWeakOrder` are instances, and so are `Order.Preimage.instIsPreorder` and its relatives. The properties of the second kind need an injective function, because they conclude an equality in $\beta$ from an equality of images: antisymmetry and trichotomy. So `InvImage.antisymm`, `InvImage.trichotomous`, `InvImage.isPartialOrder`, `InvImage.isLinearOrder` and `InvImage.isStrictTotalOrder` are theorems with a hypothesis `hf` that $f$ is injective, and the same holds for `Order.Preimage.isLinearOrder` and its relatives. The proof of `InvImage.isLinearOrder` combines the instances with injectivity: if $r\,(f\,x)\,(f\,y)$ and $r\,(f\,y)\,(f\,x)$, then $f\,x = f\,y$ by antisymmetry in $\alpha$, so $x = y$.

Well-foundedness also goes back along each function: the instance `instWellFoundedInvImage_mathlib` says that `InvImage r f` is well-founded when $r$ is. The special case `instWellFoundedInvImageNatLt_mathlib` pulls back `<` on `ℕ` along a function $f : \alpha \to \mathbb{N}$. This is the base of a proof by induction on a measure, such as the length of a list.

#### Well-founded relations and the classes of `<` and `>`

Mathlib treats `WellFounded r` as a class, so a hypothesis `[WellFounded r]` is an instance argument. The module gives the API for it in the namespace `WellFounded`. The theorem `WellFounded.induction'` is induction along $r$, the definition `WellFounded.fix'` is recursion along $r$, and `WellFounded.fix'_eq` is its unfolding equation. The theorem `WellFounded.apply'` says that each element is accessible.

A well-founded relation is asymmetric: `WellFounded.asymmetric` says that $r\,a\,b$ gives $\lnot r\,b\,a$. Proof: suppose $r\,a\,b$ and $r\,b\,a$. The set $\{a, b\}$ is nonempty, so it has an $r$-minimal element. But $b$ is below $a$ and $a$ is below $b$, so neither is minimal. The lemma `WellFounded.asymmetric₃` excludes cycles of length three in the same way. The instance `instAsymmOfWellFounded_mathlib` records asymmetry as a class, and `instWellFoundedTransGen_mathlib` says that the transitive closure of a well-founded relation is well-founded.

The abbreviations `WellFoundedLT α` and `WellFoundedGT α` say that `<` and `>` are well-founded. A well-founded `>` is the ascending chain condition. The lemmas `wellFounded_lt` and `wellFounded_gt` give the relation form. The duality lemmas `wellFoundedLT_dual_iff` and `wellFoundedGT_dual_iff` exchange the two conditions on `αᵒᵈ`. Induction and recursion are `WellFoundedLT.induction`, `WellFoundedLT.fix` and `WellFoundedLT.fix_eq`, with the twins for `WellFoundedGT`. The instance `instWellFoundedLTNat` is the induction principle of `ℕ` in this form.

The lexicographic order of two well-founded relations is well-founded: this is `WellFounded.prod_lex`, with the instance `Prod.Lex.instWellFounded`. Proof sketch with minimal elements: let $S \subseteq \alpha \times \beta$ be nonempty. Take $a_0$ minimal in the set of first coordinates of $S$, and then $b_0$ minimal in $\{b \mid (a_0, b) \in S\}$. A pair below $(a_0, b_0)$ in the lexicographic order has a first coordinate below $a_0$, or the first coordinate $a_0$ and a second coordinate below $b_0$. Neither case meets $S$, so $(a_0, b_0)$ is minimal. The dependent forms are `WellFounded.psigma_lex`, `WellFounded.psigma_revLex` and `WellFounded.psigma_skipLeft`. For the product order, `Prod.wellFoundedLT` and `Prod.wellFoundedGT` give the classes on `α × β`. Two well-orders give the well-order `instIsWellOrderProdLex` on the product. At the other end, `Subsingleton.isWellOrder` and `instIsWellOrderOfIsEmpty` treat the trivial types.

#### Bounded and unbounded sets

For a relation $r$ and a set $s$, `Set.Bounded r s` says that some $a$ satisfies $r\,b\,a$ for each $b \in s$. The set is unbounded, `Set.Unbounded r s`, if for each $a$ some $b \in s$ has $\lnot r\,b\,a$. For $r = (\cdot < \cdot)$ on a linear order an unbounded set is a cofinal set. The two notions are negations of each other: `Set.not_bounded_iff` and `Set.not_unbounded_iff`. Proof: the negation of $\exists a\, \forall b \in s,\ r\,b\,a$ is $\forall a\, \exists b \in s,\ \lnot r\,b\,a$, by the rules for the negation of quantifiers.

#### Subsets and strict subsets

The class `IsNonstrictStrictOrder α r s` says that $s$ is the strict relation of $r$: `right_iff_left_not_left` states $s\,a\,b \leftrightarrow r\,a\,b \land \lnot r\,b\,a$. The instance `instIsNonstrictStrictOrderLeLt` gives it for `≤` and `<`, and `instIrreflOfIsNonstrictStrictOrder` deduces that $s$ is irreflexive.

The second half of the module states the order lemmas in the notation `⊆` and `⊂`. A type with the tag `UsesSetNotationForOrder`, such as `Set α` and `Finset α`, writes its order `≤` as `⊆` and `<` as `⊂`. The lemmas `subset_trans`, `subset_antisymm`, `ssubset_irrefl`, `ssubset_trans` and `ssubset_iff_subset_ne` are the forms of `le_trans`, `le_antisymm`, `lt_irrefl`, `lt_trans` and `lt_iff_le_and_ne`. The dot-notation forms are `LE.le.trans_ssubset`, `LT.lt.trans_subset` and `LE.le.ssubset_of_ne`. The older names with the prefixes `HasSubset.Subset` and `HasSSubset.SSubset` are deprecated aliases.

#### Common errors

1. An instance search does not find `InvImage.isLinearOrder`, because it is a theorem with a hypothesis `hf` that $f$ is injective. Give it to Lean by `haveI := InvImage.isLinearOrder hf`.
2. A proof that uses `letI := partialOrderOfSO r` on a type that already has an order works with two orders on the same type. The lemmas then apply to the instance that Lean finds first. Use a type synonym, or keep the relation unbundled.
3. A proof writes `HasSubset.Subset.trans h₁ h₂` from an older source. The name is a deprecated alias. Write `h₁.trans h₂` or `subset_trans h₁ h₂`.

### Exercises

1. (A) Show that each irreflexive relation on a type with at most one element is a well-order, as `Subsingleton.isWellOrder` states.
2. (A) Let $r$ be a strict order on $\alpha$. Show that in the partial order `partialOrderOfSO r` the strict relation `<` is $r$.
3. (B) Show that an asymmetric and order-connected relation is transitive. This is part of `isStrictWeakOrder_of_isOrderConnected`.
4. (B) Give a function $f$ and a partial order $r$ such that `InvImage r f` is not antisymmetric. Explain why `InvImage.isPartialOrder` needs injectivity.
5. (B) Show that `<` on `ℕ × ℕ` with the lexicographic order is well-founded, from `WellFounded.prod_lex`, and use it to prove that the function of Ackermann terminates.
6. (C) Let $\alpha$ be a linear order with no maximal element. Show that `Set.Unbounded (· < ·) s` holds if and only if `Set.Unbounded (· ≤ ·) s` holds, and give a counterexample when $\alpha$ has a top element.

### Reference

<?reference?>
