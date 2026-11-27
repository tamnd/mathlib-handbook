---
title: Well-orders and order types
kind: theory
modules:
  - Mathlib.SetTheory.Ordinal.Basic
explains:
  E3: [Ordinal, Ordinal.type, Ordinal.typein, Ordinal.enum, Ordinal.lt_wf, Cardinal.ord]
  E2: [WellOrder, Ordinal.isEquivalent, Ordinal.type_eq, Ordinal.type_le_iff, Ordinal.type_lt_iff, Ordinal.typein_lt_typein, Ordinal.typein_surj, Ordinal.typein_enum, Ordinal.enum_typein, Ordinal.typein_top, Ordinal.card, Ordinal.card_type, Ordinal.lift, Ordinal.lift_le, Ordinal.omega0, Ordinal.type_nat_lt, Ordinal.type_fin, Cardinal.ord_le, Cardinal.card_ord]
  E1: auto
families: []
requires: [V31.C01, V04.C01, V04.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Well-orders and order types

### Overview

A cardinal forgets everything about a type except its size. An ordinal keeps one more piece of structure: a well-order. Two well-ordered types have the same ordinal when an order isomorphism connects them. Chapter 1 built the cardinals in the same way.

The theory rests on two facts about well-orders. First, a map from a well-order onto an initial part of another well-order is unique, so isomorphisms of well-orders are unique. Second, any two well-orders are comparable: one of them is isomorphic to an initial segment of the other. With these two facts, the ordinals form a linear order. The elements of a well-order $r$ then enumerate the ordinals below $\mathrm{type}\,r$, and $\mathrm{card}$ and $\mathrm{ord}$ connect ordinals with cardinals.

The section uses well-founded induction from Volume 4, Chapter 1 and order isomorphisms from Volume 4, Chapter 2.

### Definitions

**Definition (Well-order).** A relation $r$ on a type $\alpha$ is a *well-order* when it is irreflexive, transitive, trichotomous and well-founded. Trichotomous means that for all $a, b$, either $r\,a\,b$, or $a = b$, or $r\,b\,a$.

**Definition (Initial segment embedding).** Let $r$ on $\alpha$ and $s$ on $\beta$ be relations. An *initial segment embedding* $f : r \preceq_i s$ is an injective map $f : \alpha \to \beta$ with $s\,(f\,a)\,(f\,b) \iff r\,a\,b$, and with one more property: if $s\,b\,(f\,a)$, then $b$ is in the range of $f$. So the range of $f$ is closed downward.

**Definition (Principal segment embedding).** A *principal segment embedding* $f : r \prec_i s$ is a relation embedding together with an element $t \in \beta$, the *top*, such that the range of $f$ is exactly $\{b \mid s\,b\,t\}$.

**Definition (Ordinal).** A *well-ordered type* in universe $u$ is a triple $(\alpha, r, h)$ with $\alpha : \mathrm{Type}\ u$ and $h$ a proof that $r$ is a well-order. Two such triples are *equivalent* when an order isomorphism $r \simeq_r s$ exists. The type $\mathrm{Ordinal}_u$ is the quotient by this equivalence. The class of $(\alpha, r)$ is the *order type* $\mathrm{type}\,r$.

As for cardinals, $\mathrm{Ordinal}_u$ lives in $\mathrm{Type}\ (u+1)$.

**Definition (Order of ordinals).** $\mathrm{type}\,r \le \mathrm{type}\,s$ when an initial segment embedding $r \preceq_i s$ exists, and $\mathrm{type}\,r < \mathrm{type}\,s$ when a principal segment embedding $r \prec_i s$ exists.

**Definition (Enumeration).** Let $r$ be a well-order on $\alpha$ and let $a \in \alpha$. The ordinal $\mathrm{typein}\,r\,a$ is the type of $r$ restricted to $\{x \mid r\,x\,a\}$. The inverse map $\mathrm{enum}\,r$ sends each ordinal $o < \mathrm{type}\,r$ to the element $a$ with $\mathrm{typein}\,r\,a = o$.

**Definition (Cardinal, lift and $\omega$).** The cardinal of an ordinal is $\mathrm{card}(\mathrm{type}\,r) = \#\alpha$. The lift of $\mathrm{type}\,r$ to a higher universe is the type of $r$ moved along $\mathrm{ULift}$. The ordinal $\omega$ is the lift of the type of $<$ on $\mathbb{N}$.

**Definition (Initial ordinal of a cardinal).** For a cardinal $c = \#\alpha$, the ordinal $\mathrm{ord}\,c$ is the infimum of $\mathrm{type}\,r$ over all well-orders $r$ on $\alpha$.

### Theorems and proofs

**Theorem (Uniqueness of initial segments).** Let $s$ be a well-order on $\beta$ and let $f, g : r \preceq_i s$. Then $f = g$.

*Proof.* The relation $r$ is well-founded, since $f$ embeds it in $s$. Use well-founded induction on $a$. Suppose that $f\,x = g\,x$ for each $x$ with $r\,x\,a$. Because the range of $f$ is closed downward, the elements $b$ with $s\,b\,(f\,a)$ are exactly the $f\,x$ with $r\,x\,a$. The same holds for $g$. By the hypothesis of induction, the two sets $\{b \mid s\,b\,(f\,a)\}$ and $\{b \mid s\,b\,(g\,a)\}$ are equal. In a trichotomous irreflexive order, two elements with the same strict lower set are equal. So $f\,a = g\,a$. $\square$

**Corollary (Rigidity).** An order isomorphism between two well-orders is unique. The only automorphism of a well-order is the identity.

**Corollary (No well-order is a proper part of itself).** For a well-order $r$, no principal segment embedding $r \prec_i r$ exists.

*Proof.* Let $f : r \prec_i r$ with top $t$. Then $f$ is also an initial segment embedding $r \preceq_i r$, so $f$ is the identity by the theorem. The top $t$ is in the range of the identity, so $r\,t\,t$ holds. This contradicts irreflexivity. $\square$

**Proposition (Initial or principal).** Let $s$ be a well-order on $\beta$ and $f : r \preceq_i s$. Then $f$ is surjective, or the range of $f$ is $\{b \mid s\,b\,t\}$ for the least $t$ outside the range.

*Proof.* If $s\,b\,t$, then $b$ is in the range by the choice of $t$. If $b = f\,a$ is in the range, then $b \ne t$, and $s\,t\,b$ would put $t$ in the range, since the range is closed downward. So $s\,b\,t$ by trichotomy. $\square$

**Theorem (Comparability of well-orders).** For well-orders $r$ on $\alpha$ and $s$ on $\beta$, there is an initial segment embedding $r \preceq_i s$ or one $s \preceq_i r$.

*Proof.* Call $a \in \alpha$ and $b \in \beta$ *matched* when the restriction of $r$ below $a$ is isomorphic to the restriction of $s$ below $b$. By rigidity and the corollary above, each $a$ is matched with at most one $b$, and each $b$ with at most one $a$. Let $A$ be the set of $a$ that have a match and let $h : A \to \beta$ give the match. If $a \in A$ and $r\,a'\,a$, then the isomorphism for $a$ restricts to an isomorphism below $a'$, so $a' \in A$ and $h$ preserves the order. Thus $A$ is closed downward, $h$ is an order isomorphism onto its range $B$, and $B$ is also closed downward. Suppose that $A \ne \alpha$ and $B \ne \beta$. Let $a$ be least outside $A$ and $b$ least outside $B$. Then $A = \{x \mid r\,x\,a\}$ and $B = \{y \mid s\,y\,b\}$, and $h$ shows that $a$ and $b$ are matched. This contradicts $a \notin A$. So $A = \alpha$, and $h$ is an initial segment embedding of $r$ in $s$, or $B = \beta$, and $h^{-1}$ is one of $s$ in $r$. $\square$

**Theorem (The order of ordinals).** The relations $\le$ and $<$ on ordinals do not depend on the choice of representatives, and they make $\mathrm{Ordinal}$ a linear order.

*Proof.* An isomorphism composes with an initial or principal segment embedding on each side, so the relations are well defined. For antisymmetry, let $f : r \preceq_i s$ and $g : s \preceq_i r$. Then $g \circ f : r \preceq_i r$ is the identity by uniqueness, and in the same way $f \circ g$ is the identity, so $f$ is an isomorphism. By the proposition, $a < b$ holds exactly when $a \le b$ and not $b \le a$: a principal embedding and an initial one in the other direction would compose to a principal embedding $r \prec_i r$. Comparability gives totality. $\square$

**Theorem (Enumeration of the ordinals below a type).** Let $r$ be a well-order on $\alpha$.

1. $\mathrm{typein}\,r\,a < \mathrm{typein}\,r\,b \iff r\,a\,b$.
2. $\mathrm{typein}\,r\,a < \mathrm{type}\,r$ for each $a$.
3. For each ordinal $o < \mathrm{type}\,r$, there is a unique $a$ with $\mathrm{typein}\,r\,a = o$.

So $\mathrm{typein}\,r$ is an order isomorphism from $\alpha$ onto $\{o \mid o < \mathrm{type}\,r\}$, with inverse $\mathrm{enum}\,r$.

*Proof.* The inclusion of $\{x \mid r\,x\,a\}$ in $\alpha$ is a principal segment embedding with top $a$, which gives 2. If $r\,a\,b$, then the inclusion of the part below $a$ in the part below $b$ is principal with top $a$, which gives one direction of 1. The other direction follows from trichotomy. For 3, let $o = \mathrm{type}\,t$ with $f : t \prec_i r$. Let $a$ be the top of $f$. Then $f$ is an isomorphism from $t$ onto the part below $a$, so $o = \mathrm{typein}\,r\,a$. Uniqueness follows from 1. $\square$

**Theorem (The ordinals are well-founded).** The relation $<$ on $\mathrm{Ordinal}_u$ is well-founded.

*Proof.* It suffices to show that each ordinal $o$ is accessible. Every ordinal below $o = \mathrm{type}\,r$ is an element of $\{p \mid p < o\}$, and this set is order isomorphic to $\alpha$ by the theorem above. The relation $r$ is well-founded, so $<$ restricted to this set is well-founded. The set is closed downward, so a descending chain that starts below $o$ stays in it. Thus each $p < o$ is accessible, and so is $o$. $\square$

So $\mathrm{Ordinal}_u$ is itself a well-order. Section 2 computes its order type below each $o$.

**Proposition (Cardinals and ordinals).** The map $\mathrm{card}$ is monotone and surjective. For each cardinal $c$, $\mathrm{card}(\mathrm{ord}\,c) = c$, and for each ordinal $o$, $\mathrm{ord}\,c \le o \iff c \le \mathrm{card}\,o$.

*Proof.* An initial segment embedding is injective, so $\mathrm{card}$ is monotone. Let $c = \#\alpha$. A well-order on $\alpha$ exists by Chapter 1, Section 2, and the ordinals are well-founded, so the infimum is attained: $\mathrm{ord}\,c = \mathrm{type}\,r$ for some $r$ on $\alpha$. Then $\mathrm{card}(\mathrm{ord}\,c) = \#\alpha = c$, and $\mathrm{ord}\,c \le o$ gives $c \le \mathrm{card}\,o$. Conversely, let $o = \mathrm{type}\,s$ on $\beta$ and let $e : \alpha \hookrightarrow \beta$. Pull $s$ back along $e$ to a well-order on $\alpha$. The map $e$ is a relation embedding of it in $s$, so its type is at most $o$ by Exercise 4. So $\mathrm{ord}\,c \le o$. $\square$

So $\mathrm{ord}$ and $\mathrm{card}$ form a Galois connection in the sense of Volume 4, Chapter 6. Chapter 5 builds the alephs on $\mathrm{ord}$.

### Examples

**Example (Finite order types).** For $n \in \mathbb{N}$, the order type of $<$ on $\mathrm{Fin}\,n$ is the ordinal $n$. Any two linear orders on a type of $n$ elements are isomorphic: send the $k$th smallest element to the $k$th smallest. So each well-order on a finite type of $n$ elements has type $n$, and for finite types the ordinal holds no more information than the cardinal.

**Example (Two orders on $\mathbb{N}$).** Let $r$ be the order on $\mathbb{N}$ that puts $0$ above everything and orders the rest as usual: $1, 2, 3, \dots, 0$. The order $r$ has a largest element and $<$ has none, so no isomorphism exists and $\mathrm{type}\,r \ne \omega$. The map $n \mapsto n + 1$ is a principal segment embedding of $<$ in $r$ with top $0$. So $\omega < \mathrm{type}\,r$, while $\mathrm{card}\,\omega = \mathrm{card}(\mathrm{type}\,r) = \aleph_0$. Chapter 3 names this ordinal $\omega + 1$.

**Counterexample (Rigidity needs well-foundedness).** The order $<$ on $\mathbb{Z}$ is linear but not well-founded. The map $n \mapsto n + 1$ is an automorphism other than the identity, so rigidity fails. In $\mathbb{Q}$, the initial part $\{q \mid q < 0\}$ is a countable dense order without end points, so it is isomorphic to $\mathbb{Q}$ by Cantor's theorem on such orders. So a linear order can be isomorphic to a proper initial part of itself.

### The library around it

::: mathlib
`Ordinal` · `Mathlib.SetTheory.Ordinal.Basic`

`Ordinal.{u}` is the quotient of the structure `WellOrder` by the setoid `Ordinal.isEquivalent`, which relates two well-orders when `Nonempty (r ≃r s)`. The well-order is a relation `r : α → α → Prop` with an instance `IsWellOrder α r`, not a `LinearOrder` instance.

<?decl Ordinal?>
:::

::: mathlib
`Ordinal.type` · `Mathlib.SetTheory.Ordinal.Basic`

`Ordinal.type r` takes the relation explicitly and finds the well-order instance. The lemma `Ordinal.type_eq` states `type r = type s ↔ Nonempty (r ≃r s)`. The lemmas `Ordinal.type_le_iff` and `Ordinal.type_lt_iff` unfold the order into `Nonempty (r ≼i s)` and `Nonempty (r ≺i s)`, both by `Iff.rfl`.

<?decl Ordinal.type?>
:::

::: mathlib
`InitialSeg` · `Mathlib.Order.InitialSeg`

The structure `InitialSeg r s`, written `r ≼i s`, extends `r ↪r s` with the field that its range is closed downward. The structure `PrincipalSeg r s`, written `r ≺i s`, adds a `top`. Their home is Volume 4. The uniqueness theorem is `InitialSeg.eq`, comparability is `InitialSeg.total`, and antisymmetry is `InitialSeg.antisymm`, which returns an order isomorphism. The corollary on proper parts is `PrincipalSeg.irrefl`.

<?decl InitialSeg?>
:::

::: mathlib
`Ordinal.typein` · `Mathlib.SetTheory.Ordinal.Basic`

`Ordinal.typein r` is a bundled principal segment `r ≺i (· < ·)` into `Ordinal`, with top `type r`. The lemmas `Ordinal.typein_lt_typein`, `Ordinal.typein_lt_type` and `Ordinal.typein_surj` give the three parts of the enumeration theorem. `Ordinal.typein_top` computes the ordinal of the top of a principal segment.

<?decl Ordinal.typein?>
:::

::: mathlib
`Ordinal.enum` · `Mathlib.SetTheory.Ordinal.Basic`

`Ordinal.enum r` is an order isomorphism from the subtype `Set.Iio (type r)` to `r`. It takes a pair `⟨o, h⟩` with `h : o < type r`. The lemmas `Ordinal.typein_enum` and `Ordinal.enum_typein` state that it inverts `typein`.

<?decl Ordinal.enum?>
:::

::: mathlib
`Ordinal.lt_wf` · `Mathlib.SetTheory.Ordinal.Basic`

The instance `Ordinal.lt_wf : WellFoundedLT Ordinal` is the well-foundedness theorem.

<?decl Ordinal.lt_wf?>
:::

::: mathlib
`Cardinal.ord` · `Mathlib.SetTheory.Ordinal.Basic`

`Cardinal.ord c` is the least ordinal with cardinal `c`. The lemmas `Cardinal.card_ord`, `Cardinal.ord_le`, `Cardinal.ord_le_type` and `Cardinal.gc_ord_card` give the Galois connection with `Ordinal.card`. The value `Cardinal.ord_aleph0` is `ord ℵ₀ = ω`.

<?decl Cardinal.ord?>
:::

The lemma `Ordinal.card_type` is `card (type r) = #α`. `Ordinal.lift_le` shows that `Ordinal.lift` preserves the order. `Ordinal.type_fin` and `Ordinal.type_nat_lt` compute the types of `Fin n` and `ℕ`.

Common errors of a learner:

- `ω` is notation for `Ordinal.omega0` and needs `open Ordinal`. The name ends in `0` because `Ordinal.omega` is a different object, the initial ordinal function of Chapter 5.
- `typeLT α` is notation for `type (· < ·)` on `α`. A goal with `type r` for an explicit `r` does not unify with it unless `r` is literally `(· < ·)`.
- `Ordinal.enum r` takes a subtype element, not an ordinal and a proof as two arguments. Write `enum r ⟨o, h⟩`.
- The type of `<` on `ℕ` lives in `Ordinal.{0}`. In another universe, `ω` is a lift, and a goal with `type (· < ·)` on `ℕ` and `ω.{u}` needs `Ordinal.lift`.

### Exercises

1. (A) Show that the order on $\mathbb{N} \times \mathrm{Bool}$ that compares the second coordinate first, with $\mathrm{false}$ below $\mathrm{true}$, and then the first coordinate, is a well-order. Show that its type is strictly above $\omega$.
2. (A) Show that $\mathrm{typein}\,r\,a = 0$ if and only if $a$ is the least element of $r$.
3. (A) Show that an ordinal $o$ is $0$ if and only if its underlying type is empty, and that $\mathrm{card}\,o = 0$ if and only if $o = 0$.
4. (B) Show that each order embedding of a well-order $r$ in a well-order $s$ gives $\mathrm{type}\,r \le \mathrm{type}\,s$. Hint: send each $a$ to the least element of $\beta$ that is above the images of all $x$ with $r\,x\,a$.
5. (B) Show that if $o < \mathrm{type}\,r$ and $o' < \mathrm{type}\,r$, then $\mathrm{enum}\,r\,o$ is below $\mathrm{enum}\,r\,o'$ for $r$ if and only if $o < o'$.
6. (B) Show that $\mathrm{ord}$ is strictly monotone, and that $\mathrm{ord}\,n = n$ for each natural number $n$.
7. (C) Let $r$ be a well-order on $\alpha$ and $S \subseteq \alpha$. Show that the type of $r$ restricted to $S$ is at most $\mathrm{type}\,r$. Find all $S \subseteq \mathbb{N}$ whose restricted type is $\omega$, and show that equality can hold with $S \ne \alpha$.

### Notes and history

Cantor developed well-ordered sets and their order types in the second part of his *Beiträge* in 1897, including the comparability of well-orders. The definition of an ordinal as a class of isomorphic well-orders is the one in Russell and Whitehead, *Principia Mathematica*. In set theory this class is too large to be a set, and von Neumann chose one representative in each class instead. Chapter 7 treats that definition. Mathlib keeps the classes and avoids the size problem with universes: the well-orders in $\mathrm{Type}\ u$ give an ordinal in $\mathrm{Type}\ (u+1)$. Jech, *Set Theory*, Chapter 2, and Kunen, *Set Theory*, Chapter I, give the ZFC treatment.

### Reference

<?reference?>
