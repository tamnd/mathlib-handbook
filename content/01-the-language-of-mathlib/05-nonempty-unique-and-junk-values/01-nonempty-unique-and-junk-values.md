---
title: Empty, nonempty and unique types
kind: theory
modules:
  - Mathlib.Basic.Unique
  - Mathlib.Basic.Nonempty
  - Mathlib.Basic.IsEmpty.Defs
  - Mathlib.Basic.IsEmpty.Basic
  - Mathlib.Basic.Nontrivial.Defs
  - Mathlib.Basic.Nontrivial.Basic
  - Mathlib.Algebra.PEmptyInstances
explains:
  E3: [Unique, IsEmpty, Nontrivial]
  E2: [Unique.instSubsingleton, Nonempty.some, uniqueOfSubsingleton, Unique.uniq, Pi.unique, isEmpty_or_nonempty, not_nonempty_iff, Function.isEmpty, IsEmpty.elim, isEmpty_prod, exists_pair_ne, not_nontrivial_iff_subsingleton, subsingleton_or_nontrivial, Function.Injective.nontrivial, Classical.arbitrary]
  E1: auto
families: []
requires: [V01.C04]
reads_with: ["MIL"]
lean:
  - MathlibHandbook/V01/C05/Examples.lean
  - MathlibHandbook/V01/C05/Exercises.lean
  - MathlibHandbook/V01/C05/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Empty, nonempty and unique types

### Overview

Many statements depend on the number of elements of a type, at least in a rough way. Chapter 1 showed that $(\forall x,\ q \land p(x)) \to q$ fails over an empty type. Chapter 3 showed that an injective map has a left inverse only when its domain is nonempty. A ring with $0 = 1$ has only one element, and many theorems of algebra exclude it. Mathlib has a class for each of these conditions: `IsEmpty α` for a type with no element, `Nonempty α` for a type with some element, `Subsingleton α` for a type with at most one element, `Unique α` for a type with exactly one element, and `Nontrivial α` for a type with at least two elements.

This section defines the classes, proves the relations between them, and shows their use as hypotheses. The classes are found by instance search, as Chapter 4 explains, so a lemma with the hypothesis `[Nonempty α]` applies to $\mathbb{N}$ with no extra work. The next section uses these ideas for the junk values of total functions.

### Definitions

**Definition (Empty and nonempty).** A type $\alpha$ is *empty* when it has no element: `IsEmpty α` states that there is a function $\alpha \to \mathrm{False}$. It is *nonempty* when it has an element: `Nonempty α` is the proposition $\exists a : \alpha,\ \mathrm{True}$, in the form of an inductive type with one constructor that takes an element.

**Definition (Inhabited).** `Inhabited α` is a class with one field, an element `default : α`. It is data, not a proposition. Two instances can give different defaults, and a definition can use the default.

**Definition (Subsingleton and unique).** A type $\alpha$ is a *subsingleton* when any two of its elements are equal. A type is *unique* when it has an element and every element is equal to it: `Unique α` is a structure with a field `default : α` and a field `uniq : ∀ a, a = default`.

**Definition (Nontrivial).** A type $\alpha$ is *nontrivial* when it has two different elements: $\exists x\ y,\ x \neq y$.

::: mathlib
`Unique` · `Mathlib.Basic.Unique`

`Unique α` extends `Inhabited α` with the field `uniq`. Its instances include `Unit`, `PUnit`, `Fin 1`, the functions into a unique type (`Pi.unique`), and the functions out of an empty type. An instance gives `Subsingleton α` by `Unique.instSubsingleton`. Conversely, `uniqueOfSubsingleton a` builds `Unique α` from a subsingleton type and an element.

<?decl Unique?>
:::

::: mathlib
`IsEmpty` · `Mathlib.Basic.IsEmpty.Defs`

`IsEmpty α` has the field `false : α → False`. The function `isEmptyElim` proves any statement about an element of an empty type. The instances include `Empty`, `Fin 0` and `False`, and `α × β` when `α` is empty. The two forms of emptiness are linked by `not_nonempty_iff : ¬Nonempty α ↔ IsEmpty α`.

<?decl IsEmpty?>
:::

### Theorems and proofs

**Theorem (Empty or nonempty).** Every type is empty or nonempty, and not both.

*Proof.* By the excluded middle, $\mathrm{Nonempty}\ \alpha$ holds or fails. If it fails, then each $a : \alpha$ gives $\mathrm{Nonempty}\ \alpha$ and a contradiction, so $\alpha \to \mathrm{False}$, and $\alpha$ is empty. Not both: an element $a$ and a function $\alpha \to \mathrm{False}$ give $\mathrm{False}$. $\square$

The theorem is classical. A constructive proof would decide, for every type, whether it has an element, and this includes the type of proofs of any open conjecture.

**Theorem (Functions and emptiness).** Let $f : \alpha \to \beta$.

1. If $\beta$ is empty, then $\alpha$ is empty.
2. If $\alpha$ is empty, then there is exactly one function $\alpha \to \beta$, for every $\beta$.
3. If $\alpha$ is nonempty and $\beta$ is empty, then there is no function $\alpha \to \beta$.

*Proof.* 1. For $a : \alpha$, the element $f(a) : \beta$ gives a contradiction. So $\alpha \to \mathrm{False}$.

2. The function $a \mapsto \mathrm{elim}(a)$, where $\mathrm{elim}$ is ex falso from the contradiction at $a$, is a function $\alpha \to \beta$. Two functions $g, h : \alpha \to \beta$ agree at every $a$, because there is no $a$. By function extensionality, $g = h$.

3. This is part 1: a function would make $\alpha$ empty. $\square$

In Mathlib, part 1 is the instance `Function.isEmpty`, and the elimination of an element of an empty type is `IsEmpty.elim`.

So the type $\alpha \to \beta$ is unique when $\alpha$ is empty. In particular, $\mathrm{Empty} \to \mathrm{Empty}$ has exactly one element, the identity, and it is a bijection.

**Theorem (Unique is inhabited and subsingleton).** A type is unique if and only if it is nonempty and a subsingleton.

*Proof.* Let $\alpha$ be unique, with $d$ and $u : \forall a,\ a = d$. Then $d$ shows that $\alpha$ is nonempty. For $a, b : \alpha$, $a = d = b$ by $u(a)$ and $u(b)$. Conversely, let $\alpha$ be a subsingleton with an element $d$. Then every $a$ equals $d$. So $\langle d, u\rangle$ is a unique structure. $\square$

The direction from right to left gives `Unique` from `Nonempty` only by choosing the element, and so `uniqueOfSubsingleton` takes an element as an argument, not a proof of `Nonempty`.

**Theorem (Unique types are equivalent).** If $\alpha$ and $\beta$ are unique, then $\alpha \simeq \beta$, and this equivalence is the only one.

*Proof.* Let $d_\alpha$ and $d_\beta$ be the elements. The functions $a \mapsto d_\beta$ and $b \mapsto d_\alpha$ are inverse to each other: $d_\alpha$ is the only element of $\alpha$, so the composite on $\alpha$ sends every $a$ to $d_\alpha = a$, and the same on $\beta$. Any two equivalences agree at every point, since $\beta$ is a subsingleton, and extensionality makes them equal. $\square$

**Theorem (Subsingleton or nontrivial).** Every type is a subsingleton or nontrivial, and not both.

*Proof.* By the excluded middle, $\exists x\ y,\ x \neq y$ holds or fails. If it holds, the type is nontrivial. If it fails, then for all $x, y$, $\lnot(x \neq y)$, and the elimination of double negation gives $x = y$. Not both: $x \neq y$ contradicts $x = y$. $\square$

The lemma `not_nontrivial_iff_subsingleton` states the same fact as an equivalence, and `exists_pair_ne` extracts the two different elements from `[Nontrivial α]`.

::: mathlib
`subsingleton_or_nontrivial` · `Mathlib.Basic.Nontrivial.Defs`

The statement is `Subsingleton α ∨ Nontrivial α`. A proof that splits on the size of a type uses `rcases subsingleton_or_nontrivial α with h | h`. In the first case `Subsingleton.elim` proves equations. In the second case lemmas with `[Nontrivial α]` apply, such as `zero_ne_one` for a ring.

<?decl subsingleton_or_nontrivial?>
:::

**Theorem (Nontrivial rings).** Let $R$ be a ring. Then $R$ is nontrivial if and only if $0 \neq 1$ in $R$.

*Proof.* If $0 \neq 1$, then $0$ and $1$ are two different elements. Conversely, assume $0 = 1$. For every $a : R$, $a = a \cdot 1 = a \cdot 0 = 0$, by the identity law and the law $a \cdot 0 = 0$ of Section 1 of Chapter 4. So every element equals $0$, and $R$ is a subsingleton. By the previous theorem it is not nontrivial. $\square$

This is why a field in Mathlib extends `Nontrivial`, and why many lemmas of algebra take `[Nontrivial R]`. The trivial ring $\{0\}$ satisfies every equational axiom of a ring with $0 = 1$, and it would make some theorems false, such as the theorem that a field has exactly two ideals: the trivial ring has only one.

**Theorem (Transfer of nontriviality).** Let $f : \alpha \to \beta$ be injective. If $\alpha$ is nontrivial, then $\beta$ is nontrivial.

*Proof.* Let $x \neq y$ in $\alpha$. Injectivity gives $f(x) \neq f(y)$ by contraposition. $\square$

This is `Function.Injective.nontrivial`. The dual statement, `Function.Surjective.nontrivial`, transfers nontriviality from the codomain of a surjection to its domain. The product of unique types is unique by the same kind of argument, and `Pi.unique` gives the instance for function types.

### Examples

**Example (A nonempty type).** The proposition `Nonempty ℕ` has the proof `⟨0⟩`. The proof contains the element $0$, but the proposition forgets it: any two proofs are equal, by proof irrelevance.

<?lean MathlibHandbook/V01/C05/Examples.lean#nonempty?>

**Example (A default element).** `Inhabited ℕ` is data, with the default $0$. The equation `default = 0` holds by `rfl`, because the instance is a definition that Lean can unfold.

<?lean MathlibHandbook/V01/C05/Examples.lean#inhabited?>

**Example (A unique type).** `Fin 1` has exactly one element, $0$. The instance `Unique (Fin 1)` exists, so `Subsingleton (Fin 1)` follows, and `Subsingleton.elim` proves that any two elements are equal.

<?lean MathlibHandbook/V01/C05/Examples.lean#unique?>

**Example (An empty product).** The type $\mathbb{N} \times \mathrm{Empty}$ is empty, by the lemma `isEmpty_prod`: a product is empty if and only if one factor is empty. So the statement $\forall z : \mathbb{N} \times \mathrm{Empty},\ P(z)$ holds for every $P$, and $\exists z : \mathbb{N} \times \mathrm{Empty},\ P(z)$ is false. The sum $\mathbb{N} \oplus \mathrm{Empty}$ is nonempty, and in fact equivalent to $\mathbb{N}$.

**Counterexample (Nonempty does not give an element in a definition).** From `h : Nonempty ℕ`, the term `Nonempty.some h` is an element of `ℕ`, by the axiom of choice. Its value cannot be computed, and no proof can show that it is $0$. A definition that needs a specific element must take `[Inhabited α]` or an explicit argument. For this reason, Mathlib uses `Inhabited` for data and `Nonempty` in hypotheses of theorems.

### The library around it

The modules are `Mathlib.Basic.Nonempty`, with `Nonempty.some`, `Nonempty.map` and `Classical.arbitrary`; `Mathlib.Basic.IsEmpty.Defs` and `Mathlib.Basic.IsEmpty.Basic`, with `IsEmpty`, `isEmptyElim`, `isEmpty_or_nonempty`, `isEmpty_prod`, `isEmpty_sum` and `isEmpty_pi`; `Mathlib.Basic.Unique`, with `Unique`, `Unique.forall_iff` and `Unique.exists_iff`; and `Mathlib.Basic.Nontrivial.Defs`, with `Nontrivial`, `exists_pair_ne`, `nontrivial_iff` and `Function.Surjective.nontrivial`. The core library defines `Nonempty`, `Inhabited` and `Subsingleton`.

The module `Mathlib.Basic.Nontrivial.Basic` gives the instances that make `Nontrivial` pass through the type constructors. A product $\alpha \times \beta$ is nontrivial when one factor is nontrivial and the other is nonempty (`nontrivial_prod_left`, `nontrivial_prod_right`). A sum $\alpha \oplus \beta$ is nontrivial when one summand is nontrivial, or when both are nonempty (`instNontrivialSum`, `instNontrivialSumOfNonempty`). The type `Option α` is nontrivial when `α` is nonempty (`Option.nontrivial`), because `none` differs from each `some a`. A function type `α → β` is nontrivial when `α` is nonempty and `β` is nontrivial (`Function.nontrivial`), and `Pi.nontrivial_at` gives the dependent form from one nontrivial factor. For a linear order, `nontrivial_iff_lt` states that $\alpha$ is nontrivial if and only if $x < y$ for some $x$ and $y$, and `nontrivial_of_lt` is one direction for a preorder. The definition `nontrivialPSumUnique` decides, for an inhabited type, between the two cases "nontrivial" and "unique"; it uses choice. The module `Mathlib.Algebra.PEmptyInstances` has no live declarations.

The equivalences `Equiv.equivEmpty : α ≃ Empty` and `Equiv.equivPUnit : α ≃ PUnit` exist under `[IsEmpty α]` and `[Unique α]`. The tactic `simp` uses `IsEmpty.forall_iff` and `Unique.forall_iff` to remove quantifiers over such types.

#### Common errors

1. A learner uses `Nonempty α` where a definition needs an element, and gets a noncomputable definition. Use `Inhabited α`.
2. A learner proves `x = y` in `Fin 1` by `rfl`. This works here, but in a general subsingleton use `Subsingleton.elim x y`.
3. A learner forgets the hypothesis `[Nontrivial R]` for a lemma such as `zero_ne_one`, and the instance search fails for a general ring.

### Exercises

1. (A) Decide which of the classes `IsEmpty`, `Nonempty`, `Subsingleton`, `Unique` and `Nontrivial` hold for `Empty`, `Unit`, `Bool`, `Fin 0`, `Fin 1` and `ℕ`.
2. (A) Prove that every function $\beta \to \alpha$ is injective when $\beta$ is a subsingleton. Give an example that shows that the hypothesis on $\alpha$ alone is not sufficient.
3. (B) Prove that $\alpha \to \beta$ is unique when $\beta$ is unique, for every $\alpha$.
4. (B) Prove that $\alpha \times \beta$ is nontrivial when $\alpha$ is nontrivial and $\beta$ is nonempty. Show that the second hypothesis is needed.
5. (B) Prove that a surjection from a subsingleton type has a subsingleton codomain.
6. (C) Show that `Prop` is nontrivial and that `Unique` of a proposition $p$ is equivalent to $p$.
7. (L) Prove that any two elements of `Fin 1` are equal. The solution is `subsingleton_fin_one` in `Solutions.lean`.

### Notes and history

The empty set has been part of set theory since Zermelo's axioms of 1908, and the convention that there is exactly one function from the empty set is due to the definition of a function as a set of pairs. The distinction between a proposition that a type has an element and the data of an element is a theme of constructive mathematics, and it is the difference between `Nonempty` and `Inhabited`.

### Reference

<?reference?>
