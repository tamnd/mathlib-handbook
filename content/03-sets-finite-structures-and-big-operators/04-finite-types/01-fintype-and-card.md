---
title: The class Fintype and the card of a type
kind: theory
modules:
  - Mathlib.Data.Fintype.Card
explains:
  E3: [Fintype, Fintype.card, Fintype.exists_ne_map_eq_of_card_lt]
  E2: [Finset.univ, Fintype.card_fin, Fintype.card_prod, Fintype.card_fun, Fintype.card_congr, Fintype.card_le_of_injective]
  E1: auto
families: []
requires: [V03.C03]
reads_with: ["MIL", "MSG"]
lean:
  - MathlibHandbook/V03/C04/Examples.lean
  - MathlibHandbook/V03/C04/Exercises.lean
  - MathlibHandbook/V03/C04/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The class Fintype and the card of a type

### Overview

Many types of mathematics are finite: `Bool`, `Fin n`, the products and the function types of finite types, the permutations of a finite type. A statement such as "a map from a set with five elements to a set with four elements is not injective" is about the type, not about a finset in it. The class `Fintype α` gives a finset `Finset.univ` that contains each element of `α`. With it, `Fintype.card α` is the number of elements, and the big operators of Chapter 6 can sum over the whole type. This section gives the class, the card of the common type constructions and the pigeonhole principle.

### Definitions

**Definition (Fintype).** A term of the class `Fintype α` has two fields: a finset `elems : Finset α` and a proof that each `x : α` is in it. The finset is `Finset.univ`, and `Finset.mem_univ x` is the proof.

**Definition (Card of a type).** `Fintype.card α` is `Finset.univ.card`. The value does not depend on the instance, because two instances have the same finset of all elements.

**Definition (Instances).** Mathlib has instances for `Bool`, `Fin n`, `Option α`, `α × β`, `α ⊕ β`, `α → β`, `Equiv.Perm α`, `Set α` and `Finset α` when the parts are finite. A subtype `{x // p x}` of a finite type with a decidable `p` is finite too.

### Theorems and proofs

**Theorem (Card of the constructions).** For finite types $\alpha$ and $\beta$, $|\alpha \times \beta| = |\alpha| \cdot |\beta|$, $|\alpha \oplus \beta| = |\alpha| + |\beta|$, $|\alpha \to \beta| = |\beta|^{|\alpha|}$ and $|\mathrm{Option}\ \alpha| = |\alpha| + 1$.

*Proof.* The finset of all pairs is the product of the two finsets of all elements, so the card of a product is the product of the cards. The other rules follow in the same way from the form of the finset of all elements. $\square$

**Theorem (Equivalent types).** If $\alpha \simeq \beta$, then $|\alpha| = |\beta|$.

*Proof.* The equivalence sends the finset of all elements of $\alpha$ to the finset of all elements of $\beta$ by an injective map. $\square$

**Theorem (Pigeonhole principle).** If $|\beta| < |\alpha|$ and $f : \alpha \to \beta$, then there are $x \ne y$ with $f(x) = f(y)$.

*Proof.* If $f$ were injective, the image of the finset of all elements of $\alpha$ would have $|\alpha|$ elements. It is a finset of $\beta$, so $|\alpha| \le |\beta|$, which is false. $\square$

::: mathlib
`Fintype` · `Mathlib.Data.Fintype.Defs`

The class of the finite types with a finset of all elements. It is data, so two instances can be different terms. A lemma with a `Fintype` hypothesis that comes from a different instance can need `convert` or `Subsingleton.elim`.

<?decl Fintype?>
:::

::: mathlib
`Fintype.card` · `Mathlib.Data.Fintype.Card`

The number of elements of a finite type. For a concrete type, `simp` with the `card` lemmas often computes it.

<?decl Fintype.card?>
:::

::: mathlib
`Fintype.exists_ne_map_eq_of_card_lt` · `Mathlib.Data.Fintype.Pigeonhole`

The pigeonhole principle for finite types. The last argument is the inequality of the cards.

<?decl Fintype.exists_ne_map_eq_of_card_lt?>
:::

### Examples

**Example (All elements).**

<?lean MathlibHandbook/V03/C04/Examples.lean#univ?>

**Example (The card of Fin n).**

<?lean MathlibHandbook/V03/C04/Examples.lean#card_fin?>

**Example (A product).**

<?lean MathlibHandbook/V03/C04/Examples.lean#card_prod?>

**Example (Functions).**

<?lean MathlibHandbook/V03/C04/Examples.lean#card_fun?>

**Example (Subsets).**

<?lean MathlibHandbook/V03/C04/Examples.lean#card_set?>

**Example (Pigeonhole).** Five pigeons in four holes.

<?lean MathlibHandbook/V03/C04/Examples.lean#pigeonhole?>

**Example (Check all cases).** In `Fin 4` the squares are $0, 1, 0, 1$, so no square is $2$.

<?lean MathlibHandbook/V03/C04/Examples.lean#decide?>

**Counterexample (A type with no instance).** The type `ℕ` has no `Fintype` instance, because no finset contains all natural numbers. The class `Infinite ℕ` of Chapter 5 states this.

### The library around it

`Fintype.card_perm` gives the number of permutations, $n!$. `Fintype.card_subtype` gives the card of a subtype as the card of a filter. `Fintype.card_finset` and `Fintype.card_set` give $2^n$ for the subsets. `Finset.card_univ` connects the card of the type with the card of the finset. For a type with no `Fintype` instance, the class `Finite` of Chapter 5 is a proposition, and `Nat.card` counts with no data. The instance `Fintype.ofFinset` makes an instance from a finset that contains each element.

### Exercises

1. (A) Give `Fintype.card (Fin 2 ⊕ Fin 3 → Bool)`.
2. (A) Explain why `Fintype.card` gives the same number for two different instances.
3. (B) Prove the pigeonhole principle for 13 people and 12 months of birth with `decide` or with `Fintype.exists_ne_map_eq_of_card_lt`.
4. (L) Prove that an injective map does not go to a smaller finite type. The solution is `card_le_of_injective_example`.
5. (L) Prove that equivalent finite types have the same card. The solution is `card_congr_example`.
6. (L) Prove that `Option α` has one more element than `α`. The solution is `card_option_example`.
7. (L) Prove that the card of `Finset.univ` is the card of the type. The solution is `card_univ_example`.

### Notes and history

The pigeonhole principle has the name "Schubfachprinzip" from Dirichlet, who used it in number theory in 1834. In Mathlib, the class `Fintype` is data, and the class `Finite` is a proposition. The two classes exist because a sum over a type needs a finset that a program can use, but a statement often needs only the fact that the type is finite. MSG shows how `decide` uses the `Fintype` instance to check a statement for all elements.

### Reference

<?reference?>
