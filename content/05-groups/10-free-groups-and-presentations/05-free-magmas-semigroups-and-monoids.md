---
title: Free magmas, semigroups and monoids
kind: api
modules:
  - Mathlib.Algebra.Free
  - Mathlib.Algebra.FreeMonoid.Basic
  - Mathlib.Algebra.FreeMonoid.Count
  - Mathlib.Algebra.FreeMonoid.FreeSemigroup
  - Mathlib.Algebra.FreeMonoid.Symbols
explains:
  E2: [FreeMagmaAssocQuotientEquiv, FreeMonoid.lift_apply, FreeMonoid.hom_eq, FreeMonoid.toList_mul, FreeMonoid.of_injective, FreeMonoid.equivWithOneFreeSemigroup, FreeSemigroup.range_toFreeMonoid, FreeMonoid.count_apply, FreeMonoid.symbols_mul]
  E1: auto
families: []
requires: [V01, V03.C02, V05.C01, V05.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Free magmas, semigroups and monoids

### Overview

The free group of Section 2 is one member of a family of free objects. Each level of the hierarchy of Chapter 1 has its own free object on a type $\alpha$ of letters. The free magma has a multiplication and no axiom, so its elements are binary trees with leaves in $\alpha$. The free semigroup adds associativity, so its elements are the nonempty words. The free monoid adds an identity, so its elements are all the words, the empty word included. Each free object comes with the inclusion of the letters and a universal property: a map from $\alpha$ to a structure of the same kind extends in exactly one way to a homomorphism.

These modules hold the three constructions, the maps between them, and the first invariants of words: the length, the number of occurrences of a letter and the set of letters that occur. The free monoid is the most used of the three. It is the base of the presented monoids of Chapter 5 and of the free products of Section 1 of this chapter. The free semigroup and the free magma appear less often, but they show how the universal property changes when an axiom is added or removed.

### The library around it

#### The free magma

The module `Mathlib.Algebra.Free` defines `FreeMagma α` as an inductive type with two constructors. The constructor `FreeMagma.of` makes a leaf from a letter, and `FreeMagma.mul` joins two trees. The lemma `FreeMagma.mul_eq` says that `FreeMagma.mul` is the multiplication of the instance `FreeMagma.instMul`, so the simp normal form uses `*`. Two different bracketings of the same letters give different elements: $(a b) c \ne a (b c)$ in the free magma.

A magma has no identity, so the maps of the universal property are the multiplicative maps `α →ₙ* β` of Chapter 2, not monoid homomorphisms. The equivalence `FreeMagma.lift : (α → β) ≃ (FreeMagma α →ₙ* β)` holds for each type $\beta$ with a multiplication. The lemma `FreeMagma.lift_of` gives the value on a letter, and `FreeMagma.hom_ext` says that two multiplicative maps that agree on the letters are equal. The map `FreeMagma.map` applies a function to each leaf. The length `FreeMagma.length` counts the leaves, and `FreeMagma.length_pos` says that it is never $0$. The module also makes `FreeMagma` a monad and a traversable functor, with lemmas such as `FreeMagma.mul_bind`, for use in programs.

#### The associativity quotient

Each magma $M$ has a largest quotient that is a semigroup. The relation `Magma.AssocRel` identifies $x y z$ with $x (y z)$, and also the same pair after a left factor $w$. The quotient `Magma.AssocQuotient M` carries the instance `Magma.AssocQuotient.instSemigroup`, and the map `Magma.AssocQuotient.of` is multiplicative. Its universal property `Magma.AssocQuotient.lift` says that a multiplicative map from $M$ to a semigroup factors uniquely through the quotient. The lemma `Magma.AssocQuotient.quot_mk_assoc` is the defining identity in the quotient.

#### The free semigroup

The type `FreeSemigroup α` is a structure with a first letter `FreeSemigroup.head` and a list of further letters `FreeSemigroup.tail`. A nonempty word is thus the pair of its first letter and the rest. The product joins the two words: `FreeSemigroup.mk_mul_mk` gives $(x, L_1) (y, L_2) = (x, L_1 \mathbin{+\!\!+} y :: L_2)$. The lemmas `FreeSemigroup.head_mul` and `FreeSemigroup.tail_mul` are the two components of this identity, and `FreeSemigroup.ext` says that the two components fix the element. The length `FreeSemigroup.length` satisfies `FreeSemigroup.length_mul` and `FreeSemigroup.length_of`. The universal property `FreeSemigroup.lift` needs a semigroup as the target, and `FreeSemigroup.lift_mk_eq_foldl` computes the extended map as a left fold.

The map `FreeMagma.toFreeSemigroup` forgets the bracketing. It preserves the length, by `FreeMagma.length_toFreeSemigroup`. The equivalence `FreeMagmaAssocQuotientEquiv α` identifies the associativity quotient of the free magma with the free semigroup.

**Theorem (`FreeMagmaAssocQuotientEquiv`).** The semigroup `Magma.AssocQuotient (FreeMagma α)` is isomorphic to `FreeSemigroup α`.

*Proof sketch.* Both sides are free semigroups on $\alpha$. The quotient has the universal property for semigroups, because a multiplicative map from the quotient to a semigroup is the same as a multiplicative map from the free magma, which is the same as a function on $\alpha$. Two objects with the same universal property are isomorphic, and the isomorphism sends `of x` to `FreeSemigroup.of x`.

#### The free monoid

The module `Mathlib.Algebra.FreeMonoid.Basic` defines `FreeMonoid α` as a structure around a list. The constructor is `FreeMonoid.ofList`, and the field is `FreeMonoid.toList`. The equivalence `FreeMonoid.toListEquiv` identifies the two types. The identity is the empty list and the product is concatenation: `FreeMonoid.toList_one` and `FreeMonoid.toList_mul` say this. The letter $x$ is the word `FreeMonoid.of x`, with `FreeMonoid.toList_of`, and `FreeMonoid.of_injective` says that different letters give different words. The additive form is `FreeAddMonoid`, made by to_additive.

The universal property is the equivalence `FreeMonoid.lift : (α → M) ≃ (FreeMonoid α →* M)` for a monoid $M$. Its value is a product.

**Theorem (`FreeMonoid.lift_apply`).** For $f : \alpha \to M$ and a word $l$, $\operatorname{lift}(f)(l) = \prod_{x \in l} f(x)$, the product of the list `List.map f l.toList` in its order.

*Proof.* The map $l \mapsto (\text{map } f\ l).\text{prod}$ sends the empty list to $1$, and it sends a concatenation to the product of the two values because the product of a concatenation of lists is the product of the two products. So it is a monoid homomorphism, and this is the definition of `FreeMonoid.lift`.

**Theorem (`FreeMonoid.hom_eq`).** Two monoid homomorphisms $f, g$ from `FreeMonoid α` that agree on each `FreeMonoid.of x` are equal.

*Proof.* Use induction on the word with `FreeMonoid.inductionOn'`. Both maps send $1$ to $1$. If they agree on $w$, then $f(\operatorname{of} x \cdot w) = f(\operatorname{of} x) f(w) = g(\operatorname{of} x) g(w) = g(\operatorname{of} x \cdot w)$.

The recursors `FreeMonoid.mulRecOn` and `FreeMonoid.mulCasesOn` split a word into its first letter and the rest. The induction principle `FreeMonoid.inductionOn` uses $1$, the letters and products. The map `FreeMonoid.map` applies a function to each letter, with `FreeMonoid.map_comp` and `FreeMonoid.map_id`, and `FreeMonoid.freeMonoidCongr` turns an equivalence of letters into an isomorphism of free monoids. The lemma `FreeMonoid.map_surjective` says that `FreeMonoid.map f` is surjective if and only if $f$ is surjective. A function `α → β → β` gives an action of the free monoid on $\beta$, by `FreeMonoid.mkMulAction`, and `FreeMonoid.smul_def` computes it as a right fold.

The length of a word $a$ is the length of its list, `a.toList.length`. The library measures the length through the list, so the lemmas about lists apply after a rewrite with `FreeMonoid.toList_mul`.

**Theorem (`FreeMonoid.toList_mul`).** The list of $a b$ is the concatenation of the lists of $a$ and $b$. So the length of $a b$ is the sum of the lengths.

*Proof.* The product of the free monoid is defined as the concatenation of the lists, so the first claim holds by definition. The second claim is the length of a concatenation of lists.

**Theorem (`FreeMonoid.of_injective`).** If `FreeMonoid.of x = FreeMonoid.of y`, then $x = y$.

*Proof.* Apply `FreeMonoid.toList`. The lists $[x]$ and $[y]$ are equal, so their first entries are equal.

The length gives the facts that a free monoid is cancellative, by `FreeMonoid.instCancelMonoid`, and that its only unit is $1$, by `FreeMonoid.instUniqueUnits`: if $a b = 1$, then the two lengths add up to $0$, so both words are empty. The lemmas `FreeMonoid.of_ne_one` and `FreeMonoid.one_ne_of` say that a letter is not the empty word. A letter occurs in a word $a$ when it is a member of `a.toList`.

#### Free semigroups inside free monoids

The module `Mathlib.Algebra.FreeMonoid.FreeSemigroup` compares the two free objects. The map `FreeSemigroup.toFreeMonoid` sends a nonempty word to the same word in the free monoid. It is injective, by `FreeSemigroup.toFreeMonoid_injective`.

**Theorem (`FreeSemigroup.range_toFreeMonoid`).** The range of `FreeSemigroup.toFreeMonoid` is the set of words different from $1$.

*Proof.* A word $(x, L)$ goes to the list $x :: L$, which is not empty. Conversely, a nonempty list $x :: L$ is the image of $(x, L)$.

**Theorem (`FreeMonoid.equivWithOneFreeSemigroup`).** The free monoid on $\alpha$ is isomorphic to the free semigroup on $\alpha$ with an identity adjoined, `WithOne (FreeSemigroup α)`.

*Proof sketch.* The map in one direction is `FreeMonoid.lift` of the letters, and the map back is `WithOne.lift` of `FreeSemigroup.toFreeMonoid`. Both composites fix the letters, so they are the identity by the uniqueness parts of the two universal properties.

#### Counting letters

The module `Mathlib.Algebra.FreeMonoid.Count` counts occurrences. For a decidable predicate $p$ on the letters, `FreeMonoid.countP p` is a monoid homomorphism to `Multiplicative ℕ`, and `FreeMonoid.count x` counts the letter $x$. The target is multiplicative because a monoid homomorphism must take products to products, and the count of a concatenation is a sum.

**Theorem (`FreeMonoid.count_apply`).** `FreeMonoid.count x l` is `Multiplicative.ofAdd (List.count x l.toList)`.

*Proof.* Both sides are monoid homomorphisms in $l$, and they agree on each letter, so `FreeMonoid.hom_eq` applies.

The function `FreeMonoid.countP'` gives the same number in `ℕ` itself, with `FreeMonoid.countP'_mul` for products.

The module `Mathlib.Algebra.FreeMonoid.Symbols` gives the finite set of letters of a word, `FreeMonoid.symbols`. By `FreeMonoid.mem_symbols` a letter is in this set if and only if it occurs in the word.

**Theorem (`FreeMonoid.symbols_mul`).** `(a * b).symbols = a.symbols ∪ b.symbols`.

*Proof.* By `FreeMonoid.mem_symbols`, a letter is in the left side if and only if it occurs in the list of $a b$. By `FreeMonoid.toList_mul`, this list is the concatenation of the two lists, so the letter occurs in $a$ or in $b$.

The lemmas `FreeMonoid.symbols_one` and `FreeMonoid.symbols_of` give the empty set and a singleton.

#### Common errors

1. `FreeMonoid α` is a structure, not the type `List α`. A goal can show `{ toList := l }` where a list is expected. Use `FreeMonoid.toList_ofList`, `FreeMonoid.ofList_toList` and `FreeMonoid.toList_mul` to move between the two sides, and write `*`, not `++`, in the free monoid.
2. The universal properties need the right structure on the target. `FreeMagma.lift` needs only a multiplication, `FreeSemigroup.lift` needs a semigroup, and `FreeMonoid.lift` needs a monoid. The first two give maps `→ₙ*`, which do not preserve an identity, because the source has none.
3. `FreeMonoid.count x l` is an element of `Multiplicative ℕ`, not of `ℕ`. To compute with it, apply `Multiplicative.toAdd`, or use `FreeMonoid.countP'`, which takes values in `ℕ`.

### Exercises

1. (A) For letters $a, b$, compute the list of `FreeMonoid.of a * FreeMonoid.of b * FreeMonoid.of a` with `FreeMonoid.toList_mul` and `FreeMonoid.toList_of`, and give its length.
2. (A) Show that in `FreeMonoid α`, $a b = 1$ implies $a = 1$ and $b = 1$. Use the lengths of the lists.
3. (B) Show that if $\alpha$ has two different letters $a \ne b$, then `FreeMonoid α` is not commutative. Compare the lists of $\operatorname{of}(a)\operatorname{of}(b)$ and $\operatorname{of}(b)\operatorname{of}(a)$.
4. (B) Show that `FreeMonoid.map f` is injective if and only if $f$ is injective.
5. (B) Let $\alpha$ have one element. Show that the number of elements of `FreeMagma α` of length $n + 1$ is the Catalan number $C_n = \frac{1}{n+1}\binom{2n}{n}$.
6. (C) Let $u, v$ be words of `FreeMonoid α` with $u v = v u$. Show that there are a word $w$ and natural numbers $i, j$ with $u = w^i$ and $v = w^j$. Use induction on the sum of the lengths.

### Reference

<?reference?>
