---
title: Symmetric powers and unordered pairs
kind: api
modules:
  - Mathlib.Data.Multiset.Sym
  - Mathlib.Data.Sym.Basic
  - Mathlib.Data.Sym.Card
  - Mathlib.Data.Sym.NatCard
  - Mathlib.Data.Sym.Sym2
  - Mathlib.Data.Sym.Sym2.Card
  - Mathlib.Data.Sym.Sym2.Finsupp
  - Mathlib.Data.Sym.Sym2.Init
  - Mathlib.Data.Sym.Sym2.Order
explains:
  E2: [Sym, Sym2, Sym.cons_swap, Sym.card_sym_eq_choose, Sym2.mk_eq_mk_iff, Sym2.mem_iff, Sym2.lift, Sym2.mk_isDiag_iff, Sym2.card, Multiset.card_sym2]
  E1: auto
families: []
requires: [V01.C02, V03.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Symmetric powers and unordered pairs

### Overview

A multiset of card $n$ is an unordered tuple of $n$ elements: the tuple $(a_1, \dots, a_n)$ up to permutation of its entries. The type of these is the $n$th symmetric power `Sym α n`. For $n = 2$ the library has a separate type, `Sym2 α`, the type of unordered pairs $\{a, b\}$ with $a = b$ allowed. The edges of a simple graph, the monomials of degree $2$ and the entries of a symmetric matrix above the diagonal are all indexed by unordered pairs, so `Sym2` is the more frequent of the two.

The modules of this section give the two types, the membership and the equality rules, the recursion on unordered pairs, the diagonal, the counts of both types for a finite type (the number of multisets of card $k$ from $n$ elements is $\binom{n + k - 1}{k}$), and the multiset of unordered pairs of a multiset.

### The library around it

#### The symmetric power

The type `Sym α n` is the subtype of multisets of card $n$. A term is built by `Sym.mk m h` from a multiset $m$ and a proof $h$ that $|m| = n$, and the coercion `Sym.toMultiset` forgets the proof. Two terms are equal if and only if their multisets are equal (`Sym.ext`, `Sym.coe_inj`), and membership is membership in the multiset (`Sym.mem_coe`, `Sym.mem_mk`).

The type has the same constructors as a list of fixed length: `Sym.nil` of card $0$ and `a ::ₛ s`, the term `Sym.cons a s` of card $n + 1$. The rules are `Sym.coe_cons`, `Sym.mem_cons` ($x \in a ::_s s \iff x = a \lor x \in s$) and the commutativity that makes it a symmetric power:

$$a ::_s b ::_s s = b ::_s a ::_s s.$$

This is `Sym.cons_swap`. Each term of card $n + 1$ has this form (`Sym.exists_eq_cons_of_succ`), and each member can be taken out: `Sym.exists_cons_of_mem` and `Sym.erase` with `Sym.cons_erase`. The term `Sym.replicate n a` has $n$ copies of $a$, with `Sym.mem_replicate` and `Sym.val_replicate`. The map `Sym.map f` applies $f$ to each entry and keeps the card (`Sym.mem_map`, `Sym.map_injective`). Two terms can be joined: `Sym.append` gives a term of card $n + n'$, with `Sym.coe_append`.

The type also has the form of a quotient of vectors: `Sym.ofVector` sends a vector of length $n$ to its class, `Sym.sound` says that permuted vectors give the same class, and `Sym.symEquivSym'` is the equivalence with `Sym.Sym'`, the quotient of `List.Vector α n` by permutation. The small cases are `Sym.oneEquiv` ($\alpha \simeq$ `Sym α 1`) and the unique term of `Sym α 0` (`Sym.uniqueZero`).

#### Counting the symmetric power

For a finite type with $n$ elements, the terms of `Sym α k` are the ways to choose $k$ elements with repetition and without order. Their number is the stars and bars count:

$$|\operatorname{Sym}(\alpha, k)| = \binom{n + k - 1}{k}.$$

This is `Sym.card_sym_eq_choose`, and `Sym.card_sym_eq_multichoose` gives the same count as `Nat.multichoose n k`. The proof goes by `Sym.card_sym_fin_eq_multichoose` on `Fin n`, with the split of `Sym (Fin (n + 1)) k` into the terms that contain $0$ and those that do not. The module `Mathlib.Data.Sym.NatCard` gives the forms with `Nat.card` for any type, `Sym.natCard_sym_eq_choose` and `Sym.natCard_sym_eq_multichoose`, and the instance `Sym.instInfiniteOfNeZeroNat`: for an infinite type and $k \ne 0$ the symmetric power is infinite.

#### Unordered pairs

The type `Sym2 α` is the quotient of $\alpha \times \alpha$ by the relation `Sym2.Rel` that relates $(a, b)$ to itself and to $(b, a)$. The class of $(a, b)$ is written `s(a, b)`, through `Sym2.mk`. Equality of two classes has two cases:

$$s(p_1, p_2) = s(q_1, q_2) \iff p = q \text{ or } p = \operatorname{swap}(q).$$

This is `Sym2.mk_eq_mk_iff`, and `Sym2.eq` and `Sym2.rel_iff` give the same with the relation. Membership has the expected form:

$$a \in s(b, c) \iff a = b \text{ or } a = c.$$

This is `Sym2.mem_iff`, with `Sym2.mem_mk_left` and `Sym2.mem_mk_right`. An unordered pair is determined by its members (`Sym2.ext`), and two distinct members determine it: `Sym2.mem_and_mem_iff` gives $x \in z \land y \in z \iff z = s(x, y)$ for $x \ne y$. For $a \in z$, `Sym2.Mem.other` gives the other member, with `Sym2.other_spec` saying that $z = s(a, \operatorname{other})$. The instance `Sym2.instSetLike` makes an unordered pair a set of one or two elements, and `Sym2.instPartialOrder` orders the pairs by the inclusion of these sets.

A proof about all unordered pairs goes by `Sym2.ind` or `Sym2.inductionOn`: prove the statement for each `s(x, y)`. The quantifier rules `Sym2.forall` and `Sym2.exists` do the same in one step. A function on unordered pairs comes from a symmetric function of two arguments:

$$\operatorname{lift} : \{f : \alpha \to \alpha \to \beta \mid \forall a\, b,\ f(a, b) = f(b, a)\} \simeq (\operatorname{Sym2}(\alpha) \to \beta).$$

This is `Sym2.lift`, with `Sym2.lift_mk` for the value at `s(a, b)`. Examples are `Sym2.map f` (with `Sym2.map_mk`), and `Sym2.mul` and `Sym2.add`, the product and the sum of the two members in a commutative magma (`Sym2.mul_mk`).

The module `Mathlib.Data.Sym.Sym2.Init` declares the rule set `Sym2` for the `aesop` tactic. The module `Mathlib.Data.Sym.Sym2.Order` is deprecated and only imports `Mathlib.Order.Sym2`, which gives `Sym2.sup`, `Sym2.inf` and the equivalence `Sym2.sortEquiv` of `Sym2 α` with the ordered pairs $(a, b)$ with $a \le b$ in a linear order.

#### The diagonal and symmetric relations

An unordered pair is diagonal when its two members are equal. The predicate is `Sym2.IsDiag`, and

$$\operatorname{IsDiag}(s(x, y)) \iff x = y.$$

This is `Sym2.mk_isDiag_iff`. The diagonal map `Sym2.diag` sends $a$ to `s(a, a)`, it is injective (`Sym2.diag_injective`), and its range is the set `Sym2.diagSet` (`Sym2.range_diag`). A symmetric relation $r$ gives the set `Sym2.fromRel` of pairs `s(a, b)` with $r(a, b)$ (`Sym2.fromRel_prop`), and `Sym2.ToRel` goes back. The edge set of a simple graph is `Sym2.fromRel` of its adjacency relation, which is irreflexive, so it contains no diagonal pair (`Sym2.fromRel_irrefl`).

The equivalences `Sym2.equivSym` and `Sym2.equivMultiset` connect `Sym2 α` with `Sym α 2` and with the multisets of card $2$, and `Sym2.toMultiset` gives the multiset of a pair, of card $2$ (`Sym2.card_toMultiset`).

#### Counting unordered pairs

For a finite type with $n$ elements there are $\binom{n + 1}{2}$ unordered pairs: $n$ diagonal pairs and $\binom{n}{2}$ others.

$$|\operatorname{Sym2}(\alpha)| = \binom{n + 1}{2}.$$

This is `Sym2.card`, and `Sym2.card_subtype_diag` and `Sym2.card_subtype_not_diag` give the two parts. The forms for `Nat.card` are `Sym2.natCard`, `Sym2.natCard_subtype_diag` and `Sym2.natCard_subtype_not_diag`. The module `Mathlib.Data.Sym.Sym2.Card` gives the finiteness: `Sym2.finite_sym2_iff` says that `Sym2 α` is finite if and only if $\alpha$ is, and `Set.finite_sym2_iff` gives the same for the set `Set.sym2 s` of pairs with both members in $s$. For any type, the quotient map has fibers of one or two elements (`Sym2.ncard_mk_fiber_of_isDiag`, `Sym2.ncard_mk_fiber_of_not_isDiag`), and `Sym2.two_mul_cardinalMk_sym2` gives the count as a cardinal identity.

#### Pairs from a multiset

The module `Mathlib.Data.Multiset.Sym` gives `Multiset.sym2 m`, the multiset of the unordered pairs of members of $m$, with repetition allowed. It comes from the list form by passing to the quotient. The rules are `Multiset.mem_sym2_iff` ($z \in m.\operatorname{sym2} \iff \forall y \in z,\ y \in m$) and `Multiset.mk_mem_sym2_iff`, and the card is the count of the last subsection:

$$|\operatorname{sym2}(m)| = \binom{|m| + 1}{2}.$$

This is `Multiset.card_sym2`. The operation is monotone (`Multiset.sym2_mono`), commutes with maps (`Multiset.sym2_map`) and keeps the predicate Nodup (`Multiset.Nodup.sym2`). The finset `Finset.sym2` of Chapter 3 is built on it.

The module `Mathlib.Data.Sym.Sym2.Finsupp` gives the product on pairs of a finitely supported function: `Finsupp.sym2Mul f` sends `s(a, b)` to $f(a) f(b)$ (`Finsupp.sym2Mul_apply_mk`), and its support is in the pairs of members of the support of $f$ (`Finsupp.support_sym2Mul_subset`).

#### Common errors

1. A learner proves `s(a, b) = s(c, d) → a = c` with no other case. It fails for `s(1, 2) = s(2, 1)`. Use `Sym2.mk_eq_mk_iff` and handle the swapped case.
2. A learner counts the pairs of a finite type as $\binom{n}{2}$. That count is only for the pairs off the diagonal. `Sym2 α` also has the $n$ pairs `s(a, a)`, so the total is $\binom{n+1}{2}$.
3. A learner defines a function on `Sym2 α` by pattern matching on `s(a, b)` and gets an error. A function on a quotient needs a proof that it respects the relation. Use `Sym2.lift` with a proof of symmetry.

### Exercises

1. (A) List all terms of `Sym (Fin 3) 2` as multisets, and check `Sym.card_sym_eq_choose`.
2. (A) Use `Sym2.mem_iff` to decide whether $3 \in s(1, 3)$ and whether $2 \in s(1, 3)$.
3. (B) Define the function $s(a, b) \mapsto |a - b|$ on `Sym2 ℤ` with `Sym2.lift`, and give the proof of symmetry.
4. (B) Prove `Sym2.card` for a type with three elements by a list of the diagonal and the other pairs.
5. (B) Prove that $z \in \operatorname{Sym2}(\alpha)$ is diagonal if and only if it has exactly one member, with `Sym2.mk_isDiag_iff` and `Sym2.ind`.
6. (C) Prove `Multiset.card_sym2` by `Multiset.induction_on`, with `Multiset.sym2_cons` and the identity $\binom{m + 2}{2} = \binom{m + 1}{2} + m + 1$.

### Reference

<?reference?>
