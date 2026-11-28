---
title: Lexicographic orders, sums and order types
kind: api
modules:
  - Mathlib.Order.Lex
  - Mathlib.Order.PiLex
  - Mathlib.Order.Prod.Lex.Basic
  - Mathlib.Order.Prod.Lex.Hom
  - Mathlib.Order.Sigma
  - Mathlib.Order.Sigma.Lex
  - Mathlib.Order.PSigma
  - Mathlib.Order.Sum.Order
  - Mathlib.Order.Sum.Lattice
  - Mathlib.Order.Types.Defs
  - Mathlib.Order.Types.Arithmetic
explains:
  E2: [Pi.Lex.linearOrder, Pi.lex_desc, Prod.Lex.toLex_covBy_toLex_iff, Sigma.Lex.linearOrder, Sum.Lex.linearOrder, OrderIso.sumLexDualAntidistrib, WithBot.orderIsoPUnitSumLex, OrderType.type_le_type_iff, OrderType.type_lex_sum, OrderType.type_lex_prod]
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

## Lexicographic orders, sums and order types

### Overview

The first section of this chapter defines the lexicographic order on $\mathbb{N} \times \mathbb{N}$: compare the first coordinates, and compare the second coordinates only when the first ones are equal. The same idea orders functions on a well-ordered index set, dependent pairs and disjoint sums. This section describes these orders as Mathlib states them. Each of them lives on a type synonym, because the same type already carries another order: the product $\alpha \times \beta$ has the pointwise order, and so has the function type $\iota \to \beta$.

The disjoint sum has two natural orders. In the first one, the two parts are not comparable. In the second one, the lexicographic sum $\alpha \oplus_\ell \beta$, each element of $\alpha$ is below each element of $\beta$. The lexicographic sum and the lexicographic product are the addition and the multiplication of order types. The last part of the section describes the type `OrderType` of the linear orders up to isomorphism, with this arithmetic.

### The library around it

#### The type synonyms Lex and Colex

The module `Mathlib.Order.Lex` defines the type synonyms `Lex α` and `Colex α`. They are equal to $\alpha$ as types, but they carry no instances of $\alpha$. The equivalences `toLex : α ≃ Lex α` and `ofLex : Lex α ≃ α` move an element between the two types, and `toColex`, `ofColex` do the same for `Colex α`. The simp lemmas `toLex_ofLex`, `ofLex_toLex`, `toLex_inj` and `ofLex_inj` say that the maps are inverse bijections, and `Lex.forall` and `Lex.exists` turn a quantifier over `Lex α` into a quantifier over $\alpha$. The rule of the library is to write `toLex x` and not to use the definitional equality between $\alpha$ and `Lex α`. The lemmas are stated with the explicit maps, so a proof that skips them does not match the simp normal form.

#### Lexicographic products of two orders

The module `Mathlib.Order.Prod.Lex.Basic` orders `Lex (α × β)`, with the notation `α ×ₗ β`. The rule `Prod.Lex.le_iff` of the first section reads $x \le y \leftrightarrow x_1 < y_1 \lor (x_1 = y_1 \land x_2 \le y_2)$, and `Prod.Lex.lt_iff` is the strict form. In a partial order, the forms `Prod.Lex.le_iff'` and `Prod.Lex.lt_iff'` say $x_1 \le y_1$ and $(x_1 = y_1 \to x_2 \le y_2)$, which is often easier to use. The map `toLex` from the product order is monotone and strictly monotone, by `Prod.Lex.toLex_mono` and `Prod.Lex.toLex_strictMono`, and the module `Mathlib.Order.Prod.Lex.Hom` bundles it as the order homomorphism `Prod.Lex.toLexOrderHom`. The first projection is monotone, by `Prod.Lex.monotone_fst_ofLex`. The order is bounded when both factors are bounded (`Prod.Lex.boundedOrder`), and it has no maximum when the first factor has none (`Prod.Lex.noMaxOrder_of_left`).

The covering relation shows the shape of the order. The lemma `Prod.Lex.toLex_covBy_toLex_iff` says that $(a_1, b_1) \lessdot (a_2, b_2)$ if and only if $a_1 = a_2$ and $b_1 \lessdot b_2$, or $a_1 \lessdot a_2$, $b_1$ is maximal and $b_2$ is minimal. For the proof of the second case, let $a_1 \lessdot a_2$ and let $c$ be strictly between the two pairs. Its first coordinate is $a_1$ or $a_2$, since nothing lies strictly between them. If it is $a_1$, then $b_1 < c_2$, which contradicts the maximality of $b_1$. If it is $a_2$, then $c_2 < b_2$, which contradicts the minimality of $b_2$. So in $\mathbb{N} \times_\ell \mathbb{N}$ no element covers $(0, 5)$ except $(0, 6)$, and $(1, 0)$ covers nothing.

#### Lexicographic orders on functions

The module `Mathlib.Order.PiLex` orders functions. For a relation $r$ on the index set $\iota$ and relations $s$ on the values, `Pi.Lex r s x y` holds if there is an index $i$ with $x_j = y_j$ for each $j$ with $r\,j\,i$, and $s\,(x_i)\,(y_i)$. With $r = {<}$ and $s = {<}$ this is the strict lexicographic order: $x$ and $y$ agree below $i$, and $x_i < y_i$. The instance on `Lex (∀ i, β i)` uses this relation, and the notation `Πₗ i, β i` stands for that type.

The relation is a linear order when $\iota$ is a well-ordered linear order and each $\beta_i$ is a linear order: this is the instance `Pi.Lex.linearOrder`. For the proof of totality, take $x \ne y$. The set of the indices where $x$ and $y$ differ is nonempty, so it has a least element $i$, because $\iota$ is well-founded. Then $x$ and $y$ agree below $i$, and the linear order on $\beta_i$ compares $x_i$ and $y_i$. Without well-foundedness the set of differences need not have a least element, and two functions $\mathbb{Z} \to \{0, 1\}$ can be incomparable. The colexicographic order `Colex (∀ i, β i)` compares at the greatest index of difference and needs `WellFoundedGT ι`; its instance is `Pi.Colex.linearOrder`.

The pointwise order is finer than the lexicographic order: `Pi.toLex_strictMono` says that $x < y$ pointwise gives `toLex x < toLex y`, and `Pi.lex_lt_of_lt` is the form for a general well-founded relation. A change of one coordinate is easy to compare: `Pi.toLex_update_lt_self_iff` says that the update of $x$ at $i$ to the value $a$ is lexicographically smaller than $x$ if and only if $a < x_i$. The lemma `Pi.lex_desc` is the basis of sorting arguments. Let $i \le j$ and $f(j) < f(i)$. Then the function $f \circ (i\ j)$, with the values at $i$ and $j$ swapped, is lexicographically smaller than $f$. The proof takes the index $i$ in the definition: below $i$ the two functions agree, and at $i$ the new value $f(j)$ is smaller than $f(i)$. The twin `Pi.colex_asc` is the colexicographic form. The lemma `Pi.Lex.noMaxOrder'` says that there is no maximum when one factor has no maximum.

#### Dependent pairs

Let $\alpha_i$ be a family of orders indexed by $\iota$. The module `Mathlib.Order.Sigma` gives the type of the pairs $\langle i, a \rangle$ with $a \in \alpha_i$ two orders. The default order compares only pairs in the same fibre: `Sigma.le_def` says $\langle i, a \rangle \le \langle j, b \rangle$ if and only if $i = j$ and $a \le b$ after the transport along $i = j$, and `Sigma.mk_le_mk_iff` is the form with a common index. This is the disjoint union of the orders. The lexicographic order lives on the synonym written `Σₗ i, α i`. There `Sigma.Lex.le_def` says $\langle i, a \rangle \le \langle j, b \rangle$ if and only if $i < j$, or $i = j$ and $a \le b$. It is a linear order when $\iota$ and each $\alpha_i$ are linear orders (`Sigma.Lex.linearOrder`). The proof of totality compares the indices first and then compares the second entries when the indices are equal. The module also has `Sigma.Lex.boundedOrder`, `Sigma.Lex.noMaxOrder` and `Sigma.Lex.denselyOrdered`. The last one needs a dense index order and nonempty dense fibres. For the proof, take $\langle i, a \rangle < \langle j, b \rangle$. If $i = j$, density of $\alpha_i$ gives an element between $a$ and $b$. If $i < j$, density of $\iota$ gives $k$ with $i < k < j$, and each element of the nonempty fibre $\alpha_k$ lies between the two pairs.

The module `Mathlib.Order.Sigma.Lex` treats the relation of the lexicographic order of dependent pairs for general relations $r$ on $\iota$ and $s_i$ on $\alpha_i$. The lemma `Sigma.lex_iff` unfolds it, `Sigma.Lex.mono` says that it is monotone in $r$ and $s$, and `Sigma.lex_swap` reverses it. The module `Mathlib.Order.PSigma` gives the same orders for the pairs with a proposition as a component, with `PSigma.lex_iff` and `PSigma.Lex.linearOrder` and the notation `Σₗ' i, α i`.

#### Sums of two orders

The module `Mathlib.Order.Sum.Order` orders the sum $\alpha \oplus \beta$ in two ways. The default order is the disjoint sum: `Sum.le_def` says that two elements compare only when they lie in the same part, and `Sum.not_inl_le_inr` says that a left element is never below a right element. The lexicographic sum $\alpha \oplus_\ell \beta$, the synonym `Lex (α ⊕ β)` with the notation `α ⊕ₗ β`, puts all of $\alpha$ below all of $\beta$, by `Sum.Lex.le_def`. The maps `Sum.inlₗ` and `Sum.inrₗ` are the two inclusions into the lexicographic sum. The instance `Sum.Lex.linearOrder` makes it a linear order when both parts are linear orders: two elements of one part compare in that part, and a left element is below a right element. It is well-founded when both parts are (`Sum.Lex.instWellFoundedLTLex`), and it is bounded when $\alpha$ has a bottom and $\beta$ has a top (`Sum.Lex.boundedOrder`), with `Sum.Lex.inl_bot` and `Sum.Lex.inr_top`.

The module gives the order isomorphisms of the algebra of sums.

| Lean name | Statement |
|---|---|
| `OrderIso.sumComm` | $\alpha \oplus \beta \simeq_o \beta \oplus \alpha$ for the disjoint sum |
| `OrderIso.sumAssoc` | $(\alpha \oplus \beta) \oplus \gamma \simeq_o \alpha \oplus (\beta \oplus \gamma)$ |
| `OrderIso.sumLexAssoc` | $(\alpha \oplus_\ell \beta) \oplus_\ell \gamma \simeq_o \alpha \oplus_\ell (\beta \oplus_\ell \gamma)$ |
| `OrderIso.sumDualDistrib` | $(\alpha \oplus \beta)^{\mathrm{op}} \simeq_o \alpha^{\mathrm{op}} \oplus \beta^{\mathrm{op}}$ |
| `OrderIso.sumLexDualAntidistrib` | $(\alpha \oplus_\ell \beta)^{\mathrm{op}} \simeq_o \beta^{\mathrm{op}} \oplus_\ell \alpha^{\mathrm{op}}$ |
| `OrderIso.sumLexEmpty` | $\alpha \oplus_\ell \beta \simeq_o \alpha$ when $\beta$ is empty |
| `WithBot.orderIsoPUnitSumLex` | `WithBot α` is a one-point order followed by $\alpha$ |
| `WithTop.orderIsoSumLexPUnit` | `WithTop α` is $\alpha$ followed by a one-point order |

There is no commutativity for the lexicographic sum: $\mathbb{N} \oplus_\ell 1$ has a greatest element and $1 \oplus_\ell \mathbb{N}$ has none. The dual of a lexicographic sum reverses the two parts. For the proof of `OrderIso.sumLexDualAntidistrib`, the map is the swap of the two parts. In the dual of $\alpha \oplus_\ell \beta$, each element of $\beta$ is below each element of $\alpha$, and inside each part the order is reversed; this is the order of $\beta^{\mathrm{op}} \oplus_\ell \alpha^{\mathrm{op}}$. The isomorphism `WithBot.orderIsoPUnitSumLex` has the same kind of proof: the new bottom goes to the single point, and each element $a$ goes to the element $a$ of the right part.

The module `Mathlib.Order.Sum.Lattice` makes the lexicographic sum of two lattices a lattice (`Sum.Lex.instLattice`) and of two distributive lattices a distributive lattice (`Sum.Lex.instDistribLattice`). The supremum of a left and a right element is the right element. The inclusions are lattice homomorphisms, `Sum.Lex.inlLatticeHom` and `Sum.Lex.inrLatticeHom`, and `Sum.Lex.inl_sup` and `Sum.Lex.inr_inf` state this on elements.

#### Order types

The module `Mathlib.Order.Types.Defs` defines `OrderType`, the linear orders of one universe up to order isomorphism. The order type of a linear order $\alpha$ is `OrderType.type α`. Two linear orders have the same type if and only if they are isomorphic, by `OrderType.type_eq_type`, and `OrderIso.type_congr` gives one direction from an isomorphism. The induction principle `OrderType.inductionOn` reduces a statement about all order types to a statement about all linear orders, and `OrderType.ToType` picks a representative, with `OrderType.type_toType`. The constant `OrderType.omega0`, with the notation $\omega$, is the type of $\mathbb{N}$ (`OrderType.type_nat`). The function `OrderType.lift` moves an order type to a higher universe, and `OrderType.type_ulift` says that it is the type of `ULift α`.

The preorder `OrderType.instPreorder` compares order types by embeddings: `OrderType.type_le_type_iff` says $\mathrm{type}(\alpha) \le \mathrm{type}(\beta)$ if and only if there is an order embedding $\alpha \hookrightarrow_o \beta$. It is a preorder and not a partial order. The rationals and the rationals in $[0,1]$ embed into each other, but they are not isomorphic, since the second order has a greatest element. The bottom element is the type of the empty order, `OrderType.bot_eq_zero`, and `OrderType.type_eq_zero` and `OrderType.type_eq_one` characterize the types $0$ and $1$.

The module `Mathlib.Order.Types.Arithmetic` defines the sum and the product. The sum is the lexicographic sum, `OrderType.type_lex_sum`: $\mathrm{type}(\alpha) + \mathrm{type}(\beta) = \mathrm{type}(\alpha \oplus_\ell \beta)$. The product is the lexicographic product with the factors exchanged, `OrderType.type_lex_prod`: $\mathrm{type}(\alpha \times_\ell \beta) = \mathrm{type}(\beta) \cdot \mathrm{type}(\alpha)$. So $\mathrm{type}(\alpha) \cdot \mathrm{type}(\beta)$ is $\beta$ copies of $\alpha$, the convention of the ordinals. These operations are well defined because `OrderIso.sumLexCongr` and the matching product map turn two isomorphisms into an isomorphism of the sums. The instances `OrderType.instAddMonoid` and `OrderType.instMonoid` hold the laws, and `OrderType.instLeftDistribClass` says $a(b + c) = ab + ac$; associativity of the sum comes from `OrderIso.sumLexAssoc`. Neither operation is commutative: $1 + \omega = \omega$ but $\omega + 1 \ne \omega$. The constants `OrderType.eta` and `OrderType.theta`, with the notations $\eta$ and $\theta$, are the types of $\mathbb{Q}$ and $\mathbb{R}$. The function `OrderType.card` forgets the order, `OrderType.card_type` says that it gives the cardinal `Cardinal.mk α`, and `OrderType.card_mono` says that it is monotone.

#### Common errors

1. An element of `Lex (α × β)` is not a pair of the product order. A lemma about the product order does not apply to it; first write it as `toLex x` and use the lemmas `Prod.Lex.le_iff` and `Prod.Lex.lt_iff`.
2. The default order on a sum or on dependent pairs is the disjoint union, in which elements of different parts are incomparable. For the order that puts one part below the other, use `α ⊕ₗ β` or `Σₗ i, α i`.
3. The product of order types takes the factors in the reverse order: `OrderType.type_lex_prod` gives $\mathrm{type}(\beta) \cdot \mathrm{type}(\alpha)$ for `Lex (α × β)`.

### Exercises

1. (A) Use `Prod.Lex.toLex_covBy_toLex_iff` to find all the covering pairs in $\mathbb{N} \times_\ell \mathbb{Z}$ and in $\mathbb{Z} \times_\ell \mathbb{N}$.
2. (A) Show that $1 + \omega = \omega$ and $\omega + 1 \ne \omega$ as order types, with `OrderType.type_lex_sum`.
3. (B) Find two functions $\mathbb{Z} \to \{0, 1\}$ that the lexicographic relation `Pi.Lex (· < ·) (· < ·)` does not compare, and explain why `Pi.Lex.linearOrder` needs `WellFoundedLT ι`.
4. (B) Prove that the lexicographic sum of two well-founded orders is well-founded, as in `Sum.Lex.instWellFoundedLTLex`.
5. (B) Show that $2 \cdot \omega = \omega$ and $\omega \cdot 2 = \omega + \omega$ as order types, and conclude that the product of order types is not commutative.
6. (C) Use `Pi.lex_desc` to prove that each function $f : \mathrm{Fin}\,n \to \mathbb{N}$ can be sorted by a finite sequence of swaps of two values that are out of order. *Hint:* the lexicographic order on these functions is well-founded on the finite set of rearrangements of $f$.

### Reference

<?reference?>
