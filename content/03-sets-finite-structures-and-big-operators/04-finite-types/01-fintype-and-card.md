---
title: The class Fintype and the card of a type
kind: theory
modules:
  - Mathlib.Data.Fintype.Card
  - Mathlib.Data.Fintype.Defs
  - Mathlib.Data.Fintype.Sum
  - Mathlib.Data.Fintype.Option
  - Mathlib.Data.Fintype.Prod
  - Mathlib.Data.Fintype.Pigeonhole
  - Mathlib.Data.FinEnum
  - Mathlib.Data.FinEnum.Option
explains:
  E3: [Fintype, Fintype.card, Fintype.exists_ne_map_eq_of_card_lt]
  E2: [Finset.univ, Fintype.card_fin, Fintype.card_prod, Fintype.card_fun, Fintype.card_congr, Fintype.card_le_of_injective, Fintype.card_sum, Fintype.card_option, Fintype.card_bool, Finset.card_univ, Fintype.subsingleton, Fintype.card_set]
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

Many types of mathematics are finite: the truth values, the residues modulo $n$, the products and the function types of finite types, the permutations of a finite set. A statement such as "a map from a set with five elements to a set with four elements is not injective" is about a whole type, not about a finset inside a type. Chapter 3 counted finsets. This section counts types.

The tool is the class `Fintype α`. An instance of it is a finset `Finset.univ` that contains each element of `α`. With this finset, `Fintype.card α` is the number of elements of `α`, and the sums of Chapter 6 can run over the whole type. The section gives the class, proves that the card does not depend on the instance, computes the card of the sum, the product, the option type and the function type, proves that equivalent types have the same card, and proves the pigeonhole principle. After the section the reader can compute the card of a type that is built from smaller finite types, and can use the pigeonhole principle in a proof.

### Definitions

**Definition (Finite type).** A *finite type structure* on a type $\alpha$ is a finite set $U \subseteq \alpha$ such that each $x \in \alpha$ is in $U$. So $U$ is all of $\alpha$, but $U$ is given as a finset: a list of the elements with no repetition, up to order.

The condition "each $x$ is in $U$" forces $U = \alpha$ as a set. So the content of the structure is not the set $U$ but the fact that $U$ is given as a finset. In mathematics on paper this difference is invisible. In a library that computes it matters, because a finset is data that a program can walk through.

::: mathlib
`Fintype` · `Mathlib.Data.Fintype.Defs`

The class has two fields: `elems : Finset α` and `complete : ∀ x, x ∈ elems`. The finset is `Finset.univ`, and `Finset.mem_univ x` is the proof that `x` is in it. The class is data, not a proposition, so two instances are two terms. They are equal, by `Fintype.subsingleton`, but they are not always equal by definition. A lemma that was stated with one instance can fail to apply to a goal with another instance, and then `convert` or `Subsingleton.elim` closes the gap.

<?decl Fintype?>
:::

**Definition (Card of a finite type).** For a finite type $\alpha$ with the structure $U$, the *card* of $\alpha$ is $|\alpha| = |U|$, the number of elements of the finset $U$.

::: mathlib
`Fintype.card` · `Mathlib.Data.Fintype.Card`

`Fintype.card α` is defined as `Finset.univ.card`, and `Finset.card_univ` states this. In the source the notation `‖α‖` sometimes stands for it inside a proof. For a concrete type, `simp` with the lemmas `Fintype.card_fin`, `Fintype.card_bool`, `Fintype.card_prod` and the others computes the number.

<?decl Fintype.card?>
:::

**Definition (The standard finite types).** The type $\mathrm{Fin}\ n$ has the elements $0, 1, \ldots, n - 1$. The type $\mathrm{Bool}$ has the two elements true and false. For types $\alpha$ and $\beta$, the product $\alpha \times \beta$ has the pairs $(a, b)$, the sum $\alpha \oplus \beta$ has a copy $\mathrm{inl}\ a$ of each $a \in \alpha$ and a copy $\mathrm{inr}\ b$ of each $b \in \beta$, the option type $\mathrm{Option}\ \alpha$ has a new element $\mathrm{none}$ and a copy $\mathrm{some}\ a$ of each $a$, and $\alpha \to \beta$ has the functions from $\alpha$ to $\beta$.

The sum $\alpha \oplus \beta$ is a disjoint union. Even when $\alpha = \beta$, the two copies $\mathrm{inl}\ a$ and $\mathrm{inr}\ a$ are different. This is the reason the card of a sum is always the sum of the cards, with no correction term.

::: mathlib
`Finset.univ` · `Mathlib.Data.Fintype.Defs`

Mathlib has instances of `Fintype` for `Bool`, `Fin n`, `Option α`, `α × β`, `α ⊕ β`, `α → β` (with `DecidableEq α`), `Equiv.Perm α`, `Set α` and `Finset α`, when the parts have instances. A subtype `{x // p x}` of a finite type is finite when `p` is decidable. Instance search builds the instance of a composite type from the instances of its parts, so the reader seldom writes an instance by hand. `Finset.univ` of the composite type is then the finset that these instances build, for example `univ ×ˢ univ` for a product.

<?decl Finset.univ?>
:::

### Theorems and proofs

**Theorem (The card does not depend on the structure).** Let $U$ and $V$ be two finite type structures on $\alpha$. Then $U = V$, and so $|U| = |V|$.

*Proof.* Two finsets are equal when they have the same elements. Each $x \in \alpha$ is in $U$, and each $x \in \alpha$ is in $V$. So $x \in U$ if and only if $x \in V$ for every $x$, and $U = V$. $\square$

::: mathlib
`Fintype.subsingleton` · `Mathlib.Data.Fintype.Defs`

This is the statement `Subsingleton (Fintype α)`: any two instances are equal. The proof in Mathlib is the proof above, with `Finset.ext`. The consequence for the user is that `Fintype.card α` is the same number for every instance. Two different instances may still be different terms in a goal, and `simp` sees them as different until the lemma is applied.

<?decl Fintype.subsingleton?>
:::

**Theorem (Card of a product).** For finite types $\alpha$ and $\beta$, $|\alpha \times \beta| = |\alpha| \cdot |\beta|$.

*Proof.* Let $U$ be the finset of all elements of $\alpha$ and $V$ that of $\beta$. The finset of all pairs is $U \times V$. For each $a \in U$, the pairs with first coordinate $a$ form the set $\{a\} \times V$, which has $|V|$ elements, since $b \mapsto (a, b)$ is injective. The sets $\{a\} \times V$ for different $a$ are disjoint, and their union is $U \times V$. So $|U \times V|$ is a sum of $|U|$ terms, each equal to $|V|$, and this sum is $|U| \cdot |V|$. $\square$

**Theorem (Card of a sum and of an option type).** For finite types $\alpha$ and $\beta$, $|\alpha \oplus \beta| = |\alpha| + |\beta|$ and $|\mathrm{Option}\ \alpha| = |\alpha| + 1$.

*Proof.* The finset of all elements of $\alpha \oplus \beta$ is the union of the image of $U$ under $\mathrm{inl}$ and the image of $V$ under $\mathrm{inr}$. The map $\mathrm{inl}$ is injective, so its image has $|U|$ elements. In the same way the second image has $|V|$ elements. No element is both $\mathrm{inl}\ a$ and $\mathrm{inr}\ b$, so the two images are disjoint. The card of a disjoint union is the sum of the cards, which gives $|\alpha| + |\beta|$. The type $\mathrm{Option}\ \alpha$ is the union of the one element set $\{\mathrm{none}\}$ and the image of $U$ under the injective map $\mathrm{some}$, and these are disjoint. So its card is $1 + |\alpha|$. $\square$

::: mathlib
`Fintype.card_sum` · `Mathlib.Data.Fintype.Sum`

The rules for the constructions are `Fintype.card_prod`, `Fintype.card_sum`, `Fintype.card_option`, `Fintype.card_bool` and `Fintype.card_fin`. They are `simp` lemmas, so a goal such as `Fintype.card (Bool × Fin 3 ⊕ Fin 2) = 8` closes by `simp`. The proofs in Mathlib follow the proofs above: the finset `univ` of a sum is a disjoint union of two maps, and `Finset.card_disjUnion` and `Finset.card_map` give the count.

<?decl Fintype.card_sum?>
:::

**Theorem (Equivalent types).** Let $e : \alpha \to \beta$ be a bijection of finite types. Then $|\alpha| = |\beta|$.

*Proof.* Let $U$ be the finset of all elements of $\alpha$. The image $e(U)$ is a finset of $\beta$. The map $e$ is injective, so $|e(U)| = |U|$. The map $e$ is surjective, so each $b \in \beta$ is $e(a)$ for an $a \in U$, and so $e(U)$ contains each element of $\beta$. By the first theorem, $e(U)$ is the finset of all elements of $\beta$. So $|\beta| = |e(U)| = |U| = |\alpha|$. $\square$

The converse holds too: two finite types with the same card are equivalent. For $|\alpha| = n$, list the elements of $U$ as $a_0, \ldots, a_{n-1}$ and send $i \in \mathrm{Fin}\ n$ to $a_i$. This gives $\alpha \simeq \mathrm{Fin}\ n$, and two types equivalent to $\mathrm{Fin}\ n$ are equivalent to each other. Mathlib states this as `Fintype.card_eq`. The list of the elements is chosen, so the equivalence is not canonical, and Mathlib gives it as `Fintype.equivFin`, a noncomputable definition.

::: mathlib
`Fintype.card_congr` · `Mathlib.Data.Fintype.Card`

The input is an equivalence `α ≃ β`, a bundled bijection with its inverse. This is the main tool to count a type: find an equivalence with a type whose card is known, then apply `Fintype.card_congr`. The proof of the function rule below uses it in this way.

<?decl Fintype.card_congr?>
:::

**Theorem (Card of a function type).** For finite types $\alpha$ and $\beta$, $|\alpha \to \beta| = |\beta|^{|\alpha|}$.

*Proof.* By the theorem on equivalent types, it is enough to prove the rule for $\alpha = \mathrm{Fin}\ n$, since $\alpha \simeq \mathrm{Fin}\ |\alpha|$, and then $(\alpha \to \beta) \simeq (\mathrm{Fin}\ |\alpha| \to \beta)$ by composition with the equivalence. Use induction on $n$. For $n = 0$ there is exactly one function from the empty type to $\beta$, and $|\beta|^0 = 1$. For the step, a function $f : \mathrm{Fin}\ (n+1) \to \beta$ is determined by its value $f(0)$ and the function $i \mapsto f(i + 1)$ on $\mathrm{Fin}\ n$. Conversely, each pair $(b, g)$ with $b \in \beta$ and $g : \mathrm{Fin}\ n \to \beta$ comes from exactly one $f$, the function with $f(0) = b$ and $f(i+1) = g(i)$. So $(\mathrm{Fin}\ (n+1) \to \beta) \simeq \beta \times (\mathrm{Fin}\ n \to \beta)$. By the product rule and the induction hypothesis, the card is $|\beta| \cdot |\beta|^n = |\beta|^{n+1}$. $\square$

**Theorem (Card of the subsets).** For a finite type $\alpha$, the type $\mathrm{Set}\ \alpha$ has $2^{|\alpha|}$ elements.

*Proof.* Send a subset $S$ to its indicator function $\chi_S : \alpha \to \mathrm{Bool}$, with $\chi_S(x) = \mathrm{true}$ if $x \in S$ and $\mathrm{false}$ if not. The inverse sends $g$ to $\{x : g(x) = \mathrm{true}\}$. So $\mathrm{Set}\ \alpha \simeq (\alpha \to \mathrm{Bool})$, and the function rule gives $2^{|\alpha|}$. $\square$

::: mathlib
`Fintype.card_fun` · `Mathlib.Data.Fintype.BigOperators`

The rule needs `DecidableEq α`, because the instance `Fintype (α → β)` builds each function as a table and must compare the arguments. It is a special case of `Fintype.card_pi` for dependent functions, whose card is a product $\prod_i |\beta_i|$. The rule for the subsets is `Fintype.card_set`, and `Fintype.card_finset` is the same rule for `Finset α`.

<?decl Fintype.card_fun?>
:::

**Theorem (Injective maps).** If $f : \alpha \to \beta$ is injective and $\alpha$, $\beta$ are finite, then $|\alpha| \le |\beta|$.

*Proof.* Let $U$ and $V$ be the finsets of all elements. Since $f$ is injective, the image $f(U)$ has $|U|$ elements. The image is a subset of $V$, and a subset of a finset has a card at most the card of the finset (Chapter 3). So $|\alpha| = |f(U)| \le |V| = |\beta|$. $\square$

**Theorem (Pigeonhole principle).** Let $\alpha$ and $\beta$ be finite types with $|\beta| < |\alpha|$, and let $f : \alpha \to \beta$. Then there are $x \ne y$ in $\alpha$ with $f(x) = f(y)$.

*Proof.* Assume, for a contradiction, that $f(x) = f(y)$ implies $x = y$ for all $x$ and $y$. Then $f$ is injective, and the theorem on injective maps gives $|\alpha| \le |\beta|$. This contradicts $|\beta| < |\alpha|$. So there are $x$ and $y$ with $f(x) = f(y)$ and $x \ne y$. $\square$

The proof is by contradiction, and it does not say which two elements collide. For a small type the pair can be found by search, and `decide` does this search. Section 2 proves a stronger form: some value of $f$ has more than $k$ preimages when $|\alpha| > k |\beta|$.

::: mathlib
`Fintype.exists_ne_map_eq_of_card_lt` · `Mathlib.Data.Fintype.Pigeonhole`

The arguments are the map `f` and the proof of `Fintype.card β < Fintype.card α`. The conclusion is `∃ x y, x ≠ y ∧ f x = f y`. For the form inside a type with finsets, `Finset.exists_ne_map_eq_of_card_lt_of_maps_to` takes a finset `s`, a finset `t` with `t.card < s.card`, and a proof that `f` sends `s` into `t`. The inequality of the cards is often proved by `simp` or by `decide`.

<?decl Fintype.exists_ne_map_eq_of_card_lt?>
:::

::: mathlib
`Fintype.card_le_of_injective` · `Mathlib.Data.Fintype.Card`

The rule for injective maps. The dual rule for surjective maps is `Fintype.card_le_of_surjective`, and `Fintype.card_of_bijective` gives equality for a bijective map that is not bundled as an equivalence.

<?decl Fintype.card_le_of_injective?>
:::

### Examples

**Example (All elements).** Each element of `Fin 5` is in `Finset.univ`. The proof is the field `complete` of the instance.

<?lean MathlibHandbook/V03/C04/Examples.lean#univ?>

**Example (The card of Fin n).**

<?lean MathlibHandbook/V03/C04/Examples.lean#card_fin?>

**Example (A product).** $|\mathrm{Bool} \times \mathrm{Fin}\ 3| = 2 \cdot 3 = 6$. The six pairs are $(b, i)$ with $b$ true or false and $i \in \{0, 1, 2\}$.

<?lean MathlibHandbook/V03/C04/Examples.lean#card_prod?>

**Example (Functions).** $|\mathrm{Fin}\ 3 \to \mathrm{Bool}| = 2^3 = 8$. A function is a word of length three in the letters true and false, and there are eight such words.

<?lean MathlibHandbook/V03/C04/Examples.lean#card_fun?>

**Example (Subsets).** $\mathrm{Fin}\ 4$ has $2^4 = 16$ subsets: one empty set, four singletons, six pairs, four triples and the whole set. The sum $1 + 4 + 6 + 4 + 1 = 16$ is a row of the triangle of Pascal, which Chapter 3 explains.

<?lean MathlibHandbook/V03/C04/Examples.lean#card_set?>

**Example (A composite type).** The rules combine. For $\gamma = (\mathrm{Fin}\ 2 \oplus \mathrm{Fin}\ 3) \to \mathrm{Bool}$, the sum rule gives $|\mathrm{Fin}\ 2 \oplus \mathrm{Fin}\ 3| = 5$, and the function rule gives $|\gamma| = 2^5 = 32$. For $\delta = \mathrm{Option}\ (\mathrm{Fin}\ 3 \times \mathrm{Bool})$ the product rule gives $6$ and the option rule gives $|\delta| = 7$. For $\mathrm{Bool} \to \mathrm{Fin}\ 3$ the count is $3^2 = 9$, not $2^3 = 8$: the exponent is the card of the domain.

**Example (Pigeonhole).** Five pigeons in four holes: a map from $\mathrm{Fin}\ 5$ to $\mathrm{Fin}\ 4$ sends two different elements to the same value.

<?lean MathlibHandbook/V03/C04/Examples.lean#pigeonhole?>

**Example (Birthdays).** In a group of $367$ people, two have the same birthday. The map from the people to the days of a year has a target with at most $366$ elements, and $366 < 367$. The pigeonhole principle applies to the type of the people, with no knowledge of the map.

**Example (Remainders).** Among any $n + 1$ integers $a_0, \ldots, a_n$, two have a difference divisible by $n$. The map $i \mapsto a_i \bmod n$ goes from $\mathrm{Fin}\ (n+1)$ to $\mathrm{Fin}\ n$ for $n \ge 1$. By the pigeonhole principle there are $i \ne j$ with $a_i \bmod n = a_j \bmod n$, and then $n$ divides $a_i - a_j$.

**Example (Check all cases).** In $\mathrm{Fin}\ 4$, with arithmetic modulo $4$, the squares are $0^2 = 0$, $1^2 = 1$, $2^2 = 0$ and $3^2 = 1$. So no square is $2$. The instance `Fintype (Fin 4)` lets `decide` check the four cases.

<?lean MathlibHandbook/V03/C04/Examples.lean#decide?>

**Counterexample (A type with no instance).** The type $\mathbb{N}$ has no finite type structure. A finset $U$ of natural numbers has a largest element $m$ or is empty, and $m + 1 \notin U$. So no finset contains all natural numbers. The class `Infinite ℕ` of Chapter 5 states this, and the pigeonhole principle has no analogue for $f : \mathbb{N} \to \mathbb{N}$, $f(n) = n + 1$, which is injective.

### Common errors

A learner often writes `Fintype.card` for the number of elements of a finset. For a finset `s`, the number is `s.card`. The expression `Fintype.card s` also makes sense, because `s` coerces to a subtype, and `Fintype.card_coe` says that it is `s.card`, but it is a detour.

A second error is to state a lemma with `[Fintype α]` when the proof needs no finset. Such a lemma then needs an instance at each use, and an instance from another source can block a rewrite. If the statement only needs finiteness, the class `Finite α` of Chapter 5 is the better hypothesis.

### The library around it

The file `Mathlib.Data.Fintype.Card` has the card lemmas for the basic types: `Fintype.card_unique` for a type with one element, `Fintype.card_eq_zero_iff` for an empty type and `Fintype.card_pos_iff` for a nonempty type. The lemmas `Fintype.card_subtype_le`, `Fintype.card_subtype_compl` and `Fintype.card_compl_set` count subtypes and complements, and Section 2 uses them. `Fintype.card_range` counts the range of an injective map. The construction `Fintype.ofFinset` builds an instance from a finset that contains each element, and `Fintype.ofEquiv` moves an instance along an equivalence. The induction principle `Fintype.induction_empty_option` proves a statement for all finite types from the empty type, from equivalences and from `Option`. The name pattern is regular: `Fintype.card_X` gives the card of the construction `X`, and most of these are `simp` lemmas. The reference table at the end lists the declarations of the section.

The file `Mathlib.Data.FinEnum` gives a stronger class than `Fintype`. An instance of `FinEnum α` holds a number `FinEnum.card α` and an equivalence `FinEnum.equiv : α ≃ Fin (FinEnum.card α)`, together with decidable equality. So it fixes an order of the elements, and `FinEnum.toList α` lists them in this order, with `FinEnum.mem_toList` and `FinEnum.nodup_toList`. A `Fintype` instance gives only a finset, with no order. Each `FinEnum` gives a `Fintype` by the instance `FinEnum.instFintype`, and `FinEnum.card_eq_fintypeCard` says that the two counts agree. The constructions follow the same pattern as for `Fintype`: `FinEnum.ofList` and `FinEnum.ofNodupList` build an instance from a list that contains each element, `FinEnum.ofEquiv` moves an instance along an equivalence, and `FinEnum.ofInjective` and `FinEnum.ofSurjective` move it along an injection or a surjection. There are instances for `Fin n`, products, sums, subtypes, sigma types and `Finset α`, and `FinEnum.card_fin` gives $|\mathrm{Fin}\ n| = n$. The file `Mathlib.Data.FinEnum.Option` adds `FinEnum.insertNone`, which puts `none` at a chosen place of the enumeration of `Option α`, and the recursor `FinEnum.recEmptyOption`. This recursor is the analogue of `Fintype.induction_empty_option` for data: it builds a value for each enumerable type from the empty type, from `Option` and from the transport along an equal card.

### Exercises

1. (A) Give `Fintype.card (Fin 2 ⊕ Fin 3 → Bool)` and `Fintype.card (Bool → Fin 2 ⊕ Fin 3)`.
2. (A) Explain why `Fintype.card` gives the same number for two different instances.
3. (A) Compute $|\mathrm{Option}\ (\mathrm{Option}\ (\mathrm{Fin}\ 2 \times \mathrm{Fin}\ 2))|$ and $|\mathrm{Set}\ (\mathrm{Bool} \times \mathrm{Bool})|$.
4. (B) Prove the pigeonhole principle for $13$ people and $12$ months of birth with `decide` or with `Fintype.exists_ne_map_eq_of_card_lt`. Hint: model the people as `Fin 13` and the months as `Fin 12`.
5. (B) Prove that among any five points with integer coordinates in the plane, two have a midpoint with integer coordinates. Hint: map a point $(x, y)$ to $(x \bmod 2, y \bmod 2)$ in $\mathrm{Fin}\ 2 \times \mathrm{Fin}\ 2$.
6. (B) Prove $|\alpha \times \beta| = |\alpha| \cdot |\beta|$ by induction on $|\alpha|$, with $\mathrm{Option}\ \alpha \times \beta \simeq \beta \oplus (\alpha \times \beta)$.
7. (C) Prove that a set of $n + 1$ numbers from $\{1, \ldots, 2n\}$ contains two numbers such that one divides the other. Hint: write each number as $2^k m$ with $m$ odd and apply the pigeonhole principle to $m$.
8. (L) Prove that an injective map does not go to a smaller finite type. The solution is `card_le_of_injective_example`.
9. (L) Prove that equivalent finite types have the same card. The solution is `card_congr_example`.
10. (L) Prove that `Option α` has one more element than `α`. The solution is `card_option_example`.
11. (L) Prove that the card of `Finset.univ` is the card of the type. The solution is `card_univ_example`.

### Notes and history

The pigeonhole principle has the name "Schubfachprinzip", the drawer principle, from Dirichlet. He used it in 1834 and in his work on the approximation of real numbers by rationals: among the fractional parts of $0, x, 2x, \ldots, nx$, two lie in the same interval of length $1/n$. The counting rules for products, sums and functions are the arithmetic of finite cardinals, and Cantor defined the operations on cardinals by these constructions.

In Mathlib, the file `Mathlib.Data.Fintype.Defs` and the first card lemmas come from the Lean 3 library, by Mario Carneiro. The class `Fintype` is data, and the class `Finite` is a proposition. Both exist because a sum over a type needs a finset that a program can use, but a statement often needs only the fact that the type is finite. The library advice, in the source of `Mathlib.Basic.Finite.Defs`, is to write computable `Fintype` instances and to use `Finite` for the noncomputable cases. MSG shows how `decide` uses the `Fintype` instance to check a statement for all elements, and MIL uses `Fintype.card` in its chapter on combinatorics.

### Reference

<?reference?>
