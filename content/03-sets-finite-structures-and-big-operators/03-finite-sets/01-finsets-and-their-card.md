---
title: Finsets and their card
kind: theory
modules:
  - Mathlib.Data.Finset.Card
explains:
  E3: [Finset, Finset.card_union_add_card_inter]
  E2: [Finset.card, Finset.card_insert_of_notMem, Finset.filter, Finset.card_image_of_injective, Finset.card_powerset, Finset.induction_on, Finset.card_le_card]
  E1: auto
families: []
requires: [V03.C01, V03.C02]
reads_with: ["MIL", "MSG"]
lean:
  - MathlibHandbook/V03/C03/Examples.lean
  - MathlibHandbook/V03/C03/Exercises.lean
  - MathlibHandbook/V03/C03/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Finsets and their card

### Overview

The type `Set α` of Chapter 1 holds any set, finite or not. A set is a predicate, and a predicate can be any proposition, so a set has no number of elements that a program can compute. Combinatorics needs such a number. The type `Finset α` holds the finite sets in a form that has data: a multiset with no repeated element, as in Chapter 2. With this form the card is a function to $\mathbb{N}$, the union and the filter are functions that compute, and `decide` can check a statement about a small finset.

This section gives the structure of a finset, its operations, and the first counting rules: the card of an insert, of a subset, of an image and of the power set, and $|s \cup t| + |s \cap t| = |s| + |t|$. The tool for almost all the proofs is induction on finsets: a statement that holds for $\emptyset$, and that passes from $s$ to $s \cup \{a\}$ for $a \notin s$, holds for all finsets.

Section 2 counts the subsets of a given size, and Section 3 gives the other rules of counting and the pigeonhole principle.

### Definitions

Fix a type $\alpha$. In the text a finset is a finite subset of $\alpha$, and $|s|$ is its number of elements. The definitions below say how Mathlib makes this precise.

**Definition (Finset).** A finset of $\alpha$ is a pair $(m, h)$ of a multiset $m$ of elements of $\alpha$ and a proof $h$ that no element occurs twice in $m$. The element $a$ is a member of the finset when $a$ occurs in $m$.

A multiset is a list up to the order of its entries (Chapter 2). So a finset is a list up to order with no repetition. This is the usual finite set: the order does not count, and an element is in the set or it is not.

**Theorem (Extensionality).** Two finsets with the same members are equal.

*Proof.* Let $s = (m, h)$ and $t = (m', h')$ have the same members. In a multiset with no repetition, the count of an element $a$ is $1$ if $a$ is a member and $0$ if not. So $m$ and $m'$ give each $a$ the same count. Two multisets with the same count function are equal (Chapter 2). So $m = m'$. The proofs $h$ and $h'$ are proofs of the same proposition, and two proofs of one proposition are equal in Lean. So $s = t$. $\square$

::: mathlib
`Finset` · `Mathlib.Data.Finset.Defs`

A term `s : Finset α` is a structure with the two fields `s.val : Multiset α` and `s.nodup : s.val.Nodup`. Membership `a ∈ s` is `a ∈ s.val`. The lemma `Finset.ext` is the extensionality theorem above, and the tactic `ext a` applies it. The coercion `(s : Set α)` sends a finset to the set of its members, and the `coe` lemmas such as `Finset.coe_insert` move the operations across it.

<?decl Finset?>
:::

**Definition (Card).** The card $|s|$ of a finset $s = (m, h)$ is the number of entries of $m$, that is, the length of any list that represents $m$.

Two lists that represent $m$ are permutations of each other, so they have the same length. Thus the card is well defined. Mathlib writes `s.card` or `#s`.

::: mathlib
`Finset.card` · `Mathlib.Data.Finset.Card`

`Finset.card s` is `Multiset.card s.val`. The notation `#s` needs `open Finset`. The value is a natural number, so a statement about cards is a statement in $\mathbb{N}$. A subtraction of cards truncates at zero. For this reason most counting lemmas of Mathlib have a form with addition, such as `Finset.card_union_add_card_inter`, beside a form with subtraction.

<?decl Finset.card?>
:::

**Definition (Operations).** Let $s$ and $t$ be finsets of $\alpha$, let $a \in \alpha$, let $p$ be a predicate on $\alpha$ and let $f : \alpha \to \beta$.

1. $\emptyset$ is the finset with no member, and $\{a\}$ is the finset with the one member $a$.
2. $\operatorname{insert} a\, s$ is the finset $s \cup \{a\}$, and $\operatorname{erase} s\, a$ is $s \setminus \{a\}$.
3. $s \cup t$, $s \cap t$ and $s \setminus t$ are the union, the intersection and the difference.
4. The filter $\{x \in s : p(x)\}$ is the finset of the members of $s$ that satisfy $p$.
5. The image $f(s) = \{f(x) : x \in s\}$ is a finset of $\beta$.
6. $\operatorname{range} n = \{0, 1, \ldots, n - 1\}$, a finset of $\mathbb{N}$ with $n$ members.
7. The power set $\mathcal{P}(s)$ is the finset of all the finsets $u$ with $u \subseteq s$.

Each operation is computed on the multiset. The union and the image must remove repeated entries, so they test whether two elements are equal. Thus union, intersection, difference, insert, erase and image need the class `DecidableEq`. The filter only drops entries, so it needs a decidable predicate `DecidablePred p` and no equality test.

::: mathlib
`Finset.filter` · `Mathlib.Data.Finset.Filter`

`Finset.filter p s` keeps the members of `s` that satisfy `p`. The notation `{x ∈ s | p x}` stands for it. The predicate must have an instance `DecidablePred p`. For a predicate on $\mathbb{N}$ such as `fun n => n % 3 = 0` the instance is found by Lean. In a proof about an abstract predicate, the line `classical` at the start of the proof gives every predicate a decidable instance.

<?decl Finset.filter?>
:::

The notation `{1, 2, 3}` is `insert 1 (insert 2 {3})`. So a finset that is written out by its members needs `DecidableEq α`. For $\mathbb{N}$, $\mathbb{Z}$ and the other concrete types this instance exists.

### Theorems and proofs

The main tool comes first.

**Theorem (Induction on finsets).** Let $P$ be a property of the finsets of $\alpha$. Assume that $P(\emptyset)$ holds, and that for each finset $s$ and each $a \notin s$, $P(s)$ implies $P(s \cup \{a\})$. Then $P(s)$ holds for every finset $s$.

*Proof.* Use induction on the number $n = |s|$. Let $n = 0$. A finset of card $0$ comes from the empty multiset, so it is $\emptyset$, and $P(\emptyset)$ holds. Let $n \geq 1$, and assume that $P$ holds for every finset of card $n - 1$. Let $|s| = n$. The multiset of $s$ is not empty, so it has an entry $a$. Put $s' = s \setminus \{a\}$. The entry $a$ occurs once in $s$, so the multiset of $s'$ is that of $s$ with one entry removed, and $|s'| = n - 1$. By the hypothesis of induction $P(s')$ holds. Also $a \notin s'$ and $s' \cup \{a\} = s$. By the second assumption, $P(s)$ holds. $\square$

::: mathlib
`Finset.induction_on` · `Mathlib.Data.Finset.Insert`

The tactic form is `induction s using Finset.induction_on with | empty => ... | insert a s ha ih => ...`, where `ha : a ∉ s` and `ih` is the statement for `s`. The principle needs `DecidableEq α`, because `insert` needs it; the variant `Finset.cons_induction` does not. `Finset.strongInduction` gives the statement for all proper subsets at each step.

<?decl Finset.induction_on?>
:::

**Theorem (Card of an insert).** Let $s$ be a finset and $a \in \alpha$. If $a \notin s$, then $|s \cup \{a\}| = |s| + 1$. If $a \in s$, then $s \cup \{a\} = s$.

*Proof.* Let $a \notin s$. Mathlib computes the multiset of $\operatorname{insert} a\, s$ as the multiset of $s$ with one more entry $a$, because $a$ is not yet an entry. A multiset with one more entry has one more element, so the card is $|s| + 1$. Let $a \in s$. Then $s \cup \{a\}$ and $s$ have the same members, and by extensionality they are equal. $\square$

::: mathlib
`Finset.card_insert_of_notMem` · `Mathlib.Data.Finset.Card`

The hypothesis is `a ∉ s`, and the conclusion is `#(insert a s) = #s + 1`. The case of a member is `Finset.card_insert_of_mem`. Older versions of Mathlib wrote `not_mem` in the name, and that name is now deprecated.

<?decl Finset.card_insert_of_notMem?>
:::

**Theorem (Card of a disjoint union).** If $s \cap t = \emptyset$, then $|s \cup t| = |s| + |t|$.

*Proof.* Fix $t$ and use induction on $s$. For $s = \emptyset$, the union is $t$ and both sides are $|t|$. Let $a \notin s$, assume the statement for $s$, and assume that $s \cup \{a\}$ does not meet $t$. Then $s$ does not meet $t$, so $|s \cup t| = |s| + |t|$ by the hypothesis of induction. Also $a \notin t$ and $a \notin s$, so $a \notin s \cup t$. By the card of an insert, $$|(s \cup \{a\}) \cup t| = |(s \cup t) \cup \{a\}| = |s \cup t| + 1 = |s| + 1 + |t| = |s \cup \{a\}| + |t|.$$ This is the statement for $s \cup \{a\}$. $\square$

**Theorem (Card of a subset).** If $s \subseteq t$, then $|s| \leq |t|$ and $|t \setminus s| + |s| = |t|$. If $s \subsetneq t$, then $|s| < |t|$.

*Proof.* The finsets $t \setminus s$ and $s$ do not meet. Their union is $t$, because $s \subseteq t$: a member of $t$ is in $s$ or it is not. By the card of a disjoint union, $|t| = |t \setminus s| + |s|$. Since $|t \setminus s| \geq 0$, $|s| \leq |t|$. If $s \neq t$, then some member of $t$ is not in $s$, so $t \setminus s \neq \emptyset$ and $|t \setminus s| \geq 1$. Then $|s| < |t|$. $\square$

::: mathlib
`Finset.card_le_card` · `Mathlib.Data.Finset.Card`

The hypothesis is `s ⊆ t` and the conclusion is `#s ≤ #t`. The strict form `Finset.card_lt_card` takes `s ⊂ t`. The equality `Finset.card_sdiff_add_card_eq_card` is the second claim of the theorem. A useful consequence is the converse rule: a subset with a card that is not smaller is the whole finset.

<?decl Finset.card_le_card?>
:::

**Theorem (Inclusion and exclusion for two finsets).** For finsets $s$ and $t$, $$|s \cup t| + |s \cap t| = |s| + |t|.$$

*Proof.* Fix $t$ and use induction on $s$. For $s = \emptyset$, the union is $t$ and the intersection is $\emptyset$, so both sides are $|t|$. Let $a \notin s$ and assume the statement for $s$. Put $s_1 = s \cup \{a\}$. There are two cases.

Case $a \in t$. Then $s_1 \cup t = s \cup t$, because $a$ is already in $t$. The intersection is $s_1 \cap t = (s \cap t) \cup \{a\}$, and $a \notin s \cap t$, so $|s_1 \cap t| = |s \cap t| + 1$. The left side grows by $1$.

Case $a \notin t$. Then $s_1 \cap t = s \cap t$, and $s_1 \cup t = (s \cup t) \cup \{a\}$ with $a \notin s \cup t$. So $|s_1 \cup t| = |s \cup t| + 1$. The left side grows by $1$.

In both cases the right side grows by $1$, because $|s_1| = |s| + 1$. So the equality for $s$ gives the equality for $s_1$. $\square$

::: mathlib
`Finset.card_union_add_card_inter` · `Mathlib.Data.Finset.Card`

The statement is `#(s ∪ t) + #(s ∩ t) = #s + #t`, with `DecidableEq α`. The form with a sum on both sides has no subtraction in $\mathbb{N}$, so `omega` and `linarith` use it directly. The form with subtraction is `Finset.card_union`: `#(s ∪ t) = #s + #t - #(s ∩ t)`. The bound `Finset.card_union_le` drops the intersection.

<?decl Finset.card_union_add_card_inter?>
:::

**Theorem (Card of an image).** Let $f : \alpha \to \beta$ and let $s$ be a finset of $\alpha$. Then $|f(s)| \leq |s|$. If $f$ is injective on $s$, then $|f(s)| = |s|$.

*Proof.* Use induction on $s$. For $s = \emptyset$, the image is $\emptyset$, and both cards are $0$. Let $a \notin s$, and assume the claims for $s$. The image of $s \cup \{a\}$ is $f(s) \cup \{f(a)\}$. By the card of an insert, $|f(s) \cup \{f(a)\}| \leq |f(s)| + 1 \leq |s| + 1 = |s \cup \{a\}|$. This is the first claim. Now let $f$ be injective on $s \cup \{a\}$. Then $f$ is injective on $s$, so $|f(s)| = |s|$. If $f(a) \in f(s)$, then $f(a) = f(x)$ for some $x \in s$, and injectivity gives $a = x \in s$. This is false. So $f(a) \notin f(s)$ and $|f(s) \cup \{f(a)\}| = |f(s)| + 1 = |s| + 1$. $\square$

::: mathlib
`Finset.card_image_of_injective` · `Mathlib.Data.Finset.Card`

This form asks that `f` is injective on all of `α`. The form `Finset.card_image_of_injOn` asks only `Set.InjOn f s`, and `Finset.card_image_iff` gives the converse. The bound with no hypothesis on `f` is `Finset.card_image_le`.

<?decl Finset.card_image_of_injective?>
:::

**Theorem (Card of the power set).** If $|s| = n$, then $|\mathcal{P}(s)| = 2^n$.

*Proof.* Use induction on $s$. The power set of $\emptyset$ is $\{\emptyset\}$, with $1 = 2^0$ member. Let $a \notin s$ and assume $|\mathcal{P}(s)| = 2^{|s|}$. Split the subsets $u$ of $s \cup \{a\}$ into two kinds. A subset of the first kind does not contain $a$. These are exactly the subsets of $s$, so there are $2^{|s|}$ of them. A subset of the second kind contains $a$. The map $v \mapsto v \cup \{a\}$ sends a subset $v$ of $s$ to a subset of the second kind. It is injective, because $v = (v \cup \{a\}) \setminus \{a\}$ when $a \notin v$. It is onto the second kind, because $u = (u \setminus \{a\}) \cup \{a\}$ and $u \setminus \{a\} \subseteq s$. So the second kind has $2^{|s|}$ members, by the card of an image. The two kinds do not meet. By the card of a disjoint union, $|\mathcal{P}(s \cup \{a\})| = 2^{|s|} + 2^{|s|} = 2^{|s| + 1}$. $\square$

::: mathlib
`Finset.card_powerset` · `Mathlib.Data.Finset.Powerset`

The statement is `#s.powerset = 2 ^ #s`. The proof in Mathlib goes through the multiset `Multiset.powerset`, whose card is computed from a list of all sublists. The decomposition of the proof above is `Finset.powerset_insert`: `(insert a s).powerset = s.powerset ∪ s.powerset.image (insert a)`.

<?decl Finset.card_powerset?>
:::

### Examples

**Example (A finset of numbers).** The finset $\{1, 2, 3\}$ contains $3$ and has card $3$. Lean checks both facts by computation.

<?lean MathlibHandbook/V03/C03/Examples.lean#decide?>

**Example (Insert).** Insert the number $7$ into $s = \{1, 2, 3\}$. Since $7 \notin s$, the card goes from $3$ to $4$. Insert $2$ into $s$. Since $2 \in s$, the result is $s$ again and the card stays $3$. The general rule with the hypothesis $a \notin s$:

<?lean MathlibHandbook/V03/C03/Examples.lean#insert?>

**Example (Filter).** The multiples of $3$ in $\operatorname{range} 10 = \{0, \ldots, 9\}$ are $0, 3, 6, 9$. So the filter has card $4$. In general there are $\lceil n / d \rceil$ multiples of $d \geq 1$ in $\operatorname{range} n$, and $\lceil 10/3 \rceil = 4$.

<?lean MathlibHandbook/V03/C03/Examples.lean#filter?>

**Example (Image).** The map $n \mapsto 2n$ is injective on $\mathbb{N}$, because $2a = 2b$ gives $a = b$. So the image of any finset has the same card. For $s = \{0, 1, 2, 3\}$ the image is $\{0, 2, 4, 6\}$, with card $4$.

<?lean MathlibHandbook/V03/C03/Examples.lean#image?>

**Example (Inclusion and exclusion).** Let $s = \{0, 2, 4, 6, 8\}$, the even numbers below $10$, and $t = \{0, 3, 6, 9\}$, the multiples of $3$ below $10$. Then $s \cup t = \{0, 2, 3, 4, 6, 8, 9\}$ and $s \cap t = \{0, 6\}$. The two sides are $7 + 2 = 9$ and $5 + 4 = 9$. The general statement:

<?lean MathlibHandbook/V03/C03/Examples.lean#incl_excl?>

**Example (Power set).** The set $s = \{a, b, c\}$ has the $8 = 2^3$ subsets $$\emptyset,\ \{a\},\ \{b\},\ \{c\},\ \{a, b\},\ \{a, c\},\ \{b, c\},\ \{a, b, c\}.$$ The proof of the theorem splits them as the four subsets of $\{a, b\}$ and the four subsets that contain $c$. The general statement:

<?lean MathlibHandbook/V03/C03/Examples.lean#powerset?>

**Example (Induction).** The tactic `induction s using Finset.induction_on` gives a case for $\emptyset$ and a case for `insert a s` with `a ∉ s`.

<?lean MathlibHandbook/V03/C03/Examples.lean#induction?>

**Counterexample (An image that is smaller).** Let $f(n) = n \bmod 2$ and $s = \{0, 1, 2, 3\}$. The image is $\{0, 1\}$, with card $2 < 4$. The function is not injective: $f(0) = f(2)$. So the hypothesis of injectivity in the card of an image is needed. The general rule is the inequality `Finset.card_image_le`.

### Common errors

- To forget that a finset has no repetition. The term `({1, 1, 2} : Finset ℕ)` is the finset $\{1, 2\}$, with card $2$. The multiset `({1, 1, 2} : Multiset ℕ)` has card $3$.
- To use `Finset.card_union` and then fight with the subtraction in $\mathbb{N}$. Use `Finset.card_union_add_card_inter` and `omega`.
- To apply `Finset.card_insert_of_notMem` with no proof of `a ∉ s`. The tactic `simp` often proves the hypothesis for a concrete finset, for example `7 ∉ {1, 2, 3}`.
- To write `Finset.image` on a type with no decidable equality in a general proof. Put `classical` at the start of the proof, or use `Finset.map` with an embedding.
### The library around it

The lemmas of `Mathlib.Data.Finset.Card` follow the operations, with names `Finset.card_<op>` or `Finset.card_<op>_of_<hyp>`: `Finset.card_empty`, `Finset.card_singleton`, `Finset.card_insert_of_mem`, `Finset.card_erase_of_mem`, `Finset.card_range` and `Finset.card_filter_le`. The basic ones are `simp` lemmas, so `simp` computes the card of a small explicit finset. The predicates on the card are `Finset.card_eq_zero`, `Finset.card_pos`, `Finset.card_le_one` and `Finset.one_lt_card`. The reference table below lists the lemmas of the module.

### Exercises

1. (A) Give the card of `(Finset.range 6).filter Even`. List its members.
2. (A) Explain why `Finset.image` needs decidable equality on the target type and `Finset.filter` does not.
3. (B) Use inclusion and exclusion to show that two subsets of $\{0, \ldots, 9\}$ with six members each meet. Hint: $|s \cup t| \leq 10$.
4. (B) Prove by induction on $s$ that $|s \cup t| \leq |s| + |t|$, with no use of the intersection.
5. (B) Let $f : \alpha \to \beta$ and let $s$ be a finset with $|f(s)| = |s|$. Prove that $f$ is injective on $s$. Hint: if $f(x) = f(y)$ with $x \neq y$, then $f(s) = f(s \setminus \{y\})$.
6. (C) Prove the principle of strong induction on finsets: if $P(s)$ follows from $P(u)$ for all $u \subsetneq s$, then $P$ holds for all finsets. Hint: use induction on $|s|$ and the strict form of the card of a subset.
7. (L) Prove that a subset has a card that is not larger. The solution is `card_le_of_subset_example`.
8. (L) Prove that the card of a union is at most the sum of the cards. The solution is `card_union_le_example`.
9. (L) Prove that a filter does not make a finset larger. The solution is `card_filter_le_example`.
10. (L) Prove that the card of a product is the product of the cards. The solution is `card_product_example`.

### Notes and history

The rule $|s \cup t| + |s \cap t| = |s| + |t|$ is the first case of the principle of inclusion and exclusion, which de Moivre used in the eighteenth century and Sylvester stated in general. The proof by induction on finsets matches the view of a finite set as one built from $\emptyset$ by adding one element at a time.

In Lean, finsets come from the Lean 3 library; the authors line of `Mathlib.Data.Finset.Defs` names Leonardo de Moura, Jeremy Avigad, Minchao Wu and Mario Carneiro. Mathlib keeps both `Finset α`, for computation and the sums of Chapter 6, and `Set.Finite` of Chapter 5, for statements about sets. MIL uses finsets in its chapter on combinatorics, and MSG shows how `decide` counts small cases.

### Reference

<?reference?>
