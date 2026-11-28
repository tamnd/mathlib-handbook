---
title: Counting maps, injections and permutations
kind: theory
modules:
  - Mathlib.Data.Fintype.Perm
  - Mathlib.Data.Fintype.CardEmbedding
  - Mathlib.Data.Fintype.BigOperators
  - Mathlib.Data.Finite.Perm
explains:
  E3: [Fintype.card_embedding_eq, Fintype.card_perm, Finite.injective_iff_surjective]
  E2: [Fintype.card_equiv, Fintype.card_subtype, Fintype.card_subtype_compl, Fintype.card_lt_of_injective_not_surjective, Fintype.bijective_iff_injective_and_card, Function.Injective.bijective_of_finite, Fintype.card_pi, Fintype.card_sigma, Fintype.card_embedding_eq_of_infinite]
  E1: auto
families: []
requires: [V03.C03]
reads_with: ["MIL"]
lean:
  - MathlibHandbook/V03/C04/Examples.lean
  - MathlibHandbook/V03/C04/Exercises.lean
  - MathlibHandbook/V03/C04/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Counting maps, injections and permutations

### Overview

Section 1 counted all the functions from a finite type $\alpha$ to a finite type $\beta$: there are $|\beta|^{|\alpha|}$ of them. This section counts the functions with a property. The main results are three. The number of injective maps from a set with $k$ elements to a set with $n$ elements is the falling factorial $n(n-1)\cdots(n-k+1)$. The number of permutations of a set with $n$ elements is $n!$. A map from a finite type to itself is injective if and only if it is surjective.

All three results rest on one counting rule: the elements of $\alpha$ are the disjoint union of the fibers of a map $f : \alpha \to \beta$, so $|\alpha|$ is the sum of the cards of the fibers. The same rule gives the strong form of the pigeonhole principle, and it gives the relation $n(n-1)\cdots(n-k+1) = k! \binom{n}{k}$ between injections and subsets. After this section the reader can count injections, permutations and subtypes, and can turn an argument "by the size of the fibers" into a proof.

### Definitions

**Definition (Fiber).** Let $f : \alpha \to \beta$ and $b \in \beta$. The *fiber* of $f$ over $b$ is $f^{-1}(b) = \{a \in \alpha : f(a) = b\}$.

Two fibers over different points are disjoint, because $f(a)$ has only one value. Each $a$ lies in the fiber over $f(a)$. So the fibers form a partition of $\alpha$, with some empty parts when $f$ is not surjective.

**Definition (Embedding and permutation).** An *embedding* of $\alpha$ in $\beta$ is an injective map $\alpha \to \beta$. The set of embeddings is written $\alpha \hookrightarrow \beta$. A *permutation* of $\alpha$ is a bijection $\alpha \to \alpha$. The set of permutations is $\mathrm{Perm}(\alpha)$, and with composition it is a group, the symmetric group of $\alpha$.

**Definition (Falling factorial).** For natural numbers $n$ and $k$, the *falling factorial* is $$n^{\underline{k}} = n (n-1) (n-2) \cdots (n - k + 1),$$ the product of $k$ factors that start at $n$ and go down by one. The empty product gives $n^{\underline{0}} = 1$. The recursion is $n^{\underline{k+1}} = n^{\underline{k}} \cdot (n - k)$. If $k > n$, one factor is $0$, so $n^{\underline{k}} = 0$. Also $n^{\underline{n}} = n!$.

::: mathlib
`Fintype.card_embedding_eq` · `Mathlib.Data.Fintype.CardEmbedding`

The type of embeddings is `α ↪ β`, a structure `Function.Embedding` with a function and a proof that it is injective. The falling factorial is `Nat.descFactorial n k`, the "descending factorial", in `Mathlib.Data.Nat.Factorial.Basic`. Its recursion uses truncated subtraction, and for $k > n$ the factor $n - k$ is $0$ in `ℕ`, which is the value that the count needs. The theorem states `Fintype.card (α ↪ β) = (Fintype.card β).descFactorial (Fintype.card α)`, and it is a `simp` lemma.

<?decl Fintype.card_embedding_eq?>
:::

### Theorems and proofs

**Theorem (Sum over the fibers).** Let $\alpha$ and $\beta$ be finite and let $f : \alpha \to \beta$. Then $$|\alpha| = \sum_{b \in \beta} |f^{-1}(b)|.$$ In particular, if each fiber has exactly $m$ elements, then $|\alpha| = m |\beta|$.

*Proof.* The fibers $f^{-1}(b)$ for $b \in \beta$ are pairwise disjoint, and their union is $\alpha$, as the definition shows. The card of a union of pairwise disjoint finsets is the sum of their cards. This is the rule for two disjoint finsets of Chapter 3, applied once for each new fiber by induction on the number of fibers. So $|\alpha| = \sum_b |f^{-1}(b)|$. If each term is $m$, the sum has $|\beta|$ terms equal to $m$, and it is $m |\beta|$. $\square$

::: mathlib
`Finset.card_eq_sum_card_fiberwise` · `Mathlib.Algebra.BigOperators.Group.Finset.Basic`

Mathlib states the rule for finsets: if `f` sends `s` into `t`, then `s.card = ∑ b ∈ t, {a ∈ s | f a = b}.card`. The fiber is a filter of `s`, so the rule needs `DecidableEq` on the target. The sum notation is that of Chapter 6. For a whole type, take `s` and `t` to be `Finset.univ`. The rule `Fintype.card_sigma` is the same fact for a dependent pair type: $|\Sigma_i \beta_i| = \sum_i |\beta_i|$.

<?decl Finset.card_eq_sum_card_fiberwise?>
:::

**Theorem (Number of injections).** Let $|\alpha| = k$ and $|\beta| = n$. The number of injective maps $\alpha \to \beta$ is $n^{\underline{k}}$.

*Proof.* The number of injections depends only on $k$ and $n$, because an equivalence $\alpha \simeq \alpha'$ gives a bijection between the injections from $\alpha$ and the injections from $\alpha'$, by composition. So take $\alpha = \mathrm{Fin}\ k$. Use induction on $k$. For $k = 0$ there is one map from the empty type, the empty map, and it is injective. So the count is $1 = n^{\underline{0}}$.

For the step, let $E_{k}$ be the set of injections $\mathrm{Fin}\ k \to \beta$. Define $R : E_{k+1} \to E_k$ by restriction: $R(f)$ is $f$ on $0, \ldots, k - 1$. A restriction of an injective map is injective, so $R$ is well defined. Fix $g \in E_k$. An element $f$ of the fiber $R^{-1}(g)$ agrees with $g$ on $0, \ldots, k-1$, so it is determined by the value $c = f(k)$. The map $f$ is injective exactly when $c$ is not one of $g(0), \ldots, g(k-1)$. These $k$ values are distinct, because $g$ is injective. So there are $n - k$ choices of $c$ when $k \le n$, and each choice gives an element of the fiber. Thus each fiber of $R$ has $n - k$ elements. If $k > n$, then $E_k$ is empty by the pigeonhole principle, so $E_{k+1}$ is empty too, and both sides are $0$. In the case $k \le n$ the sum over the fibers gives $$|E_{k+1}| = (n - k) |E_k| = (n-k) \, n^{\underline{k}} = n^{\underline{k+1}}.$$ $\square$

**Theorem (Injective and surjective).** Let $\alpha$ be finite and let $f : \alpha \to \alpha$. Then $f$ is injective if and only if $f$ is surjective.

*Proof.* Let $U$ be the finset of all elements of $\alpha$, and let $|U| = n$. Assume that $f$ is injective. Then the image $f(U)$ has $n$ elements. It is a subset of $U$ with the same card as $U$. A subset $S \subseteq U$ with $|S| = |U|$ is all of $U$, because $|U \setminus S| = |U| - |S| = 0$. So $f(U) = U$, and $f$ is surjective.

Now assume that $f$ is surjective. For each $y$ choose an $x$ with $f(x) = y$, and call it $g(y)$. Then $f(g(y)) = y$ for all $y$. So $g$ is injective: if $g(y) = g(y')$, then $y = f(g(y)) = f(g(y')) = y'$. By the first part, $g$ is surjective. Let $f(x) = f(x')$. Write $x = g(y)$ and $x' = g(y')$. Then $y = f(g(y)) = f(x) = f(x') = y'$, so $x = x'$. Thus $f$ is injective. $\square$

The second half uses a choice of preimages. For a finite type the choice can be made without the axiom of choice, by a search through the finset, but the proof on paper does not need this.

::: mathlib
`Finite.injective_iff_surjective` · `Mathlib.Data.Fintype.Card`

The hypothesis is `[Finite α]`, the propositional class of Chapter 5, not `Fintype α`. The theorem needs no finset, only the fact that the type is finite. The forms `Function.Injective.bijective_of_finite` and `Finite.surjective_of_injective` give one direction. For two types with the same card, `Fintype.bijective_iff_injective_and_card` says that a map is bijective exactly when it is injective and the cards agree. For two types with different cards, `Fintype.card_lt_of_injective_not_surjective` gives the strict inequality.

<?decl Finite.injective_iff_surjective?>
:::

**Theorem (Number of permutations).** Let $|\alpha| = n$. Then $|\mathrm{Perm}(\alpha)| = n!$. More generally, if $|\alpha| = |\beta| = n$, the number of bijections $\alpha \to \beta$ is $n!$.

*Proof.* By the theorem on injective and surjective maps, a map $\alpha \to \alpha$ is a bijection exactly when it is injective. So the permutations are the injections $\alpha \to \alpha$, and their number is $n^{\underline{n}} = n (n-1) \cdots 1 = n!$. For the general case fix one bijection $e : \alpha \to \beta$, which exists because the cards agree. The map $\sigma \mapsto e \circ \sigma$ is a bijection from $\mathrm{Perm}(\alpha)$ to the bijections $\alpha \to \beta$, with the inverse $\tau \mapsto e^{-1} \circ \tau$. So the count is $n!$ again. $\square$

::: mathlib
`Fintype.card_perm` · `Mathlib.Data.Fintype.Perm`

The type is `Equiv.Perm α`, the equivalences from `α` to itself, and the result is `(Fintype.card α).factorial`. The instance `Fintype (Equiv.Perm α)` needs `DecidableEq α`, because it builds the permutations as lists. The general form is `Fintype.card_equiv`. It takes an equivalence `e : α ≃ β` as an argument, so the user must give one bijection to count all of them.

<?decl Fintype.card_perm?>
:::

**Theorem (Injections and subsets).** For natural numbers $k \le n$, $$n^{\underline{k}} = k! \binom{n}{k}.$$

*Proof.* Let $|\beta| = n$. Count the injections $f : \mathrm{Fin}\ k \to \beta$ in two ways. The first way is the theorem on injections, which gives $n^{\underline{k}}$. For the second way, send $f$ to its image $f(\mathrm{Fin}\ k)$, a subset of $\beta$ with exactly $k$ elements, since $f$ is injective. Fix a subset $S$ with $k$ elements. The injections with image $S$ are the bijections $\mathrm{Fin}\ k \to S$, and there are $k!$ of them by the theorem on permutations. So each fiber of the map $f \mapsto f(\mathrm{Fin}\ k)$ has $k!$ elements, and there are $\binom{n}{k}$ fibers, one for each subset with $k$ elements (Chapter 3). The sum over the fibers gives $n^{\underline{k}} = k! \binom{n}{k}$. $\square$

This proof is a first example of double counting: one set is counted in two ways, and the two counts are equal. Chapter 6 gives the method in general. The identity also holds for $k > n$, where both sides are $0$. In Mathlib it is `Nat.descFactorial_eq_factorial_mul_choose`.

**Theorem (Strong pigeonhole principle).** Let $f : \alpha \to \beta$ with $\alpha$, $\beta$ finite, and let $m$ be a natural number with $|\alpha| > m |\beta|$. Then some fiber of $f$ has more than $m$ elements.

*Proof.* Assume, for a contradiction, that $|f^{-1}(b)| \le m$ for each $b \in \beta$. By the sum over the fibers, $$|\alpha| = \sum_{b \in \beta} |f^{-1}(b)| \le \sum_{b \in \beta} m = m |\beta|.$$ This contradicts $|\alpha| > m |\beta|$. $\square$

For $m = 1$ this is the pigeonhole principle of Section 1: a fiber with two elements gives $x \ne y$ with $f(x) = f(y)$. In words: if $N$ objects lie in $r$ boxes, some box holds at least $\lceil N / r \rceil$ objects.

::: mathlib
`Fintype.exists_lt_card_fiber_of_mul_lt_card` · `Mathlib.Combinatorics.Pigeonhole`

The strong form is in the combinatorics part of the library, which Volume 30 covers. The hypothesis is `Fintype.card β * n < Fintype.card α`, and the conclusion is `∃ y, n < {x | f x = y}.card`, with the fiber as a filter of `Finset.univ`. The file has many variants: with `≤` in place of `<`, for finsets, and for sums of weights in place of cards.

<?decl Fintype.exists_lt_card_fiber_of_mul_lt_card?>
:::

**Theorem (Card of a subtype).** Let $\alpha$ be finite and let $p$ be a property of the elements of $\alpha$. The subtype $\{x : p(x)\}$ has as many elements as the finset of the $x \in \alpha$ with $p(x)$, and $|\{x : \neg p(x)\}| = |\alpha| - |\{x : p(x)\}|$.

*Proof.* The map that sends an element of the subtype to the underlying element of $\alpha$ is injective, and its image is the filter $\{x \in U : p(x)\}$ of the finset $U$ of all elements. So the two cards agree. For the second claim, $U$ is the disjoint union of the filter by $p$ and the filter by $\neg p$, so the two cards add up to $|\alpha|$. $\square$

::: mathlib
`Fintype.card_subtype` · `Mathlib.Data.Fintype.Card`

The statement is `Fintype.card {x // p x} = {x | p x}.card`, where the right side is the filter of `Finset.univ`, written with the set builder notation for finsets. The complement rule is `Fintype.card_subtype_compl`. It uses truncated subtraction in `ℕ`, which is harmless here because the subtracted card is at most `Fintype.card α`.

<?decl Fintype.card_subtype?>
:::

### Examples

**Example (Passwords).** A password of three distinct letters from an alphabet of $26$ letters is an injection $\mathrm{Fin}\ 3 \to \mathrm{Fin}\ 26$. The number is $26^{\underline{3}} = 26 \cdot 25 \cdot 24 = 15600$. With repetitions allowed the count is $26^3 = 17576$. So $17576 - 15600 = 1976$ words of length three have a repeated letter.

**Example (Injections between small types).** The number of injections $\mathrm{Fin}\ 3 \to \mathrm{Fin}\ 5$ is $5 \cdot 4 \cdot 3 = 60$. By the theorem on injections and subsets, $60 = 3! \binom{5}{3} = 6 \cdot 10$. The number of injections $\mathrm{Fin}\ 5 \to \mathrm{Fin}\ 3$ is $3^{\underline{5}} = 3 \cdot 2 \cdot 1 \cdot 0 \cdot (-1)$ by the formula over the integers, which is $0$. This agrees with the pigeonhole principle. In `ℕ` the factor $3 - 3 = 0$ appears first, and the result is $0$ again.

**Example (Permutations of four letters).** $|\mathrm{Perm}(\mathrm{Fin}\ 4)| = 4! = 24$. A check by the type of the cycles: one identity, $\binom{4}{2} = 6$ transpositions, $3$ products of two disjoint transpositions, $8$ cycles of length three ($4$ choices of the fixed point, $2$ orders of the other three), and $6$ cycles of length four. The sum is $1 + 6 + 3 + 8 + 6 = 24$.

**Example (Bijections between two types).** The number of bijections from $\mathrm{Bool} \times \mathrm{Bool}$ to $\mathrm{Fin}\ 4$ is $4! = 24$. The number of bijections from $\mathrm{Fin}\ 4$ to $\mathrm{Fin}\ 5$ is $0$, since the cards differ. The general formula `Fintype.card_equiv` needs one bijection as input, and in the second case none exists.

**Example (Strong pigeonhole).** A class has $25$ students. The map from the students to the $12$ months has $25 > 2 \cdot 12$, so some month holds the birthday of at least $3$ students. For $37$ students, $37 > 3 \cdot 12$ gives a month with at least $4$. For $36$ students the bound fails: three birthdays in each month is possible.

**Example (A subtype).** The subtype of the $x \in \mathrm{Fin}\ 10$ with $x$ even has $5$ elements, namely $0, 2, 4, 6, 8$. The complement rule gives $10 - 5 = 5$ odd elements. The subtype of the $f : \mathrm{Fin}\ 3 \to \mathrm{Bool}$ with $f(0) = \mathrm{true}$ has $4$ elements, since the other two values are free, and its complement has $8 - 4 = 4$.

**Counterexample (The infinite case).** On $\mathbb{N}$, the map $n \mapsto n + 1$ is injective but not surjective, since no $n$ goes to $0$. The map $n \mapsto \lfloor n / 2 \rfloor$ is surjective but not injective, since $0$ and $1$ both go to $0$. So the theorem on injective and surjective maps needs a finite type. It also needs the same type at both ends: the inclusion $\mathrm{Fin}\ 3 \to \mathrm{Fin}\ 4$ is injective and not surjective.

### Common errors

A learner who counts injections often multiplies $n (n - 1) \cdots$ with one factor too many or too few. The count of factors is the card of the domain, $k$, and the last factor is $n - k + 1$. The check $k = 1$, with $n$ injections, fixes the count.

A second error is to use `Fintype.card_perm` for the bijections between two different types. The lemma is for `Equiv.Perm α`, the maps from a type to itself. For two types, use `Fintype.card_equiv`, which needs an equivalence as its argument.

A third error is to state the strong pigeonhole principle with a division, as $|\alpha| / |\beta|$. In `ℕ`, the division rounds down, and the form with a product, $m |\beta| < |\alpha|$, is the form that Mathlib uses and that `omega` can prove.

### The library around it

The file `Mathlib.Data.Fintype.Perm` builds the list of all permutations of a list and the instance `Fintype (Equiv.Perm α)`, and it proves `Fintype.card_perm` and `Fintype.card_equiv`. The file `Mathlib.Data.Fintype.CardEmbedding` proves `Fintype.card_embedding_eq` by the induction principle `Fintype.induction_empty_option`, which is the proof by induction above in the form "add one new element". It also proves `Fintype.card_embedding_eq_of_infinite`: there are no embeddings of an infinite type in a finite type. The file `Mathlib.Data.Fintype.BigOperators` counts the dependent functions with `Fintype.card_pi` and the dependent pairs with `Fintype.card_sigma`, and it states the rule for functions `Fintype.card_fun` of Section 1. The fiber rule for finsets is `Finset.card_eq_sum_card_fiberwise`, which Chapter 6 places among the sums. The reference table lists the declarations of the section.

The file `Mathlib.Data.Finite.Perm` states the count of permutations with `Nat.card`, for a type with only an instance `Finite`: `Nat.card_perm` says that $|\mathrm{Perm}\ \alpha| = |\alpha|!$. It also gives two facts about the group of permutations. The lemma `Equiv.Perm.isMulCommutative_iff_card_le_two` says that this group is commutative exactly when $|\alpha| \le 2$, and `Equiv.Perm.isCyclic_iff_card_le_two` says the same for the property of being cyclic. For $|\alpha| \ge 3$, take three distinct elements $a, b, c$. The transpositions $(a\ b)$ and $(b\ c)$ do not commute, so the group is not commutative, and so it is not cyclic. For $|\alpha| \le 2$, the group has at most $2$ elements, and a group of order $1$ or $2$ is cyclic.

### Exercises

1. (A) Compute the number of injections $\mathrm{Fin}\ 4 \to \mathrm{Fin}\ 7$ and check it against $4! \binom{7}{4}$.
2. (A) Compute the number of bijections from $\mathrm{Option}\ (\mathrm{Fin}\ 2)$ to $\mathrm{Bool} \oplus \mathrm{Unit}$.
3. (A) A drawer holds socks of $5$ colours. How many socks must one take, in the dark, to be sure of $3$ socks of one colour?
4. (B) Prove that a surjective map $f : \alpha \to \beta$ of finite types with $|\alpha| = |\beta|$ is injective. Hint: compose with a bijection $\beta \to \alpha$.
5. (B) Prove that the number of maps $f : \mathrm{Fin}\ n \to \mathrm{Fin}\ n$ that are not injective is $n^n - n!$, and compute it for $n = 3$.
6. (B) Prove the formula for the injections by a sum over the fibers of the map $f \mapsto f(0)$ in place of the restriction.
7. (B) A permutation $\sigma$ with $\sigma \circ \sigma = \mathrm{id}$ is an involution. Count the involutions of $\mathrm{Fin}\ 4$. Hint: classify them by the number of transpositions.
8. (C) Let $D_n$ be the number of permutations of $\mathrm{Fin}\ n$ with no fixed point. Prove $D_{n+1} = n (D_n + D_{n-1})$ for $n \ge 1$, and compute $D_4 = 9$. Hint: look at $\sigma(n)$ and at whether $\sigma$ swaps $n$ and $\sigma(n)$.
9. (C) Prove that each sequence of $n^2 + 1$ distinct real numbers has a monotone subsequence of length $n + 1$ (Erdős-Szekeres). Hint: label each term with the length of the longest increasing subsequence that starts there, and apply the strong pigeonhole principle to the labels.

### Notes and history

The count $n!$ of the arrangements of $n$ objects is old. It appears in the Sefer Yetzirah, and Bhaskara II gave the falling factorial for the arrangements of $k$ of $n$ objects in the twelfth century. The notation $n^{\underline{k}}$ for the falling factorial is the one of *Concrete Mathematics* by Graham, Knuth and Patashnik. The equivalence of injective and surjective for self-maps of a finite set is the base of the definition of a finite set by Dedekind, which Chapter 5 states. The theorem of Erdős and Szekeres is from 1935.

In Mathlib, the file `Mathlib.Data.Fintype.CardEmbedding` is by Eric Rodriguez, and the files on permutations come from the Lean 3 library, by Mario Carneiro. The strong pigeonhole principle, in `Mathlib.Combinatorics.Pigeonhole`, has many variants for weighted sums. MIL counts permutations and subsets in its chapter on combinatorics.

### Reference

<?reference?>
