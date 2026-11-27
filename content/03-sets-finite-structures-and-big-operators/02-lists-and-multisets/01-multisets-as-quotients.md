---
title: Multisets as a quotient of lists
kind: theory
modules:
  - Mathlib.Data.Multiset.Defs
explains:
  E3: [Multiset, Multiset.coe_eq_coe]
  E2: [Multiset.card, Multiset.count, Multiset.cons_swap, Multiset.card_add, Multiset.count_add]
  E1: auto
families: []
requires: [V01.C02, V03.C01]
reads_with: ["MIL", "TPIL"]
lean:
  - MathlibHandbook/V03/C02/Examples.lean
  - MathlibHandbook/V03/C02/Exercises.lean
  - MathlibHandbook/V03/C02/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Multisets as a quotient of lists

### Overview

A list $[1, 2, 2]$ has an order, and it can repeat an element. A set $\{1, 2\}$ has no order and no repetition. Between the two there is a third kind of finite collection: a collection with repetition and with no order. This is a multiset, sometimes called a bag. The roots of the polynomial $(x - 1)(x - 2)^2$ form the multiset $\{1, 2, 2\}$: the root $2$ counts twice, and there is no first root. The prime factors of $12$ form the multiset $\{2, 2, 3\}$. The sum of the elements of a finite collection does not depend on an order, but it does depend on the repetitions.

There are two standard ways to define a multiset. The first one is a function $m : \alpha \to \mathbb{N}$ with finite support, which gives the multiplicity of each element. The second one is a list up to a change of order. Mathlib takes the second way: `Multiset α` is the quotient of the type `List α` by the relation "is a permutation of". This section explains that definition. It proves that the permutation relation is an equivalence relation, that a function on lists that does not see the order passes to multisets, and that two multisets are equal exactly when each element has the same multiplicity in both. So the two definitions give the same objects. After this section the reader can compute with multisets, can prove a statement about all multisets by induction, and knows why the finsets of Chapter 3 and the sums of Chapter 6 rest on this type.

### Definitions

**Definition (List).** A list of elements of $\alpha$ is either the empty list $[\,]$ or $a :: l$, an element $a$ followed by a list $l$. The list $[a_1, a_2, a_3]$ is $a_1 :: a_2 :: a_3 :: [\,]$. The length and the count of an element are given by recursion: $$|[\,]| = 0, \quad |a :: l| = |l| + 1, \qquad \#_b [\,] = 0, \quad \#_b (a :: l) = \#_b l + [a = b],$$ where $[a = b]$ is $1$ if $a = b$ and $0$ otherwise.

**Definition (Permutation).** The relation $l_1 \sim l_2$, "$l_1$ is a permutation of $l_2$", is the least relation on lists with the four rules: $[\,] \sim [\,]$; if $l_1 \sim l_2$ then $a :: l_1 \sim a :: l_2$; $a :: b :: l \sim b :: a :: l$; and if $l_1 \sim l_2$ and $l_2 \sim l_3$ then $l_1 \sim l_3$.

*Remarks.* The definition says that $l_1 \sim l_2$ when one can go from $l_1$ to $l_2$ by a finite number of swaps of two adjacent elements. This is the same as the usual definition "there is a bijection $\sigma$ of the positions with $l_2[i] = l_1[\sigma(i)]$", because each permutation of a finite set is a product of adjacent transpositions. The inductive form is better for proofs, because each proof about $\sim$ is an induction on the four rules.

**Definition (Multiset).** The type of multisets of $\alpha$ is the quotient $$\operatorname{Multiset}(\alpha) = \operatorname{List}(\alpha) / {\sim}.$$ The class of a list $l$ is written $\langle l \rangle$, or simply $l$ when no confusion is possible. The empty multiset is $0 = \langle [\,] \rangle$, and $a ::_m \langle l \rangle = \langle a :: l \rangle$ adds one copy of $a$.

**Definition (Card, count, membership and sum).** For a multiset $m = \langle l \rangle$, the card $|m|$ is $|l|$, the count $\#_b m$ is $\#_b l$, and $b \in m$ means that $b$ occurs in $l$. The sum of two multisets is $\langle l_1 \rangle + \langle l_2 \rangle = \langle l_1 \mathbin{+\!\!+} l_2 \rangle$, the class of the concatenation.

*Remarks.* Each of these definitions chooses a list in the class, so each one needs a proof that the result does not depend on the choice. These proofs are the theorems below. The sum of multisets is not the union of sets: $\{1, 2\} + \{2, 3\} = \{1, 2, 2, 3\}$, and the count of $2$ is $2$.

::: mathlib
`Multiset` · `Mathlib.Data.Multiset.Defs`

`Multiset α` is `Quotient (List.isSetoid α)`, where the setoid is the permutation relation `List.Perm`, written `l₁ ~ l₂`. The coercion `(l : Multiset α)` is `Quot.mk _ l`, and the lemma `Multiset.quot_mk_to_coe` rewrites one form into the other. The notation `{1, 2, 2}` builds a multiset with `insert`, which for multisets is `::ₘ`, so it keeps the repetitions. A proof about all multisets often starts with `induction m using Multiset.induction_on`, or with `Quotient.inductionOn m` to work with a list.

<?decl Multiset?>
:::

::: mathlib
`Multiset.card` · `Mathlib.Data.Multiset.Defs`

The card is a function `Multiset α → ℕ`, defined with `Quot.liftOn` from `List.length` and the proof that a permutation keeps the length. The lemma `Multiset.coe_card` says that `card (l : Multiset α) = l.length`.

<?decl Multiset.card?>
:::

::: mathlib
`Multiset.count` · `Mathlib.Data.Multiset.Count`

`Multiset.count a m` needs `DecidableEq α`, because it compares `a` with each element. Over `ℕ`, `ℤ` or a `Fin n` the instance exists, and `decide` computes counts of small multisets.

<?decl Multiset.count?>
:::

### Theorems and proofs

**Theorem (The permutation relation is an equivalence).** The relation $\sim$ on lists is reflexive, symmetric and transitive.

*Proof.* Transitivity is one of the four rules. For reflexivity, prove $l \sim l$ by induction on $l$: $[\,] \sim [\,]$ is a rule, and $l \sim l$ gives $a :: l \sim a :: l$ by the rule for cons. For symmetry, prove that $l_1 \sim l_2$ implies $l_2 \sim l_1$ by induction on the proof of $l_1 \sim l_2$. The rule $[\,] \sim [\,]$ is its own reverse. If the last step is $a :: l_1 \sim a :: l_2$ from $l_1 \sim l_2$, the induction hypothesis gives $l_2 \sim l_1$, and the cons rule gives $a :: l_2 \sim a :: l_1$. The swap $a :: b :: l \sim b :: a :: l$ has the reverse $b :: a :: l \sim a :: b :: l$, which is again a swap. If the last step is transitivity from $l_1 \sim l_2$ and $l_2 \sim l_3$, the hypotheses give $l_2 \sim l_1$ and $l_3 \sim l_2$, and transitivity gives $l_3 \sim l_1$. $\square$

**Theorem (Equality of multisets).** For lists $l_1$ and $l_2$, $\langle l_1 \rangle = \langle l_2 \rangle$ if and only if $l_1 \sim l_2$.

*Proof.* This is the basic property of the quotient by an equivalence relation: two elements have the same class if and only if they are related. By the theorem of Chapter 1 on equivalence classes, the classes of related elements are equal, and two equal classes contain related elements. $\square$

::: mathlib
`Multiset.coe_eq_coe` · `Mathlib.Data.Multiset.Defs`

The statement that two lists give the same multiset if and only if they are permutations. For lists of numbers `List.Perm` is decidable, so after `rw [Multiset.coe_eq_coe]` the tactic `decide` can check a concrete case. The lemma is the special case for lists of `Quotient.eq`.

<?decl Multiset.coe_eq_coe?>
:::

**Theorem (Functions on multisets).** Let $F : \operatorname{List}(\alpha) \to X$ be a function such that $l_1 \sim l_2$ implies $F(l_1) = F(l_2)$. Then there is a unique function $\bar F : \operatorname{Multiset}(\alpha) \to X$ with $\bar F(\langle l \rangle) = F(l)$ for each list $l$.

*Proof.* Each multiset is a class $\langle l \rangle$ for some list $l$. Put $\bar F(\langle l \rangle) = F(l)$. If $\langle l \rangle = \langle l' \rangle$ then $l \sim l'$ by the previous theorem, so $F(l) = F(l')$, and the value does not depend on the choice of $l$. The uniqueness holds because each multiset is the class of a list, so the condition $\bar F(\langle l \rangle) = F(l)$ fixes $\bar F$ on each multiset. $\square$

**Theorem (Card and count are well defined).** If $l_1 \sim l_2$ then $|l_1| = |l_2|$ and $\#_b l_1 = \#_b l_2$ for each $b$.

*Proof.* Use induction on the proof of $l_1 \sim l_2$. For $[\,] \sim [\,]$ there is nothing to prove. For the cons rule, $|a :: l_1| = |l_1| + 1 = |l_2| + 1 = |a :: l_2|$, and the count is the same with $[a = b]$ in place of $1$. For a swap, both lists have the length $|l| + 2$, and the count $\#_b l + [a = b] + [c = b]$ for the elements $a$ and $c$ of the swap, in both orders. For transitivity, equalities compose. $\square$

So, by the theorem on functions on multisets, the card and the count of a multiset are defined. The same argument shows that the membership and the sum of two multisets are well defined.

**Theorem (Cons commutes).** For all $a$, $b$ and $m$, $a ::_m b ::_m m = b ::_m a ::_m m$.

*Proof.* Take a list $l$ with $m = \langle l \rangle$. The two sides are $\langle a :: b :: l \rangle$ and $\langle b :: a :: l \rangle$. The two lists are related by the swap rule, so the classes are equal. $\square$

::: mathlib
`Multiset.cons_swap` · `Mathlib.Data.Multiset.ZeroCons`

The swap of two `cons` steps. It is the rule that a function defined by recursion on multisets must respect. For example, the fold `Multiset.foldr f` asks for an instance `LeftCommutative f`, which says that `f a (f b x) = f b (f a x)`. This is the reason why the product of a multiset needs a commutative monoid.

<?decl Multiset.cons_swap?>
:::

**Theorem (Card and count of a sum).** For multisets $s$ and $t$, $|s + t| = |s| + |t|$, and $\#_b(s + t) = \#_b s + \#_b t$ for each $b$.

*Proof.* Take lists $l_1$ and $l_2$ with $s = \langle l_1 \rangle$ and $t = \langle l_2 \rangle$. Then $s + t = \langle l_1 \mathbin{+\!\!+} l_2 \rangle$. Prove $|l_1 \mathbin{+\!\!+} l_2| = |l_1| + |l_2|$ by induction on $l_1$. For $l_1 = [\,]$, both sides are $|l_2|$. For $l_1 = a :: l$, $|(a :: l) \mathbin{+\!\!+} l_2| = |a :: (l \mathbin{+\!\!+} l_2)| = |l \mathbin{+\!\!+} l_2| + 1$, and by the induction hypothesis this is $|l| + |l_2| + 1 = |a :: l| + |l_2|$. The count is the same, with $[a = b]$ in place of $1$. $\square$

::: mathlib
`Multiset.card_add` · `Mathlib.Data.Multiset.AddSub`

The card is additive. It is a `simp` lemma, so `simp` computes the card of a sum. The count form is `Multiset.count_add`, in the same file.

<?decl Multiset.card_add?>
:::

::: mathlib
`Multiset.count_add` · `Mathlib.Data.Multiset.AddSub`

The count of an element in a sum is the sum of the counts. The counts determine the multiset, by the next theorem, so the identity says that the sum of multisets is the sum of the multiplicity functions.

<?decl Multiset.count_add?>
:::

**Theorem (A multiset is determined by its counts).** Let $\alpha$ have decidable equality. Two multisets $s$ and $t$ of $\alpha$ are equal if and only if $\#_b s = \#_b t$ for each $b \in \alpha$.

*Proof.* If $s = t$ the counts are equal. For the converse, take lists $l_1$ and $l_2$ of $s$ and $t$. The plan is to show $l_1 \sim l_2$ by induction on $l_1$, for all $l_2$ at once.

If $l_1 = [\,]$, each count of $l_2$ is $0$, so no element occurs in $l_2$, and $l_2 = [\,]$.

If $l_1 = a :: l$, then $\#_a l_2 = \#_a l_1 \ge 1$, so $a$ occurs in $l_2$. Let $l_2'$ be $l_2$ with the first copy of $a$ removed. Move that copy to the front by adjacent swaps: this gives $l_2 \sim a :: l_2'$. The counts of $l_2'$ are those of $l_2$, minus $1$ at $a$. The counts of $l$ are those of $l_1$, minus $1$ at $a$. So $l$ and $l_2'$ have the same counts, and the induction hypothesis gives $l \sim l_2'$. The cons rule gives $a :: l \sim a :: l_2'$, and transitivity gives $l_1 \sim l_2$. $\square$

This theorem connects the two definitions of a multiset. A multiset of $\alpha$ is the same as a function $\alpha \to \mathbb{N}$ that is zero outside a finite set: the map is $m \mapsto (b \mapsto \#_b m)$, it is injective by the theorem, and each such function is the count function of the list that repeats each $b$ in the support $\#_b$ times. Chapter 7 makes this precise with `Multiset.toFinsupp`.

::: mathlib
`Multiset.ext` · `Mathlib.Data.Multiset.Count`

The extensionality of multisets: `s = t ↔ ∀ a, count a s = count a t`. The one-direction form `Multiset.ext'` is the one to `apply`. Then the goal is an equality of numbers for each `a`, and the lemmas `Multiset.count_add`, `Multiset.count_cons_self` and `Multiset.count_cons_of_ne` compute each side.

<?decl Multiset.ext?>
:::

### Examples

**Example (A permutation).** The lists $[1, 2, 3]$ and $[3, 1, 2]$ give the same multiset. Two swaps do the work: $[3, 1, 2] \sim [1, 3, 2] \sim [1, 2, 3]$.

<?lean MathlibHandbook/V03/C02/Examples.lean#coe_eq?>

**Example (Cons commutes).**

<?lean MathlibHandbook/V03/C02/Examples.lean#cons_swap?>

**Example (Multiplicity).** The multiset $\{1, 1, 2\}$ has two copies of $1$, one copy of $2$, and card $3$. It differs from the multiset $\{1, 2\}$, which has the same elements but card $2$. As sets the two are equal.

<?lean MathlibHandbook/V03/C02/Examples.lean#count?>

**Example (The card of a sum).** For $s = \{1, 2\}$ and $t = \{2, 3, 3\}$, $s + t = \{1, 2, 2, 3, 3\}$ has card $5 = 2 + 3$. The counts are $\#_1 = 1$, $\#_2 = 1 + 1 = 2$ and $\#_3 = 0 + 2 = 2$.

<?lean MathlibHandbook/V03/C02/Examples.lean#card_add?>

**Example (Counting multisets).** The multisets of card $2$ with elements in $\{a, b, c\}$ are $$\{a, a\}, \{a, b\}, \{a, c\}, \{b, b\}, \{b, c\}, \{c, c\},$$ six in all. In general a multiset of card $k$ on $n$ elements is a choice of counts $c_1 + \cdots + c_n = k$ with $c_i \ge 0$. Write $k$ stars and $n - 1$ bars in a row: the stars before the first bar give $c_1$, the stars between the first and the second bar give $c_2$, and so on. A row is a choice of the $n - 1$ places of the bars among $n + k - 1$ places, so the number is $\binom{n + k - 1}{k}$. For $n = 3$, $k = 2$ this is $\binom{4}{2} = 6$. Mathlib has the type of these multisets as `Sym α k`.

**Counterexample (A function that sees the order).** The function "the first element of a list" does not pass to multisets. The lists $[1, 2]$ and $[2, 1]$ are permutations of each other, but their first elements are $1$ and $2$. So the hypothesis of the theorem on functions on multisets fails, and there is no "first element of a multiset".

**Counterexample (A product with no order).** The product of a multiset needs a commutative monoid. For $2 \times 2$ matrices $A = \begin{pmatrix} 1 & 1 \\ 0 & 1 \end{pmatrix}$ and $B = \begin{pmatrix} 1 & 0 \\ 1 & 1 \end{pmatrix}$, $AB = \begin{pmatrix} 2 & 1 \\ 1 & 1 \end{pmatrix}$ and $BA = \begin{pmatrix} 1 & 1 \\ 1 & 2 \end{pmatrix}$. So the product of the lists $[A, B]$ and $[B, A]$ differ, and `List.prod` gives no function on the multisets of matrices.

### Common errors

A learner often reads `{1, 1, 2}` as a set. For a multiset it has card $3$; for a finset Lean removes the repetition and the card is $2$. A second error is to define a function on multisets by a pattern match on a list, with no proof that the result respects permutations. Lean refuses this definition, and the fix is `Quot.liftOn` with the proof, or a definition from functions that already exist, such as `Multiset.map` and `Multiset.foldr`. A third error is to confuse the sum `s + t` with the union `s ∪ t`: the union takes the maximum of the counts, the sum takes their sum.

### The library around it

The basic API of multisets comes in families. The membership lemmas `Multiset.mem_cons`, `Multiset.mem_add` and `Multiset.mem_coe` say when an element is in a multiset. The card lemmas `Multiset.card_cons`, `Multiset.card_add`, `Multiset.coe_card` and `Multiset.card_eq_zero` compute the card. The count lemmas `Multiset.count_cons_self`, `Multiset.count_cons_of_ne`, `Multiset.count_add`, `Multiset.count_eq_zero` and `Multiset.count_pos` compute the count, and `Multiset.count_le_card` bounds it. `Multiset.ext` and `Multiset.le_iff_count` reduce equality and the order `s ≤ t` to the counts. The induction principles are `Multiset.induction_on` and `Multiset.induction`. The multiset `Multiset.range n` holds the numbers below `n` once each, and `Multiset.replicate n a` holds `n` copies of `a`. The operations of the next section, `Multiset.map`, `Multiset.filter`, `Multiset.sum` and `Multiset.dedup`, are built on this base. The table at the end lists the declarations of the section.

### Exercises

1. (A) Give the card and the count of $2$ for the multiset $\{2, 3, 2, 2\}$, and write it as $\langle l \rangle$ for two different lists $l$.
2. (A) Explain why the function "the first element of a list" does not give a function on multisets, and why "the largest element of a nonempty list of natural numbers" does.
3. (A) List the multisets of card $3$ with elements in $\{0, 1\}$, and check the formula $\binom{n + k - 1}{k}$.
4. (B) Show that the count of $a$ in $m$ is at most the card of $m$. Hint: induction on a list of $m$.
5. (B) Show that $\#_b(s \cup t) = \max(\#_b s, \#_b t)$ is a valid definition of a union of multisets, and give $s \cup t$ and $s + t$ for $s = \{1, 1, 2\}$ and $t = \{1, 3\}$.
6. (B) Show by the rules of the permutation relation that $l \mathbin{+\!\!+} l' \sim l' \mathbin{+\!\!+} l$. Deduce that the sum of multisets is commutative.
7. (C) Prove the equality of the two definitions of a permutation: $l_1 \sim l_2$ if and only if $|l_1| = |l_2| = n$ and there is a bijection $\sigma$ of $\{0, \ldots, n - 1\}$ with $l_2[i] = l_1[\sigma(i)]$ for each $i$.
8. (L) Prove that the card of `a ::ₘ m` is the card of `m` plus one. The solution is `card_cons_example`.
9. (L) Prove that `a ::ₘ m` has one more copy of `a` than `m`. The solution is `count_cons_self_example`.
10. (L) Prove that `a` is an element of `a ::ₘ m`. The solution is `mem_cons_example`.
11. (L) Prove that the count in a sum is the sum of the counts. The solution is `count_add_example`.

### Notes and history

Multisets are old in algebra, as the multiset of the roots of a polynomial and the multiset of the prime factors of a number, and the word became standard through Knuth, *The Art of Computer Programming*, Volume 2, Section 4.6.3, who credits it to de Bruijn. The stars and bars count of multisets is in Feller, *An Introduction to Probability Theory and Its Applications*, Volume 1 (1950), Section II.5.

The construction of multisets as a quotient of lists was written by Mario Carneiro for the first library of Lean 3 in 2017. It uses the quotient types of the kernel of Lean, which TPIL explains in its chapter on axioms. The same construction makes finsets, so a finset is a multiset with a proof that it has no repeated element. In Mathlib the file `Mathlib/Data/Multiset/Basic.lean` was later split into `Defs`, `ZeroCons`, `AddSub`, `Count` and other files, so that a file can import only the part it needs.

### Reference

<?reference?>
