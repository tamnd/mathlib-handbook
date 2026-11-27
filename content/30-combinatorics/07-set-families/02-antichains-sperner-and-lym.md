---
title: Antichains, the LYM inequality and Sperner's theorem
kind: theory
modules:
  - Mathlib.Combinatorics.SetFamily.LYM
  - Mathlib.Combinatorics.KatonaCircle
explains:
  E3: [Finset.local_lubell_yamamoto_meshalkin_inequality_mul, Finset.lubell_yamamoto_meshalkin_inequality_sum_card_div_choose, IsAntichain.sperner, Finset.falling, Numbering, Numbering.prefixed]
  E2: [Finset.local_lubell_yamamoto_meshalkin_inequality_div, Finset.card_mul_le_card_shadow_mul, Finset.card_div_choose_le_card_shadow_div_choose, Finset.lubell_yamamoto_meshalkin_inequality_sum_inv_choose, Finset.sum_card_slice_div_choose_le_one, Finset.mem_falling, Finset.sized_falling, Finset.slice_subset_falling, Finset.falling_zero_subset, Finset.slice_union_shadow_falling_succ, Finset.IsAntichain.disjoint_slice_shadow_falling, Finset.le_card_falling_div_choose, Numbering.IsPrefix, Numbering.mem_prefixed, Numbering.IsPrefix.subset_of_card_le_card, Numbering.card_prefixed, Numbering.dens_prefixed, Numbering.disjoint_prefixed_prefixed, Numbering.prefixedEquiv, Fintype.card_numbering]
  E1: auto
families: []
requires: [V03.C03, V03.C04, V03.C06, V04.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Antichains, the LYM inequality and Sperner's theorem

### Overview

An antichain of subsets of an $n$-set is a family in which no member contains another. The family of all $r$-sets is an antichain, and the largest one is at the middle level $r = \lfloor n/2 \rfloor$. Sperner's theorem says that no antichain is larger. The LYM inequality is a stronger statement: it gives each member $A$ the weight $1/\binom{n}{|A|}$ and says that the weights of an antichain add up to at most $1$.

The section proves the LYM inequality twice. The first proof counts orderings of the ground set: each ordering has a chain of initial segments, and a chain meets an antichain at most once. The second proof uses shadows and the local LYM inequality, which compares an $r$-uniform family with its shadow. Mathlib uses the second proof, and its file `KatonaCircle` holds the tools of the first.

### Definitions

Fix a finite set $X$ with $n$ elements. A *chain* is a family totally ordered by inclusion. An *antichain* is a family $\mathcal{A}$ with $A \not\subseteq B$ for any two distinct members. The *slice* $\mathcal{A}_r$ is the family of the members of size $r$.

::: mathlib
`IsAntichain` · `Mathlib.Order.Antichain`

An antichain of finsets is `IsAntichain (· ⊆ ·) (𝒜 : Set (Finset α))`. The predicate is for any relation on any type and lives in the files on orders (Volume 4, Chapter 1). The slice $\mathcal{A}_r$ is `𝒜 # r`, the finset `Finset.slice 𝒜 r` of `Mathlib.Data.Finset.Slice`.

<?decl IsAntichain?>
:::

**Definition (Numbering and prefix).** A *numbering* of $X$ is a bijection $f : X \to \{0, 1, \ldots, n-1\}$. A set $A \subseteq X$ is a *prefix* of $f$ when $A = f^{-1}(\{0, \ldots, |A| - 1\})$, that is, $x \in A$ exactly when $f(x) < |A|$.

There are $n!$ numberings. The prefixes of one numbering $f$ form a chain $\emptyset \subset A_1 \subset \cdots \subset A_n = X$ with $|A_k| = k$. Of two prefixes of $f$, the smaller one is contained in the larger one.

::: mathlib
`Numbering` · `Mathlib.Combinatorics.KatonaCircle`

`Numbering X` is `X ≃ Fin (Fintype.card X)`, and `Fintype.card_numbering` counts $n!$ of them. `f.IsPrefix s` is `∀ x, x ∈ s ↔ f x < #s`, and `Numbering.prefixed s` is the finset of the numberings with prefix `s`. The file has the name of the cyclic orders of Katona, but it works with numberings, which are linear orders. Section 3 uses cyclic orders on paper.

<?decl Numbering?>
:::

**Definition (Falling family).** For an antichain $\mathcal{A}$ and $k \le n$, the *falling family* $\mathcal{F}_k(\mathcal{A})$ is the family of the $k$-sets contained in some member of $\mathcal{A}$.

So $\mathcal{F}_k$ is $k$-uniform, it contains the slice $\mathcal{A}_k$, and $\mathcal{F}_0 \subseteq \{\emptyset\}$.

::: mathlib
`Finset.falling` · `Mathlib.Combinatorics.SetFamily.LYM`

`Finset.falling k 𝒜` is `𝒜.sup (powersetCard k)`. `Finset.mem_falling` says that `s ∈ falling k 𝒜` if and only if `s ⊆ t` for some `t ∈ 𝒜` and `#s = k`. The definition does not need the antichain condition. The lemmas that use it ask for it.

<?decl Finset.falling?>
:::

### Theorems and proofs

**Lemma (Prefixes).** Let $A \subseteq X$ with $|A| = k$. Exactly $k!\,(n-k)!$ numberings of $X$ have $A$ as a prefix. If neither of $A, B$ contains the other, no numbering has both as prefixes.

*Proof.* A numbering with prefix $A$ maps $A$ onto $\{0, \ldots, k-1\}$ and $X \setminus A$ onto $\{k, \ldots, n-1\}$. It is a pair of bijections, with $k!$ choices for the first and $(n-k)!$ for the second. Two prefixes of one numbering are comparable, as noted above. $\square$

**Theorem (LYM inequality).** Let $\mathcal{A}$ be an antichain of subsets of an $n$-set. Then $$\sum_{A \in \mathcal{A}} \frac{1}{\binom{n}{|A|}} = \sum_{r=0}^{n} \frac{|\mathcal{A}_r|}{\binom{n}{r}} \le 1.$$

*First proof.* Count the pairs $(f, A)$ with $f$ a numbering, $A \in \mathcal{A}$ and $A$ a prefix of $f$. By the lemma, each numbering has at most one member of $\mathcal{A}$ as a prefix, so there are at most $n!$ pairs. Each $A \in \mathcal{A}$ is a prefix of $|A|!\,(n - |A|)!$ numberings. So $$\sum_{A \in \mathcal{A}} |A|!\,(n - |A|)! \le n!.$$ Divide by $n!$, and note $|A|!\,(n-|A|)!/n! = 1/\binom{n}{|A|}$. $\square$

The second proof rests on a lemma on one level.

**Theorem (Local LYM inequality).** Let $\mathcal{A}$ be an $r$-uniform family on an $n$-set with $1 \le r \le n$. Then $$|\mathcal{A}|\, r \le |\partial \mathcal{A}|\,(n - r + 1), \qquad \text{so} \qquad \frac{|\mathcal{A}|}{\binom{n}{r}} \le \frac{|\partial \mathcal{A}|}{\binom{n}{r-1}}.$$

*Proof.* Count the pairs $(A, B)$ with $A \in \mathcal{A}$, $B \in \partial \mathcal{A}$ and $B \subset A$. Each $A$ has exactly $r$ subsets of size $r - 1$, all in $\partial \mathcal{A}$. So there are $|\mathcal{A}|\, r$ pairs. Each $B \in \partial \mathcal{A}$ has $n - r + 1$ supersets of size $r$, one for each point outside $B$, and at most that many are in $\mathcal{A}$. So there are at most $|\partial \mathcal{A}|\,(n - r + 1)$ pairs. This is double counting as in Volume 3, Chapter 6. For the second form, divide by $r \binom{n}{r} = (n - r + 1)\binom{n}{r-1}$. Both sides of this identity equal $n!/((r-1)!\,(n-r)!)$. $\square$

::: mathlib
`Finset.local_lubell_yamamoto_meshalkin_inequality_mul` · `Mathlib.Combinatorics.SetFamily.LYM`

The statement is `#𝒜 * r ≤ #(∂ 𝒜) * (Fintype.card α - r + 1)` for `Set.Sized r 𝒜`, in `ℕ`. Its alias is `Finset.card_mul_le_card_shadow_mul`. The form with quotients, `Finset.local_lubell_yamamoto_meshalkin_inequality_div`, needs `r ≠ 0` and an ordered semifield `𝕜`, since division in `ℕ` rounds down. The proof calls `Finset.card_mul_le_card_mul'` of the double counting file.

<?decl Finset.local_lubell_yamamoto_meshalkin_inequality_mul?>
:::

*Second proof of the LYM inequality.* Write $\mathcal{F}_k$ for $\mathcal{F}_k(\mathcal{A})$. Claim: for $0 \le k \le n$, $$\sum_{r=k}^{n} \frac{|\mathcal{A}_r|}{\binom{n}{r}} \le \frac{|\mathcal{F}_k|}{\binom{n}{k}}.$$ The proof is by descending induction on $k$. For $k = n$, $\mathcal{F}_n = \mathcal{A}_n$, since the only $n$-set is $X$ itself. For the step from $k + 1$ to $k$, note two facts. First, $\mathcal{F}_k = \mathcal{A}_k \cup \partial \mathcal{F}_{k+1}$: a $k$-set inside a member $C$ of $\mathcal{A}$ is either $C$ itself or a set $C' \setminus \{c\}$ with $C' \in \mathcal{F}_{k+1}$. Second, the union is disjoint: if $A \in \mathcal{A}_k$ and $A \subset B \subseteq C$ with $C \in \mathcal{A}$, then $A \subsetneq C$, which the antichain condition forbids. With the local LYM inequality for the $(k+1)$-uniform family $\mathcal{F}_{k+1}$ and the induction hypothesis, $$\frac{|\mathcal{F}_k|}{\binom{n}{k}} = \frac{|\mathcal{A}_k|}{\binom{n}{k}} + \frac{|\partial \mathcal{F}_{k+1}|}{\binom{n}{k}} \ge \frac{|\mathcal{A}_k|}{\binom{n}{k}} + \frac{|\mathcal{F}_{k+1}|}{\binom{n}{k+1}} \ge \sum_{r=k}^{n} \frac{|\mathcal{A}_r|}{\binom{n}{r}}.$$ At $k = 0$, $|\mathcal{F}_0| \le 1$ and $\binom{n}{0} = 1$, which gives the theorem. $\square$

::: mathlib
`Finset.lubell_yamamoto_meshalkin_inequality_sum_card_div_choose` · `Mathlib.Combinatorics.SetFamily.LYM`

The sum is over `r ∈ range (Fintype.card α + 1)` of `#(𝒜 # r) / (Fintype.card α).choose r` in an ordered semifield. The form with a sum over the members is `Finset.lubell_yamamoto_meshalkin_inequality_sum_inv_choose`. The claim of the second proof is `Finset.le_card_falling_div_choose`, with the levels counted from the top, and its two facts are `Finset.slice_union_shadow_falling_succ` and `Finset.IsAntichain.disjoint_slice_shadow_falling`.

<?decl Finset.lubell_yamamoto_meshalkin_inequality_sum_card_div_choose?>
:::

**Corollary (Sperner).** An antichain of subsets of an $n$-set has at most $\binom{n}{\lfloor n/2 \rfloor}$ members.

*Proof.* The binomial coefficients $\binom{n}{r}$ are largest at $r = \lfloor n/2 \rfloor$: the ratio $\binom{n}{r+1}/\binom{n}{r} = (n-r)/(r+1)$ is at least $1$ exactly when $r < n/2$, so the sequence rises to the middle and then falls. So each weight $1/\binom{n}{|A|}$ is at least $1/\binom{n}{\lfloor n/2 \rfloor}$, and the LYM inequality gives $|\mathcal{A}| / \binom{n}{\lfloor n/2 \rfloor} \le 1$. $\square$

::: mathlib
`IsAntichain.sperner` · `Mathlib.Combinatorics.SetFamily.LYM`

For `[Fintype α]` and an antichain `𝒜 : Finset (Finset α)`, the conclusion is `#𝒜 ≤ (Fintype.card α).choose (Fintype.card α / 2)`. Natural division `/ 2` is the floor.

<?decl IsAntichain.sperner?>
:::

The bound is sharp: the middle level is an antichain of this size. The equality cases are known. In the LYM inequality, equality holds only for a full level $\binom{X}{r}$. In Sperner's theorem, equality holds only for a middle level. The index of this edition has no declaration for either equality case.

::: mathlib
`Numbering.card_prefixed` · `Mathlib.Combinatorics.KatonaCircle`

This is the count of the lemma: `#(prefixed s) = (#s)! * (Fintype.card X - #s)!`. `Numbering.dens_prefixed` gives the density $1/\binom{n}{|s|}$ in `ℚ≥0`, which is the weight in the LYM inequality. `Numbering.disjoint_prefixed_prefixed` is the second part of the lemma. With these the first proof needs one more step, a sum of densities of disjoint finsets.

<?decl Numbering.card_prefixed?>
:::

### Examples

**Example (Weights of an antichain).** On $X = \{0, 1, 2, 3\}$, take $\mathcal{A} = \{\{0\}, 12, 13, 23\}$, where $12$ means $\{1, 2\}$. No member contains another. The LYM sum is $1/\binom{4}{1} + 3/\binom{4}{2} = 1/4 + 1/2 = 3/4 \le 1$. The family has $4$ members, below the Sperner bound $\binom{4}{2} = 6$. Adding $\{1, 2, 3\}$ breaks the antichain, since it contains $12$.

**Example (Numberings with a given prefix).** On $\{0, 1, 2\}$, the numberings with prefix $\{0\}$ are those with $f(0) = 0$. There are $1!\,2! = 2$ of them. The numberings with prefix $\{0, 1\}$ are those with $f(2) = 2$, again $2!\,1! = 2$. One numbering, $f = \mathrm{id}$, has both, as $\{0\} \subset \{0, 1\}$.

**Example (Local LYM).** On $n = 4$ points, $\mathcal{A} = \{012, 013\}$ with $r = 3$. Its shadow is $\{01, 02, 12, 03, 13\}$. Then $|\mathcal{A}|\, r = 6$ and $|\partial \mathcal{A}|(n - r + 1) = 10$, so the inequality holds with room.

**Example (Odd ground set).** For $n = 5$, both levels $\binom{X}{2}$ and $\binom{X}{3}$ are antichains of size $10 = \binom{5}{2}$. The family of the $2$-sets that contain $0$ together with the $3$-sets that avoid $0$ is a third antichain of size $4 + 4 = 8$: a $2$-set with $0$ is never inside a $3$-set without $0$.

### The library around it

The two LYM inequalities live in an ordered semifield `𝕜`, often `ℚ`. To apply them in `ℕ`, multiply out first, or use `Finset.local_lubell_yamamoto_meshalkin_inequality_mul`. The proof of the LYM inequality in the library does not use the file `KatonaCircle`.

Common errors of a learner:

- `IsAntichain (· ⊆ ·) 𝒜` takes a `Set`, so a finset family needs the coercion `(𝒜 : Set (Finset α))`.
- The weight of $A$ is $1/\binom{n}{|A|}$, not $1/|A|$. The sum runs over all members of all sizes.
- In `ℕ`, `n / 2` is $\lfloor n/2 \rfloor$, and `(n - r + 1)` is truncated subtraction. With `r ≤ n` both agree with the text.

### Exercises

1. (A) Check the LYM inequality for the antichain $\{0\}, \{1\}, 23, 24, 34$ on $\{0, 1, 2, 3, 4\}$. Hint: the sum is $2/5 + 3/10$.
2. (A) Show that the antichain of the last example is maximal: no set can be added. Compute its LYM sum. Hint: the sum is $4/5$, so the LYM inequality can be strict for a maximal antichain.
3. (A) Use the local LYM inequality to show that $|\partial \mathcal{A}| \ge |\mathcal{A}|$ for an $r$-uniform family on $n$ points with $2r \ge n + 1$.
4. (B) Show that a family with no chain $A \subset B \subset C$ of three members has at most $\binom{n}{\lfloor n/2 \rfloor} + \binom{n}{\lfloor n/2 \rfloor + 1}$ members. Hint: each numbering has at most two members as prefixes, so the sum of the weights is at most $2$. Then fill the two largest levels first.
5. (B) Let $\mathcal{A}$ be an antichain with $\sum_A 1/\binom{n}{|A|} = 1$. Show that every numbering has exactly one member of $\mathcal{A}$ as a prefix.
6. (B) Let $\mathcal{A}$ be an antichain on $n$ points whose members have at most $k$ elements, with $k \le n/2$. Show that $|\mathcal{A}| \le \binom{n}{k}$. Hint: $\binom{n}{r} \le \binom{n}{k}$ for $r \le k$.
7. (C) Let $n = 2m + 1$. Show that an antichain of size $\binom{n}{m}$ is the full level $m$ or the full level $m + 1$. Hint: by the LYM inequality all members have size $m$ or $m + 1$, and by Exercise 5 each numbering has exactly one member as a prefix. If $A \in \mathcal{A}$ has size $m$, $a \in A$ and $b \notin A$, use two numberings with the prefixes $A \cap A'$ and $A \cup A'$, where $A' = (A \setminus \{a\}) \cup \{b\}$, to show $A' \in \mathcal{A}$.

### Notes and history

Sperner proved his theorem in 1928. The LYM inequality is named after Lubell (1966), Yamamoto (1954) and Meshalkin (1963), who found it independently. Bollobás found it in 1965 as well. Lubell's proof is the first proof above, by counting orderings. The Authors line of `LYM.lean` names Bhavik Mehta, Alena Gusakov and Yaël Dillies, and that of `KatonaCircle.lean` names Ching-Tsun Chou, Chris Wong and Yaël Dillies.

### Reference

<?reference?>
