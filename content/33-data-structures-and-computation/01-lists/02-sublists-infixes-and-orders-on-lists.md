---
title: Sublists, infixes and orders on lists
kind: theory
modules:
  - Mathlib.Data.List.Infix
  - Mathlib.Data.List.Sublists
  - Mathlib.Data.List.Lex
  - Mathlib.Data.List.Shortlex
  - Mathlib.Data.List.Forall2
  - Mathlib.Data.List.Palindrome
  - Mathlib.Data.List.PeriodicityLemma
  - Mathlib.Data.List.Prime
  - Mathlib.Data.List.SignVariations
  - Mathlib.Data.List.OffDiag
  - Mathlib.Data.List.Sym
  - Mathlib.Data.List.Duplicate
explains:
  E3: [List.mem_sublists, List.length_sublists, List.length_sublistsLen, List.mem_sublistsLen, List.Shortlex, List.Shortlex.wf, List.forall₂_iff_get, List.Palindrome, List.Palindrome.iff_reverse_eq, List.HasPeriod, List.HasPeriod.gcd, Prime.dvd_prod_iff, perm_of_prod_eq_prod, List.Duplicate, List.duplicate_iff_two_le_count]
  E2: [List.mem_inits, List.mem_tails, List.length_inits, List.infix_antisymm, List.instIsPartialOrderIsPrefix, List.sublistsLen, List.nodup_sublists, List.sublists_cons, List.lex_cons_iff, List.instLinearOrder, List.shortlex_def, List.shortlex_iff_lex, List.Forall₂.length_eq, List.forall₂_eq_eq_eq, List.SublistForall₂, List.Palindrome.append_reverse, List.Palindrome.map, List.HasPeriod.drop_prefix, mem_list_primes_of_dvd_prod, List.signVariations, List.offDiag, List.length_offDiag, List.sym2, List.length_sym2, List.mem_sym2_iff, List.sym, List.length_sym, List.nodup_iff_forall_not_duplicate]
  E1: auto
families: []
requires: [V01.C01, V03.C02, V04.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Sublists, infixes and orders on lists

### Overview

A list sits inside another list in several ways. It can be a sublist (the entries appear in order, with gaps), a prefix, a suffix or an infix (a block of consecutive entries). These relations are partial orders on `List α`, and the sublists of a list of length $n$ are $2^n$ in number. This section also studies the orders that compare lists entry by entry: the lexicographic order, which is the order of a dictionary, and the shortlex order, which compares the lengths first and is well founded. It then treats several properties of single lists: the lifting `Forall₂` of a relation to lists of equal length, palindromes, periods and the lemma of Fine and Wilf, lists of primes, the number of sign changes, the off-diagonal pairs, the symmetric powers and the duplicates.

The relations and the lexicographic order are in the core library; Mathlib adds the order structure and the other notions.

### Definitions

**Definition (Sublist).** The relation $l_1 <\!+\ l_2$ (`List.Sublist`) is the inductive relation with three rules: $[\,] <\!+\ [\,]$; if $l_1 <\!+\ l_2$ then $l_1 <\!+\ a :: l_2$ (skip $a$); if $l_1 <\!+\ l_2$ then $a :: l_1 <\!+\ a :: l_2$ (keep $a$).

**Definition (Prefix, suffix, infix).** $l_1$ is a prefix of $l_2$ ($l_1 <\!+\!:\ l_2$) if $l_2 = l_1 \mathbin{+\!\!+} t$ for some $t$, a suffix ($l_1 <\!:\!+\ l_2$) if $l_2 = s \mathbin{+\!\!+} l_1$, and an infix ($l_1 <\!:\!+\!:\ l_2$) if $l_2 = s \mathbin{+\!\!+} l_1 \mathbin{+\!\!+} t$. `inits l` is the list of the prefixes of $l$ from short to long, and `tails l` is the list of the suffixes from long to short.

**Definition (The list of sublists).** `sublists l` is the list of all sublists of $l$, by the recursion `sublists [] = [[]]` and `(a :: l).sublists = l.sublists >>= fun x => [x, a :: x]`. `sublistsLen n l` is the list of the sublists of length $n$.

**Definition (Lexicographic order).** For a relation $r$ on $\alpha$, `List.Lex r` is the inductive relation with the rules: $[\,]$ is below each $a :: l$; if $r(a, b)$ then $a :: l_1$ is below $b :: l_2$; if $l_1$ is below $l_2$ then $a :: l_1$ is below $a :: l_2$. For a linear order, the order $<$ on `List α` is `Lex (· < ·)`, and Mathlib makes `List α` a linear order.

**Definition (Shortlex).** `Shortlex r s t` holds if $|s| < |t|$, or $|s| = |t|$ and `Lex r s t`.

**Definition (Forall₂).** For $R \colon \alpha \to \beta \to \text{Prop}$, `Forall₂ R` relates $[\,]$ to $[\,]$, and $a :: l_1$ to $b :: l_2$ if $R(a, b)$ and `Forall₂ R l₁ l₂`.

**Definition (Palindrome).** `Palindrome` is the inductive predicate with the rules: $[\,]$ is a palindrome, $[x]$ is a palindrome, and if $l$ is a palindrome then so is $x :: (l \mathbin{+\!\!+} [x])$.

**Definition (Period).** A list $w$ has period $p$ (`w.HasPeriod p`) if $w$ is a prefix of $\operatorname{take} p\, w \mathbin{+\!\!+} w$. By `hasPeriod_iff_getElem?`, this means $w_i = w_{i+p}$ for all $i < |w| - p$.

**Definition (Sign variations).** For a list $l$ in a linearly ordered type with $0$, `signVariations l` is the number of changes of sign between neighbours after the zeros are removed. In the source, it is the length of the `destutter` of the list of nonzero signs, minus $1$.

**Definition (Off-diagonal, symmetric square, duplicate).** `l.offDiag` is the list of the pairs $(l_i, l_j)$ with $i \neq j$, for positions $i$ and $j$. `l.sym2` is the list of the unordered pairs $\{l_i, l_j\}$ with $i \le j$, by `sym2 (x :: xs) = (x :: xs).map (s(x, ·)) ++ xs.sym2`, and `List.sym n l` is the list of the multisets of size $n$ taken from $l$ with repetition. `Duplicate x l` (written $x \in^{+} l$) holds if $x$ occurs at least twice in $l$.

### Theorems and proofs

**Theorem (Number of sublists).** $s \in \operatorname{sublists} t$ if and only if $s <\!+\ t$, and $|\operatorname{sublists} t| = 2^{|t|}$. A list $s$ is in `sublistsLen n t` if and only if $s <\!+\ t$ and $|s| = n$, and there are $\binom{|t|}{n}$ of them.

*Proof.* Induction on $t$. For $t = [\,]$, `sublists [] = [[]]`, the only sublist of $[\,]$ is $[\,]$, and $2^0 = 1$. For $a :: t$, the recursion lists, for each $x$ in `sublists t`, the two lists $x$ and $a :: x$. By the rules of the sublist relation, a sublist of $a :: t$ either skips $a$, and is then a sublist $x$ of $t$, or keeps $a$, and is then $a :: x$ with $x <\!+\ t$. So the members are right, and the length doubles: $2 \cdot 2^{|t|} = 2^{|t| + 1}$. For `sublistsLen`, the same split gives the recursion $\binom{m + 1}{n + 1} = \binom{m}{n + 1} + \binom{m}{n}$: the sublists of length $n + 1$ of $a :: t$ are those of $t$, and $a$ in front of those of length $n$ of $t$. This is Pascal's rule,. $\square$

**Proposition (Infix is a partial order).** The relations prefix, suffix and infix are reflexive, transitive and antisymmetric.

*Proof.* Reflexivity takes $s = t = [\,]$, and transitivity composes the two decompositions. Antisymmetry: an infix is not longer than the list, so $l_1 <\!:\!+\!:\ l_2$ and $l_2 <\!:\!+\!:\ l_1$ give $|l_1| = |l_2|$. Then in $l_2 = s \mathbin{+\!\!+} l_1 \mathbin{+\!\!+} t$ the lengths give $|s| + |t| = 0$, so $s = t = [\,]$ and $l_1 = l_2$. The cases of prefix and suffix are the special cases $s = [\,]$ and $t = [\,]$. $\square$

**Theorem (Forall₂ by positions).** `Forall₂ R l₁ l₂` holds if and only if $|l_1| = |l_2|$ and $R(l_{1,i}, l_{2,i})$ for each position $i$.

*Proof.* Induction on $l_1$ for all $l_2$. For $l_1 = [\,]$, `Forall₂ R [] l₂` holds only for $l_2 = [\,]$, which is the case $|l_2| = 0$, and there are no positions. For $a :: l_1$: `Forall₂ R (a :: l₁) l₂` holds if and only if $l_2 = b :: l_2'$ with $R(a, b)$ and `Forall₂ R l₁ l₂'`. By the hypothesis, this is $|l_1| = |l_2'|$ and $R$ at each position of $l_1$, and with $R(a, b)$ at position $0$ it is the claim for $a :: l_1$. $\square$

**Theorem (Palindromes).** A list $l$ is a palindrome if and only if $\operatorname{rev}(l) = l$.

*Proof.* Suppose $l$ is a palindrome, and use induction on the rules. The reverse of $[\,]$ and of $[x]$ is the list itself. If $\operatorname{rev}(l) = l$, then $\operatorname{rev}(x :: (l \mathbin{+\!\!+} [x])) = \operatorname{rev}(l \mathbin{+\!\!+} [x]) \mathbin{+\!\!+} [x] = (x :: \operatorname{rev}(l)) \mathbin{+\!\!+} [x] = x :: (l \mathbin{+\!\!+} [x])$. Conversely, suppose $\operatorname{rev}(l) = l$, and use the bidirectional induction of the previous section. The cases $[\,]$ and $[x]$ are rules. For $l = a :: (m \mathbin{+\!\!+} [b])$, the reverse is $b :: (\operatorname{rev}(m) \mathbin{+\!\!+} [a])$. The equality with $l$ gives $a = b$ (the first entries) and then $\operatorname{rev}(m) = m$ (cancel the first and the last entries). By the hypothesis $m$ is a palindrome, and the third rule gives $a :: (m \mathbin{+\!\!+} [a])$. $\square$

**Theorem (Fine and Wilf, a weak form).** If $w$ has the periods $p$ and $q$ and $p + q \le |w|$, then $w$ has the period $\gcd(p, q)$.

*Proof.* Write $n = |w|$. Period $p$ means $w_i = w_{i + p}$ whenever $i + p < n$. Use strong induction on $p + q$. If $p = 0$, then $\gcd(0, q) = q$ and there is nothing to prove; the case $q = 0$ is the same, and so is $p = q$. Suppose $0 < p < q$ (the other case is symmetric). The claim is that $w$ has the period $q - p$. Let $i + (q - p) < n$. If $i + q < n$, then $w_i = w_{i + q}$ by the period $q$, and $w_{i + q - p} = w_{i + q}$ by the period $p$ at the position $i + q - p$. If $i + q \ge n$, then $i \ge n - q \ge p$. The period $p$ at the position $i - p$ gives $w_{i - p} = w_i$, and the period $q$ at $i - p$ gives $w_{i - p} = w_{i - p + q}$, which is allowed because $i - p + q < n$. In both cases $w_i = w_{i + (q - p)}$. Now $w$ has the periods $p$ and $q - p$, with $p + (q - p) = q \le n$ and $q < p + q$. By the hypothesis of induction, $w$ has the period $\gcd(p, q - p) = \gcd(p, q)$. $\square$

Mathlib proves the sharp form `HasPeriod.gcd`, with the hypothesis $p + q - \gcd(p, q) \le |w|$. The bound cannot be lowered by one: the word $aba$ has the periods $2$ and $3$, its length is $3 = 2 + 3 - 1 - 1$, and it has the period $1$ only if $a = b$.

**Theorem (Primes and products).** In a commutative monoid with zero, a prime $p$ divides the product of a list $L$ if and only if it divides a member of $L$. If the monoid is also cancellative and has no units but $1$, two lists of primes with the same product are permutations of each other.

*Proof.* The first claim is by induction on $L$. For $[\,]$ the product is $1$, and a prime is not a unit, so it does not divide $1$. For $a :: L$, the product is $a \cdot \prod L$, and $p \mid a \cdot \prod L$ if and only if $p \mid a$ or $p \mid \prod L$, by the definition of a prime. For the second claim, use induction on $l_1$ for all $l_2$. If $l_1 = [\,]$, then $\prod l_2 = 1$; a prime in $l_2$ would divide $1$, so $l_2 = [\,]$. If $l_1 = p :: l_1'$, then $p$ divides $\prod l_2$, so $p \mid q$ for a member $q$ of $l_2$. Write $q = p c$. Since $q$ is prime, it is irreducible, so $c$ is a unit, so $c = 1$ and $q = p$. Then $l_2$ is a permutation of $p :: l_2'$, where $l_2'$ is $l_2$ with one $p$ erased. Cancel $p$ in $p \prod l_1' = p \prod l_2'$ (a prime is not $0$), and the hypothesis gives $l_1' \sim l_2'$. So $l_1 \sim l_2$. $\square$

**Proposition (Duplicates).** $x \in^{+} l$ if and only if `count x l ≥ 2`. A list has no duplicates (`Nodup`) if and only if no $x$ is a duplicate in it.

*Proof.* Induction on $l$. For $[\,]$ both sides are false. For $y :: l$ with $y = x$, the rules give $x \in^{+} x :: l$ if and only if $x \in l$ or $x \in^{+} l$, that is, if and only if $\operatorname{count} x\, l \ge 1$; and $\operatorname{count} x\,(x :: l) = \operatorname{count} x\, l + 1$. For $y \neq x$, both sides are the same as for $l$. The second claim follows, because `Nodup l` means that each count is at most $1$. $\square$

**Proposition (Sizes).** $|\operatorname{offDiag} l| = |l|^2 - |l|$, $|\operatorname{sym2} l| = \binom{|l| + 1}{2}$, and $|\operatorname{sym}_n l| = \left(\!\binom{|l|}{n}\!\right)$, the number of multisets of size $n$ from $|l|$ kinds.

*Proof.* For the off-diagonal, each of the $|l|$ positions $i$ pairs with the $|l| - 1$ other positions, so the length is $|l|(|l| - 1) = |l|^2 - |l|$. For `sym2`, the recursion gives $|\operatorname{sym2}(x :: xs)| = (|xs| + 1) + |\operatorname{sym2} xs|$, so the length is $m + (m - 1) + \dots + 1 = \binom{m + 1}{2}$ for $m = |l|$. For `sym`, the recursion of the definition is the rule $\left(\!\binom{m + 1}{n + 1}\!\right) = \left(\!\binom{m + 1}{n}\!\right) + \left(\!\binom{m}{n + 1}\!\right)$ of the multiset numbers. $\square$

### Examples

**Example (Sublists of a list of three).** For $[1, 2, 3]$ the recursion gives `sublists [3] = [[], [3]]`, then `sublists [2, 3] = [[], [2], [3], [2, 3]]`, then `sublists [1, 2, 3] = [[], [1], [2], [1, 2], [3], [1, 3], [2, 3], [1, 2, 3]]`, eight lists. The sublists of length $2$ are $[1, 2]$, $[1, 3]$ and $[2, 3]$, and $\binom{3}{2} = 3$. The list $[1, 3]$ is a sublist, but not an infix. The infixes of length $2$ are $[1, 2]$ and $[2, 3]$. `inits [1, 2, 3] = [[], [1], [1, 2], [1, 2, 3]]`, with $3 + 1$ entries, and `tails [1, 2, 3] = [[1, 2, 3], [2, 3], [3], []]`.

**Example (Lexicographic and shortlex orders).** Over $\mathbb{N}$, $[1, 2] < [1, 3]$ (they agree at $1$ and $2 < 3$), $[1, 2] < [1, 2, 0]$ (a prefix is smaller), and $[2] > [1, 5, 5]$. In the shortlex order the lengths come first, so $[2] < [1, 5, 5]$.

**Counterexample (The lexicographic order is not well founded).** Over $\mathbb{N}$, $[1] > [0, 1] > [0, 0, 1] > \cdots$ is an infinite descending sequence for `Lex (· < ·)`, since each list starts with one more $0$. So the set $\{0^k \mathbin{+\!\!+} [1] : k \in \mathbb{N}\}$ has no least element. In shortlex this sequence increases, and `Shortlex.wf` proves that shortlex is well founded when $r$ is.

**Example (Periods).** The word $w = abaab$ has the period $3$: $w_0 = w_3 = a$ and $w_1 = w_4 = b$. It has the period $5$ trivially, since $5 \ge |w|$. The word $abaaba$ has the periods $3$ and $5$, and $3 + 5 - 1 = 7 > 6$, so Fine and Wilf do not apply, and indeed $\gcd(3, 5) = 1$ is not a period, since $w_0 \neq w_1$.

**Example (Palindromes, signs, pairs).** $[1, 2, 1]$ is $1 :: ([2] \mathbin{+\!\!+} [1])$ with $[2]$ a palindrome, and its reverse is itself. For $l = [1, -2, 0, 3, 4, -1]$, the signs without zeros are $+, -, +, +, -$, and the changes are at three places, so `signVariations l = 3`. `[1, 2, 3].offDiag = [(1, 2), (1, 3), (2, 1), (2, 3), (3, 1), (3, 2)]`, of length $9 - 3 = 6$. `[1, 2, 3].sym2` is $\{1,1\}, \{1,2\}, \{1,3\}, \{2,2\}, \{2,3\}, \{3,3\}$, of length $\binom{4}{2} = 6$. In $[1, 2, 1]$, the entry $1$ is a duplicate and $2$ is not.

```lean
example : [1, 2, 3].sublists.length = 8 := by simp
example : List.Palindrome [1, 2, 1] := .of_reverse_eq rfl
example : List.signVariations ([1, 0, -2, 3, 3] : List ℤ) = 2 := by decide
```

### The library around it

::: mathlib
`List.mem_sublists` · `Mathlib.Data.List.Sublists`

`mem_sublists`, `length_sublists`, `nodup_sublists`, `sublists_cons` and `sublists_append`. `sublistsLen` with `mem_sublistsLen`, `length_sublistsLen` and `nodup_sublistsLen`. 

<?decl List.mem_sublists?>
:::

::: mathlib
`List.infix_antisymm` · `Mathlib.Data.List.Infix`

`mem_inits`, `mem_tails`, `length_inits`, `inits_append`, `tails_append`, the partial order instances `instIsPartialOrderIsPrefix`, `instIsPartialOrderIsSuffix` and `instIsPartialOrderIsInfix`, and `decidableInfix`. The basic API of `<+:`, `<:+` and `<:+:` is in the core library.

<?decl List.infix_antisymm?>
:::

::: mathlib
`List.Shortlex.wf` · `Mathlib.Data.List.Shortlex`

`shortlex_def`, `shortlex_iff_lex` for lists of equal length, `Shortlex.of_length_lt` and `Shortlex.wf`. `Mathlib.Data.List.Lex` has `lex_cons_iff`, `Lex.isOrderConnected` and the instance `instLinearOrder`.

<?decl List.Shortlex.wf?>
:::

::: mathlib
`List.forall₂_iff_get` · `Mathlib.Data.List.Forall2`

`Forall₂.length_eq`, `forall₂_iff_get`, `forall₂_iff_zip`, `forall₂_eq_eq_eq`, the relator lemmas `rel_map`, `rel_append`, `rel_foldr`, `rel_filter`, and `SublistForall₂`.

<?decl List.forall₂_iff_get?>
:::

::: mathlib
`List.HasPeriod.gcd` · `Mathlib.Data.List.PeriodicityLemma`

`HasPeriod w p` with `hasPeriod_iff_getElem?`, `HasPeriod.drop_prefix` and `HasPeriod.gcd : w.HasPeriod p → w.HasPeriod q → p + q - p.gcd q ≤ w.length → w.HasPeriod (p.gcd q)`.

<?decl List.HasPeriod.gcd?>
:::

::: mathlib
`perm_of_prod_eq_prod` · `Mathlib.Data.List.Prime`

`Prime.dvd_prod_iff`, `Prime.not_dvd_prod`, `mem_list_primes_of_dvd_prod` and `perm_of_prod_eq_prod`, the uniqueness part of a factorization into primes, stated for lists.

<?decl perm_of_prod_eq_prod?>
:::

::: mathlib
`List.duplicate_iff_two_le_count` · `Mathlib.Data.List.Duplicate`

`Duplicate` with `duplicate_iff_two_le_count`, `nodup_iff_forall_not_duplicate` and `duplicate_iff_sublist` ($x \in^{+} l$ if and only if $[x, x] <\!+\ l$). `Mathlib.Data.List.OffDiag` has `length_offDiag` and `count_offDiag_eq_mul_sub_ite`; `Mathlib.Data.List.Sym` has `length_sym2`, `mem_sym2_iff` and `length_sym`; `Mathlib.Data.List.SignVariations` has `signVariations_zero_cons` and `signVariations_cons_cons_of_ne_zero`.

<?decl List.duplicate_iff_two_le_count?>
:::

Common errors of a learner: One error is to confuse a sublist with an infix; $[1, 3] <\!+\ [1, 2, 3]$, but $[1, 3]$ is not an infix. The second error is to confuse a sublist with a subset; `l₁ ⊆ l₂` forgets order and multiplicity, so $[1, 1] \subseteq [1]$ but $[1, 1]$ is not a sublist of $[1]$. The third error is to use the lexicographic order for termination; it is not well founded. The fourth error is to read `HasPeriod w p` as "$p$ is the least period"; each $p \ge |w|$ is a period.

### Exercises

1. (A) List the sublists of $[a, b]$ in the order of `sublists`, and the prefixes and suffixes of $[a, b, c]$. Hint: four sublists, four prefixes.
2. (A) Order the lists $[2]$, $[1, 9]$, $[1, 2, 3]$ and $[]$ by the lexicographic order and by shortlex over $\mathbb{N}$. Hint: $[]$ is least in both.
3. (B) Prove that $l_1 <\!+\ l_2$ implies $|l_1| \le |l_2|$, and that $l_1 <\!+\ l_2$ with $|l_1| = |l_2|$ implies $l_1 = l_2$. Hint: induction on the rules of the sublist relation.
4. (B) Prove that $l \mathbin{+\!\!+} \operatorname{rev}(l)$ is a palindrome, first with the reverse criterion and then by induction on $l$. Hint: $\operatorname{rev}(l \mathbin{+\!\!+} m) = \operatorname{rev}(m) \mathbin{+\!\!+} \operatorname{rev}(l)$.
5. (B) Count the entries of `count (1, 1) [1, 1, 2].offDiag` and of `count (1, 2) [1, 1, 2].offDiag`, and check them against the formula $c_a c_b - [a = b]\, c_a$. Hint: $c_1 = 2$, $c_2 = 1$.
6. (C) Prove the full form of the Fine and Wilf lemma for $p = 2$ and $q = 3$: a word of length $4$ with the periods $2$ and $3$ is constant. Hint: write $w = w_0 w_1 w_2 w_3$ and use $w_0 = w_2$, $w_1 = w_3$, $w_0 = w_3$.

### Notes and history

The periodicity lemma is due to Fine and Wilf (1965); the sharp bound $p + q - \gcd(p, q)$ is theirs. The lexicographic order is the order of dictionaries, and the shortlex order is the usual order in which the words of a formal language are listed.

The Mathlib files are by these authors, read from their headers: `Infix`, `Sublists` and `Lex` by Mario Carneiro; `Shortlex` by Hannah Fechtner; `Forall2` by Mario Carneiro and Johannes Hölzl; `Palindrome` by Chris Wong; `PeriodicityLemma` by Štěpán Holub; `Prime` by Johannes Hölzl, Jens Wagemaker and Anne Baanen; `SignVariations` by Tomaz Mascarenhas; `OffDiag` by Yury Kudryashov; `Sym` by Kyle Miller; `Duplicate` by Yakov Pechersky and Chris Hughes.

### Reference

<?reference?>
