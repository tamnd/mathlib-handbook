---
title: List operations and induction
kind: theory
modules:
  - Mathlib.Data.List.Basic
  - Mathlib.Data.List.Defs
  - Mathlib.Data.List.Induction
  - Mathlib.Data.List.TakeDrop
  - Mathlib.Data.List.TakeWhile
  - Mathlib.Data.List.DropRight
  - Mathlib.Data.List.GetD
  - Mathlib.Data.List.Indexes
  - Mathlib.Data.List.InsertIdx
  - Mathlib.Data.List.ModifyLast
  - Mathlib.Data.List.Lookmap
  - Mathlib.Data.List.Iterate
  - Mathlib.Data.List.Range
  - Mathlib.Data.List.FinRange
  - Mathlib.Data.List.Enum
  - Mathlib.Data.List.Find
  - Mathlib.Data.List.Fold
  - Mathlib.Data.List.Flatten
  - Mathlib.Data.List.Monad
  - Mathlib.Data.List.Lemmas
  - Mathlib.Data.List.OfFn
  - Mathlib.Data.List.Zip
  - Mathlib.Data.List.Map2
  - Mathlib.Data.List.ReduceOption
  - Mathlib.Data.List.SplitBy
  - Mathlib.Data.List.SplitLengths
  - Mathlib.Data.List.Interleave
  - Mathlib.Data.List.Count
  - Mathlib.Data.List.Sections
  - Mathlib.Data.List.Pi
  - Mathlib.Data.List.ProdSigma
  - Mathlib.Data.List.NatAntidiagonal
  - Mathlib.Data.List.ToFinsupp
  - Mathlib.Data.List.TFAE
  - Mathlib.Data.List.Intervals
explains:
  E3: [List.reverseRec, List.twoStepInduction, List.iterate, List.getElem_iterate, List.drop_take_append_drop, List.Nat.antidiagonal, List.Nat.mem_antidiagonal, List.length_product, List.TFAE, List.flatten_splitLengths, List.equivSigmaTuple]
  E2: [List.reverseRecOn, List.reverseRec_concat, List.bidirectionalRec, List.recNeNil, List.length_iterate, List.Nat.length_antidiagonal, List.Nat.antidiagonal_succ, List.mem_product, List.mem_sigma, List.mem_sections, List.TFAE.out, List.tfae_of_forall, List.reduceOption_mem_iff, List.length_eq_reduceOption_length_add_filter_none, List.flatten_splitBy, List.isChain_of_mem_splitBy, List.splitLengths, List.length_splitLengths, List.map_splitLengths_length, List.lookmap_cons_some, List.getD_eq_default, List.rdrop, List.rtake, List.rdrop_eq_reverse_drop_reverse, List.rdropWhile_append_rtakeWhile, List.Ico, List.Ico.length, List.Ico.mem, List.pure_def, List.idxOf_of_notMem, List.ofFn_inj, List.map₂Left, List.ranges]
  E1: auto
families: []
requires: [V01.C01, V01.C03, V03.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## List operations and induction

### Overview

A list of elements of $\alpha$ is either empty, or an element $a$ (the head) in front of a shorter list $l$ (the tail). Functions on lists are defined by recursion on this form, and facts by induction on it. This section collects the first operations, the lists built from numbers and functions, the cuts into blocks, the products and antidiagonals, two more induction principles, and the predicate TFAE.

The type `List` and most basic operations are in the core library of Lean and in Batteries; Mathlib adds lemmas and further operations.

### Definitions

**Definition (List).** `List α` is the inductive type with the constructors `nil`, written `[]`, and `cons`, written `a :: l`. The notation `[a, b, c]` means `a :: b :: c :: []`. The induction principle says: if $P([\,])$ holds, and $P(l)$ implies $P(a :: l)$ for all $a$ and $l$, then $P(l)$ holds for all $l$.

**Definition (Basic operations).** The length, the append and the map satisfy $$|[\,]| = 0,\quad |a :: l| = |l| + 1,\qquad [\,] \mathbin{+\!\!+} m = m,\quad (a :: l) \mathbin{+\!\!+} m = a :: (l \mathbin{+\!\!+} m),$$ $$\operatorname{map} f\,[\,] = [\,],\qquad \operatorname{map} f\,(a :: l) = f(a) :: \operatorname{map} f\, l.$$ The filter by a Boolean test $p$ keeps the entries with $p(a)$ true. `count a l` is the number of entries equal to $a$. The reverse satisfies $\operatorname{rev}(a :: l) = \operatorname{rev}(l) \mathbin{+\!\!+} [a]$. `flatten` appends a list of lists.

**Definition (Take and drop).** `take n l` is the list of the first $n$ entries of $l$ (all of $l$ if $|l| \le n$), and `drop n l` is the rest. `takeWhile p l` is the longest prefix whose entries satisfy $p$, and `dropWhile p l` is the rest. Mathlib adds `l.rtake n = l.drop (l.length - n)`, the last $n$ entries, `l.rdrop n = l.take (l.length - n)`, and `rtakeWhile`, `rdropWhile`, which work from the right.

**Definition (Access by index).** Positions count from $0$. `l.getD n d` is the entry at $n$, or the default $d$ if $n \ge |l|$. `idxOf a l` is the position of the first entry equal to $a$, or $|l|$ if there is none. `l.insertIdx n a` puts $a$ at position $n$. `modifyLast f l` applies $f$ to the last entry. For $f \colon \alpha \to \text{Option}\ \alpha$, `lookmap f l` replaces the first entry $a$ with $f(a) = \text{some}\ b$ by $b$.

**Definition (Lists from numbers and functions).** `range n` is $[0, \dots, n - 1]$, and `List.Ico n m` is $[n, \dots, m - 1]$. For $f \colon \text{Fin}\ n \to \alpha$, `ofFn f` is $[f(0), \dots, f(n - 1)]$, and `finRange n` is `ofFn id`. `List.iterate f a n` is $[a, f(a), \dots, f^{n-1}(a)]$: $$\operatorname{iterate} f\, a\, 0 = [\,],\qquad \operatorname{iterate} f\, a\,(n + 1) = a :: \operatorname{iterate} f\,(f(a))\, n.$$ `List.ranges [n₁, …, nₖ]` is the list of the consecutive blocks $[0, \dots, n_1 - 1]$, $[n_1, \dots, n_1 + n_2 - 1]$, and so on.

**Definition (Zips, options and blocks).** `zip l m` pairs the entries at the same position and stops at the shorter end. `map₂Left f l m` does not stop: past the end of $m$ it applies $f$ to `none`. For a list of `Option α` values, `reduceOption` keeps the values $a$ of the entries `some a`. For a Boolean relation $r$, `splitBy r l` cuts $l$ into maximal blocks in which $r$ holds between neighbours. For $s = [n_1, \dots, n_k]$, `s.splitLengths l` cuts $l$ into blocks of lengths $n_1, \dots, n_k$.

**Definition (Products).** The product $l_1 \times^{s} l_2$ is `l₁.flatMap fun a => l₂.map (a, ·)`, the list of all pairs. `l₁.sigma l₂` takes the second entry from the list $l_2(a)$. For $L = [L_1, \dots, L_k]$, `sections L` is the list of all $[x_1, \dots, x_k]$ with $x_i \in L_i$, with `sections [] = [[]]` and `sections (l :: L) = (sections L).flatMap fun s => l.map (· :: s)`. `List.Nat.antidiagonal n` is the map of $i \mapsto (i, n - i)$ over `range (n + 1)`.

**Definition (TFAE).** For a list $l$ of propositions, `TFAE l` is $\forall x \in l,\ \forall y \in l,\ x \leftrightarrow y$.

TFAE is how Mathlib states "the conditions (1) to (5) are equivalent". The proof can then be a cycle of implications instead of all pairs.

### Theorems and proofs

**Proposition (Take and drop).** For all $l$, $m$, $n$: `take n l ++ drop n l = l`, and $\operatorname{take} n\,(\operatorname{drop} m\, l) \mathbin{+\!\!+} \operatorname{drop}(m + n)\, l = \operatorname{drop} m\, l$.

*Proof.* The first claim is by induction on $n$ for all $l$. For $n = 0$, the parts are $[\,]$ and $l$. For $n + 1$ and $l = [\,]$, both parts are $[\,]$. For $n + 1$ and $a :: l'$, the left side is $a :: (\operatorname{take} n\, l' \mathbin{+\!\!+} \operatorname{drop} n\, l')$, which is $a :: l'$ by the hypothesis. For the second claim, put $k = \operatorname{drop} m\, l$. Then $\operatorname{drop}(m + n)\, l = \operatorname{drop} n\, k$ by induction on $m$, and the left side is $\operatorname{take} n\, k \mathbin{+\!\!+} \operatorname{drop} n\, k = k$. $\square$

**Theorem (Reverse induction).** If $P([\,])$ holds and $P(l)$ implies $P(l \mathbin{+\!\!+} [a])$ for all $l$ and $a$, then $P(l)$ holds for all $l$.

*Proof.* Let $Q(m)$ be $P(\operatorname{rev}(m))$. $Q([\,])$ is $P([\,])$. If $Q(m)$ holds, then $Q(a :: m)$ holds, because $\operatorname{rev}(a :: m) = \operatorname{rev}(m) \mathbin{+\!\!+} [a]$. So $Q$ holds for all lists by ordinary induction. For a list $l$, $l = \operatorname{rev}(\operatorname{rev}(l))$, so $P(l) = Q(\operatorname{rev}(l))$ holds. $\square$

Mathlib defines `List.reverseRec` by a different route: it writes a nonempty $l$ as $\operatorname{dropLast} l \mathbin{+\!\!+} [\operatorname{getLast} l]$ and recurses on the shorter list, with the length as the measure. `reverseRec_concat` is the computation rule on `l ++ [a]`.

**Theorem (Two-step induction).** Suppose $P([\,])$, $P([x])$ for each $x$, and: if $P(l)$ and $P(y :: l)$ for all $y$, then $P(x :: y :: l)$. Then $P(l)$ holds for all $l$.

*Proof.* Let $Q(l)$ be "$P(l)$, and $P(y :: l)$ for all $y$". For $l = [\,]$, both parts are hypotheses. Suppose $Q(l)$. The first part of $Q(x :: l)$ is $P(x :: l)$, which is the second part of $Q(l)$. The second part is $P(y :: x :: l)$ for all $y$; the third hypothesis gives it from $P(l)$ and $P(z :: l)$ for all $z$, and $Q(l)$ gives both. So $Q$ holds for all lists by ordinary induction, and $P(l)$ is its first part. $\square$

Mathlib has two more principles: `bidirectionalRec` removes the first and the last entry together, and `recNeNil` is the induction on nonempty lists from the singletons.

**Proposition (Entries of iterate).** `iterate f a n` has length $n$, and its entry at $i < n$ is $f^{i}(a)$.

*Proof.* Induction on $n$ for all $a$. For $n = 0$ the list is $[\,]$. Else it is $a :: \operatorname{iterate} f\,(f(a))\, n$, of length $n + 1$ by the hypothesis at $f(a)$. Its entry at $0$ is $a = f^{0}(a)$, and its entry at $i + 1$ is the entry of $\operatorname{iterate} f\,(f(a))\, n$ at $i$, that is $f^{i}(f(a)) = f^{i+1}(a)$. $\square$

**Proposition (The antidiagonal).** $(i, j) \in \operatorname{antidiagonal} n$ if and only if $i + j = n$. The antidiagonal has $n + 1$ entries, and `antidiagonal (n + 1) = (0, n + 1) :: map (Prod.map succ id) (antidiagonal n)`.

*Proof.* The list is `map (fun i => (i, n - i)) (range (n + 1))`, so it has $n + 1$ entries. An entry $(i, n - i)$ has $i \le n$, so $i + (n - i) = n$. Conversely, $i + j = n$ gives $i \le n$, so $i$ is in `range (n + 1)`, and $n - i = j$. For the recursion, the first entry for $n + 1$ is $(0, n + 1)$, and the others are $(i + 1, (n + 1) - (i + 1)) = (i + 1, n - i)$ for $i \le n$, the images of the entries $(i, n - i)$ for $n$. $\square$

**Proposition (Products).** $(a, b) \in l_1 \times^{s} l_2$ if and only if $a \in l_1$ and $b \in l_2$, and $|l_1 \times^{s} l_2| = |l_1| \cdot |l_2|$.

*Proof.* Induction on $l_1$. For $[\,]$ the product is $[\,]$, and $0 \cdot |l_2| = 0$. For $a' :: l$, the product is $\operatorname{map}(b \mapsto (a', b))\, l_2 \mathbin{+\!\!+} (l \times^{s} l_2)$. A pair $(a, b)$ is in the first part if and only if $a = a'$ and $b \in l_2$, and in the second part if and only if $a \in l$ and $b \in l_2$. The length is $|l_2| + |l| \cdot |l_2| = (|l| + 1) \cdot |l_2|$. $\square$

**Proposition (Cutting by lengths).** Let $s = [n_1, \dots, n_k]$. Then `s.splitLengths l` has $k$ blocks. If $|l| \le \Sigma s$, the flatten of the blocks is $l$. If $\Sigma s \le |l|$, the block $i$ has length $n_i$.

*Proof.* Induction on $s$ for all $l$. For $s = [\,]$ there are no blocks, and $|l| \le 0$ gives $l = [\,]$. For $s = n :: s'$, the blocks are `take n l` and the blocks of $s'$ on `drop n l`, so there are $1 + |s'|$. If $|l| \le n + \Sigma s'$, then $|\operatorname{drop} n\, l| \le \Sigma s'$, the later blocks flatten to `drop n l`, and the whole flatten is `take n l ++ drop n l = l`. If $n + \Sigma s' \le |l|$, then $|\operatorname{take} n\, l| = n$ and $\Sigma s' \le |\operatorname{drop} n\, l|$, and the hypothesis gives the other lengths. $\square$

**Remark (Proofs of TFAE).** The usual proof of `TFAE l` is a cycle $a_1 \to a_2 \to \dots \to a_k \to a_1$ (`List.tfae_of_cycle`, Chapter 2), or the tactics `tfae_have` and `tfae_finish`.

### Examples

**Example (Operations on a small list).** Let $l = [3, 1, 4, 1, 5]$. Then `map (· * 2) l = [6, 2, 8, 2, 10]`, `filter (· > 2) l = [3, 4, 5]` and `count 1 l = 2`. `take 2 l = [3, 1]` and `drop 2 l = [4, 1, 5]`. From the right, `l.rtake 2 = l.drop 3 = [1, 5]` and `l.rdrop 2 = l.take 3 = [3, 1, 4]`. `idxOf 1 l = 1`, `idxOf 7 l = 5`, `l.getD 2 0 = 4` and `l.getD 9 0 = 0`. `l.insertIdx 1 9 = [3, 9, 1, 4, 1, 5]` and `modifyLast (· + 1) l = [3, 1, 4, 1, 6]`. With $f(1) = \text{some}\ 0$ and $f(a) = \text{none}$ otherwise, `lookmap f l = [3, 0, 4, 1, 5]`: only the first $1$ changes.

**Example (Lists from functions).** `List.iterate (· * 2) 1 4` unfolds to $1 :: \operatorname{iterate}(\cdot 2)\, 2\, 3$, then $1 :: 2 :: \operatorname{iterate}(\cdot 2)\, 4\, 2$, and ends as $[1, 2, 4, 8]$. `List.Ico 2 5 = [2, 3, 4]`, of length $5 - 2$. `ofFn (fun i : Fin 3 => (i : ℕ) ^ 2) = [0, 1, 4]`. `List.ranges [2, 3] = [[0, 1], [2, 3, 4]]`.

**Example (Zips and blocks).** `zip [1, 2, 3] ['a', 'b'] = [(1, 'a'), (2, 'b')]`. With $f(a, o) = a + (\text{the value of } o, \text{ or } 0)$, `map₂Left f [1, 2, 3] [10] = [11, 2, 3]`. `reduceOption [some 1, none, some 3] = [1, 3]`. `splitBy (· ≤ ·) [1, 2, 2, 1, 3] = [[1, 2, 2], [1, 3]]`: the only cut is between $2$ and $1$. `[2, 1, 2].splitLengths [a, b, c, d, e] = [[a, b], [c], [d, e]]`.

**Example (Products, sections, antidiagonal).** `[1, 2] ×ˢ ['x', 'y'] = [(1, 'x'), (1, 'y'), (2, 'x'), (2, 'y')]`. For `sections [[1, 2], [3]]`, the recursion gives `sections [[3]] = [[3]]`, then puts $1$ and $2$ in front: $[[1, 3], [2, 3]]$. The antidiagonal of $3$ is $[(0, 3), (1, 2), (2, 1), (3, 0)]$.

**Example (The list monad).** In the monad of lists, `pure a = [a]` and `l >>= f` is the flatten of `map f l`. So `[1, 2] >>= fun x => [x, 10 * x]` is the flatten of $[[1, 10], [2, 20]]$, that is $[1, 10, 2, 20]$.

```lean
example : ([1, 2] >>= fun x => [x, 10 * x]) = [1, 10, 2, 20] := rfl
example : List.Nat.antidiagonal 2 = [(0, 2), (1, 1), (2, 0)] := rfl
example : List.iterate (· * 2) 1 4 = [1, 2, 4, 8] := rfl
```

**Example (A TFAE statement).** For $n \in \mathbb{N}$, the list $[n = 0,\ n \le 0,\ n < 1]$ satisfies TFAE, since each member is equivalent to $n = 0$. `TFAE.out 1 3` gives $n = 0 \leftrightarrow n < 1$; the positions in `TFAE.out` start at $1$, as in a printed theorem.

### The library around it

::: mathlib
`List.reverseRec` · `Mathlib.Data.List.Induction`

`reverseRec` and `reverseRecOn` with the cases `nil` and `append_singleton`, and the equations `reverseRec_nil` and `reverseRec_concat`. `bidirectionalRec` has the cases `nil`, `singleton` and `cons_append`, `twoStepInduction` the cases `nil`, `singleton` and `cons_cons`, and `recNeNil` works on nonempty lists. Use them as `induction l using List.reverseRecOn with ...`.

<?decl List.reverseRec?>
:::

::: mathlib
`List.drop_take_append_drop` · `Mathlib.Data.List.TakeDrop`

The core lemma `take_append_drop` gives the basic fact. Mathlib adds `drop_take_append_drop`, `takeD` and `takeI` (take with padding), and in the neighbouring files `takeWhile_idem`, `span_eq_takeWhile_dropWhile`, `rdrop_eq_reverse_drop_reverse` and `rdropWhile_append_rtakeWhile : rdropWhile p l ++ rtakeWhile p l = l`. `Mathlib.Data.List.GetD` has `getD_eq_getElem` and `getD_eq_default`.

<?decl List.drop_take_append_drop?>
:::

::: mathlib
`List.iterate` · `Mathlib.Data.List.Defs`

`iterate f a n` with `length_iterate`, `getElem_iterate : (iterate f a n)[i] = f^[i] a` and `mem_iterate`. `iterateTR` is a tail-recursive version for the compiler. The same file defines `dedup`, `destutter` and `permutations`, which Chapter 2 studies.

<?decl List.iterate?>
:::

::: mathlib
`List.equivSigmaTuple` · `Mathlib.Data.List.OfFn`

`equivSigmaTuple : List α ≃ Σ n, (Fin n → α)` identifies a list with its length and its function of entries. `ofFn_injective`, `ofFn_inj`, `get_ofFn` and `forall_iff_forall_tuple` use it. `Mathlib.Data.List.Indexes` writes `mapIdx` as an `ofFn`.

<?decl List.equivSigmaTuple?>
:::

::: mathlib
`List.Nat.antidiagonal` · `Mathlib.Data.List.NatAntidiagonal`

`mem_antidiagonal`, `length_antidiagonal`, `nodup_antidiagonal`, `antidiagonal_succ` and `antidiagonal_succ'`. The multiset and the finset antidiagonals of $\mathbb{N}$ are built on this list.

<?decl List.Nat.antidiagonal?>
:::

::: mathlib
`List.length_product` · `Mathlib.Data.List.ProdSigma`

`mem_product`, `length_product` and `mem_sigma`. `Mathlib.Data.List.Sections` has `mem_sections : f ∈ L.sections ↔ Forall₂ (· ∈ ·) f L`, and `Mathlib.Data.List.Pi` has `List.pi` with `mem_pi`, the dependent version.

<?decl List.length_product?>
:::

::: mathlib
`List.flatten_splitLengths` · `Mathlib.Data.List.SplitLengths`

`length_splitLengths`, `flatten_splitLengths` and `map_splitLengths_length`. `Mathlib.Data.List.SplitBy` has `flatten_splitBy` and `isChain_of_mem_splitBy` (each block is a chain of $r$), and `Mathlib.Data.List.ReduceOption` has `reduceOption_mem_iff` and `length_eq_reduceOption_length_add_filter_none`.

<?decl List.flatten_splitLengths?>
:::

::: mathlib
`List.TFAE` · `Mathlib.Data.List.TFAE`

`TFAE.out i j`, `tfae_of_forall`, `tfae_nil`, `tfae_reverse`, `Perm.tfae_iff` and `TFAE.not`. `Mathlib.Data.List.Intervals` has `List.Ico` with `Ico.mem` and `Ico.length`, `Mathlib.Data.List.ToFinsupp` has `toFinsupp_apply : l.toFinsupp i = l.getD i 0`, and `Mathlib.Data.List.Interleave` defines the relation `List.Interleaves r`, under which `[1, 3]` interleaves `[0, 2, 4]` for $\le$.

<?decl List.TFAE?>
:::

Common errors of a learner: The first error is to look for `List.map` in Mathlib; it is in the core library. The second error is to count positions from $1$; `getD`, `idxOf`, `insertIdx` and `l[i]` count from $0$, but `TFAE.out` counts from $1$. The third error is to prove a fact about `l ++ [a]` by `induction l`; the hypothesis is then about the wrong end, and `induction l using List.reverseRecOn` is the right tool. The fourth error is to forget $|l| \le \Sigma s$ in `flatten_splitLengths`: the blocks drop the entries past the sum.

### Exercises

1. (A) Compute `take 3 [5, 6, 7, 8]`, `drop 3 [5, 6, 7, 8]`, `[5, 6, 7, 8].rtake 3` and `[5, 6, 7, 8].rdrop 3`. Hint: `rtake n` drops `length - n` entries.
2. (A) Compute `List.iterate (fun n => 3 * n + 1) 1 4` and check the entry at position $2$ against $f^{2}(1)$. Hint: $f(1) = 4$.
3. (A) Write out `sections [[1, 2], [3, 4]]` and check that it has $2 \cdot 2$ entries. Hint: the last list varies slowest.
4. (B) Prove `map f (l ++ m) = map f l ++ map f m` and $|l \mathbin{+\!\!+} m| = |l| + |m|$ by induction on $l$. Hint: do not induct on $m$.
5. (B) Prove $\operatorname{rev}(\operatorname{rev}(l)) = l$. Hint: first prove $\operatorname{rev}(l \mathbin{+\!\!+} [a]) = a :: \operatorname{rev}(l)$ by induction on $l$.
6. (B) Define `pairs (x :: y :: l) = (x + y) :: pairs l`, `pairs [x] = [x]` and `pairs [] = []`. Prove with two-step induction that `pairs l` has the same sum as $l$. Hint: the sum of `x :: y :: l` is $x + y + \Sigma l$.
7. (C) Prove that `sections L` has $\prod_i |L_i|$ entries, and that $f \in \operatorname{sections} L$ if and only if $|f| = |L|$ and the entry $i$ of $f$ is in $L_i$ for each $i$. Hint: induction on $L$, with the proposition on products as the model.

### Notes and history

Lists come from Lisp, the language of McCarthy, where `cons`, `car` and `cdr` are the constructor, the head and the tail. Knuth treats linear lists as the first data structure in Volume 1 of *The Art of Computer Programming*. The view of lists as an inductive type with structural induction is the one of type theory.

The Mathlib files are by these authors, read from their headers. `Basic`, `Defs`, `Induction`, `TakeDrop`, `TakeWhile`, `InsertIdx`, `ModifyLast`, `Lookmap`, `Map2` and `Count`: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn and Mario Carneiro, with Bolton Bailey for `GetD`. `DropRight` and `ToFinsupp`: Yakov Pechersky; `Lemmas`: Yakov Pechersky and Yury Kudryashov; `ReduceOption`: Yakov Pechersky and Anthony DeRossi; `Enum`: Mario Carneiro, Yakov Pechersky and Eric Wieser. `Indexes`: Jannis Limperg. `Iterate`: Miyahara Kō. `Range`: Mario Carneiro, Kenny Lau and Kim Morrison, with Alex Keizer for `FinRange`. `Find`: Eric Wieser. `Fold`: Jeremy Tan. `Flatten`: Sébastien Gouëzel, Floris van Doorn, Mario Carneiro and Martin Dvorak. `Monad`: Leonardo de Moura. `OfFn` and `Sections`: Mario Carneiro. `Zip`: Mario Carneiro and Kenny Lau. `SplitBy`: Violeta Hernández Palacios. `SplitLengths`: Daniel Weber. `Interleave`: Yaël Dillies. `Pi`: Yuyang Zhao. `ProdSigma`: Leonardo de Moura and Mario Carneiro. `NatAntidiagonal`: Johan Commelin. `TFAE`: Johan Commelin and Simon Hudon. `Intervals`: Kim Morrison.

### Reference

<?reference?>
