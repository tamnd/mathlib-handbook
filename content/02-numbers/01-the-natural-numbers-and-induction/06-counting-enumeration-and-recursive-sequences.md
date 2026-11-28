---
title: Counting, enumeration and recursive sequences
kind: api
modules:
  - Mathlib.Data.Nat.Count
  - Mathlib.Data.Nat.Nth
  - Mathlib.Data.Nat.Periodic
  - Mathlib.Data.Nat.Fib.Basic
  - Mathlib.Data.Nat.Fib.Zeckendorf
  - Mathlib.Data.Nat.DvdSequence
  - Mathlib.Data.Nat.Hyperoperation
explains:
  E2: [Nat.count_succ, Nat.nth_count, Nat.count_nth_of_infinite, Nat.filter_Ico_card_eq_of_periodic, Nat.fib_add_two, Nat.fib_add, Nat.fib_gcd, Nat.zeckendorfEquiv]
  E1: auto
families: []
requires: [V01.C05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Counting, enumeration and recursive sequences

### Overview

A predicate $p$ on $\mathbb{N}$ gives two functions. The first counts: $\mathrm{count}_p(n)$ is the number of $k < n$ with $p(k)$. The second enumerates: $\mathrm{nth}_p(n)$ is the $n$-th number with $p$, counted from $0$. For the primes, these are the prime counting function $\pi$ (up to a shift) and the sequence $2, 3, 5, 7, \dots$. The two functions are almost inverse to each other, and the modules `Mathlib.Data.Nat.Count` and `Mathlib.Data.Nat.Nth` make this precise. The module `Mathlib.Data.Nat.Periodic` counts the values of a periodic predicate.

The other modules of the section treat sequences defined by recursion, the method of the first section of this chapter. The Fibonacci numbers have their identities, the gcd property and the representation of Zeckendorf. A divisibility sequence is a sequence that keeps divisibility, and the Fibonacci numbers are the main example. The hyperoperations continue the chain of successor, addition, multiplication and power.

### The library around it

#### Counting with `Nat.count`

The function `Nat.count p n` needs a decidable predicate, `DecidablePred p`, and is defined as the number of elements of the list $[0, 1, \dots, n - 1]$ that satisfy $p$. The lemma `Nat.count_eq_card_filter_range` gives the form with a finite set: $\mathrm{count}_p(n) = \#\{x \in \mathrm{range}(n) \mid p(x)\}$. The recursion is the basic tool.

**Theorem (`Nat.count_succ`).** $\mathrm{count}_p(0) = 0$ and $\mathrm{count}_p(n + 1) = \mathrm{count}_p(n) + [p(n)]$, where $[p(n)]$ is $1$ if $p(n)$ holds and $0$ otherwise.

*Proof.* The range $[0, n + 1)$ is the range $[0, n)$ with the one new element $n$, and $n$ adds $1$ to the count exactly when $p(n)$ holds. $\square$

From the recursion come the order properties. The function is monotone (`Nat.count_monotone`) and $\mathrm{count}_p(n) \leq n$ (`Nat.count_le`). It is strictly larger after an element of $p$: `Nat.count_strict_mono` says that $p(m)$ and $m < n$ give $\mathrm{count}_p(m) < \mathrm{count}_p(n)$. So it is injective on the elements of $p$ (`Nat.count_injective`). The lemma `Nat.count_add` splits a count: $\mathrm{count}_p(a + b) = \mathrm{count}_p(a) + \mathrm{count}_{p(a + \cdot)}(b)$. The extreme cases are `Nat.count_true` and `Nat.count_false`, and `Nat.count_eq_zero` says that the count is $0$ exactly up to the first element of $p$.

#### Enumeration with `Nat.nth`

The function `Nat.nth p n` is the $n$-th element of the set $\{k \mid p(k)\}$ in increasing order, counted from $0$. It does not need decidability, so it is noncomputable. Its definition has two cases. If the set is infinite, `Nat.nth p` is the order isomorphism `Nat.Subtype.orderIsoOfNat` from $\mathbb{N}$ onto the set, followed by the inclusion (`Nat.nth_eq_orderIsoOfNat`). If the set is finite, with $c$ elements, `Nat.nth p n` is the $n$-th element of the sorted list for $n < c$, and the junk value $0$ for $n \geq c$ (`Nat.nth_of_card_le`).

So most lemmas come in two forms: one for an infinite set, with the hypothesis `(Set.ofPred p).Infinite`, and one with a bound $n < c$ on the index. For an infinite set:

| Lean name | Statement |
|---|---|
| `Nat.nth_mem_of_infinite` | $p(\mathrm{nth}_p(n))$ |
| `Nat.nth_strictMono` | $\mathrm{nth}_p$ is strictly increasing |
| `Nat.range_nth_of_infinite` | the range of $\mathrm{nth}_p$ is $\{k \mid p(k)\}$ |
| `Nat.nth_zero` | $\mathrm{nth}_p(0)$ is the least element of the set |
| `Nat.isLeast_nth_of_infinite` | $\mathrm{nth}_p(n)$ is the least element above $\mathrm{nth}_p(0), \dots, \mathrm{nth}_p(n - 1)$ |
| `Nat.le_nth` | $n \leq \mathrm{nth}_p(n)$ |

The bounded forms are `Nat.nth_mem_of_lt_card`, `Nat.nth_strictMonoOn` and `Nat.nth_lt_nth_of_lt_card`. The general lemmas such as `Nat.nth_mem` and `Nat.nth_lt_nth'` take the hypothesis `∀ hf : (Set.ofPred p).Finite, n < hf.toFinset.card`, which covers both cases at once: it is empty when the set is infinite.

#### The connection between count and nth

The count of the numbers with $p$ below $\mathrm{nth}_p(n)$ is $n$, because these numbers are $\mathrm{nth}_p(0), \dots, \mathrm{nth}_p(n - 1)$. This is `Nat.count_nth_of_infinite`, and `Nat.count_nth` is the bounded form. In the other direction, `Nat.nth_count` says that $\mathrm{nth}_p(\mathrm{count}_p(n)) = n$ when $p(n)$ holds.

**Proof sketch of `Nat.nth_count`.** Let $p(n)$ and $k = \mathrm{count}_p(n)$. The elements of $p$ below $n$ are exactly $k$ in number, so they are $\mathrm{nth}_p(0), \dots, \mathrm{nth}_p(k - 1)$. The element $n$ is the least element of $p$ above all of them, and by `Nat.isLeast_nth` this least element is $\mathrm{nth}_p(k)$. $\square$

For an infinite set the two functions form a Galois connection: $\mathrm{count}_p(a) \leq b \iff a \leq \mathrm{nth}_p(b)$. The library states it as `Nat.count_le_iff_le_nth`, as `Nat.gc_count_nth` and as the Galois insertion `Nat.giCountNth`. Then `Nat.surjective_count_of_infinite_setOfPred` says that the count takes each value.

#### Periodic predicates

The module `Mathlib.Data.Nat.Periodic` treats predicates with period $a$, that is, $p(n + a) = p(n)$ for each $n$ (`Function.Periodic p a`). Each window of $a$ consecutive numbers has the same count.

**Theorem (`Nat.filter_Ico_card_eq_of_periodic`).** If $p$ has period $a$, then $\#\{k \in [n, n + a) \mid p(k)\} = \mathrm{count}_p(a)$ for each $n$.

*Proof.* The map $k \mapsto k \bmod a$ is a bijection from $[n, n + a)$ onto $[0, a)$, and $p(k) = p(k \bmod a)$ by periodicity (`Function.Periodic.map_mod_nat`). So the two sets have the same number of elements. $\square$

The examples in the module are `Nat.periodic_gcd`, `Nat.periodic_coprime` and `Nat.periodic_mod`: the functions $n \mapsto \gcd(a, n)$, the predicate "$n$ is coprime to $a$" and $n \mapsto n \bmod a$ have period $a$. With the theorem, the number of $k$ in each window of length $a$ that are coprime to $a$ is $\varphi(a)$.

#### The Fibonacci numbers

The module `Mathlib.Data.Nat.Fib.Basic` defines `Nat.fib` with $F_0 = 0$, $F_1 = 1$ and the recursion `Nat.fib_add_two`: $F_{n + 2} = F_n + F_{n + 1}$. The values are `Nat.fib_zero`, `Nat.fib_one` and `Nat.fib_two`. The sequence is monotone (`Nat.fib_mono`), strictly increasing from index $2$ (`Nat.fib_add_two_strictMono`), and positive at positive indices (`Nat.fib_pos`).

**Theorem (`Nat.fib_add`).** $F_{m + n + 1} = F_m F_n + F_{m + 1} F_{n + 1}$.

*Proof.* Induction on $n$, for all $m$. For $n = 0$ the right side is $F_m \cdot 0 + F_{m + 1} \cdot 1 = F_{m + 1}$. For the step, apply the hypothesis to $m + 1$: $F_{m + n + 2} = F_{m + 1} F_n + F_{m + 2} F_{n + 1}$. Write $F_{m + 2} = F_m + F_{m + 1}$ and collect: the right side is $F_m F_{n + 1} + F_{m + 1}(F_n + F_{n + 1}) = F_m F_{n + 1} + F_{m + 1} F_{n + 2}$. $\square$

With $m = n$ and $m = n + 1$, the theorem gives the doubling formulas `Nat.fib_two_mul` and `Nat.fib_two_mul_add_one`: $F_{2n} = F_n (2 F_{n + 1} - F_n)$ and $F_{2n + 1} = F_{n + 1}^2 + F_n^2$. They compute $F_n$ with $O(\log n)$ steps. The function `Nat.fastFib` uses them on the binary digits of $n$, and `Nat.fastFib_eq` proves that it agrees with `Nat.fib`. Other identities are `Nat.fib_succ_eq_succ_sum`, the formula $F_{n + 1} = 1 + \sum_{k < n} F_k$, and `Nat.fib_succ_eq_sum_choose`, the sum of binomial coefficients along a diagonal of Pascal's triangle.

**Theorem (`Nat.fib_gcd`).** $F_{\gcd(m, n)} = \gcd(F_m, F_n)$.

*Proof sketch.* Consecutive Fibonacci numbers are coprime (`Nat.fib_coprime_fib_succ`), by induction: a common divisor of $F_n$ and $F_{n + 1}$ divides $F_{n + 1} - F_n = F_{n - 1}$. For $n \geq 1$, `Nat.fib_add` gives $F_{n + m} = F_{n - 1} F_m + F_n F_{m + 1}$, so $\gcd(F_m, F_{n + m}) = \gcd(F_m, F_n F_{m + 1}) = \gcd(F_m, F_n)$, since $F_m$ and $F_{m + 1}$ are coprime. This is `Nat.gcd_fib_add_self`. The pair $(m, n)$ now follows the steps of Euclid's algorithm, and the induction ends at $\gcd(F_0, F_d) = F_d$. $\square$

#### Divisibility sequences

The module `Mathlib.Data.Nat.DvdSequence` gives the names for this property. A function $f$ is a divisibility sequence, `IsDvdSequence f`, if $a \mid b$ implies $f(a) \mid f(b)$. A function $f : \mathbb{N} \to \mathbb{N}$ is a strong divisibility sequence, `Nat.IsStrongDvdSequence f`, if $\gcd(f(a), f(b)) = f(\gcd(a, b))$. A strong divisibility sequence is a divisibility sequence (`Nat.IsStrongDvdSequence.isDvdSequence`): if $a \mid b$ then $\gcd(a, b) = a$, so $f(a) = \gcd(f(a), f(b))$ divides $f(b)$. The identity and the constants are examples (`IsDvdSequence.id`, `IsDvdSequence.const`), and products and compositions of divisibility sequences are divisibility sequences (`IsDvdSequence.mul`, `IsDvdSequence.comp`). By `Nat.fib_gcd`, the Fibonacci numbers are a strong divisibility sequence: `Nat.isStrongDvdSequence_fib` and `Nat.isDvdSequence_fib`.

#### Zeckendorf's theorem

Each natural number is a sum of Fibonacci numbers with indices that are at least $2$ apart, and this sum is unique. The module `Mathlib.Data.Nat.Fib.Zeckendorf` states it with lists of indices. The predicate `List.IsZeckendorfRep l` says that the list $l$ decreases by at least $2$ at each step and that its last element is at least $2$. The function `Nat.greatestFib n` is the largest index $k$ with $F_k \leq n$, and `Nat.zeckendorf n` is the greedy list: $n = 0$ gives the empty list, and otherwise the list starts with $k = \mathrm{greatestFib}(n)$ and continues with the list of $n - F_k$ (`Nat.zeckendorf_of_pos`).

**Theorem (`Nat.zeckendorfEquiv`).** The map $l \mapsto \sum_{k \in l} F_k$ is a bijection from the Zeckendorf lists onto $\mathbb{N}$, and its inverse is `Nat.zeckendorf`.

*Proof sketch.* The greedy list is a Zeckendorf list (`Nat.isZeckendorfRep_zeckendorf`): if $k = \mathrm{greatestFib}(n)$, then $n < F_{k + 1}$, so $n - F_k < F_{k + 1} - F_k = F_{k - 1}$, and the next index is at most $k - 2$. Its sum is $n$ (`Nat.sum_zeckendorf_fib`). For uniqueness, a Zeckendorf list with first index $k$ has a sum less than $F_{k + 1}$ (`List.IsZeckendorfRep.sum_fib_lt`), so its first index is the greatest index of its sum, and the rest follows by induction (`Nat.zeckendorf_sum_fib`). $\square$

#### Hyperoperations

The module `Mathlib.Data.Nat.Hyperoperation` defines `hyperoperation n m k` by recursion on $n$ and $k$. The level $0$ is the successor, $H_0(m, k) = k + 1$, and the recursion is `hyperoperation_recursion`: $H_{n + 1}(m, k + 1) = H_n(m, H_{n + 1}(m, k))$. The start values at $k = 0$ are $m$, $0$ and $1$ for the levels $1$, $2$ and from $3$ on. The first levels are the familiar operations: `hyperoperation_one` gives $m + k$, `hyperoperation_two` gives $m k$, and `hyperoperation_three` gives $m^k$. Level $4$ is tetration. The lemma `hyperoperation_two_two_eq_four` says that $H_n(2, 2) = 4$ at each level $n \geq 1$.

#### Common errors

1. `Nat.nth p n` has the junk value $0$ when the set of $p$ has at most $n$ elements, and $0$ can also be a true value. So a statement about `Nat.nth` needs the hypothesis `(Set.ofPred p).Infinite` or a bound on $n$, and `Nat.nth_mem` asks for one of them.
2. The index of `Nat.nth` starts at $0$, and `Nat.count p n` counts the numbers strictly below $n$. So $\mathrm{nth}_p(\mathrm{count}_p(n)) = n$ needs $p(n)$, and for the primes `Nat.count Nat.Prime n` is $\pi(n - 1)$, not $\pi(n)$.
3. The doubling formula `Nat.fib_two_mul` uses the truncated subtraction of `ℕ`. It is correct because $F_n \leq 2 F_{n + 1}$, but a proof that moves it to `ℤ` must state this inequality before the cast.

### Exercises

1. (A) Compute `Nat.count Nat.Prime 20` and `Nat.nth Nat.Prime 7` by hand, and check the identity `Nat.count_nth_of_infinite` on these values.
2. (A) Prove $\sum_{k < n} F_k = F_{n + 1} - 1$ from `Nat.fib_add_two` by induction.
3. (B) Prove that $F_m \mid F_n$ when $m \mid n$, first with `Nat.fib_gcd` and then directly from `Nat.fib_add`.
4. (B) Use `Nat.filter_Ico_card_eq_of_periodic` and `Nat.periodic_coprime` to show that each block of $12$ consecutive numbers contains exactly $4$ numbers coprime to $12$.
5. (B) Find the Zeckendorf list of $100$ with the greedy rule, and check the result with `Nat.sum_zeckendorf_fib`.
6. (C) Prove `Nat.fib_coprime_fib_succ` and Cassini's identity $F_{n - 1} F_{n + 1} - F_n^2 = (-1)^n$ in `ℤ` for $n \geq 1$.

### Reference

<?reference?>
