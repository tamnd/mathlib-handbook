---
title: Equivalences of finite and countable types
kind: api
modules:
  - Mathlib.Logic.Equiv.Fin.Basic
  - Mathlib.Logic.Equiv.Fin.Rotate
  - Mathlib.Logic.Equiv.Fintype
  - Mathlib.Logic.Equiv.Finset
  - Mathlib.Logic.Equiv.Multiset
  - Mathlib.Logic.Equiv.List
  - Mathlib.Logic.Equiv.Array
  - Mathlib.Logic.Equiv.Nat
explains:
  E2: [finSumFinEquiv, finProdFinEquiv, finSuccEquiv, Equiv.embeddingFinSucc, Equiv.natSumNatEquivNat, Denumerable.lower_raise']
  E1: auto
families: []
requires: [V01.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Equivalences of finite and countable types

### Overview

The type `Fin n` holds the natural numbers $0, 1, \ldots, n - 1$. It is the standard finite set with $n$ elements. Many proofs about finite types reduce to `Fin n`: a finite type $\alpha$ is equivalent to `Fin (Fintype.card α)` by `Fintype.equivFin`, and an argument by induction on $n$ then needs an equivalence between `Fin (n + 1)` and a type built from `Fin n`. The modules of this section give these equivalences. They are the formal form of the counting identities $m + n$, $m \cdot n$ and $n + 1$ for finite sets.

The same modules treat countable types. The type $\mathbb{N}$ is equivalent to $\mathbb{N} \oplus \mathbb{N}$, to $\mathrm{Bool} \times \mathbb{N}$, to $\mathbb{Z}$, to the lists of natural numbers, and to the finite sets of natural numbers. These equivalences give the instances of the classes `Encodable` and `Denumerable` for lists, multisets, finite sets and arrays. An `Encodable` type has an injection into $\mathbb{N}$ with a partial inverse, and a `Denumerable` type has an equivalence with $\mathbb{N}$.

The section uses the equivalences of the previous sections of this chapter: `Equiv`, its operations `Equiv.symm` and `Equiv.trans`, and the equivalences of sums, products and options.

### The library around it

#### Sums, products and successors of `Fin`

The module `Mathlib.Logic.Equiv.Fin.Basic` has the equivalences that express the arithmetic of finite cardinals. The main ones are in the table.

| Lean name | Statement |
|---|---|
| `finSumFinEquiv` | `Fin m ⊕ Fin n ≃ Fin (m + n)` |
| `finProdFinEquiv` | `Fin m × Fin n ≃ Fin (m * n)` |
| `finSuccEquiv` | `Fin (n + 1) ≃ Option (Fin n)`, with $0 \mapsto$ `none` |
| `finSuccEquivLast` | `Fin (n + 1) ≃ Option (Fin n)`, with $n \mapsto$ `none` |
| `finSuccEquiv'` | `Fin (n + 1) ≃ Option (Fin n)`, with a chosen $i \mapsto$ `none` |
| `finSuccAboveEquiv` | `Fin n ≃ { x // x ≠ p }` for `p : Fin (n + 1)` |
| `finAddFlip` | `Fin (m + n) ≃ Fin (n + m)` |
| `finSumNatEquiv` | `Fin n ⊕ ℕ ≃ ℕ` |
| `Nat.divModEquiv` | `ℕ ≃ ℕ × Fin n` for $n \neq 0$ |
| `Int.divModEquiv` | `ℤ ≃ ℤ × Fin n` for $n \neq 0$ |
| `Fin.castLEquiv` | `Fin n ≃ { i : Fin m // ↑i < n }` for $n \le m$ |

**Sums.** The equivalence `finSumFinEquiv` sends the left copy $i : \mathrm{Fin}\ m$ to the same number $i$, and it sends the right copy $j : \mathrm{Fin}\ n$ to $m + j$. The lemmas `finSumFinEquiv_apply_left` and `finSumFinEquiv_apply_right` state these two values. The inverse sends $k < m$ to the left copy and $k \ge m$ to the right copy with the value $k - m$. The equivalence `finSumNatEquiv` does the same with $n$ elements in front of all of $\mathbb{N}$: it sends $i$ in the left copy to $i$ and $j$ in the right copy to $n + j$.

**Products.** The equivalence `finProdFinEquiv` sends $(i, j)$ to $n i + j$. The lemma `finProdFinEquiv_apply_val` states the value, in the form `↑x.2 + n * ↑x.1`. The inverse sends $k$ to its quotient and remainder by $n$.

*Proof that the map is a bijection.* For $i < m$ and $j < n$, the number $n i + j$ satisfies $n i + j \le n i + n - 1 = n(i + 1) - 1 \le n m - 1$. So the map goes into $\mathrm{Fin}\ (m n)$. By the division algorithm, every $k < m n$ is $n q + r$ for one pair $(q, r)$ with $r < n$, and then $q < m$. So the map is bijective, and the inverse is $k \mapsto (\lfloor k / n \rfloor, k \bmod n)$. $\square$

The same division algorithm gives `Nat.divModEquiv n`, which sends $a$ to $(a / n, a \bmod n)$, with the inverse $(q, r) \mapsto q n + r$. The integer form `Int.divModEquiv` uses the integer quotient and the remainder in $\{0, \ldots, n - 1\}$.

**Successors.** The three equivalences `finSuccEquiv`, `finSuccEquivLast` and `finSuccEquiv'` all identify `Fin (n + 1)` with `Option (Fin n)`. They remove a different point. The first one removes $0$, and it sends $k + 1$ to `some k` (`finSuccEquiv_succ`). The second one removes the last point $n$, and it fixes the other numbers (`finSuccEquivLast_castSucc`). The third one removes a chosen point $i$, and it sends `i.succAbove j` to `some j` (`finSuccEquiv'_succAbove`). Here `Fin.succAbove i` is the increasing map from `Fin n` into `Fin (n + 1)` that skips $i$. The form with a subtype is `finSuccAboveEquiv p : Fin n ≃ { x // x ≠ p }`. These equivalences are the tool of an induction on $n$: a statement about `Fin (n + 1)` becomes a statement about `Option (Fin n)`, and the equivalences of options of the previous sections apply.

*Proof that `finSuccEquiv` is a bijection.* Every element of $\{0, \ldots, n\}$ is either $0$ or $k + 1$ for a unique $k \in \{0, \ldots, n - 1\}$. The map sends $0$ to `none` and $k + 1$ to `some k`. The inverse sends `none` to $0$ and `some k` to $k + 1$, and the two composites are the identity by the case split. $\square$

**Tuples.** A function `Fin n → α` is an $n$-tuple. The module has the equivalences that split tuples. `Fin.appendEquiv m n` identifies a pair of an $m$-tuple and an $n$-tuple with an $(m + n)$-tuple, by `Fin.append`. `Fin.succFunEquiv α n` identifies an $(n + 1)$-tuple with an $n$-tuple and a last entry. The case $n = 2$ has `finTwoArrowEquiv α : (Fin 2 → α) ≃ α × α` and `prodEquivPiFinTwo α β`, which writes a product as a dependent function on `Fin 2`.

**Embeddings.** The equivalence `Equiv.embeddingFinSucc n ι` has the type

$$(\mathrm{Fin}\ (n + 1) \hookrightarrow \iota) \simeq \Sigma\, (e : \mathrm{Fin}\ n \hookrightarrow \iota),\ \{ i \mid i \notin \mathrm{range}\ e \}.$$

It sends an injection $e$ to the pair of $e \circ \mathrm{succ}$ and $e(0)$ (`Equiv.embeddingFinSucc_fst`, `Equiv.embeddingFinSucc_snd`).

*Proof.* The restriction $e \circ \mathrm{succ}$ is injective, and $e(0)$ is not in its range, because $e$ is injective and $0 \neq k + 1$. Conversely, an injection $e'$ of `Fin n` and a point $i$ outside its range give the map $0 \mapsto i$, $k + 1 \mapsto e'(k)$, which is `Fin.cons`. It is injective because $e'$ is injective and $i$ is new. The two constructions are inverse to each other by the case split on $0$ and $k + 1$. $\square$

This equivalence is the step of the count $n (n - 1) \cdots (n - k + 1)$ of the injections of a $k$-set into an $n$-set.

#### Rotations of `Fin n`

The module `Mathlib.Logic.Equiv.Fin.Rotate` defines two permutations of `Fin n`. The permutation `finRotate n` is the cycle $(0\ 1\ \cdots\ n - 1)$: it sends $i$ to $i + 1$ and the last point to $0$. The lemma `finRotate_apply` states it as `finRotate n i = i + 1`, with the addition modulo $n$. The lemmas `finRotate_last` and `coe_finRotate` give the two cases in natural numbers. The definition is `finAddFlip.trans (finCongr _)` for $n + 1$ (`finRotate_succ`), so a rotation is a flip of the two blocks $\{0, \ldots, n - 1\}$ and $\{n\}$.

The permutation `finCycle k` adds $k$ to each element (`finCycle_apply`), and `finCycle_eq_finRotate_iterate` states that it is the $k$-th power of the rotation. The lemma `Fin.snoc_eq_cons_rotate` connects the two ways to extend a tuple: to add an entry at the end is to add it at the front and then rotate.

#### Equivalences with a finite side

The module `Mathlib.Logic.Equiv.Fintype` treats equivalences where one side is finite.

1. `Function.Embedding.toEquivRange f : α ≃ ↑(Set.range ⇑f)` turns an embedding of a finite type into an equivalence onto its range. The general `Equiv.ofInjective` does the same for any injective map, but its inverse uses choice. Here the inverse searches through the finite domain, so it is computable. The lemma `Function.Embedding.toEquivRange_eq_ofInjective` states that the two equivalences are equal.
2. `Equiv.Perm.viaFintypeEmbedding e f` moves a permutation $e$ of a finite type $\alpha$ along an embedding $f : \alpha \hookrightarrow \beta$. It acts as $f \circ e \circ f^{-1}$ on the range of $f$ and as the identity outside (`Equiv.Perm.viaFintypeEmbedding_apply_image`, `Equiv.Perm.viaFintypeEmbedding_apply_notMem_range`).
3. `Equiv.toCompl` turns an equivalence of two finite subtypes $\{x \mid p\ x\} \simeq \{x \mid q\ x\}$ into an equivalence of their complements. Then `Equiv.extendSubtype` glues the two into a permutation of the whole type, and `Equiv.extendSubtype_apply_of_mem` states that it extends the given equivalence.
4. `Equiv.setDiffEquiv` gives $s \setminus t \simeq t \setminus s$ for finite sets of the same cardinality.

These constructions give two extension results. `Equiv.Perm.exists_extending_pair` states that for two injective maps $f, g : \alpha \to \beta$ from a finite type there is a permutation $\sigma$ of $\beta$ with $\sigma(f(a)) = g(a)$ for all $a$. `Equiv.Perm.exists_map_finset_eq` states that two finite sets of the same cardinality are images of each other under a permutation. The proof of the first one applies `Equiv.extendSubtype` to the equivalence $\mathrm{range}\ f \simeq \alpha \simeq \mathrm{range}\ g$. The second one follows from the first one.

#### Countable types and encodings

The module `Mathlib.Logic.Equiv.Nat` has the classical bijections with $\mathbb{N}$.

| Lean name | Statement | Formula |
|---|---|---|
| `Equiv.boolProdNatEquivNat` | `Bool × ℕ ≃ ℕ` | $(b, n) \mapsto 2n + b$ |
| `Equiv.natSumNatEquivNat` | `ℕ ⊕ ℕ ≃ ℕ` | $\mathrm{inl}\ x \mapsto 2x$, $\mathrm{inr}\ x \mapsto 2x + 1$ |
| `Equiv.intEquivNat` | `ℤ ≃ ℕ` | through `Equiv.intEquivNatSumNat` |
| `Equiv.prodEquivOfEquivNat` | `α × α ≃ α` from `α ≃ ℕ` | through the pairing of $\mathbb{N}$ |

*Proof for `Equiv.natSumNatEquivNat`.* By division by $2$, every natural number is $2x$ or $2x + 1$ for a unique $x$, and not both. So the map is a bijection. The inverse reads the last binary digit with `Nat.bodd` and the rest with `Nat.div2`, as the lemma `Equiv.natSumNatEquivNat_symm_apply` states. $\square$

The module `Mathlib.Logic.Equiv.List` encodes lists. The code of the empty list is $0$, and the code of $a :: l$ is $\mathrm{pair}(\mathrm{code}(a), \mathrm{code}(l)) + 1$, where `Nat.pair` is the standard bijection $\mathbb{N} \times \mathbb{N} \simeq \mathbb{N}$ (`Encodable.encode_list_nil`, `Encodable.encode_list_cons`). The decoding function `Encodable.decodeList` reverses it, and `Encodable.decodeList_encodeList_eq_self` is the inverse law. This gives the instance `List.encodable`, then `Denumerable.denumerableList` and `List.countable`. The lemma `Encodable.length_le_encode` states that the code of a list is at least its length. The module also has the equivalences `Equiv.listNatEquivNat : List ℕ ≃ ℕ`, `Equiv.listEquivSelfOfEquivNat`, the functor action `Equiv.listEquivOfEquiv`, and `Equiv.listUniqueEquiv`, which identifies the lists over a type with one element with their lengths.

A finite type is encodable, but the encoding depends on an order of its elements. So `Fintype.truncEncodable` gives the encoding inside `Trunc`, the quotient that forgets which encoding was chosen. The noncomputable `Fintype.toEncodable` picks one encoding. A type with an explicit list of all its elements is encodable by `Encodable.encodableOfList`.

The modules `Mathlib.Logic.Equiv.Multiset` and `Mathlib.Logic.Equiv.Finset` encode multisets and finite sets. For an encodable type, the instance `Multiset.encodable` sorts the elements of a multiset by their codes and encodes the sorted list, by `encodeMultiset`. The instance `Finset.encodable` treats a finite set as a multiset with no repeated element. For a denumerable type, `Denumerable.multiset` and `Denumerable.finset` need a bijection, not only an injection. A sorted list is not an arbitrary list, so the code goes through the list of differences. For finite sets of natural numbers, the functions are

$$\mathrm{lower}'([a_1, a_2, a_3, \ldots], n) = [a_1 - n,\ a_2 - a_1 - 1,\ a_3 - a_2 - 1, \ldots],$$
$$\mathrm{raise}'([d_1, d_2, d_3, \ldots], n) = [n + d_1,\ n + d_1 + d_2 + 1,\ \ldots].$$

**Theorem.** `Denumerable.lower'` and `Denumerable.raise'` are inverse bijections between all lists of natural numbers and the strictly increasing lists with entries at least $n$.

*Proof.* The function `Denumerable.raise'` adds the partial sums and one more at each step, so its output is strictly increasing (`Denumerable.raise'_sorted`) and its first entry is at least $n$. The equation $\mathrm{lower}'(\mathrm{raise}'(l, n), n) = l$ is `Denumerable.lower_raise'`: at each step $(d + n) - n = d$, and the induction continues with the start $d + n + 1$. For a strictly increasing list with entries at least $n$, each difference $a_{k+1} - a_k - 1$ is a natural number with no truncation, so `Denumerable.raise_lower'` gives the other law by the same induction. $\square$

For multisets, `Denumerable.lower` and `Denumerable.raise` are the same without the $- 1$ and the $+ 1$, since a sorted list of a multiset can repeat entries (`Denumerable.lower_raise`, `Denumerable.raise_sorted`). The Finset module also defines `Encodable.sortedUniv`, the list of all elements of a finite encodable type in the order of their codes, and `Encodable.fintypeEquivFin`, a computable equivalence `α ≃ Fin (Fintype.card α)` built from that list.

The module `Mathlib.Logic.Equiv.Array` has `Equiv.arrayEquivList α : Array α ≃ List α`, and with it the instances `Array.encodable` and `Array.countable`.

#### Common errors

1. A learner uses `finSuccEquiv` and expects the last element to go to `none`. It is $0$ that goes to `none`. Use `finSuccEquivLast` for the last element, or `finSuccEquiv'` for any chosen point.
2. A learner expects `finProdFinEquiv (i, j)` to be $i + m j$. The value is $j + n i$: the first coordinate is the slow one, as in the lexicographic order.
3. A learner wants the encoding of `Multiset ℕ` from `Multiset.encodable` to be a bijection. It is only an injection. The bijection is the instance `Denumerable.multiset`, and it uses another code.

### Exercises

1. (A) Compute `finSumFinEquiv (Sum.inr 2)` in `Fin (3 + 5)` and `finProdFinEquiv (1, 2)` in `Fin (3 * 4)`.
2. (A) Show that `finRotate 3` has order $3$ in the group of permutations of `Fin 3`, and that the function of `finCycle 2` is the square of the function of `finRotate 3`.
3. (B) Use `finSuccEquiv` and induction on $n$ to prove that `Fin n → Bool` has $2^n$ elements.
4. (B) Use `Equiv.embeddingFinSucc` to prove that the number of embeddings `Fin k ↪ Fin n` is $n (n - 1) \cdots (n - k + 1)$.
5. (B) Compute `Denumerable.lower' [2, 3, 7] 0` and check that `Denumerable.raise'` sends it back to `[2, 3, 7]`.
6. (C) Prove `Equiv.Perm.exists_map_finset_eq` from `Equiv.Perm.exists_extending_pair`: two finite sets of the same cardinality are images of each other under a permutation. Hint: compare the cardinalities of $\sigma(s)$ and $t$.

### Reference

<?reference?>
