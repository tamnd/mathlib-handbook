---
title: Association lists and finite maps
kind: theory
modules:
  - Mathlib.Data.List.Sigma
  - Mathlib.Data.List.AList
  - Mathlib.Data.Finmap
explains:
  E3: [List.NodupKeys, List.dlookup, List.mem_dlookup_iff, List.perm_dlookup, List.lookup_ext, List.kerase, List.kinsert, List.dlookup_kinsert_ne, List.kunion, List.dlookup_kunion_right, AList, AList.insert, AList.insert_insert_of_ne, Finmap, AList.toFinmap_eq, Finmap.ext_lookup, Finmap.union_comm_of_disjoint]
  E2: [List.keys, List.of_mem_dlookup, List.dlookup_kerase_ne, List.keys_kerase, List.kinsert_nodupKeys, List.dlookup_kinsert, List.dedupKeys, List.dlookup_dedupKeys, List.dlookup_kunion_left, List.NodupKeys.kunion, List.mem_ext, AList.lookup, AList.erase, AList.union, AList.lookup_insert, AList.lookup_union_left, AList.lookup_union_right, AList.union_assoc, AList.union_comm_of_disjoint, AList.insertRec, List.toAList, AList.toFinmap, Finmap.lookup, Finmap.induction_on, Finmap.insert, Finmap.insert_insert_of_ne, Finmap.union, Finmap.Disjoint, Finmap.lookup_union_left, Finmap.lookup_union_right, Finmap.union_assoc, Finmap.keysLookupEquiv]
  E1: auto
families: []
requires: [V01.C02, V03.C02, V03.C03, V33.C01, V33.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Association lists and finite maps

### Overview

A phone book sends names to numbers. It has finitely many entries, each name occurs once, and the order of the entries carries no meaning. The simplest data structure for such a map is a list of pairs. This section follows the three steps that Mathlib takes from a list of pairs to a mathematical finite map. The first step works on any list of pairs and defines the operations: lookup, erase, insert and union. The second step, `AList`, adds the condition that the keys are distinct. The third step, `Finmap`, forgets the order of the entries. At this step two maps with the same lookups become equal, and the laws of insertion and union hold as equalities.

The value type may depend on the key. A pair is an element of the sigma type `Sigma β`, written $\langle a, b \rangle$ with $a : \alpha$ and $b : \beta\,a$. In most examples $\beta$ is constant, for example `fun _ => ℕ`, and the dependence plays no role. All operations that compare keys need `[DecidableEq α]`.

### Definitions

**Definition (Keys and distinct keys).** For a list $l$ of pairs, `l.keys` is the list of first components, `l.map Sigma.fst`. The list has distinct keys, `l.NodupKeys`, if `l.keys` has no duplicate. A list with distinct keys has no duplicate pair, since two equal pairs have equal keys (`List.NodupKeys.nodup`).

**Definition (Lookup).** The function `List.dlookup a : List (Sigma β) → Option (β a)` returns the value of the first pair with key $a$: $$\operatorname{dlookup} a\,[\,] = \text{none}, \qquad \operatorname{dlookup} a\,(\langle a', b\rangle :: l) = \begin{cases} \text{some } b & \text{if } a' = a,\\ \operatorname{dlookup} a\, l & \text{otherwise.}\end{cases}$$ In the first case Lean must transport $b : \beta\,a'$ to $\beta\,a$ along the proof of $a' = a$. The letter d in the name stands for dependent.

**Definition (Erase, insert and union of lists).** The list `kerase a l` removes the first pair with key $a$; it is `eraseP (fun s => a = s.1) l`. The list `kinsert a b l` is $\langle a, b\rangle :: \operatorname{kerase} a\, l$: it removes the old pair and puts the new pair at the front. The union is defined by recursion on the first list: $$\operatorname{kunion}\,[\,]\,l_2 = l_2, \qquad \operatorname{kunion}\,(s :: l_1)\,l_2 = s :: \operatorname{kunion}\,l_1\,(\operatorname{kerase}\,s.1\,l_2).$$ Each pair of $l_1$ removes the pair with the same key from $l_2$, so the union is left biased. The list `dedupKeys l` is the right fold of `kinsert` over $l$; it keeps the first pair of each key.

**Definition (Association list).** An `AList β` is a structure with a field `entries : List (Sigma β)` and a field `nodupKeys : entries.NodupKeys`. Its operations act on the entries: `s.lookup a` is `s.entries.dlookup a`, `s.erase a` uses `kerase`, `s.insert a b` uses `kinsert`, and `s₁ ∪ s₂` uses `kunion`. Each operation carries a proof that the result again has distinct keys. Membership `a ∈ s` means `a ∈ s.keys`. Any list becomes an association list by `List.toAList`, which applies `dedupKeys`.

**Definition (Finite map).** A `Finmap β` is a structure with a field `entries : Multiset (Sigma β)` and a proof that the entries have distinct keys. The map `AList.toFinmap` sends an association list to the multiset of its entries. The docstring describes `Finmap` as effectively the quotient of `AList` by permutation of the entries: every finite map comes from an association list (`Finmap.induction_on`), and two association lists give the same finite map exactly when their entries are permutations of each other. All operations of `Finmap` (lookup, insert, erase, union) come from the operations on `AList` and a proof that they respect permutation.

On a list, equality sees the order of the entries, but no lookup can see it. A multiset hides the order, so the equality of finite maps matches their lookups.

### Theorems and proofs

**Theorem (Membership and lookup).** If $l$ has distinct keys, then $b \in \operatorname{dlookup} a\, l$ if and only if $\langle a, b\rangle \in l$. The direction from left to right holds without the hypothesis.

*Proof.* Induction on $l$. For $l = [\,]$ both sides are false. Let $l = \langle a', b'\rangle :: l'$. From left to right: if $a' = a$, the lookup is $\text{some } b'$, so $b = b'$ after the transport, and the pair $\langle a, b\rangle$ is the head of $l$. If $a' \neq a$, the lookup is $\operatorname{dlookup} a\, l'$, and the hypothesis of induction gives $\langle a, b\rangle \in l'$. From right to left, assume that $l$ has distinct keys and $\langle a, b\rangle \in l$. If the pair is the head, then $a' = a$ and the lookup is $\text{some } b$. Otherwise $\langle a, b\rangle \in l'$, so $a \in l'.\text{keys}$. Distinct keys give $a' \notin l'.\text{keys}$, hence $a' \neq a$. Then the lookup is $\operatorname{dlookup} a\, l'$, and $l'$ has distinct keys, so the hypothesis of induction gives $b \in \operatorname{dlookup} a\, l'$. $\square$

The hypothesis is necessary. For $l = [\langle 1, 10\rangle, \langle 1, 11\rangle]$ the pair $\langle 1, 11\rangle$ is in $l$, but the lookup of $1$ is $\text{some } 10$.

**Theorem (Lookup is invariant under permutation).** If $l_1$ has distinct keys and $l_1 \sim l_2$, then $\operatorname{dlookup} a\, l_1 = \operatorname{dlookup} a\, l_2$ for every key $a$.

*Proof.* A permutation does not change the multiset of keys, so $l_2$ also has distinct keys (`List.perm_nodupKeys`). For each $b$, the previous theorem and the permutation give $$b \in \operatorname{dlookup} a\, l_1 \iff \langle a, b\rangle \in l_1 \iff \langle a, b\rangle \in l_2 \iff b \in \operatorname{dlookup} a\, l_2.$$ Two values of type `Option (β a)` with the same members are equal. $\square$

**Theorem (Extensionality of lists with distinct keys).** If $l_0$ and $l_1$ have distinct keys and $b \in \operatorname{dlookup} a\, l_0 \iff b \in \operatorname{dlookup} a\, l_1$ for all $a$ and $b$, then $l_0 \sim l_1$.

*Proof.* For a pair $\langle a, b\rangle$, the theorem on membership gives $\langle a, b\rangle \in l_0 \iff b \in \operatorname{dlookup} a\, l_0 \iff b \in \operatorname{dlookup} a\, l_1 \iff \langle a, b\rangle \in l_1$. So $l_0$ and $l_1$ have the same members. Both lists have no duplicate, because they have distinct keys. Two lists without duplicates and with the same members are permutations of each other; this is `List.mem_ext` in the sigma file. $\square$

**Theorem (Insertion).** Let $l$ have distinct keys. Then `kinsert a b l` has distinct keys, its lookup at $a$ is $\text{some } b$, and its lookup at $a \neq a'$ is the lookup of $l$ for `kinsert a' b' l`.

*Proof.* First, the lookup after an erasure. For $a \neq a'$, $\operatorname{dlookup} a\,(\operatorname{kerase} a'\, l) = \operatorname{dlookup} a\, l$. Induction on $l$: if the head $s$ has $s.1 = a'$, the erasure gives the tail, and the lookup of $a$ skips $s$ because $s.1 = a' \neq a$. If $s.1 \neq a'$, the erasure keeps $s$ and erases in the tail, and both lookups test $s$ the same way and then use the hypothesis of induction. Second, the keys of `kerase a l` are `l.keys.erase a` (`List.keys_kerase`). If `l.keys` has no duplicate, then its erasure of $a$ has no duplicate and does not contain $a$. So the keys $a :: (l.\text{keys}.\text{erase } a)$ of `kinsert a b l` have no duplicate. The lookup of $a$ meets the head $\langle a, b\rangle$ at once. For $a \neq a'$, the lookup of $a$ in $\langle a', b'\rangle :: \operatorname{kerase} a'\, l$ skips the head and gives $\operatorname{dlookup} a\,(\operatorname{kerase} a'\, l) = \operatorname{dlookup} a\, l$ by the first step. $\square$

**Theorem (Lookup in a union).** For all lists $l_1$, $l_2$ and keys $a$: if $a \in l_1.\text{keys}$, then $\operatorname{dlookup} a\,(\operatorname{kunion} l_1\, l_2) = \operatorname{dlookup} a\, l_1$; if $a \notin l_1.\text{keys}$, then it equals $\operatorname{dlookup} a\, l_2$. No hypothesis on distinct keys is necessary.

*Proof.* Induction on $l_1$, for all $l_2$. For $l_1 = [\,]$, the key $a$ is not in the keys, and the union is $l_2$. Let $l_1 = s :: l$, so the union is $s :: \operatorname{kunion} l\,(\operatorname{kerase} s.1\, l_2)$. If $s.1 = a$, both lookups stop at the head $s$ and give the same value. If $s.1 \neq a$, both lookups skip $s$. When $a \in l.\text{keys}$, the hypothesis of induction for the list $\operatorname{kerase} s.1\, l_2$ gives $\operatorname{dlookup} a\, l$, which is the lookup in $s :: l$. When $a \notin l.\text{keys}$, then $a \notin (s :: l).\text{keys}$, and the hypothesis of induction gives $\operatorname{dlookup} a\,(\operatorname{kerase} s.1\, l_2)$. This equals $\operatorname{dlookup} a\, l_2$ by the lookup after an erasure, because $a \neq s.1$. $\square$

**Proposition (Insertions commute only up to permutation in AList).** For $a \neq a'$, the entries of `(s.insert a b).insert a' b'` and of `(s.insert a' b').insert a b` are permutations of each other. In general they are not equal.

*Proof.* Write $l$ for the entries of $s$. Since $a' \neq a$, the erasure of $a'$ does not remove the new head $\langle a, b\rangle$, so the first entries are $\langle a', b'\rangle :: \langle a, b\rangle :: \operatorname{kerase} a'(\operatorname{kerase} a\, l)$. In the same way the second entries are $\langle a, b\rangle :: \langle a', b'\rangle :: \operatorname{kerase} a(\operatorname{kerase} a'\, l)$. Two erasures commute (`List.kerase_comm`), so the tails are equal, and a swap of the two heads is a permutation. The example below shows two different lists. $\square$

**Theorem (Extensionality of finite maps).** If $s_1.\text{lookup}\ x = s_2.\text{lookup}\ x$ for every key $x$, then $s_1 = s_2$.

*Proof.* By `Finmap.induction_on` for both maps, $s_1$ and $s_2$ come from association lists $t_1$ and $t_2$. The lookup of a finite map from $t_i$ is the lookup of $t_i$, which is the `dlookup` of its entries. The hypothesis says that the entries of $t_1$ and of $t_2$ have equal lookups, so they have the same members of each lookup. Both entry lists have distinct keys, so the extensionality of lists gives a permutation. By `AList.toFinmap_eq`, a permutation of the entries gives equal finite maps. $\square$

**Corollary (Disjoint union commutes).** If $s_1$ and $s_2$ are disjoint, that is, no key of $s_1$ is a key of $s_2$, then $s_1 \cup s_2 = s_2 \cup s_1$.

*Proof.* By extensionality, fix a key $x$ and compare the lookups. If $x \in s_1$, then $x \notin s_2$ by disjointness. The left biased rule gives $\operatorname{lookup} x\,(s_1 \cup s_2) = \operatorname{lookup} x\, s_1$, and the right rule gives $\operatorname{lookup} x\,(s_2 \cup s_1) = \operatorname{lookup} x\, s_1$. If $x \notin s_1$ and $x \in s_2$, the two rules give $\operatorname{lookup} x\, s_2$ on both sides. If $x$ is in neither map, both lookups are $\text{none}$, since a lookup is $\text{none}$ exactly at the keys that are not members. $\square$

### Examples

**Example (Insert into an association list).** Take the entries $l = [\langle 1, 10\rangle, \langle 2, 20\rangle, \langle 3, 30\rangle]$ with values in $\mathbb{N}$. The lookup of $2$ tests the key $1$, then the key $2$, and returns $\text{some } 20$. The lookup of $4$ tests three keys and returns $\text{none}$. Insertion of $\langle 2, 25\rangle$ first erases $\langle 2, 20\rangle$, which gives $[\langle 1, 10\rangle, \langle 3, 30\rangle]$, and then puts the new pair in front: $[\langle 2, 25\rangle, \langle 1, 10\rangle, \langle 3, 30\rangle]$. The new pair moves to the front, the other pairs keep their order, and the length stays $3$. Erasure of $1$ from the original list gives $[\langle 2, 20\rangle, \langle 3, 30\rangle]$.

```lean
example : (List.kinsert 2 25 [⟨1, 10⟩, ⟨2, 20⟩, ⟨3, 30⟩] : List (Σ _ : ℕ, ℕ)) =
    [⟨2, 25⟩, ⟨1, 10⟩, ⟨3, 30⟩] := rfl
```

**Example (Union is left biased).** Let $l_1 = [\langle 1, 10\rangle, \langle 2, 20\rangle]$ and $l_2 = [\langle 2, 21\rangle, \langle 3, 30\rangle]$. The pair with key $1$ erases nothing from $l_2$. The pair with key $2$ erases $\langle 2, 21\rangle$. The rest of $l_2$ follows: $$\operatorname{kunion} l_1\, l_2 = [\langle 1, 10\rangle, \langle 2, 20\rangle, \langle 3, 30\rangle].$$ In the other order, $\langle 2, 21\rangle$ erases $\langle 2, 20\rangle$ from $l_1$, the pair $\langle 3, 30\rangle$ erases nothing, and $\operatorname{kunion} l_2\, l_1 = [\langle 2, 21\rangle, \langle 3, 30\rangle, \langle 1, 10\rangle]$. The lookup of $2$ gives $20$ in the first union and $21$ in the second. So union is not commutative when the key sets meet, and the corollary above needs disjointness.

**Example (Deduplication keeps the first pair).** For $l = [\langle 1, 10\rangle, \langle 1, 11\rangle]$, the right fold computes $\operatorname{kinsert} 1\ 10\,(\operatorname{kinsert} 1\ 11\, [\,]) = \operatorname{kinsert} 1\ 10\, [\langle 1, 11\rangle] = [\langle 1, 10\rangle]$. This agrees with the lookup: $\operatorname{dlookup} 1\, l = \text{some } 10$, and `List.dlookup_dedupKeys` says that deduplication never changes a lookup.

**Example (Two orders of insertion).** Insert $\langle 1, 10\rangle$ and then $\langle 2, 20\rangle$ into the empty association list. The entries are $[\langle 2, 20\rangle, \langle 1, 10\rangle]$. In the other order the entries are $[\langle 1, 10\rangle, \langle 2, 20\rangle]$. These are two different values of `AList`, because the equality of association lists is the equality of their entries. The two lists are permutations of each other, so `AList.toFinmap_eq` makes the two finite maps equal. This is the equality of `Finmap.insert_insert_of_ne`.

**Example (A dependent value type).** Let $\beta\,a = \text{Fin}(a + 1)$, so the value at the key $a$ is a number at most $a$. The list $[\langle 0, 0\rangle, \langle 2, 2\rangle]$ is an association list; the pair $\langle 0, 1\rangle$ is not even a term, since $1 \notin \text{Fin } 1$. A lookup of $2$ returns a term of $\text{Option}(\text{Fin } 3)$, and the transport in the definition of `dlookup` is what makes this type correct.

### The library around it

::: mathlib
`List.dlookup` · `Mathlib.Data.List.Sigma`

The lookup in a list of dependent pairs. The file has `of_mem_dlookup`, `mem_dlookup_iff` (with the hypothesis of distinct keys), `perm_dlookup` and `lookup_ext`. The function `lookupAll` returns all values of a key, and `kreplace` changes a value in place.

<?decl List.dlookup?>
:::

::: mathlib
`List.kunion` · `Mathlib.Data.List.Sigma`

The left biased union. The lemmas are `mem_keys_kunion`, `NodupKeys.kunion`, `dlookup_kunion_left` and `dlookup_kunion_right`, and the last two need no hypothesis on the keys.

<?decl List.kunion?>
:::

::: mathlib
`AList.insert_insert_of_ne` · `Mathlib.Data.List.AList`

Two insertions at different keys give entries that are permutations of each other, `~` and not `=`. The equality `AList.insert_insert` holds when both keys are equal: the second value wins.

<?decl AList.insert_insert_of_ne?>
:::

::: mathlib
`AList.insertRec` · `Mathlib.Data.List.AList`

The recursion principle of association lists: a property that holds for the empty list and passes from `s` to `s.insert a b` for a new key `a` holds for all association lists.

<?decl AList.insertRec?>
:::

::: mathlib
`Finmap.ext_lookup` · `Mathlib.Data.Finmap`

Two finite maps with the same lookups are equal. With it, `Finmap.union_assoc`, `Finmap.insert_insert_of_ne` and `Finmap.union_comm_of_disjoint` are equalities, and `Finmap.union_cancel` cancels a disjoint summand.

<?decl Finmap.ext_lookup?>
:::

::: mathlib
`Finmap.keysLookupEquiv` · `Mathlib.Data.Finmap`

A finite map is the same as a finset of keys together with a lookup function that is `some` exactly on the keys. This equivalence shows that `Finmap` is the finitely supported dependent function in another form.

<?decl Finmap.keysLookupEquiv?>
:::

Common errors of a learner: The first error is to state `mem_dlookup_iff` for a list with a repeated key; the lookup sees only the first pair. The second error is to expect `AList.insert_insert_of_ne` to be an equality; the entries of an association list keep their order, and only a permutation holds. The third error is to assume that `s₁ ∪ s₂ = s₂ ∪ s₁` holds for all finite maps; the union is left biased, and the law needs disjointness. The fourth error is to forget the transport in `dlookup` with a dependent value type, and to try to rewrite a value of type `β a'` as a value of type `β a` without the equality of keys. The fifth error is to define a function on `Finmap` by pattern matching on its entries; use `Finmap.liftOn` with a proof that the function respects permutation.

### Exercises

1. (A) Compute `kerase 2`, `kinsert 3 31` and the lookup of $3$ for the list $[\langle 3, 30\rangle, \langle 2, 20\rangle, \langle 3, 33\rangle]$. Say which of these lists have distinct keys. Hint: each erasure removes only the first pair with the key.
2. (A) Compute $\operatorname{kunion}\,[\langle 1, 1\rangle]\,[\langle 2, 2\rangle, \langle 1, 3\rangle, \langle 4, 4\rangle]$ step by step, and check the lookup rule at the keys $1$, $2$ and $5$. Hint: the first pair erases $\langle 1, 3\rangle$.
3. (A) Show that `dedupKeys` of a list with distinct keys is a permutation of the list. Hint: use the extensionality of lists with `List.dlookup_dedupKeys`.
4. (B) Prove that `kerase a` keeps distinct keys, with the formula for the keys of an erasure. Hint: a sublist of a list without duplicates has no duplicate.
5. (B) Prove that the union of finite maps is associative from the lookup rules and extensionality. Hint: compare the lookups of $x$ in three cases: $x \in s_1$; $x \notin s_1$ and $x \in s_2$; $x$ in neither.
6. (B) Prove that $s \cup \varnothing = s$ and $\varnothing \cup s = s$ for finite maps, and find a finite map $s$ and a key $a$ with $(s.\text{erase } a) \cup s = s$ but $s.\text{erase } a \neq s$. Hint: the lookups of the empty map are all `none`.
7. (C) Build the equivalence between finite maps and pairs of a finset $K$ and a function $f \colon (a : \alpha) \to \text{Option}(\beta\,a)$ with $f\,a$ defined exactly on $K$. Prove that the two maps are inverse. Hint: the inverse direction needs a list of the keys; use the finset and `Finmap.ext_lookup` for one composite.

### Notes and history

Association lists are among the oldest data structures of symbolic computation; the Lisp languages use them for environments that send names to values, and a left biased lookup models the shadowing of an old binding by a new one. Knuth treats search in an unordered list in Volume 3 of The Art of Computer Programming. A lookup in a list takes time proportional to the length of the list, so the search trees of the next section replace lists when the keys have an order.

The Mathlib files are by these authors, read from their headers: `Mathlib.Data.List.Sigma` by Mario Carneiro and Sean Leather, `Mathlib.Data.List.AList` by Sean Leather and Mario Carneiro, and `Mathlib.Data.Finmap` by Sean Leather and Mario Carneiro.

### Reference

<?reference?>
